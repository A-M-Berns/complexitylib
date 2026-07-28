/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseBoundsProof
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDecision
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseSpaceDefs
import Complexitylib.Models.TuringMachine.Hoare.Space
import
  Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# Fixed-register dense-simulator space proofs

This proof layer establishes a local all-prefix bound for every dense loop
segment, resets that bound at the canonical twenty-tape ABI between segments,
and composes initialization, execution, and verdict extraction.
-/

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

private theorem registerRead_nonzero_mem (overlay : Store) (address : ℕ)
    (hread : RegisterStore.read overlay address ≠ 0) :
    (address, RegisterStore.read overlay address) ∈ overlay := by
  induction overlay with
  | nil => simp [RegisterStore.read] at hread
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, storedTag⟩
      by_cases haddress : address = storedAddress
      · subst storedAddress
        simp [RegisterStore.read]
      · have hreadRest : RegisterStore.read rest address ≠ 0 := by
          simpa only [RegisterStore.read, haddress, ↓reduceIte] using hread
        have hmem := ih hreadRest
        simp only [RegisterStore.read, haddress, ↓reduceIte, List.mem_cons]
        exact Or.inr hmem

private theorem bitlen_pred_le (value : ℕ) :
    bitlen (value - 1) ≤ bitlen value := by
  unfold bitlen
  exact Nat.size_le_size (Nat.sub_le value 1)

private theorem snapshotBound_one_le_wordBits
    {snapshot : DenseOverlay.Snapshot} {entryBudget wordBits : ℕ}
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    1 ≤ wordBits := by
  have hread := hvalid.2
  change RegisterStore.read snapshot.overlay 0 ≠ 0 at hread
  have hmem := registerRead_nonzero_mem snapshot.overlay 0 hread
  have hwidth :
      bitlen (RegisterStore.read snapshot.overlay 0) ≤ wordBits := by
    simpa using (hbound.entries
      (0, RegisterStore.read snapshot.overlay 0) hmem).2
  have hpositive :
      1 ≤ bitlen (RegisterStore.read snapshot.overlay 0) := by
    unfold bitlen
    exact Nat.size_pos.mpr (Nat.pos_of_ne_zero hread)
  omega

private theorem snapshotBound_read_bitlen_le
    {input : List Bool} {snapshot : DenseOverlay.Snapshot}
    {entryBudget wordBits address : ℕ}
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    bitlen (DenseOverlay.read input snapshot.overlay address) ≤ wordBits := by
  have hone := snapshotBound_one_le_wordBits hvalid hbound
  unfold DenseOverlay.read
  by_cases htag : RegisterStore.read snapshot.overlay address = 0
  · rw [if_pos htag]
    by_cases hzero : address = 0
    · subst address
      exact (hvalid.2 htag).elim
    · simp only [RAM.initRegs, hzero, ↓reduceIte]
      split
      · split
        · simpa [bitlen] using hone
        · simp [bitlen]
      · simp [bitlen]
  · rw [if_neg htag]
    have hwidth :
        bitlen (RegisterStore.read snapshot.overlay address) ≤ wordBits := by
      simpa using (hbound.entries
        (address, RegisterStore.read snapshot.overlay address)
        (registerRead_nonzero_mem snapshot.overlay address htag)).2
    exact (bitlen_pred_le _).trans hwidth

private theorem snapshotBound_decode_bitlen_le
    {input : List Bool} {snapshot : DenseOverlay.Snapshot}
    {entryBudget wordBits : ℕ}
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    ∀ address, bitlen ((snapshot.decode input).regs address) ≤ wordBits := by
  intro address
  exact snapshotBound_read_bitlen_le hvalid hbound

private theorem snapshot_encodedStoreLength_le_encode
    (snapshot : DenseOverlay.Snapshot) :
    encodedStoreLength snapshot.overlay ≤ snapshot.encode.length := by
  unfold encodedStoreLength DenseOverlay.Snapshot.encode
    RegisterStore.Snapshot.encode
  simp only [List.length_append, List.length_flatMap]
  omega

private theorem binaryInstrResult_bitlen_le
    (op : BinaryInstrOp) (lhs rhs : ℕ) :
    bitlen (op.eval lhs rhs) ≤ bitlen lhs + bitlen rhs + 1 := by
  unfold bitlen
  cases op with
  | add =>
      exact le_trans (TM.binaryRippleAdd_sum_size_le lhs rhs) (by omega)
  | sub =>
      exact le_trans (Nat.size_le_size (Nat.sub_le lhs rhs)) (by omega)
  | mul =>
      exact le_trans (BinaryShiftMul.size_mul_le_add lhs rhs) (by omega)

private theorem selectedInstruction_staticWidth_le
    (program : Program) (selector : ℕ) :
    RegisterStore.Instr.staticWidth
        (selectedInstruction program selector) ≤
      programStaticWidth program := by
  induction program generalizing selector with
  | nil =>
      simp [selectedInstruction, RegisterStore.Instr.staticWidth,
        programStaticWidth]
  | cons instruction rest ih =>
      cases selector with
      | zero => simp [selectedInstruction, programStaticWidth]
      | succ selector =>
          exact (ih selector).trans (by simp [programStaticWidth])

private theorem denseStepWidth_le_fixed
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) (wordBits : ℕ)
    (hregs : ∀ address,
      bitlen ((snapshot.decode input).regs address) ≤ wordBits) :
    denseStepWidth program input snapshot ≤
      denseFixedStepWidth program wordBits := by
  let instruction := selectedInstruction program snapshot.pc
  have hstatic := selectedInstruction_staticWidth_le program snapshot.pc
  change RegisterStore.Instr.staticWidth instruction ≤
    programStaticWidth program at hstatic
  have hcost : instruction.logCost (snapshot.decode input) ≤
      programStaticWidth program + 4 * wordBits + 3 := by
    generalize hinstruction : instruction = current at hstatic ⊢
    cases current with
    | imm destination value =>
        simp only [RegisterStore.Instr.staticWidth, Instr.logCost]
          at hstatic ⊢
        omega
    | add destination source₀ source₁ =>
        simp only [Instr.logCost]
        have hlhs := hregs source₀
        have hrhs := hregs source₁
        have hresult := binaryInstrResult_bitlen_le .add
          ((snapshot.decode input).regs source₀)
          ((snapshot.decode input).regs source₁)
        simp only [BinaryInstrOp.eval] at hresult
        omega
    | sub destination source₀ source₁ =>
        simp only [Instr.logCost]
        have hlhs := hregs source₀
        have hrhs := hregs source₁
        omega
    | mul destination source₀ source₁ =>
        simp only [Instr.logCost]
        have hlhs := hregs source₀
        have hrhs := hregs source₁
        have hresult := binaryInstrResult_bitlen_le .mul
          ((snapshot.decode input).regs source₀)
          ((snapshot.decode input).regs source₁)
        simp only [BinaryInstrOp.eval] at hresult
        omega
    | load destination addressRegister =>
        simp only [Instr.logCost]
        have haddress := hregs addressRegister
        have hvalue := hregs ((snapshot.decode input).regs addressRegister)
        omega
    | store addressRegister source =>
        simp only [Instr.logCost]
        have haddress := hregs addressRegister
        have hvalue := hregs source
        omega
    | jz source target =>
        simp only [Instr.logCost]
        have hvalue := hregs source
        omega
    | jmp target => simp [Instr.logCost]
    | halt => simp [Instr.logCost]
  unfold denseStepWidth RAM.stepLogCost RAM.curInstr
  simp only [DenseOverlay.Snapshot.decode]
  rw [← selectedInstruction_eq_getElem?_getD]
  change programStaticWidth program + instruction.logCost
      (snapshot.decode input) + 1 ≤ _
  simpa only [denseFixedStepWidth] using (show
    programStaticWidth program + instruction.logCost
        (snapshot.decode input) + 1 ≤
      2 * programStaticWidth program + 4 * wordBits + 4 by omega)

private theorem denseProgramLoopIterationTime_le_fixedSpace
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) (entryBudget wordBits : ℕ)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hpc : snapshot.pc ≤ programResourceMagnitude program)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    denseProgramLoopIterationTime standardControlInstructionTapes
        program input snapshot + 1 ≤
      denseFixedIterationSpace program input.length entryBudget wordBits := by
  have hraw := denseProgramLoopIterationTime_le_product_internal
    standardControlInstructionTapes program input snapshot hvalid hpc
  have hcode : encodedStoreLength snapshot.overlay ≤
      DenseOverlay.FixedRegisters.codeBudget entryBudget wordBits :=
    (snapshot_encodedStoreLength_le_encode snapshot).trans
      hbound.encode_length_le
  have hwidth := denseStepWidth_le_fixed program input snapshot wordBits
    (snapshotBound_decode_bitlen_le hvalid hbound)
  have hvolume :
      denseStepVolume program input snapshot ≤
        DenseOverlay.FixedRegisters.codeBudget entryBudget wordBits +
          input.length + denseFixedStepWidth program wordBits + 1 := by
    unfold denseStepVolume
    omega
  have hproduct := Nat.mul_le_mul
    (Nat.mul_le_mul_left
      (2000000000 * (programResourceMagnitude program + 1) ^ 2)
      hvolume)
    (Nat.add_le_add_right hwidth 1)
  unfold denseFixedIterationSpace
  omega

private theorem denseProgramOutputTime_le_fixedSpace
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (entryBudget wordBits : ℕ)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    denseProgramOutputTime standardControlInstructionTapes input
        snapshot.overlay + 1 ≤
      denseFixedOutputSpace input.length entryBudget wordBits := by
  have hraw := denseProgramOutputTime_le_encoded_internal
    standardControlInstructionTapes input snapshot.overlay hvalid
  have hcode : encodedStoreLength snapshot.overlay ≤
      DenseOverlay.FixedRegisters.codeBudget entryBudget wordBits :=
    (snapshot_encodedStoreLength_le_encode snapshot).trans
      hbound.encode_length_le
  unfold denseFixedOutputSpace
  omega

private theorem denseSnapshot_run_pc_le_resourceMagnitude
    (program : Program) (input : List Bool) :
    ∀ (fuel : ℕ) (snapshot : DenseOverlay.Snapshot),
      snapshot.pc ≤ programResourceMagnitude program →
      (snapshot.run program input fuel).pc ≤
        programResourceMagnitude program
  | 0, _, hpc => hpc
  | fuel + 1, snapshot, hpc => by
      rw [DenseOverlay.Snapshot.run]
      split
      · exact hpc
      · exact denseSnapshot_run_pc_le_resourceMagnitude program input fuel
          (snapshot.step program input)
          (denseSnapshot_step_pc_le_resourceMagnitude_internal
            program input snapshot hpc)

set_option linter.unusedSimpArgs false in
private theorem standardInstructionExecutionReady_head
    {store : Store} {pcValue : ℕ} {work : Fin 20 → Tape}
    (hready : InstructionExecutionReady standardControlInstructionTapes
      store pcValue work) :
    ∀ i, (work i).head = 1 := by
  intro i
  fin_cases i
  all_goals
    simp only [standardControlInstructionTapes,
      ControlInstructionTapes.lifted,
      ControlInstructionTapes.liftedPC,
      ControlInstructionTapes.liftedLhs,
      ControlInstructionTapes.liftedSource,
      ControlInstructionTapes.buffer,
      BinaryInstructionTapes.lhsLookup,
      BinaryInstructionTapes.lhsLookupSlot,
      EntryLookupRestoreTapes.scan, EntryScanTapes.entry,
      EntryMatchTapes.source, EntryMatchTapes.address,
      EntryMatchTapes.value, EntryMatchTapes.addressCounter,
      EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
      EntryMatchTapes.valueWidth, EntryMatchTapes.query,
      EntryMatchTapes.result, EntryScanTapes.count,
      EntryLookupRestoreTapes.countSource,
      EntryLookupRestoreTapes.querySource,
      EntryLookupRestoreTapes.destination,
      EntryLookupRestoreTapes.copyScratch,
      BinaryInstructionTapes.rhs, EntryUpdateTapes.replacement,
      BinaryInstructionTapes.tmp, BinaryInstructionTapes.dbl]
      at hready ⊢
  · exact hready.control.lookup.sourceHead
  · exact hready.control.lookup.scanner.address.1
  · exact hready.control.lookup.scanner.value.1
  · exact hready.control.lookup.scanner.addressCounter.2.1
  · exact hready.control.lookup.scanner.addressWidth.2.1
  · exact hready.control.lookup.scanner.valueCounter.2.1
  · exact hready.control.lookup.scanner.valueWidth.2.1
  · exact hready.control.lookup.scanner.query.1
  · exact hready.control.lookup.scanner.result.1
  · exact hready.control.lookup.count.2.1
  · exact hready.replacement.2.1
  · exact hready.control.lookup.copyScratch.2.1
  · exact hready.control.lookup.countSource.2.1
  · exact hready.control.lookup.destination.2.1
  · exact hready.rhs.2.1
  · exact hready.control.lookup.querySource.2.1
  · exact hready.tmp.2.1
  · exact hready.dbl.2.1
  · exact hready.control.pc.2.1
  · have h := congrArg Tape.head hready.buffer
    simpa [Tape.move] using h

private theorem standardLoopStart_withinAuxSpace
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) (work : Fin 20 → Tape)
    (hready : InstructionExecutionReady standardControlInstructionTapes
      snapshot.overlay snapshot.pc work) :
    ({ state :=
        (denseProgramLoopTM standardControlInstructionTapes program).qstart
       input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
       work := work
       output := (Tape.init []).move Dir3.right } :
      Complexity.Cfg 20
        (denseProgramLoopTM standardControlInstructionTapes program).Q
    ).WithinAuxSpace input.length 1 := by
  constructor
  · intro i
    rw [standardInstructionExecutionReady_head hready i]
  · simp [Tape.move]

/-- A local Hoare-style contract for the otherwise uncharged output head. -/
private def HoareOutputHead {n : ℕ} (tm : TM n) (pre : TM.TapePred n)
    (bound : ℕ) : Prop :=
  ∀ inp work out, pre inp work out →
    ∀ cfg, tm.reaches
      { state := tm.qstart, input := inp, work := work, output := out } cfg →
      cfg.output.head ≤ bound

private theorem HoareOutputHead.mono {n : ℕ} {tm : TM n}
    {pre : TM.TapePred n} {bound bound' : ℕ}
    (h : HoareOutputHead tm pre bound) (hle : bound ≤ bound') :
    HoareOutputHead tm pre bound' := by
  intro inp work out hpre cfg hreach
  exact (h inp work out hpre cfg hreach).trans hle

private theorem hoareOutputHead_of_hoareTime {n : ℕ} {tm : TM n}
    {pre post : TM.TapePred n} {time initialHead : ℕ}
    (htime : tm.HoareTime pre post time)
    (hinitial : ∀ inp work out, pre inp work out →
      out.head ≤ initialHead) :
    HoareOutputHead tm pre (initialHead + time) := by
  intro inp work out hpre cfg hreach
  obtain ⟨done, doneTime, hdoneTime, hdoneReach, hdoneHalted, _hpost⟩ :=
    htime inp work out hpre
  obtain ⟨steps, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  have hsteps : steps ≤ doneTime :=
    tm.reachesIn_le_halt hreachIn hdoneReach hdoneHalted
  have hhead := tm.output_head_reachesIn_bound hreachIn
  change cfg.output.head ≤ out.head + steps at hhead
  have hinitialHead := hinitial inp work out hpre
  omega

private theorem seqTM_hoareOutputHead {n : ℕ} (tm₁ tm₂ : TM n)
    {pre mid mid' post : TM.TapePred n}
    {time₁ time₂ bound₁ bound₂ : ℕ}
    (htime₁ : tm₁.HoareTime pre mid time₁)
    (htrans : ∀ inp work out, mid inp work out →
      mid' (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i))
        (TM.transitionTape out))
    (htime₂ : tm₂.HoareTime mid' post time₂)
    (houtput₁ : HoareOutputHead tm₁ pre bound₁)
    (houtput₂ : HoareOutputHead tm₂ mid' bound₂) :
    HoareOutputHead (TM.seqTM tm₁ tm₂) pre (max bound₁ bound₂) := by
  intro inp work out hpre cfg hreach
  obtain ⟨cfg₁, time₁', _htime₁', hreach₁, hhalted₁, hmid⟩ :=
    htime₁ inp work out hpre
  have hmid' := htrans cfg₁.input cfg₁.work cfg₁.output hmid
  obtain ⟨cfg₂, time₂', _htime₂', hreach₂, hhalted₂, _hpost⟩ :=
    htime₂ (TM.transitionInput cfg₁.input)
      (fun i => TM.transitionTape (cfg₁.work i))
      (TM.transitionTape cfg₁.output) hmid'
  have hfull := TM.seqTM_reachesIn_of_reachesIn tm₁ tm₂
    hreach₁ hhalted₁ hreach₂
  have hfullHalted :
      (TM.seqTM tm₁ tm₂).halted (TM.phase2Wrap tm₁ tm₂ cfg₂) :=
    (TM.phase2Wrap_halted_iff tm₁ tm₂ cfg₂).2 hhalted₂
  obtain ⟨time, hreachIn⟩ :=
    (TM.seqTM tm₁ tm₂).reaches_to_reachesIn hreach
  have htime : time ≤ time₁' + 1 + time₂' :=
    (TM.seqTM tm₁ tm₂).reachesIn_le_halt
      hreachIn hfull hfullHalted
  by_cases hphase₁ : time ≤ time₁'
  · obtain ⟨partialCfg, hprefix, _hsuffix⟩ :=
      TM.reachesIn_prefix_internal hreach₁ hphase₁
    have hwrapped := TM.seqTM_reachesIn_phase1Wrap tm₁ tm₂ hprefix
    have hwrapped' :
        (TM.seqTM tm₁ tm₂).reachesIn time
          { state := (TM.seqTM tm₁ tm₂).qstart,
            input := inp, work := work, output := out }
          (TM.phase1Wrap tm₁ tm₂ partialCfg) := by
      simpa [TM.phase1Wrap, TM.seqTM] using hwrapped
    have hcfg : cfg = TM.phase1Wrap tm₁ tm₂ partialCfg :=
      (TM.seqTM tm₁ tm₂).reachesIn_right_unique hreachIn hwrapped'
    rw [hcfg]
    exact (houtput₁ inp work out hpre partialCfg
      (TM.reaches_of_reachesIn hprefix)).trans (le_max_left _ _)
  · have hphase₂ : time₁' + 1 ≤ time := by omega
    let tailTime := time - (time₁' + 1)
    have htailTime : tailTime ≤ time₂' := by
      dsimp only [tailTime]
      omega
    obtain ⟨partialCfg, hprefix, _hsuffix⟩ :=
      TM.reachesIn_prefix_internal hreach₂ htailTime
    have hwrapped := TM.seqTM_reachesIn_of_reachesIn tm₁ tm₂
      hreach₁ hhalted₁ hprefix
    have htimeEq : time₁' + 1 + tailTime = time := by
      dsimp only [tailTime]
      omega
    rw [htimeEq] at hwrapped
    have hcfg : cfg = TM.phase2Wrap tm₁ tm₂ partialCfg :=
      (TM.seqTM tm₁ tm₂).reachesIn_right_unique hreachIn hwrapped
    rw [hcfg]
    exact (houtput₂ (TM.transitionInput cfg₁.input)
      (fun i => TM.transitionTape (cfg₁.work i))
      (TM.transitionTape cfg₁.output) hmid' partialCfg
      (TM.reaches_of_reachesIn hprefix)).trans (le_max_right _ _)

private theorem denseProgramLoopTM_hoareSpace_from
    (program : Program) (input : List Bool)
    (entryBudget wordBits : ℕ) :
    ∀ (fuel : ℕ) (snapshot : DenseOverlay.Snapshot)
      (initialWork : Fin 20 → Tape),
      DenseOverlay.Valid snapshot.overlay →
      InstructionExecutionReady standardControlInstructionTapes
        snapshot.overlay snapshot.pc initialWork →
      snapshot.pc ≤ programResourceMagnitude program →
      (snapshot.run program input fuel).Halted program →
      (∀ k, k ≤ fuel →
        DenseOverlay.FixedRegisters.SnapshotBound
          (snapshot.run program input k) entryBudget wordBits) →
      (denseProgramLoopTM standardControlInstructionTapes program).HoareSpace
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          work = initialWork ∧
          out = (Tape.init []).move Dir3.right)
        input.length
        (denseFixedIterationSpace program input.length entryBudget wordBits) := by
  intro fuel
  induction fuel with
  | zero =>
      intro snapshot initialWork hvalid hready hpc hhalted htrace inp work out hpre cfg hreach
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      have hsnapshotHalted : snapshot.Halted program := by
        simpa [DenseOverlay.Snapshot.run] using hhalted
      have hstepSelf := denseSnapshot_step_eq_self_of_halted_internal
        program input snapshot hsnapshotHalted
      obtain ⟨nextWork, time, htime, hnextReady, hbranch⟩ :=
        denseProgramLoopTM_iteration_internal
          standardControlInstructionTapes program input snapshot
          initialWork hvalid hready
      rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
          ⟨hnextRunning, _hsegment⟩
      · obtain ⟨steps, hreachIn⟩ :=
          (denseProgramLoopTM standardControlInstructionTapes program
            ).reaches_to_reachesIn hreach
        have hsegmentHalted :
            (denseProgramLoopTM standardControlInstructionTapes program
              ).halted
              { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                work := nextWork
                output := instructionHaltOutput
                  ((snapshot.step program input).curInstr program) } := by
          rfl
        have hsteps : steps ≤ time :=
          (denseProgramLoopTM standardControlInstructionTapes program
            ).reachesIn_le_halt hreachIn hsegment hsegmentHalted
        have hbound := htrace 0 (by omega)
        have hlocal :=
          denseProgramLoopIterationTime_le_fixedSpace
            program input snapshot entryBudget wordBits hvalid
              hpc hbound
        have hstart :=
          standardLoopStart_withinAuxSpace program input snapshot initialWork
            hready
        exact (hstart.reachesIn hreachIn).mono le_rfl (by omega)
      · exact (hnextRunning (by simpa only [hstepSelf] using
          hsnapshotHalted)).elim
  | succ fuel ih =>
      intro snapshot initialWork hvalid hready hpc hhalted htrace inp work out hpre cfg hreach
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      by_cases hsnapshotHalted : snapshot.Halted program
      · have hstepSelf := denseSnapshot_step_eq_self_of_halted_internal
          program input snapshot hsnapshotHalted
        obtain ⟨nextWork, time, htime, hnextReady, hbranch⟩ :=
          denseProgramLoopTM_iteration_internal
            standardControlInstructionTapes program input snapshot
            initialWork hvalid hready
        rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
            ⟨hnextRunning, _hsegment⟩
        · obtain ⟨steps, hreachIn⟩ :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).reaches_to_reachesIn hreach
          have hsegmentHalted :
              (denseProgramLoopTM standardControlInstructionTapes program
                ).halted
                { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                  input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                  work := nextWork
                  output := instructionHaltOutput
                    ((snapshot.step program input).curInstr program) } := by
            rfl
          have hsteps : steps ≤ time :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).reachesIn_le_halt hreachIn hsegment hsegmentHalted
          have hbound := htrace 0 (by omega)
          have hlocal :=
            denseProgramLoopIterationTime_le_fixedSpace
              program input snapshot entryBudget wordBits hvalid hpc hbound
          have hstart :=
            standardLoopStart_withinAuxSpace program input snapshot initialWork
              hready
          exact (hstart.reachesIn hreachIn).mono le_rfl (by omega)
        · exact (hnextRunning (by simpa only [hstepSelf] using
            hsnapshotHalted)).elim
      · have hrunHalted :
            ((snapshot.step program input).run program input fuel).Halted
              program := by
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hhalted
        obtain ⟨nextWork, time, htime, hnextReady, hbranch⟩ :=
          denseProgramLoopTM_iteration_internal
            standardControlInstructionTapes program input snapshot
            initialWork hvalid hready
        have hbound := htrace 0 (by omega)
        have hlocal :=
          denseProgramLoopIterationTime_le_fixedSpace
            program input snapshot entryBudget wordBits hvalid hpc hbound
        have hstart :=
          standardLoopStart_withinAuxSpace program input snapshot initialWork
            hready
        obtain ⟨steps, hreachIn⟩ :=
          (denseProgramLoopTM standardControlInstructionTapes program
            ).reaches_to_reachesIn hreach
        rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
            ⟨hnextRunning, hsegment⟩
        · have hsegmentHalted :
              (denseProgramLoopTM standardControlInstructionTapes program
                ).halted
                { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                  input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                  work := nextWork
                  output := instructionHaltOutput
                    ((snapshot.step program input).curInstr program) } := by
            rfl
          have hsteps : steps ≤ time :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).reachesIn_le_halt hreachIn hsegment hsegmentHalted
          exact (hstart.reachesIn hreachIn).mono le_rfl (by omega)
        · by_cases hprefix : steps ≤ time
          · exact (hstart.reachesIn hreachIn).mono le_rfl (by omega)
          · have htimeSteps : time ≤ steps := by omega
            let tailTime := steps - time
            have htimeEq : time + tailTime = steps :=
              Nat.add_sub_of_le htimeSteps
            have hreachSplit :
                (denseProgramLoopTM standardControlInstructionTapes program
                  ).reachesIn (time + tailTime)
                    { state :=
                        (denseProgramLoopTM
                          standardControlInstructionTapes program).qstart
                      input :=
                        (Tape.init (input.map Γ.ofBool)).move Dir3.right
                      work := initialWork
                      output := (Tape.init []).move Dir3.right }
                    cfg := by
              simpa only [htimeEq] using hreachIn
            obtain ⟨boundary, hfirst, htail⟩ :=
              TM.reachesIn_split_internal hreachSplit
            have hboundary :
                boundary =
                  { state :=
                      (denseProgramLoopTM
                        standardControlInstructionTapes program).qstart
                    input :=
                      (Tape.init (input.map Γ.ofBool)).move Dir3.right
                    work := nextWork
                    output := (Tape.init []).move Dir3.right } :=
              (denseProgramLoopTM standardControlInstructionTapes program
                ).reachesIn_right_unique hfirst hsegment
            subst boundary
            have hnextValid :=
              DenseOverlay.Snapshot.step_valid program input snapshot hvalid
            have htailTrace :
                ∀ k, k ≤ fuel →
                  DenseOverlay.FixedRegisters.SnapshotBound
                    ((snapshot.step program input).run program input k)
                    entryBudget wordBits := by
              intro k hk
              have hk' : k + 1 ≤ fuel + 1 := by omega
              have hbound' := htrace (k + 1) hk'
              simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hbound'
            have hrecursive := ih (snapshot.step program input) nextWork
              hnextValid hnextReady
              (denseSnapshot_step_pc_le_resourceMagnitude_internal
                program input snapshot hpc)
              hrunHalted htailTrace
            exact hrecursive _ _ _ ⟨rfl, rfl, rfl⟩ cfg
              (TM.reaches_of_reachesIn htail)

private theorem denseProgramLoopTM_hoareOutputHead_from
    (program : Program) (input : List Bool)
    (entryBudget wordBits : ℕ) :
    ∀ (fuel : ℕ) (snapshot : DenseOverlay.Snapshot)
      (initialWork : Fin 20 → Tape),
      DenseOverlay.Valid snapshot.overlay →
      InstructionExecutionReady standardControlInstructionTapes
        snapshot.overlay snapshot.pc initialWork →
      snapshot.pc ≤ programResourceMagnitude program →
      (snapshot.run program input fuel).Halted program →
      (∀ k, k ≤ fuel →
        DenseOverlay.FixedRegisters.SnapshotBound
          (snapshot.run program input k) entryBudget wordBits) →
      HoareOutputHead
        (denseProgramLoopTM standardControlInstructionTapes program)
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          work = initialWork ∧
          out = (Tape.init []).move Dir3.right)
        (denseFixedIterationSpace program input.length entryBudget wordBits) := by
  intro fuel
  induction fuel with
  | zero =>
      intro snapshot initialWork hvalid hready hpc hhalted htrace inp work out hpre cfg hreach
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      have hsnapshotHalted : snapshot.Halted program := by
        simpa [DenseOverlay.Snapshot.run] using hhalted
      have hstepSelf := denseSnapshot_step_eq_self_of_halted_internal
        program input snapshot hsnapshotHalted
      obtain ⟨nextWork, time, _htime, _hnextReady, hbranch⟩ :=
        denseProgramLoopTM_iteration_internal
          standardControlInstructionTapes program input snapshot
          initialWork hvalid hready
      rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
          ⟨hnextRunning, _hsegment⟩
      · obtain ⟨steps, hreachIn⟩ :=
          (denseProgramLoopTM standardControlInstructionTapes program
            ).reaches_to_reachesIn hreach
        have hsegmentHalted :
            (denseProgramLoopTM standardControlInstructionTapes program
              ).halted
              { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                work := nextWork
                output := instructionHaltOutput
                  ((snapshot.step program input).curInstr program) } := by
          rfl
        have hsteps : steps ≤ time :=
          (denseProgramLoopTM standardControlInstructionTapes program
            ).reachesIn_le_halt hreachIn hsegment hsegmentHalted
        have hbound := htrace 0 (by omega)
        have hlocal :=
          denseProgramLoopIterationTime_le_fixedSpace
            program input snapshot entryBudget wordBits hvalid hpc hbound
        have hhead :=
          (denseProgramLoopTM standardControlInstructionTapes program
            ).output_head_reachesIn_bound hreachIn
        change cfg.output.head ≤
          ((Tape.init []).move Dir3.right).head + steps at hhead
        simp only [Tape.move, Tape.init] at hhead
        omega
      · exact (hnextRunning (by simpa only [hstepSelf] using
          hsnapshotHalted)).elim
  | succ fuel ih =>
      intro snapshot initialWork hvalid hready hpc hhalted htrace inp work out hpre cfg hreach
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      by_cases hsnapshotHalted : snapshot.Halted program
      · have hstepSelf := denseSnapshot_step_eq_self_of_halted_internal
          program input snapshot hsnapshotHalted
        obtain ⟨nextWork, time, _htime, _hnextReady, hbranch⟩ :=
          denseProgramLoopTM_iteration_internal
            standardControlInstructionTapes program input snapshot
            initialWork hvalid hready
        rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
            ⟨hnextRunning, _hsegment⟩
        · obtain ⟨steps, hreachIn⟩ :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).reaches_to_reachesIn hreach
          have hsegmentHalted :
              (denseProgramLoopTM standardControlInstructionTapes program
                ).halted
                { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                  input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                  work := nextWork
                  output := instructionHaltOutput
                    ((snapshot.step program input).curInstr program) } := by
            rfl
          have hsteps : steps ≤ time :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).reachesIn_le_halt hreachIn hsegment hsegmentHalted
          have hbound := htrace 0 (by omega)
          have hlocal :=
            denseProgramLoopIterationTime_le_fixedSpace
              program input snapshot entryBudget wordBits hvalid hpc hbound
          have hhead :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).output_head_reachesIn_bound hreachIn
          change cfg.output.head ≤
            ((Tape.init []).move Dir3.right).head + steps at hhead
          simp only [Tape.move, Tape.init] at hhead
          omega
        · exact (hnextRunning (by simpa only [hstepSelf] using
            hsnapshotHalted)).elim
      · have hrunHalted :
            ((snapshot.step program input).run program input fuel).Halted
              program := by
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hhalted
        obtain ⟨nextWork, time, _htime, hnextReady, hbranch⟩ :=
          denseProgramLoopTM_iteration_internal
            standardControlInstructionTapes program input snapshot
            initialWork hvalid hready
        have hbound := htrace 0 (by omega)
        have hlocal :=
          denseProgramLoopIterationTime_le_fixedSpace
            program input snapshot entryBudget wordBits hvalid hpc hbound
        obtain ⟨steps, hreachIn⟩ :=
          (denseProgramLoopTM standardControlInstructionTapes program
            ).reaches_to_reachesIn hreach
        rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
            ⟨_hnextRunning, hsegment⟩
        · have hsegmentHalted :
              (denseProgramLoopTM standardControlInstructionTapes program
                ).halted
                { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                  input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
                  work := nextWork
                  output := instructionHaltOutput
                    ((snapshot.step program input).curInstr program) } := by
            rfl
          have hsteps : steps ≤ time :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).reachesIn_le_halt hreachIn hsegment hsegmentHalted
          have hhead :=
            (denseProgramLoopTM standardControlInstructionTapes program
              ).output_head_reachesIn_bound hreachIn
          change cfg.output.head ≤
            ((Tape.init []).move Dir3.right).head + steps at hhead
          simp only [Tape.move, Tape.init] at hhead
          omega
        · by_cases hprefix : steps ≤ time
          · have hhead :=
              (denseProgramLoopTM standardControlInstructionTapes program
                ).output_head_reachesIn_bound hreachIn
            change cfg.output.head ≤
              ((Tape.init []).move Dir3.right).head + steps at hhead
            simp only [Tape.move, Tape.init] at hhead
            omega
          · have htimeSteps : time ≤ steps := by omega
            let tailTime := steps - time
            have htimeEq : time + tailTime = steps :=
              Nat.add_sub_of_le htimeSteps
            have hreachSplit :
                (denseProgramLoopTM standardControlInstructionTapes program
                  ).reachesIn (time + tailTime)
                    { state :=
                        (denseProgramLoopTM
                          standardControlInstructionTapes program).qstart
                      input :=
                        (Tape.init (input.map Γ.ofBool)).move Dir3.right
                      work := initialWork
                      output := (Tape.init []).move Dir3.right }
                    cfg := by
              simpa only [htimeEq] using hreachIn
            obtain ⟨boundary, hfirst, htail⟩ :=
              TM.reachesIn_split_internal hreachSplit
            have hboundary :
                boundary =
                  { state :=
                      (denseProgramLoopTM
                        standardControlInstructionTapes program).qstart
                    input :=
                      (Tape.init (input.map Γ.ofBool)).move Dir3.right
                    work := nextWork
                    output := (Tape.init []).move Dir3.right } :=
              (denseProgramLoopTM standardControlInstructionTapes program
                ).reachesIn_right_unique hfirst hsegment
            subst boundary
            have hnextValid :=
              DenseOverlay.Snapshot.step_valid program input snapshot hvalid
            have htailTrace :
                ∀ k, k ≤ fuel →
                  DenseOverlay.FixedRegisters.SnapshotBound
                    ((snapshot.step program input).run program input k)
                    entryBudget wordBits := by
              intro k hk
              have hk' : k + 1 ≤ fuel + 1 := by omega
              have hbound' := htrace (k + 1) hk'
              simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hbound'
            have hrecursive := ih (snapshot.step program input) nextWork
              hnextValid hnextReady
              (denseSnapshot_step_pc_le_resourceMagnitude_internal
                program input snapshot hpc)
              hrunHalted htailTrace
            exact hrecursive _ _ _ ⟨rfl, rfl, rfl⟩ cfg
              (TM.reaches_of_reachesIn htail)

private theorem denseProgramLoopTM_hoareOutputHead_traceBound
    (program : Program) (input : List Bool) (fuel entryBudget wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel entryBudget wordBits) :
    HoareOutputHead
      (denseProgramLoopTM standardControlInstructionTapes program)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork standardControlInstructionTapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = (Tape.init []).move Dir3.right)
      (denseFixedIterationSpace program input.length entryBudget wordBits) := by
  let initial := DenseOverlay.Snapshot.initial input
  let initialWork :=
    denseProgramSnapshotWork standardControlInstructionTapes initial
  have hvalid : DenseOverlay.Valid initial.overlay := by
    simpa only [initial] using DenseOverlay.Snapshot.initial_valid input
  let sparseInitial : Snapshot :=
    { pc := initial.pc, store := initial.overlay }
  have hready :
      InstructionExecutionReady standardControlInstructionTapes
        initial.overlay initial.pc initialWork := by
    dsimp only [initialWork]
    simpa only [denseProgramSnapshotWork, sparseInitial] using
      programSnapshotWork_ready_internal standardControlInstructionTapes
        sparseInitial hvalid.1
  have hpc : initial.pc ≤ programResourceMagnitude program := by
    dsimp only [initial, DenseOverlay.Snapshot.initial]
    exact Nat.zero_le _
  have htrace :
      ∀ k, k ≤ fuel →
        DenseOverlay.FixedRegisters.SnapshotBound
          (initial.run program input k) entryBudget wordBits := by
    simpa only [DenseOverlay.FixedRegisters.TraceBound, initial] using hbound
  simpa only [initial, initialWork] using
    denseProgramLoopTM_hoareOutputHead_from
      program input entryBudget wordBits fuel initial initialWork
        hvalid hready hpc (by simpa only [initial] using hhalted) htrace

private theorem copyWorkToWorkTM_isTransducer
    {n : ℕ} (source destination : Fin n) :
    (TM.copyWorkToWorkTM source destination).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> dsimp only [TM.copyWorkToWorkTM, TM.allIdle]
  · split <;> simp only [TM.idleDir] <;> split <;> decide
  · simp only [TM.idleDir]
    split <;> decide

private theorem rewindInputTM_isTransducer {n : ℕ} :
    (TM.rewindInputTM (n := n)).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> simp only [TM.rewindInputTM]
  · split <;> simp only [TM.idleDir] <;> split <;> decide
  · simp only [TM.idleDir]
    split <;> decide
  · simp only [TM.allIdle, TM.idleDir]
    split <;> decide

private theorem denseProgramInitTM_isTransducer
    {n : ℕ} (tapes : ControlInstructionTapes n) :
    (denseProgramInitTM tapes).IsTransducer := by
  have hemit :
      (initialLengthEmitTM tapes).IsTransducer :=
    (TM.retargetOutput_isTransducer
      (rewindEntryEncodeRestoreTM (initialLengthEntryTapes tapes))).seqTM
        (TM.binarySuccTM_isTransducer
          tapes.lifted.data.update.remaining)
  have habi :
      (initialAbiInstallTM tapes).IsTransducer :=
    (TM.binaryCopyIntoTM_isTransducer
      tapes.lifted.data.update.remaining
      tapes.lifted.data.update.resultCount
      tapes.lifted.data.update.found).seqTM
        ((TM.rewindWorkTM_isTransducer tapes.buffer).seqTM
          ((copyWorkToWorkTM_isTransducer
            tapes.buffer tapes.liftedSource).seqTM
            ((TM.rewindWorkTM_isTransducer tapes.liftedSource).seqTM
              ((TM.resetBinaryWorkTM_isTransducer tapes.buffer).seqTM
                (TM.resetBinaryWorkManyTM_isTransducer
                  (initialCleanupTargets tapes))))))
  exact (TM.binaryLengthTM_isTransducer tapes.liftedLhs).seqTM
    ((TM.binarySuccTM_isTransducer tapes.liftedLhs).seqTM
      ((TM.binarySuccTM_isTransducer tapes.lifted.data.rhs).seqTM
        (hemit.seqTM (habi.seqTM rewindInputTM_isTransducer))))

private theorem denseProgramInitTime_eq_fixedOutputSpace
    (input : List Bool) :
    denseProgramInitTime standardControlInstructionTapes input =
      denseFixedInitOutputSpace input.length := by
  simp [denseFixedInitOutputSpace, denseProgramInitTime,
    denseProgramInitialStore, DenseOverlay.Snapshot.initial]

/-- A fixed-register trace bound upgrades the exact loop simulation to an
all-prefix time-and-space contract. -/
theorem denseProgramLoopTM_hoareTimeSpace_traceBound_internal
    (program : Program) (input : List Bool) (fuel entryBudget wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel entryBudget wordBits) :
    (denseProgramLoopTM standardControlInstructionTapes program).HoareTimeSpace
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork standardControlInstructionTapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        let final :=
          (DenseOverlay.Snapshot.initial input).run program input fuel
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady standardControlInstructionTapes
          final.overlay final.pc work ∧
        out = instructionHaltOutput (final.curInstr program))
      (denseProgramLoopTime standardControlInstructionTapes program input
        (fuel + 1) (DenseOverlay.Snapshot.initial input))
      input.length
      (denseFixedIterationSpace program input.length entryBudget wordBits) := by
  let initial := DenseOverlay.Snapshot.initial input
  let initialWork :=
    denseProgramSnapshotWork standardControlInstructionTapes initial
  have hvalid : DenseOverlay.Valid initial.overlay := by
    simpa only [initial] using DenseOverlay.Snapshot.initial_valid input
  let sparseInitial : Snapshot :=
    { pc := initial.pc, store := initial.overlay }
  have hready :
      InstructionExecutionReady standardControlInstructionTapes
        initial.overlay initial.pc initialWork := by
    dsimp only [initialWork]
    simpa only [denseProgramSnapshotWork, sparseInitial] using
      programSnapshotWork_ready_internal standardControlInstructionTapes
        sparseInitial hvalid.1
  have hpc : initial.pc ≤ programResourceMagnitude program := by
    dsimp only [initial, DenseOverlay.Snapshot.initial]
    exact Nat.zero_le _
  have htrace :
      ∀ k, k ≤ fuel →
        DenseOverlay.FixedRegisters.SnapshotBound
          (initial.run program input k) entryBudget wordBits := by
    simpa only [DenseOverlay.FixedRegisters.TraceBound, initial] using hbound
  have htime := denseProgramLoopTM_hoareTime_run_internal
    standardControlInstructionTapes program input fuel initial initialWork
      hvalid hready (by simpa only [initial] using hhalted)
  have hspace := denseProgramLoopTM_hoareSpace_from
    program input entryBudget wordBits fuel initial initialWork
      hvalid hready hpc (by simpa only [initial] using hhalted) htrace
  simpa only [initial, initialWork] using htime.and_hoareSpace hspace

/-- A bounded halted snapshot gives an all-prefix contract for the final
lookup-and-verdict phase. -/
theorem denseProgramOutputTM_hoareTimeSpace_snapshotBound_internal
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (entryBudget wordBits : ℕ)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    (denseProgramOutputTM standardControlInstructionTapes).HoareTimeSpace
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady standardControlInstructionTapes
          snapshot.overlay snapshot.pc work ∧
        out = instructionHaltOutput .halt)
      (fun inp _work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        out = registerVerdictOutput
          (DenseOverlay.read input snapshot.overlay 0))
      (denseProgramOutputTime standardControlInstructionTapes input
        snapshot.overlay)
      input.length
      (denseFixedOutputSpace input.length entryBudget wordBits) := by
  have htime :
      (denseProgramOutputTM standardControlInstructionTapes).HoareTime
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          InstructionExecutionReady standardControlInstructionTapes
            snapshot.overlay snapshot.pc work ∧
          out = instructionHaltOutput .halt)
        (fun inp _work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          out = registerVerdictOutput
            (DenseOverlay.read input snapshot.overlay 0))
        (denseProgramOutputTime standardControlInstructionTapes input
          snapshot.overlay) := by
    intro inp work out hpre
    exact denseProgramOutputTM_hoareTime_haltOutput_internal
      standardControlInstructionTapes input snapshot.overlay snapshot.pc
        work hvalid hpre.2.1 inp work out ⟨hpre.1, rfl, hpre.2.2⟩
  have hbase := htime.toHoareTimeSpace
    (inputLength := input.length) (initialSpace := 1) (by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hready, _hout⟩
    subst inp
    constructor
    · intro i
      rw [standardInstructionExecutionReady_head hready i]
    · simp [Tape.move])
  apply hbase.consequence
  · exact fun _ _ _ hpre => hpre
  · exact fun _ _ _ hpost => hpost
  · exact le_rfl
  · exact le_rfl
  · have hspace := denseProgramOutputTime_le_fixedSpace
      input snapshot entryBudget wordBits hvalid hbound
    omega

/-- The complete standard dense simulator has an exact endpoint/time contract
and a fuel-independent all-prefix auxiliary-space bound. -/
theorem denseProgramDecisionTM_hoareTimeSpace_traceBound_internal
    (program : Program) (input : List Bool) (fuel entryBudget wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel entryBudget wordBits) :
    (denseProgramDecisionTM standardControlInstructionTapes program
      ).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        let final :=
          (DenseOverlay.Snapshot.initial input).run program input fuel
        out = registerVerdictOutput
          (DenseOverlay.read input final.overlay 0))
      (denseProgramDecisionTime standardControlInstructionTapes program
        input fuel)
      input.length
      (denseProgramDecisionSpace program input.length entryBudget wordBits) := by
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  have hinitialValid : DenseOverlay.Valid initial.overlay := by
    simpa only [initial] using DenseOverlay.Snapshot.initial_valid input
  let sparseInitial : Snapshot :=
    { pc := initial.pc, store := initial.overlay }
  have hinitialReady :
      InstructionExecutionReady standardControlInstructionTapes
        initial.overlay initial.pc
        (denseProgramSnapshotWork standardControlInstructionTapes initial) := by
    simpa only [denseProgramSnapshotWork, sparseInitial] using
      programSnapshotWork_ready_internal standardControlInstructionTapes
        sparseInitial hinitialValid.1
  have hfinalValid : DenseOverlay.Valid final.overlay := by
    simpa only [final, initial] using DenseOverlay.Snapshot.run_valid
      program input fuel (DenseOverlay.Snapshot.initial input)
        (DenseOverlay.Snapshot.initial_valid input)
  have hfinalBound :
      DenseOverlay.FixedRegisters.SnapshotBound final
        entryBudget wordBits := by
    simpa only [final, initial] using hbound.at le_rfl
  have hinit := denseProgramInitTM_hoareTimeSpace_internal
    standardControlInstructionTapes input
  have hloop := denseProgramLoopTM_hoareTimeSpace_traceBound_internal
    program input fuel entryBudget wordBits hhalted hbound
  have houtput :=
    denseProgramOutputTM_hoareTimeSpace_snapshotBound_internal
      input final entryBudget wordBits hfinalValid hfinalBound
  have htransitionLoop :
      ∀ inp work out,
        (let final :=
          (DenseOverlay.Snapshot.initial input).run program input fuel
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady standardControlInstructionTapes
          final.overlay final.pc work ∧
        out = instructionHaltOutput (final.curInstr program)) →
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          InstructionExecutionReady standardControlInstructionTapes
            final.overlay final.pc work ∧
          out = instructionHaltOutput .halt)
          (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out hpost
    dsimp only at hpost
    rcases hpost with ⟨hinp, hready, hout⟩
    have hfinalHalted : final.Halted program := by
      simpa only [final, initial] using hhalted
    have houtHalt : out = instructionHaltOutput .halt := by
      rw [hout, hfinalHalted]
    have hinputParked : TM.Parked inp := by
      rw [hinp]
      refine ⟨by simp [Tape.move], ?_⟩
      simpa using Tape.init_ofBool_move_right_cells_ne_start input
    have houtputParked : TM.Parked out := by
      rw [houtHalt]
      exact ⟨by rw [instructionHaltOutput_head_internal],
        instructionHaltOutput_cells_ne_start_internal .halt⟩
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinputParked.read_ne_start
      (fun i => (hready.control.lookup.scanner.parked i).read_ne_start)
      houtputParked.read_ne_start
    rw [hi, hw, ho]
    exact ⟨hinp, hready, houtHalt⟩
  have hloopOutput := TM.seqTM_hoareTimeSpace
    (denseProgramLoopTM standardControlInstructionTapes program)
    (denseProgramOutputTM standardControlInstructionTapes)
    hloop htransitionLoop houtput
  have htransitionInit :
      ∀ inp work out,
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          work = denseProgramSnapshotWork standardControlInstructionTapes
            (DenseOverlay.Snapshot.initial input) ∧
          out = TM.resetBinaryBlank) inp work out →
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          work = denseProgramSnapshotWork standardControlInstructionTapes
            (DenseOverlay.Snapshot.initial input) ∧
          out = (Tape.init []).move Dir3.right)
          (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out hpost
    rcases hpost with ⟨hinp, hwork, hout⟩
    have hinputParked : TM.Parked inp := by
      rw [hinp]
      refine ⟨by simp [Tape.move], ?_⟩
      simpa using Tape.init_ofBool_move_right_cells_ne_start input
    have hworkParked : ∀ i, TM.Parked (work i) := by
      intro i
      rw [hwork]
      exact hinitialReady.control.lookup.scanner.parked i
    have houtputParked : TM.Parked out := by
      rw [hout]
      have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
        simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
      exact ⟨by rw [hblankNat.2.1],
        hblankNat.2.hasBinaryContent.cells_ne_start⟩
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinputParked.read_ne_start
      (fun i => (hworkParked i).read_ne_start)
      houtputParked.read_ne_start
    rw [hi, hw, ho]
    exact ⟨hinp, hwork, by simpa [TM.resetBinaryBlank] using hout⟩
  have hfull := TM.seqTM_hoareTimeSpace
    (denseProgramInitTM standardControlInstructionTapes)
    (TM.seqTM
      (denseProgramLoopTM standardControlInstructionTapes program)
      (denseProgramOutputTM standardControlInstructionTapes))
    hinit htransitionInit hloopOutput
  have hspace :
      max (denseProgramInitSpace input.length)
          (max
            (denseFixedIterationSpace program input.length entryBudget wordBits)
            (denseFixedOutputSpace input.length entryBudget wordBits)) ≤
        denseProgramDecisionSpace program input.length entryBudget wordBits := by
    unfold denseProgramDecisionSpace
    apply max_le
    · exact le_max_left _ _
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hfull' := hfull.consequence
    (fun _ _ _ hpre => hpre) (fun _ _ _ hpost => hpost.2)
    le_rfl le_rfl hspace
  simpa only [denseProgramDecisionTM, denseProgramDecisionTime, initial,
    final] using hfull'

/-- Every reachable configuration of the complete fixed simulator also keeps
the two-way verdict head inside the advertised decision-space budget. -/
theorem denseProgramDecisionTM_output_head_le_traceBound_internal
    (program : Program) (input : List Bool) (fuel entryBudget wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel entryBudget wordBits) :
    ∀ cfg,
      (denseProgramDecisionTM standardControlInstructionTapes program
        ).reaches
        ((denseProgramDecisionTM standardControlInstructionTapes program
          ).initCfg input) cfg →
      cfg.output.head ≤
        denseProgramDecisionSpace program input.length entryBudget wordBits := by
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  have hinitialValid : DenseOverlay.Valid initial.overlay := by
    simpa only [initial] using DenseOverlay.Snapshot.initial_valid input
  let sparseInitial : Snapshot :=
    { pc := initial.pc, store := initial.overlay }
  have hinitialReady :
      InstructionExecutionReady standardControlInstructionTapes
        initial.overlay initial.pc
        (denseProgramSnapshotWork standardControlInstructionTapes initial) := by
    simpa only [denseProgramSnapshotWork, sparseInitial] using
      programSnapshotWork_ready_internal standardControlInstructionTapes
        sparseInitial hinitialValid.1
  have hfinalValid : DenseOverlay.Valid final.overlay := by
    simpa only [final, initial] using DenseOverlay.Snapshot.run_valid
      program input fuel (DenseOverlay.Snapshot.initial input)
        (DenseOverlay.Snapshot.initial_valid input)
  have hfinalBound :
      DenseOverlay.FixedRegisters.SnapshotBound final
        entryBudget wordBits := by
    simpa only [final, initial] using hbound.at le_rfl
  have hinit := denseProgramInitTM_hoareTimeSpace_internal
    standardControlInstructionTapes input
  have hloop := denseProgramLoopTM_hoareTimeSpace_traceBound_internal
    program input fuel entryBudget wordBits hhalted hbound
  have houtput :=
    denseProgramOutputTM_hoareTimeSpace_snapshotBound_internal
      input final entryBudget wordBits hfinalValid hfinalBound
  have hinitOutputBase := hoareOutputHead_of_hoareTime
    hinit.1 (initialHead := 0) (by
      intro inp work out hpre
      rw [hpre.2.2]
      rfl)
  have hinitOutput :
      HoareOutputHead
        (denseProgramInitTM standardControlInstructionTapes)
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
          work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (denseFixedInitOutputSpace input.length) := by
    simpa only [zero_add, denseProgramInitTime_eq_fixedOutputSpace input] using
      hinitOutputBase
  have hloopOutput :=
    denseProgramLoopTM_hoareOutputHead_traceBound
      program input fuel entryBudget wordBits hhalted hbound
  have houtputBase := hoareOutputHead_of_hoareTime
    houtput.1 (initialHead := 1) (by
      intro inp work out hpre
      rw [hpre.2.2, instructionHaltOutput_head_internal])
  have houtputSpace := denseProgramOutputTime_le_fixedSpace
    input final entryBudget wordBits hfinalValid hfinalBound
  have houtputOutput :
      HoareOutputHead
        (denseProgramOutputTM standardControlInstructionTapes)
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          InstructionExecutionReady standardControlInstructionTapes
            final.overlay final.pc work ∧
          out = instructionHaltOutput .halt)
        (denseFixedOutputSpace input.length entryBudget wordBits) := by
    apply houtputBase.mono
    omega
  have htransitionLoop :
      ∀ inp work out,
        (let final :=
          (DenseOverlay.Snapshot.initial input).run program input fuel
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady standardControlInstructionTapes
          final.overlay final.pc work ∧
        out = instructionHaltOutput (final.curInstr program)) →
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          InstructionExecutionReady standardControlInstructionTapes
            final.overlay final.pc work ∧
          out = instructionHaltOutput .halt)
          (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out hpost
    dsimp only at hpost
    rcases hpost with ⟨hinp, hready, hout⟩
    have hfinalHalted : final.Halted program := by
      simpa only [final, initial] using hhalted
    have houtHalt : out = instructionHaltOutput .halt := by
      rw [hout, hfinalHalted]
    have hinputParked : TM.Parked inp := by
      rw [hinp]
      refine ⟨by simp [Tape.move], ?_⟩
      simpa using Tape.init_ofBool_move_right_cells_ne_start input
    have houtputParked : TM.Parked out := by
      rw [houtHalt]
      exact ⟨by rw [instructionHaltOutput_head_internal],
        instructionHaltOutput_cells_ne_start_internal .halt⟩
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinputParked.read_ne_start
      (fun i => (hready.control.lookup.scanner.parked i).read_ne_start)
      houtputParked.read_ne_start
    rw [hi, hw, ho]
    exact ⟨hinp, hready, houtHalt⟩
  have hloopOutputTimeSpace := TM.seqTM_hoareTimeSpace
    (denseProgramLoopTM standardControlInstructionTapes program)
    (denseProgramOutputTM standardControlInstructionTapes)
    hloop htransitionLoop houtput
  have hloopOutputOutput := seqTM_hoareOutputHead
    (denseProgramLoopTM standardControlInstructionTapes program)
    (denseProgramOutputTM standardControlInstructionTapes)
    hloop.1 htransitionLoop houtput.1 hloopOutput houtputOutput
  have htransitionInit :
      ∀ inp work out,
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          work = denseProgramSnapshotWork standardControlInstructionTapes
            (DenseOverlay.Snapshot.initial input) ∧
          out = TM.resetBinaryBlank) inp work out →
        (fun inp work out =>
          inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
          work = denseProgramSnapshotWork standardControlInstructionTapes
            (DenseOverlay.Snapshot.initial input) ∧
          out = (Tape.init []).move Dir3.right)
          (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out hpost
    rcases hpost with ⟨hinp, hwork, hout⟩
    have hinputParked : TM.Parked inp := by
      rw [hinp]
      refine ⟨by simp [Tape.move], ?_⟩
      simpa using Tape.init_ofBool_move_right_cells_ne_start input
    have hworkParked : ∀ i, TM.Parked (work i) := by
      intro i
      rw [hwork]
      exact hinitialReady.control.lookup.scanner.parked i
    have houtputParked : TM.Parked out := by
      rw [hout]
      have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
        simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
      exact ⟨by rw [hblankNat.2.1],
        hblankNat.2.hasBinaryContent.cells_ne_start⟩
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinputParked.read_ne_start
      (fun i => (hworkParked i).read_ne_start)
      houtputParked.read_ne_start
    rw [hi, hw, ho]
    exact ⟨hinp, hwork, by simpa [TM.resetBinaryBlank] using hout⟩
  have hfullOutput := seqTM_hoareOutputHead
    (denseProgramInitTM standardControlInstructionTapes)
    (TM.seqTM
      (denseProgramLoopTM standardControlInstructionTapes program)
      (denseProgramOutputTM standardControlInstructionTapes))
    hinit.1 htransitionInit hloopOutputTimeSpace.1
      hinitOutput hloopOutputOutput
  have hfullOutput' :
      HoareOutputHead
        (denseProgramDecisionTM standardControlInstructionTapes program)
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
          work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (denseProgramDecisionSpace program input.length entryBudget
          wordBits) := by
    apply hfullOutput.mono
    unfold denseProgramDecisionSpace
    exact le_max_right _ _
  intro cfg hreach
  exact hfullOutput' _ _ _ ⟨rfl, rfl, rfl⟩ cfg hreach

private theorem denseInitialRun_halted_of_ramRun
    (program : Program) (input : List Bool) (fuel : ℕ)
    (hhalted : RAM.Halted program
      (RAM.run program fuel (RAM.initCfg input))) :
    ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
      program := by
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  have hdecode : final.decode input =
      RAM.run program fuel (RAM.initCfg input) := by
    rw [show RAM.initCfg input = initial.decode input by
      simpa only [initial] using
        (DenseOverlay.Snapshot.initial_decode input).symm]
    simpa only [final] using DenseOverlay.Snapshot.decode_run
      program input fuel initial (by
        simpa only [initial] using
          DenseOverlay.Snapshot.initial_canonical input)
  change RAM.Halted program (final.decode input)
  rw [hdecode]
  exact hhalted

/-- A single fixed twenty-work-tape TM decides every language decided by a
fixed RAM run whose dense prefixes satisfy one length-uniform register bound. -/
theorem denseProgramDecisionTM_decidesInSpace_traceBound_internal
    (program : Program) (L : Language)
    (fuel : List Bool → ℕ) (entryBudget wordBits : ℕ → ℕ)
    (hhalted : ∀ input, RAM.Halted program
      (RAM.run program (fuel input) (RAM.initCfg input)))
    (hbound : ∀ input,
      DenseOverlay.FixedRegisters.TraceBound program input (fuel input)
        (entryBudget input.length) (wordBits input.length))
    (hyes : ∀ input, input ∈ L →
      (RAM.run program (fuel input) (RAM.initCfg input)).verdict = 1)
    (hno : ∀ input, input ∉ L →
      (RAM.run program (fuel input) (RAM.initCfg input)).verdict = 0) :
    (denseProgramDecisionTM standardControlInstructionTapes program
      ).DecidesInSpace L
      (fun inputLength =>
        denseProgramDecisionSpace program inputLength
          (entryBudget inputLength) (wordBits inputLength)) := by
  apply TM.decidesInSpace_of_hoareSpace
  · intro input
    have hdenseHalted := denseInitialRun_halted_of_ramRun
      program input (fuel input) (hhalted input)
    exact
      (denseProgramDecisionTM_hoareTimeSpace_traceBound_internal
        program input (fuel input) (entryBudget input.length)
          (wordBits input.length) hdenseHalted (hbound input)).2
  · intro input
    obtain ⟨cfg, time, _htime, hreach, hhalt, hpost⟩ :=
      denseProgramDecisionTM_hoareTime_ramRun_internal
        standardControlInstructionTapes program input (fuel input)
          (hhalted input) _ _ _ ⟨rfl, rfl, rfl⟩
    refine ⟨cfg, TM.reaches_of_reachesIn hreach, hhalt, ?_, ?_⟩
    · intro hmem
      rw [hpost, registerVerdictOutput_cell_one, hyes input hmem]
      decide
    · intro hnotmem
      rw [hpost, registerVerdictOutput_cell_one, hno input hnotmem]
      rfl
  · intro input cfg hreach
    have hdenseHalted := denseInitialRun_halted_of_ramRun
      program input (fuel input) (hhalted input)
    have hhead :=
      denseProgramDecisionTM_output_head_le_traceBound_internal
        program input (fuel input) (entryBudget input.length)
          (wordBits input.length) hdenseHalted (hbound input) cfg hreach
    omega

end Machine
end RegisterStore
end RAM
end Complexity
