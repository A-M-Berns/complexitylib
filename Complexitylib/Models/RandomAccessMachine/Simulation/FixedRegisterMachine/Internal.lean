/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.FixedRegisterMachine.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.FixedRegisterMachine.SpaceBounds
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Internal
import Complexitylib.Models.TuringMachine.Combinators.WorkBranch
import Complexitylib.Models.TuringMachine.Hoare.Space.Decision
import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub
import Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.ResetBinary
import Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# Direct fixed-register RAM simulation -- proof internals
-/

namespace Complexity
namespace RAM
namespace FixedRegisterMachine

open RegisterStore DenseOverlay
open DenseOverlay.FixedRegisters.Footprint

namespace Internal

theorem programNoStore_of_writesWithin_internal
    {program : Program} {allowed : Finset ℕ}
    (hwrites : ProgramWritesWithin program allowed) :
    ProgramNoStore program := by
  intro pc
  have hinstr := hwrites pc
  generalize (program[pc]?).getD Instr.halt = instruction at hinstr ⊢
  cases instruction <;> simp_all [InstrWritesWithin, InstrNoStore]

private theorem le_foldr_max_internal {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih hmem) (le_max_right _ _)

theorem allowed_lt_compilationRegisterBound_internal
    (program : Program) (allowed : Finset ℕ)
    (address : ℕ) (haddress : address ∈ allowed) :
    address < compilationRegisterBound program allowed := by
  apply Nat.lt_succ_of_le
  apply le_foldr_max_internal
  simp [compilationRegisters, haddress]

private theorem instrRegistersBelow_compilationRegisterBound_internal
    (program : Program) (allowed : Finset ℕ)
    (instruction : Instr) (hinstruction : instruction ∈ program) :
    InstrRegistersBelow (compilationRegisterBound program allowed)
      instruction := by
  have hoperand :
      ∀ address ∈ instructionRegisters instruction,
        address < compilationRegisterBound program allowed := by
    intro address haddress
    apply Nat.lt_succ_of_le
    apply le_foldr_max_internal
    apply List.mem_append_right
    exact List.mem_flatMap.mpr
      ⟨instruction, hinstruction, haddress⟩
  cases instruction with
  | imm destination value =>
      exact hoperand destination (by simp [instructionRegisters])
  | add destination source₀ source₁
  | sub destination source₀ source₁
  | mul destination source₀ source₁ =>
      exact
        ⟨hoperand destination (by simp [instructionRegisters]),
          hoperand source₀ (by simp [instructionRegisters]),
          hoperand source₁ (by simp [instructionRegisters])⟩
  | load destination addressRegister
  | store destination addressRegister =>
      exact
        ⟨hoperand destination (by simp [instructionRegisters]),
          hoperand addressRegister (by simp [instructionRegisters])⟩
  | jz source target =>
      exact hoperand source (by simp [instructionRegisters])
  | jmp target =>
      simp [InstrRegistersBelow]
  | halt =>
      simp [InstrRegistersBelow]

theorem programRegistersBelow_compilationRegisterBound_internal
    (program : Program) (allowed : Finset ℕ) :
    ProgramRegistersBelow program
      (compilationRegisterBound program allowed) := by
  intro pc
  cases hget : program[pc]? with
  | none =>
      simp [InstrRegistersBelow]
  | some instruction =>
      have hinstruction : instruction ∈ program :=
        List.mem_of_getElem? hget
      simpa only [Option.getD_some] using
        instrRegistersBelow_compilationRegisterBound_internal
          program allowed instruction hinstruction

theorem registerTape_val_internal {program : Program} (spec : Spec program)
    (address : ℕ) (haddress : address < spec.registerBound) :
    (registerTape spec address haddress).val = address := by
  rfl

theorem scratchTape_val_internal {program : Program} (spec : Spec program)
    (slot : Fin scratchCount) :
    (scratchTape spec slot).val = spec.registerBound + slot.val := by
  rfl

theorem registerTape_injective_internal {program : Program}
    (spec : Spec program) {first second : ℕ}
    (hfirst : first < spec.registerBound)
    (hsecond : second < spec.registerBound)
    (heq : registerTape spec first hfirst =
      registerTape spec second hsecond) :
    first = second := by
  exact congrArg Fin.val heq

theorem registerTape_ne_scratchTape_internal {program : Program}
    (spec : Spec program) (address : ℕ)
    (haddress : address < spec.registerBound)
    (slot : Fin scratchCount) :
    registerTape spec address haddress ≠ scratchTape spec slot := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [registerTape_val_internal, scratchTape_val_internal] at hval
  omega

theorem scratchTape_injective_internal {program : Program}
    (spec : Spec program) {first second : Fin scratchCount}
    (heq : scratchTape spec first = scratchTape spec second) :
    first = second := by
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp only [scratchTape_val_internal] at hval
  omega

theorem scratchTape_ne_internal {program : Program}
    (spec : Spec program) {first second : Fin scratchCount}
    (hne : first ≠ second) :
    scratchTape spec first ≠ scratchTape spec second := by
  intro heq
  exact hne (scratchTape_injective_internal spec heq)

theorem natTape_hasBinaryNat_internal (value : ℕ) :
    (natTape value).HasBinaryNat value := by
  simpa [natTape] using Tape.init_move_right_hasBinaryNat value

theorem natTape_parked_internal (value : ℕ) :
    TM.Parked (natTape value) := by
  have hnat := natTape_hasBinaryNat_internal value
  exact ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩

theorem registerBound_pos_internal {program : Program}
    (spec : Spec program) :
    0 < spec.registerBound :=
  spec.allowed_lt 0 spec.zero_mem

@[simp]
theorem executionWork_register_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (address : ℕ) (haddress : address < spec.registerBound) :
    executionWork spec input snapshot
        (registerTape spec address haddress) =
      natTape (DenseOverlay.read input snapshot.overlay address) := by
  have hne := registerTape_ne_scratchTape_internal spec address haddress
    (10 : Fin scratchCount)
  rw [executionWork]
  change Function.update (snapshotWork spec input snapshot)
      (scratchTape spec 10) (natTape snapshot.pc)
        (registerTape spec address haddress) = _
  rw [Function.update_of_ne hne]
  simp [snapshotWork, registerTape, workTapeCount, haddress]

@[simp]
theorem executionWork_pc_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) :
    executionWork spec input snapshot (pcTape spec) =
      natTape snapshot.pc := by
  simp [executionWork]

@[simp]
theorem executionWork_scratch_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (slot : Fin scratchCount) (hne : slot ≠ 10) :
    executionWork spec input snapshot (scratchTape spec slot) =
      natTape 0 := by
  have hpc : scratchTape spec slot ≠ scratchTape spec 10 := by
    exact scratchTape_ne_internal spec hne
  have hnot :
      ¬(spec.registerBound + slot.val < spec.registerBound) := by omega
  rw [executionWork]
  change Function.update (snapshotWork spec input snapshot)
      (scratchTape spec 10) (natTape snapshot.pc)
        (scratchTape spec slot) = _
  rw [Function.update_of_ne hpc]
  simp [snapshotWork, scratchTape, workTapeCount, hnot]

theorem executionWork_parked_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) :
    ∀ i, TM.Parked (executionWork spec input snapshot i) := by
  intro i
  by_cases hpc : i = pcTape spec
  · subst i
    rw [executionWork_pc_internal]
    exact natTape_parked_internal snapshot.pc
  · rw [executionWork, Function.update_of_ne hpc]
    by_cases hregister : i.val < spec.registerBound
    · simp [snapshotWork, hregister, natTape_parked_internal]
    · simp [snapshotWork, hregister, natTape_parked_internal]

theorem executionWork_setPC_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) (pc : ℕ) :
    Function.update (executionWork spec input snapshot)
        (pcTape spec) (natTape pc) =
      executionWork spec input { snapshot with pc := pc } := by
  unfold executionWork
  rw [Function.update_idem]
  rfl

theorem executionWork_write_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (destination value pc : ℕ)
    (hdestination : destination < spec.registerBound) :
    Function.update
        (Function.update (executionWork spec input snapshot)
          (registerTape spec destination hdestination) (natTape value))
        (pcTape spec) (natTape pc) =
      executionWork spec input
        { pc := pc
          overlay :=
            DenseOverlay.write snapshot.overlay destination value } := by
  funext i
  by_cases hregister : i.val < spec.registerBound
  · let address := i.val
    have haddress : address < spec.registerBound := by
      simpa [address] using hregister
    have hi :
        i = registerTape spec address haddress := by
      apply Fin.ext
      simpa [address] using
        (registerTape_val_internal spec address haddress).symm
    rw [hi]
    have hpc :
        registerTape spec address haddress ≠ pcTape spec :=
      registerTape_ne_scratchTape_internal spec address haddress 10
    rw [Function.update_of_ne hpc]
    by_cases hdestinationEq : address = destination
    · subst destination
      rw [Function.update_self, executionWork_register_internal,
        DenseOverlay.read_write input snapshot.overlay hcanonical]
      simp
    · have htape :
          registerTape spec address haddress ≠
            registerTape spec destination hdestination := by
        intro heq
        exact hdestinationEq
          (registerTape_injective_internal spec haddress hdestination heq)
      rw [Function.update_of_ne htape, executionWork_register_internal,
        executionWork_register_internal,
        DenseOverlay.read_write input snapshot.overlay hcanonical]
      simp [hdestinationEq]
  · have hdestinationTape :
        i ≠ registerTape spec destination hdestination := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [registerTape_val_internal] at hval
      omega
    by_cases hpc : i = pcTape spec
    · subst i
      simp [executionWork_pc_internal]
    · simp [executionWork, snapshotWork, hregister, hdestinationTape, hpc]

private theorem prefixInitValue_final
    {program : Program} (spec : Spec program)
    (input : List Bool) (address : ℕ)
    (haddress : address < spec.registerBound) :
    prefixInitValue input address (prefixInitTime spec) =
      RAM.initRegs input address := by
  have hbound := registerBound_pos_internal spec
  by_cases hzero : address = 0
  · subst address
    simp [prefixInitValue, RAM.initRegs]
  · have hle : address ≤ spec.registerBound - 1 := by omega
    simp [prefixInitValue, prefixInitTime, hzero, hle]

private theorem initial_denseRead_eq_initRegs
    (input : List Bool) (address : ℕ) :
    DenseOverlay.read input (DenseOverlay.Snapshot.initial input).overlay
      address = RAM.initRegs input address := by
  have hdecode := congrArg (fun cfg => cfg.regs address)
    (DenseOverlay.Snapshot.initial_decode input)
  simpa [DenseOverlay.Snapshot.decode, DenseOverlay.decode] using hdecode

theorem prefixInitWork_ready_initial_internal {program : Program}
    (spec : Spec program) (input : List Bool) :
    Ready spec input (DenseOverlay.Snapshot.initial input)
      (prefixInitWork spec input (prefixInitTime spec)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro address haddress
    have hvalue := prefixInitValue_final spec input address haddress
    have hread := initial_denseRead_eq_initRegs input address
    simpa [prefixInitWork, registerTape, workTapeCount, haddress, hvalue,
      hread] using
      natTape_hasBinaryNat_internal (RAM.initRegs input address)
  · intro slot
    have hnot :
        ¬(spec.registerBound + slot.val < spec.registerBound) := by omega
    simpa [prefixInitWork, scratchTape, workTapeCount, hnot] using
      natTape_hasBinaryNat_internal 0
  · intro i
    by_cases hregister : i.val < spec.registerBound
    · simpa [prefixInitWork, hregister] using
        natTape_parked_internal
          (prefixInitValue input i.val (prefixInitTime spec))
    · simpa [prefixInitWork, hregister] using natTape_parked_internal 0

private theorem prefixInitInput_step (input : List Bool) (processed : ℕ) :
    (prefixInitInput input processed).move
        (if (prefixInitInput input processed).read = Γ.zero ∨
            (prefixInitInput input processed).read = Γ.one then
          Dir3.right
        else TM.idleDir (prefixInitInput input processed).read) =
      prefixInitInput input (processed + 1) := by
  apply Tape.ext
  · by_cases hprocessed : processed < input.length
    · have hhead :
          min (processed + 1) (input.length + 1) = processed + 1 := by
        omega
      have hread : (prefixInitInput input processed).read =
          Γ.ofBool (input[processed]'hprocessed) := by
        simpa [prefixInitInput, Tape.read, hhead] using
          Tape.init_ofBool_cells_lt input processed hprocessed
      rw [hread]
      cases input[processed]'hprocessed <;>
        simp [prefixInitInput, Tape.move, Γ.ofBool, hhead]
      all_goals omega
    · have hhead : min (processed + 1) (input.length + 1) =
          input.length + 1 := by omega
      have hread : (prefixInitInput input processed).read = Γ.blank := by
        simpa [prefixInitInput, Tape.read, hhead] using
          Tape.init_ofBool_cells_ge input input.length le_rfl
      rw [hread]
      simp [prefixInitInput, Tape.move, TM.idleDir, hhead]
      omega
  · rw [Tape.move_cells]
    rfl

private theorem prefixInitValue_next_other
    (input : List Bool) (address processed : ℕ)
    (hne : address ≠ processed + 1) :
    prefixInitValue input address processed =
      prefixInitValue input address (processed + 1) := by
  unfold prefixInitValue
  by_cases hzero : address = 0
  · simp [hzero]
  · simp only [hzero, if_false]
    by_cases hle : address ≤ processed
    · rw [if_pos hle, if_pos (by omega)]
    · rw [if_neg hle, if_neg (by omega)]

private theorem natTape_zero_write_input
    (input : List Bool) (processed : ℕ) :
    (natTape 0).writeAndMove
        ((if (prefixInitInput input processed).read = Γ.one then Γw.one
          else Γw.blank).toΓ)
        (TM.idleDir (natTape 0).read) =
      natTape (RAM.initRegs input (processed + 1)) := by
  have hzeroRead : (natTape 0).read = Γ.blank := by
    simp [natTape, Tape.read, Tape.move, Tape.init]
  rw [hzeroRead]
  by_cases hprocessed : processed < input.length
  · have hhead :
        min (processed + 1) (input.length + 1) = processed + 1 := by
      omega
    have hread : (prefixInitInput input processed).read =
        Γ.ofBool (input[processed]'hprocessed) := by
      simpa [prefixInitInput, Tape.read, hhead] using
        Tape.init_ofBool_cells_lt input processed hprocessed
    have hindex : processed + 1 - 1 = processed := by omega
    have hregs : RAM.initRegs input (processed + 1) =
        if input[processed]'hprocessed then 1 else 0 := by
      simp [RAM.initRegs, hindex, List.getElem?_eq_getElem hprocessed]
    cases hvalue : input[processed]'hprocessed with
    | false =>
        simp [hvalue, Γ.ofBool] at hread hregs
        rw [hread, hregs]
        simp [natTape, TM.idleDir, Tape.writeAndMove, Tape.write,
          Tape.move, Tape.init]
    | true =>
        simp [hvalue, Γ.ofBool] at hread hregs
        rw [hread, hregs]
        apply Tape.ext
        · simp [natTape, TM.idleDir, Tape.writeAndMove, Tape.write,
            Tape.move, Tape.init]
        · funext j
          by_cases hj0 : j = 0
          · subst j
            simp [natTape, TM.idleDir, Tape.writeAndMove, Tape.write,
              Tape.move, Tape.init]
          · by_cases hj1 : j = 1
            · subst j
              simp [natTape, TM.idleDir, Tape.writeAndMove, Tape.write,
                Tape.move, Tape.init, Γ.ofBool]
            · have hnone : [Γ.one][j - 1]? = none := by
                apply List.getElem?_eq_none
                simp
                omega
              simp [natTape, TM.idleDir, Tape.writeAndMove, Tape.write,
                Tape.move, Tape.init, hj0, hj1, hnone, Γ.ofBool]
  · have hhead : min (processed + 1) (input.length + 1) =
        input.length + 1 := by omega
    have hread : (prefixInitInput input processed).read = Γ.blank := by
      simpa [prefixInitInput, Tape.read, hhead] using
        Tape.init_ofBool_cells_ge input input.length le_rfl
    have hnone : input[processed]? = none :=
      List.getElem?_eq_none (by omega)
    have hregs : RAM.initRegs input (processed + 1) = 0 := by
      simp [RAM.initRegs, hnone]
    rw [hread, hregs]
    simp [natTape, TM.idleDir, Tape.writeAndMove, Tape.write, Tape.move,
      Tape.init]

private theorem prefixInitWork_step {program : Program}
    (spec : Spec program) (input : List Bool) (processed : ℕ)
    (haddress : processed + 1 < spec.registerBound) :
    (fun i =>
      (prefixInitWork spec input processed i).writeAndMove
        ((if i = registerTape spec (processed + 1) haddress then
            if (prefixInitInput input processed).read = Γ.one then
              Γw.one
            else Γw.blank
          else
            TM.readBackWrite
              (prefixInitWork spec input processed i).read).toΓ)
        (TM.idleDir (prefixInitWork spec input processed i).read)) =
      prefixInitWork spec input (processed + 1) := by
  funext i
  by_cases hselected :
      i = registerTape spec (processed + 1) haddress
  · subst i
    have hpositive : processed + 1 ≠ 0 := by omega
    have hnotle : ¬processed + 1 ≤ processed := by omega
    simpa [prefixInitWork, registerTape, workTapeCount, haddress,
      prefixInitValue, hpositive, hnotle] using
      natTape_zero_write_input input processed
  · rw [if_neg hselected]
    have hparked :
        TM.Parked (prefixInitWork spec input processed i) := by
      by_cases hregister : i.val < spec.registerBound
      · simpa [prefixInitWork, hregister] using
          natTape_parked_internal
            (prefixInitValue input i.val processed)
      · simpa [prefixInitWork, hregister] using natTape_parked_internal 0
    rw [hparked.writeAndMove_readBack_idle]
    by_cases hregister : i.val < spec.registerBound
    · have hneValue : i.val ≠ processed + 1 := by
        intro hval
        apply hselected
        apply Fin.ext
        simpa using hval
      simp [prefixInitWork, hregister,
        prefixInitValue_next_other input i.val processed hneValue]
    · simp [prefixInitWork, hregister]

private theorem prefixInitTM_step {program : Program}
    (spec : Spec program) (input : List Bool) (processed : ℕ)
    (hprocessed : processed < prefixInitTime spec) :
    (prefixInitTM spec).step (prefixInitCfg spec input processed) =
      some (prefixInitCfg spec input (processed + 1)) := by
  have haddress : processed + 1 < spec.registerBound := by
    simp only [prefixInitTime] at hprocessed
    omega
  have hstate : (saturate spec.registerBound (processed + 1)).val <
      spec.registerBound := by
    simp [saturate, Nat.min_eq_left (Nat.le_of_lt haddress), haddress]
  have hne : saturate spec.registerBound (processed + 1) ≠
      saturate spec.registerBound spec.registerBound := by
    intro heq
    have hval := congrArg Fin.val heq
    simp [saturate, Nat.min_eq_left (Nat.le_of_lt haddress)] at hval
    omega
  simp only [TM.step, prefixInitCfg, prefixInitTM, hne, if_false, hstate,
    dite_true]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨?_, ?_, ?_, ?_⟩)
  · simp [saturate, Nat.min_eq_left (Nat.le_of_lt haddress)]
  · exact prefixInitInput_step input processed
  · simpa [saturate, Nat.min_eq_left (Nat.le_of_lt haddress)] using
      prefixInitWork_step spec input processed haddress
  · exact (natTape_parked_internal 0).writeAndMove_readBack_idle

private theorem prefixInitTM_loop {program : Program}
    (spec : Spec program) (input : List Bool) :
    ∀ count processed, processed + count = prefixInitTime spec →
      (prefixInitTM spec).reachesIn count
        (prefixInitCfg spec input processed)
        (prefixInitCfg spec input (prefixInitTime spec)) := by
  intro count
  induction count with
  | zero =>
      intro processed htotal
      have hprocessed : processed = prefixInitTime spec := by omega
      subst processed
      exact .zero
  | succ count ih =>
      intro processed htotal
      have hprocessed : processed < prefixInitTime spec := by omega
      exact .step (prefixInitTM_step spec input processed hprocessed)
        (ih (processed + 1) (by omega))

theorem prefixInitTM_reachesIn_internal {program : Program}
    (spec : Spec program) (input : List Bool) :
    (prefixInitTM spec).reachesIn (prefixInitTime spec)
      (prefixInitCfg spec input 0)
      (prefixInitCfg spec input (prefixInitTime spec)) :=
  prefixInitTM_loop spec input (prefixInitTime spec) 0 (by omega)

private theorem prefixInitTM_reachesIn_prefix {program : Program}
    (spec : Spec program) (input : List Bool) :
    ∀ time, time ≤ prefixInitTime spec →
      (prefixInitTM spec).reachesIn time
        (prefixInitCfg spec input 0)
        (prefixInitCfg spec input time) := by
  intro time
  induction time with
  | zero =>
      intro _
      exact .zero
  | succ time ih =>
      intro htime
      have hprevious : time ≤ prefixInitTime spec := by omega
      have hstrict : time < prefixInitTime spec := by omega
      exact TM.reachesIn_trans (prefixInitTM spec) (ih hprevious)
        (.step (prefixInitTM_step spec input time hstrict) .zero)

private theorem prefixInitCfg_withinAuxSpace {program : Program}
    (spec : Spec program) (input : List Bool) (processed : ℕ) :
    (prefixInitCfg spec input processed).WithinAuxSpace input.length 1 := by
  constructor
  · intro i
    by_cases hregister : i.val < spec.registerBound
    · simp [prefixInitCfg, prefixInitWork, hregister, natTape, Tape.move]
    · simp [prefixInitCfg, prefixInitWork, hregister, natTape, Tape.move]
  · simp [prefixInitCfg, prefixInitInput]

theorem prefixInitTM_prefix_withinAuxSpace_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (time : ℕ) (current : Complexity.Cfg
      (workTapeCount spec) (prefixInitTM spec).Q)
    (hreach : (prefixInitTM spec).reachesIn time
      (prefixInitCfg spec input 0) current)
    (htime : time ≤ prefixInitTime spec) :
    current.WithinAuxSpace input.length 1 := by
  have hprefix := prefixInitTM_reachesIn_prefix spec input time htime
  have hcanonical := (prefixInitTM spec).reachesIn_right_unique
    hreach hprefix
  rw [hcanonical]
  exact prefixInitCfg_withinAuxSpace spec input time

private theorem prefixInitTM_final_halted {program : Program}
    (spec : Spec program) (input : List Bool) :
    (prefixInitTM spec).halted
      (prefixInitCfg spec input (prefixInitTime spec)) := by
  have hbound := registerBound_pos_internal spec
  change saturate spec.registerBound (prefixInitTime spec + 1) =
    saturate spec.registerBound spec.registerBound
  congr 1
  simp [prefixInitTime]
  omega

theorem prefixInitTM_hoareTimeSpace_internal {program : Program}
    (spec : Spec program) (input : List Bool) :
    (prefixInitTM spec).HoareTimeSpace
      (fun inp work out =>
        inp = prefixInitInput input 0 ∧
        work = prefixInitWork spec input 0 ∧
        out = natTape 0)
      (fun inp work out =>
        inp = prefixInitInput input (prefixInitTime spec) ∧
        work = prefixInitWork spec input (prefixInitTime spec) ∧
        Ready spec input (DenseOverlay.Snapshot.initial input) work ∧
        out = natTape 0)
      (prefixInitTime spec) input.length 1 := by
  refine ⟨?_, ?_⟩
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    let done := prefixInitCfg spec input (prefixInitTime spec)
    exact ⟨done, prefixInitTime spec, le_rfl,
      prefixInitTM_reachesIn_internal spec input,
      prefixInitTM_final_halted spec input,
      rfl, rfl, prefixInitWork_ready_initial_internal spec input, rfl⟩
  · rintro inp work out ⟨rfl, rfl, rfl⟩ current hreach
    obtain ⟨time, hreachIn⟩ :=
      (prefixInitTM spec).reaches_to_reachesIn hreach
    have hfull := prefixInitTM_reachesIn_internal spec input
    have htime : time ≤ prefixInitTime spec :=
      (prefixInitTM spec).reachesIn_le_halt hreachIn hfull
        (prefixInitTM_final_halted spec input)
    exact prefixInitTM_prefix_withinAuxSpace_internal spec input time current
      hreachIn htime

private theorem prefixInitInput_zero_parked (input : List Bool) :
    TM.Parked (prefixInitInput input 0) := by
  constructor
  · simp [prefixInitInput]
  · intro j hj
    simp only [prefixInitInput]
    simpa using Tape.init_ofBool_cells_ne_start input j hj

private theorem prefixInitWork_parked {program : Program}
    (spec : Spec program) (input : List Bool) (processed : ℕ) :
    ∀ i, TM.Parked (prefixInitWork spec input processed i) := by
  intro i
  by_cases hregister : i.val < spec.registerBound
  · simpa [prefixInitWork, hregister] using
      natTape_parked_internal (prefixInitValue input i.val processed)
  · simpa [prefixInitWork, hregister] using natTape_parked_internal 0

private structure LengthReady {program : Program}
    (spec : Spec program) (input : List Bool)
    (inp : Tape) (work : Fin (workTapeCount spec) → Tape)
    (out : Tape) : Prop where
  inputCells : inp.cells = (Tape.init (input.map Γ.ofBool)).cells
  inputHead : inp.head = input.length + 1
  lengthValue : (work (registerTape spec 0
    (spec.allowed_lt 0 spec.zero_mem))).HasBinaryNat input.length
  otherWork : ∀ i, i ≠ registerTape spec 0
    (spec.allowed_lt 0 spec.zero_mem) →
    work i = (Tape.init []).move Dir3.right
  output : out = (Tape.init []).move Dir3.right

private theorem LengthReady.input_startInvariant
    {program : Program} {spec : Spec program} {input : List Bool}
    {inp : Tape} {work : Fin (workTapeCount spec) → Tape} {out : Tape}
    (hready : LengthReady spec input inp work out) :
    inp.StartInvariant := by
  constructor
  · rw [hready.inputCells]
    simp [Tape.init]
  · intro j hj
    rw [hready.inputCells]
    simpa using Tape.init_ofBool_cells_ne_start input j hj

private theorem LengthReady.work_parked
    {program : Program} {spec : Spec program} {input : List Bool}
    {inp : Tape} {work : Fin (workTapeCount spec) → Tape} {out : Tape}
    (hready : LengthReady spec input inp work out) :
    ∀ i, TM.Parked (work i) := by
  intro i
  by_cases hi : i = registerTape spec 0
      (spec.allowed_lt 0 spec.zero_mem)
  · subst i
    exact ⟨by rw [hready.lengthValue.2.1],
      hready.lengthValue.2.hasBinaryContent.cells_ne_start⟩
  · rw [hready.otherWork i hi]
    exact natTape_parked_internal 0

private theorem LengthReady.work_head_eq_one
    {program : Program} {spec : Spec program} {input : List Bool}
    {inp : Tape} {work : Fin (workTapeCount spec) → Tape} {out : Tape}
    (hready : LengthReady spec input inp work out) :
    ∀ i, (work i).head = 1 := by
  intro i
  by_cases hi : i = registerTape spec 0
      (spec.allowed_lt 0 spec.zero_mem)
  · subst i
    exact hready.lengthValue.2.1
  · rw [hready.otherWork i hi]
    simp [Tape.move]

private theorem LengthReady.output_parked
    {program : Program} {spec : Spec program} {input : List Bool}
    {inp : Tape} {work : Fin (workTapeCount spec) → Tape} {out : Tape}
    (hready : LengthReady spec input inp work out) :
    TM.Parked out := by
  rw [hready.output]
  exact natTape_parked_internal 0

private theorem LengthReady.work_eq_prefixInitWork
    {program : Program} {spec : Spec program} {input : List Bool}
    {inp : Tape} {work : Fin (workTapeCount spec) → Tape} {out : Tape}
    (hready : LengthReady spec input inp work out) :
    work = prefixInitWork spec input 0 := by
  funext i
  by_cases hi : i = registerTape spec 0
      (spec.allowed_lt 0 spec.zero_mem)
  · subst i
    have hcanonical := hready.lengthValue.eq_init_move_right
    simpa [prefixInitWork, registerTape, workTapeCount,
      spec.allowed_lt 0 spec.zero_mem, prefixInitValue, natTape] using
      hcanonical
  · rw [hready.otherWork i hi]
    by_cases hregister : i.val < spec.registerBound
    · have hpositive : i.val ≠ 0 := by
        intro hzero
        apply hi
        apply Fin.ext
        simpa using hzero
      simp [prefixInitWork, hregister, prefixInitValue, hpositive, natTape]
    · simp [prefixInitWork, hregister, natTape]

private theorem LengthReady.output_eq_natTape
    {program : Program} {spec : Spec program} {input : List Bool}
    {inp : Tape} {work : Fin (workTapeCount spec) → Tape} {out : Tape}
    (hready : LengthReady spec input inp work out) :
    out = natTape 0 := by
  simpa [natTape] using hready.output

private structure RewindSpaceInvariant {n : ℕ}
    (inputLength space : ℕ)
    (cfg : Complexity.Cfg n (TM.rewindInputTM (n := n)).Q) : Prop where
  inputStart : cfg.input.StartInvariant
  inputHead : cfg.input.head ≤ inputLength + 1
  workParked : ∀ i, TM.Parked (cfg.work i)
  workSpace : ∀ i, (cfg.work i).head ≤ space
  outputParked : TM.Parked cfg.output

private theorem RewindSpaceInvariant.withinAuxSpace
    {n inputLength space : ℕ}
    {cfg : Complexity.Cfg n (TM.rewindInputTM (n := n)).Q}
    (hinvariant : RewindSpaceInvariant inputLength space cfg) :
    cfg.WithinAuxSpace inputLength space := by
  refine ⟨hinvariant.workSpace, ?_⟩
  exact hinvariant.inputHead.trans (by omega)

private theorem rewindInputTM_step_preserves
    {n inputLength space : ℕ}
    {cfg cfg' : Complexity.Cfg n (TM.rewindInputTM (n := n)).Q}
    (hinvariant : RewindSpaceInvariant inputLength space cfg)
    (hstep : (TM.rewindInputTM (n := n)).step cfg = some cfg') :
    RewindSpaceInvariant inputLength space cfg' := by
  cases hstate : cfg.state with
  | moveLeft =>
      simp only [TM.step, TM.rewindInputTM, hstate, reduceCtorEq,
        if_false] at hstep
      by_cases hread : cfg.input.read = Γ.start
      · simp only [hread, if_true] at hstep
        injection hstep with hcfg
        subst cfg'
        have hinputZero : cfg.input.head = 0 := by
          by_contra hne
          exact hinvariant.inputStart.read_ne_start (by omega) hread
        refine ⟨hinvariant.inputStart.move Dir3.right, ?_, ?_, ?_, ?_⟩
        · simp [Tape.move, hinputZero]
        · intro i
          change TM.Parked ((cfg.work i).writeAndMove
            (TM.readBackWrite (cfg.work i).read).toΓ
            (TM.idleDir (cfg.work i).read))
          rw [(hinvariant.workParked i).writeAndMove_readBack_idle]
          exact hinvariant.workParked i
        · intro i
          change ((cfg.work i).writeAndMove
            (TM.readBackWrite (cfg.work i).read).toΓ
            (TM.idleDir (cfg.work i).read)).head ≤ space
          rw [(hinvariant.workParked i).writeAndMove_readBack_idle]
          exact hinvariant.workSpace i
        · rw [hinvariant.outputParked.writeAndMove_readBack_idle]
          exact hinvariant.outputParked
      · simp only [hread, if_false] at hstep
        injection hstep with hcfg
        subst cfg'
        refine ⟨hinvariant.inputStart.move
          (TM.moveLeftDir cfg.input.read), ?_, ?_, ?_, ?_⟩
        · simp [TM.moveLeftDir, hread, Tape.move]
          exact hinvariant.inputHead.trans (by omega)
        · intro i
          change TM.Parked ((cfg.work i).writeAndMove
            (TM.readBackWrite (cfg.work i).read).toΓ
            (TM.idleDir (cfg.work i).read))
          rw [(hinvariant.workParked i).writeAndMove_readBack_idle]
          exact hinvariant.workParked i
        · intro i
          change ((cfg.work i).writeAndMove
            (TM.readBackWrite (cfg.work i).read).toΓ
            (TM.idleDir (cfg.work i).read)).head ≤ space
          rw [(hinvariant.workParked i).writeAndMove_readBack_idle]
          exact hinvariant.workSpace i
        · rw [hinvariant.outputParked.writeAndMove_readBack_idle]
          exact hinvariant.outputParked
  | moveRight =>
      simp only [TM.step, TM.rewindInputTM, hstate, reduceCtorEq,
        if_false] at hstep
      injection hstep with hcfg
      subst cfg'
      refine ⟨hinvariant.inputStart.move
        (TM.idleDir cfg.input.read), ?_, ?_, ?_, ?_⟩
      · by_cases hread : cfg.input.read = Γ.start
        · have hinputZero : cfg.input.head = 0 := by
            by_contra hne
            exact hinvariant.inputStart.read_ne_start (by omega) hread
          simp [TM.idleDir, hread, Tape.move, hinputZero]
        · simp [TM.idleDir, hread, Tape.move]
          exact hinvariant.inputHead
      · intro i
        change TM.Parked ((cfg.work i).writeAndMove
          (TM.readBackWrite (cfg.work i).read).toΓ
          (TM.idleDir (cfg.work i).read))
        rw [(hinvariant.workParked i).writeAndMove_readBack_idle]
        exact hinvariant.workParked i
      · intro i
        change ((cfg.work i).writeAndMove
          (TM.readBackWrite (cfg.work i).read).toΓ
          (TM.idleDir (cfg.work i).read)).head ≤ space
        rw [(hinvariant.workParked i).writeAndMove_readBack_idle]
        exact hinvariant.workSpace i
      · rw [hinvariant.outputParked.writeAndMove_readBack_idle]
        exact hinvariant.outputParked
  | done =>
      simp [TM.step, TM.rewindInputTM, hstate] at hstep

private theorem rewindInputTM_reachesIn_preserves
    {n inputLength space time : ℕ}
    {start current : Complexity.Cfg n (TM.rewindInputTM (n := n)).Q}
    (hinvariant : RewindSpaceInvariant inputLength space start)
    (hreach : (TM.rewindInputTM (n := n)).reachesIn time start current) :
    RewindSpaceInvariant inputLength space current := by
  induction hreach with
  | zero => exact hinvariant
  | step hstep _hrest ih =>
      exact ih (rewindInputTM_step_preserves hinvariant hstep)

theorem rewindInputTM_hoareSpace_internal {n inputLength space : ℕ} :
    (TM.rewindInputTM (n := n)).HoareSpace
      (fun inp work out =>
        inp.StartInvariant ∧ inp.head ≤ inputLength + 1 ∧
        (∀ i, TM.Parked (work i)) ∧
        (∀ i, (work i).head ≤ space) ∧ TM.Parked out)
      inputLength space := by
  intro inp work out hpre current hreach
  obtain ⟨time, hreachIn⟩ :=
    (TM.rewindInputTM (n := n)).reaches_to_reachesIn hreach
  have hinvariant : RewindSpaceInvariant inputLength space
      { state := (TM.rewindInputTM (n := n)).qstart
        input := inp
        work := work
        output := out } :=
    ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.1, hpre.2.2.2.2⟩
  have hfinal := rewindInputTM_reachesIn_preserves hinvariant hreachIn
  exact hfinal.withinAuxSpace

private theorem rewindInputTM_hoareTimeSpace_initializer
    {program : Program} (spec : Spec program) (input : List Bool) :
    (TM.rewindInputTM (n := workTapeCount spec)).HoareTimeSpace
      (LengthReady spec input)
      (fun inp work out =>
        inp = prefixInitInput input 0 ∧
        work = prefixInitWork spec input 0 ∧
        out = natTape 0)
      (input.length + 3) input.length
      (initializeSpace spec input.length) := by
  let stable : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
      work = prefixInitWork spec input 0 ∧ out = natTape 0
  have hrawTime := TM.rewindInputTM_hoareTime_frame
    (n := workTapeCount spec) (input.length + 1) (P := stable)
    (by
      intro inp work out inp' work' out' hstable hcells hhead
        hwork hout
      subst work'
      subst out'
      exact ⟨hcells.trans hstable.1, hstable.2⟩)
  have htime : (TM.rewindInputTM (n := workTapeCount spec)).HoareTime
      (LengthReady spec input)
      (fun inp work out =>
        inp = prefixInitInput input 0 ∧
        work = prefixInitWork spec input 0 ∧
        out = natTape 0)
      (input.length + 3) := by
    apply hrawTime.consequence
    · intro inp work out hready
      have hinputStart := hready.input_startInvariant
      have hworkParked := hready.work_parked
      have houtputParked := hready.output_parked
      exact ⟨hinputStart.1, hinputStart.2, by rw [hready.inputHead],
        houtputParked.read_ne_start, houtputParked.1,
        fun i => ⟨(hworkParked i).read_ne_start, (hworkParked i).1⟩,
        hready.inputCells, hready.work_eq_prefixInitWork,
        hready.output_eq_natTape⟩
    · intro inp work out hpost
      rcases hpost with ⟨hhead, hcells, hwork, hout⟩
      have hinp : inp = prefixInitInput input 0 := by
        apply Tape.ext
        · simpa [prefixInitInput] using hhead
        · exact hcells
      exact ⟨hinp, hwork, hout⟩
    · omega
  have hspace : (TM.rewindInputTM
      (n := workTapeCount spec)).HoareSpace
      (LengthReady spec input) input.length
      (initializeSpace spec input.length) := by
    apply (rewindInputTM_hoareSpace_internal
      (n := workTapeCount spec)
      (inputLength := input.length)
      (space := initializeSpace spec input.length)).weaken_pre
    intro inp work out hready
    refine ⟨hready.input_startInvariant, by rw [hready.inputHead],
      hready.work_parked, ?_, hready.output_parked⟩
    intro i
    rw [hready.work_head_eq_one i]
    simp [initializeSpace]
  exact htime.and_hoareSpace hspace

theorem initializeTM_hoareTimeSpace_internal {program : Program}
    (spec : Spec program) (input : List Bool) :
    (initializeTM spec).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = prefixInitInput input (prefixInitTime spec) ∧
        work = prefixInitWork spec input (prefixInitTime spec) ∧
        Ready spec input (DenseOverlay.Snapshot.initial input) work ∧
        out = natTape 0)
      (initializeTime spec input.length) input.length
      (initializeSpace spec input.length) := by
  let zeroAddress : Fin (workTapeCount spec) :=
    registerTape spec 0 (spec.allowed_lt 0 spec.zero_mem)
  have hlengthRaw := TM.binaryLengthTM_hoareTimeSpace zeroAddress input
  have hlength : (TM.binaryLengthTM zeroAddress).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (LengthReady spec input)
      (TM.binaryLengthTime input.length) input.length
      (initializeSpace spec input.length) := by
    apply hlengthRaw.consequence
    · intro inp work out hpre
      exact hpre
    · intro inp work out hpost
      exact ⟨hpost.1, hpost.2.1, hpost.2.2.1,
        hpost.2.2.2.1, hpost.2.2.2.2⟩
    · exact le_rfl
    · exact le_rfl
    · simp [initializeSpace]
  have hrewind := rewindInputTM_hoareTimeSpace_initializer spec input
  have hprefix := prefixInitTM_hoareTimeSpace_internal spec input
  have hprefixTransition :
      ∀ inp work out,
        (inp = prefixInitInput input 0 ∧
          work = prefixInitWork spec input 0 ∧ out = natTape 0) →
        (TM.transitionInput inp = prefixInitInput input 0 ∧
          (fun i => TM.transitionTape (work i)) =
            prefixInitWork spec input 0 ∧
          TM.transitionTape out = natTape 0) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
      (prefixInitInput_zero_parked input).read_ne_start
      (fun i => (prefixInitWork_parked spec input 0 i).read_ne_start)
      (natTape_parked_internal 0).read_ne_start
    exact ⟨htransition.1, htransition.2.1, htransition.2.2⟩
  have htail := TM.seqTM_hoareTimeSpace
    (TM.rewindInputTM (n := workTapeCount spec)) (prefixInitTM spec)
    hrewind hprefixTransition hprefix
  have hlengthTransition :
      ∀ inp work out, LengthReady spec input inp work out →
        LengthReady spec input (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out hready
    have hinputParked : TM.Parked inp :=
      ⟨by rw [hready.inputHead]; omega,
        hready.input_startInvariant.2⟩
    have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
      hinputParked.read_ne_start
      (fun i => (hready.work_parked i).read_ne_start)
      hready.output_parked.read_ne_start
    rw [htransition.1, htransition.2.1, htransition.2.2]
    exact hready
  have hfull := TM.seqTM_hoareTimeSpace
    (TM.binaryLengthTM zeroAddress)
    (TM.seqTM TM.rewindInputTM (prefixInitTM spec))
    hlength hlengthTransition htail
  simpa [initializeTM, zeroAddress, initializeTime, initializeSpace,
    max_eq_left] using hfull

private theorem prefixInitInput_parked
    (input : List Bool) (processed : ℕ) :
    TM.Parked (prefixInitInput input processed) := by
  constructor
  · simp [prefixInitInput]
  · intro j hj
    simp only [prefixInitInput]
    simpa using Tape.init_ofBool_cells_ne_start input j hj

private theorem prefixInitWork_eq_executionWork_initial_internal
    {program : Program} (spec : Spec program) (input : List Bool) :
    prefixInitWork spec input (prefixInitTime spec) =
      executionWork spec input (DenseOverlay.Snapshot.initial input) := by
  funext i
  by_cases hregister : i.val < spec.registerBound
  · have hpc : i ≠ pcTape spec := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [pcTape, scratchTape_val_internal] at hval
      omega
    rw [executionWork, Function.update_of_ne hpc]
    simp only [snapshotWork, prefixInitWork, hregister, ↓reduceDIte]
    rw [prefixInitValue_final spec input i.val hregister,
      initial_denseRead_eq_initRegs]
  · by_cases hpc : i = pcTape spec
    · subst i
      rw [executionWork_pc_internal]
      simp [prefixInitWork, pcTape, scratchTape_val_internal,
        DenseOverlay.Snapshot.initial]
    · rw [executionWork, Function.update_of_ne hpc]
      simp [snapshotWork, prefixInitWork, hregister]

private theorem executionWork_head_internal
    {program : Program} (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) (i : Fin (workTapeCount spec)) :
    (executionWork spec input snapshot i).head = 1 := by
  by_cases hpc : i = pcTape spec
  · subst i
    simp [executionWork_pc_internal, natTape, Tape.move]
  · rw [executionWork, Function.update_of_ne hpc]
    by_cases hregister : i.val < spec.registerBound
    · simp [snapshotWork, hregister, natTape, Tape.move]
    · simp [snapshotWork, hregister, natTape, Tape.move]

/-- The executable initializer reaches the exact direct-register boundary
used by the instruction controller, with the public input rewound to cell
one. -/
private theorem executionInitializeTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program) (input : List Bool) :
    (executionInitializeTM spec).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
          work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = executionInput input ∧
          work =
            executionWork spec input (DenseOverlay.Snapshot.initial input) ∧
          out = natTape 0)
      (initializeTime spec input.length + 1 + (input.length + 3))
      input.length (initializeSpace spec input.length) := by
  let initial := DenseOverlay.Snapshot.initial input
  let mid : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = prefixInitInput input (prefixInitTime spec) ∧
      work = prefixInitWork spec input (prefixInitTime spec) ∧
      Ready spec input initial work ∧ out = natTape 0
  let final : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = executionInput input ∧
      work = executionWork spec input initial ∧ out = natTape 0
  let stable : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
      work = executionWork spec input initial ∧ out = natTape 0
  have hrewindTimeRaw := TM.rewindInputTM_hoareTime_frame
    (n := workTapeCount spec) (input.length + 1) (P := stable)
    (by
      intro inp work out inp' work' out' hstable hcells hhead hwork hout
      subst work'
      subst out'
      exact ⟨hcells.trans hstable.1, hstable.2⟩)
  have hrewindTime :
      (TM.rewindInputTM (n := workTapeCount spec)).HoareTime mid final
        (input.length + 3) := by
    apply hrewindTimeRaw.consequence
    · rintro inp work out ⟨rfl, rfl, hready, rfl⟩
      have hinputParked :=
        prefixInitInput_parked input (prefixInitTime spec)
      have hworkEq :=
        prefixInitWork_eq_executionWork_initial_internal spec input
      refine ⟨?_, ?_, ?_, (natTape_parked_internal 0).read_ne_start,
        (natTape_parked_internal 0).1, ?_, ?_⟩
      · simp [prefixInitInput, Tape.init]
      · intro j hj
        simpa [prefixInitInput] using
          Tape.init_ofBool_cells_ne_start input j hj
      · simp [prefixInitInput]
      · intro i
        exact ⟨(hready.parked i).read_ne_start, (hready.parked i).1⟩
      · exact ⟨by simp [prefixInitInput], hworkEq, rfl⟩
    · rintro inp work out ⟨hhead, hcells, hwork, hout⟩
      have hinp : inp = executionInput input := by
        apply Tape.ext
        · simpa [executionInput, Tape.move] using hhead
        · simpa [executionInput] using hcells
      exact ⟨hinp, hwork, hout⟩
    · omega
  have hrewindSpace :
      (TM.rewindInputTM (n := workTapeCount spec)).HoareSpace mid
        input.length (initializeSpace spec input.length) := by
    apply (rewindInputTM_hoareSpace_internal
      (n := workTapeCount spec)
      (inputLength := input.length)
      (space := initializeSpace spec input.length)).weaken_pre
    rintro inp work out ⟨rfl, rfl, hready, rfl⟩
    refine ⟨?_, ?_, hready.parked, ?_, natTape_parked_internal 0⟩
    · constructor
      · simp [prefixInitInput, Tape.init]
      · intro j hj
        simpa [prefixInitInput] using
          Tape.init_ofBool_cells_ne_start input j hj
    · simp [prefixInitInput]
    · intro i
      rw [prefixInitWork_eq_executionWork_initial_internal spec input,
        executionWork_head_internal]
      simp [initializeSpace]
  have hrewind :
      (TM.rewindInputTM (n := workTapeCount spec)).HoareTimeSpace
        mid final (input.length + 3) input.length
          (initializeSpace spec input.length) :=
    hrewindTime.and_hoareSpace hrewindSpace
  have hinitialize := initializeTM_hoareTimeSpace_internal spec input
  have htransition :
      ∀ inp work out, mid inp work out →
        mid (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    rintro inp work out ⟨rfl, rfl, hready, rfl⟩
    have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
      (prefixInitInput_parked input
        (prefixInitTime spec)).read_ne_start
      (fun i => (hready.parked i).read_ne_start)
      (natTape_parked_internal 0).read_ne_start
    rw [htransition.1, htransition.2.1, htransition.2.2]
    exact ⟨rfl, rfl, hready, rfl⟩
  have hfull := TM.seqTM_hoareTimeSpace
    (initializeTM spec) TM.rewindInputTM
    hinitialize htransition hrewind
  simpa [executionInitializeTM, initial, mid, final] using hfull

theorem snapshotWork_ready_internal {program : Program}
    (spec : Spec program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot) :
    Ready spec input snapshot (snapshotWork spec input snapshot) := by
  refine ⟨?_, ?_, ?_⟩
  · intro address haddress
    simpa [snapshotWork, registerTape, workTapeCount, haddress] using
      natTape_hasBinaryNat_internal
        (DenseOverlay.read input snapshot.overlay address)
  · intro slot
    have hnot :
        ¬(spec.registerBound + slot.val < spec.registerBound) := by omega
    simpa [snapshotWork, scratchTape, workTapeCount, hnot] using
      natTape_hasBinaryNat_internal 0
  · intro i
    by_cases hregister : i.val < spec.registerBound
    · simpa [snapshotWork, hregister] using
        natTape_parked_internal
          (DenseOverlay.read input snapshot.overlay i.val)
    · simpa [snapshotWork, hregister] using natTape_parked_internal 0

theorem readRoute_eq_direct_internal {registerBound address : ℕ}
    (haddress : address < registerBound) :
    readRoute registerBound address = .inl ⟨address, haddress⟩ := by
  simp [readRoute, haddress]

theorem readRoute_eq_fallback_internal {registerBound address : ℕ}
    (haddress : registerBound ≤ address) :
    readRoute registerBound address = .inr () := by
  simp [readRoute, Nat.not_lt.mpr haddress]

private theorem registerStore_read_eq_zero_of_covered_ge
    {overlay : DenseOverlay.Store} {allowed : Finset ℕ}
    {registerBound address : ℕ}
    (hcovered : Covered overlay allowed)
    (hallowed : ∀ current ∈ allowed, current < registerBound)
    (haddress : registerBound ≤ address) :
    RegisterStore.read overlay address = 0 := by
  induction overlay with
  | nil =>
      simp [RegisterStore.read]
  | cons entry rest ih =>
      rcases entry with ⟨storedAddress, tag⟩
      have hstoredMem : storedAddress ∈ allowed :=
        hcovered (storedAddress, tag) (by simp)
      have hstoredLt := hallowed storedAddress hstoredMem
      have hne : address ≠ storedAddress := by omega
      simp only [RegisterStore.read, if_neg hne]
      apply ih
      intro current hcurrent
      exact hcovered current (by simp [hcurrent])

theorem routedRead_eq_denseRead_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (address : ℕ) :
    routedRead input snapshot spec.registerBound address =
      DenseOverlay.read input snapshot.overlay address := by
  by_cases haddress : address < spec.registerBound
  · simp [routedRead, readRoute, haddress]
  · have hge : spec.registerBound ≤ address := Nat.le_of_not_gt haddress
    have htag : RegisterStore.read snapshot.overlay address = 0 :=
      registerStore_read_eq_zero_of_covered_ge hcovered spec.allowed_lt hge
    simp [routedRead, readRoute, haddress, DenseOverlay.read, htag]

private theorem hasBinaryNat_eq_natTape {tape : Tape} {value : ℕ}
    (hvalue : tape.HasBinaryNat value) :
    tape = natTape value := by
  simpa [natTape] using hvalue.eq_init_move_right

private theorem executionInput_parked (input : List Bool) :
    TM.Parked (executionInput input) := by
  refine ⟨by simp [executionInput, Tape.move], ?_⟩
  simpa [executionInput] using
    Tape.init_ofBool_move_right_cells_ne_start input

private theorem readTreeReady_update_selector
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address base base' value : ℕ)
    (work₀ : Fin (workTapeCount spec) → Tape)
    (hready : ReadTreeReady spec input snapshot address base work₀)
    (hvalue : value = address - base') :
    ReadTreeReady spec input snapshot address base'
      (Function.update work₀ (selectorTape spec) (natTape value)) := by
  have hlhs : lhsTape spec ≠ selectorTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hresult : resultTape spec ≠ selectorTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcounter : counterTape spec ≠ selectorTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcopy : copyScratchTape spec ≠ selectorTape spec :=
    scratchTape_ne_internal spec (by decide)
  refine
    { query := by
        rw [Function.update_of_ne hlhs]
        exact hready.query
      selector := by
        rw [Function.update_self, ← hvalue]
        exact natTape_hasBinaryNat_internal value
      result := by
        rw [Function.update_of_ne hresult]
        exact hready.result
      counter := by
        rw [Function.update_of_ne hcounter]
        exact hready.counter
      copyScratch := by
        rw [Function.update_of_ne hcopy]
        exact hready.copyScratch
      register := by
        intro bounded
        have hne :
            registerTape spec bounded.val bounded.isLt ≠
              selectorTape spec :=
          registerTape_ne_scratchTape_internal spec bounded.val
            bounded.isLt 11
        rw [Function.update_of_ne hne]
        exact hready.register bounded
      parked := by
        intro i
        by_cases hi : i = selectorTape spec
        · subst i
          rw [Function.update_self]
          exact natTape_parked_internal value
        · rw [Function.update_of_ne hi]
          exact hready.parked i }

private theorem directReadTreeBranchTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (bounded : Fin spec.registerBound)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (hready : ReadTreeReady spec input snapshot bounded.val bounded.val work₀)
    (houtput : TM.Parked out₀) :
    (directReadTreeBranchTM spec bounded).HoareTime
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work = Function.update work₀ (resultTape spec)
          (natTape
            (DenseOverlay.read input snapshot.overlay bounded.val)) ∧
        out = out₀)
      (TM.binaryCopyTime
        (DenseOverlay.read input snapshot.overlay bounded.val) 0) := by
  have hsrcResult :
      registerTape spec bounded.val bounded.isLt ≠ resultTape spec :=
    registerTape_ne_scratchTape_internal spec bounded.val bounded.isLt 2
  have hsrcScratch :
      registerTape spec bounded.val bounded.isLt ≠ copyScratchTape spec :=
    registerTape_ne_scratchTape_internal spec bounded.val bounded.isLt 9
  have hresultScratch : resultTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame
    (registerTape spec bounded.val bounded.isLt)
    (resultTape spec) (copyScratchTape spec)
    hsrcResult hsrcScratch hresultScratch
    (DenseOverlay.read input snapshot.overlay bounded.val) 0
    (executionInput input) work₀ out₀
    (hready.register bounded) hready.result hready.copyScratch
    (executionInput_parked input)
    (fun i _ _ _ => hready.parked i) houtput
  simpa [directReadTreeBranchTM, natTape] using hcopy

private theorem fallbackReadTreeBranchTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address base : ℕ)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (haddress : address ≠ 0)
    (hready : ReadTreeReady spec input snapshot address base work₀)
    (houtput : TM.Parked out₀) :
    (fallbackReadTreeBranchTM spec).HoareTime
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work = Function.update work₀ (resultTape spec)
          (natTape (RAM.initRegs input address)) ∧
        out = out₀)
      (Machine.denseInputLookupTime input.length address) := by
  have hqc : lhsTape spec ≠ counterTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hqr : lhsTape spec ≠ resultTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hqs : lhsTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcr : counterTape spec ≠ resultTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcs : counterTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hrs : resultTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hlookup := Machine.denseInputLookupTM_hoareTime
    (lhsTape spec) (counterTape spec) (resultTape spec)
    (copyScratchTape spec) hqc hqr hqs hcr hcs hrs
    input address work₀ out₀ haddress
    ({ query := hready.query
       counter := hready.counter
       result := hready.result
       scratch := hready.copyScratch
       parked := hready.parked } :
      Machine.DenseInputLookupReady
        (lhsTape spec) (counterTape spec) (resultTape spec)
        (copyScratchTape spec) address work₀)
    houtput
  apply hlookup.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hresult, hout⟩
    refine ⟨hinp, ?_, hout⟩
    funext i
    by_cases hiResult : i = resultTape spec
    · subst i
      rw [Function.update_self]
      exact hasBinaryNat_eq_natTape hresult.result_value
    · rw [Function.update_of_ne hiResult]
      by_cases hiQuery : i = lhsTape spec
      · subst i
        exact hresult.query_eq
      by_cases hiCounter : i = counterTape spec
      · subst i
        rw [hasBinaryNat_eq_natTape hresult.counter_zero,
          hasBinaryNat_eq_natTape hready.counter]
      by_cases hiScratch : i = copyScratchTape spec
      · subst i
        exact hresult.scratch_eq
      · exact hresult.frame i hiQuery hiCounter hiResult hiScratch
  · exact le_rfl

theorem readDispatchTreeTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address remaining base : ℕ)
    (hbound : base + remaining = spec.registerBound)
    (hbase : base ≤ address)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (hready : ReadTreeReady spec input snapshot address base work₀)
    (houtput : TM.Parked out₀) :
    (readDispatchTreeTM spec remaining base hbound).HoareTime
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work =
          Function.update
            (Function.update work₀ (selectorTape spec) (natTape 0))
            (resultTape spec)
            (natTape
              (routedRead input snapshot spec.registerBound address)) ∧
        out = out₀)
      (readDispatchTreeTime spec input snapshot address remaining base) := by
  induction remaining generalizing base work₀ with
  | zero =>
      have hge : spec.registerBound ≤ address := by omega
      have haddress : address ≠ 0 := by
        have hpositive := registerBound_pos_internal spec
        omega
      let work₁ :=
        Function.update work₀ (selectorTape spec) (natTape 0)
      have hresetRaw := TM.resetBinaryWorkTM_hoareTime_frame
        (selectorTape spec) (address - base).bits 1
        (executionInput input) work₀ out₀
        hready.selector.2.hasBinaryContent hready.selector.1
        ⟨by rw [hready.selector.2.1],
          by rw [hready.selector.2.1]⟩
        (executionInput_parked input)
        (fun i _ => hready.parked i) houtput
      have hreset :
          (TM.resetBinaryWorkTM (selectorTape spec)).HoareTime
            (fun inp work out =>
              inp = executionInput input ∧ work = work₀ ∧ out = out₀)
            (fun inp work out =>
              inp = executionInput input ∧ work = work₁ ∧ out = out₀)
            (TM.resetBinaryWorkTime 1 (address - base).bits.length) := by
        simpa [work₁, natTape] using hresetRaw
      have hready₁ :
          ReadTreeReady spec input snapshot address address work₁ := by
        exact readTreeReady_update_selector spec input snapshot address base
          address 0 work₀ hready (by simp)
      have hfallback :=
        fallbackReadTreeBranchTM_hoareTime_internal spec input snapshot
          address address work₁ out₀ haddress hready₁ houtput
      have htransition :
          ∀ inp work out,
            (inp = executionInput input ∧ work = work₁ ∧ out = out₀) →
            (TM.transitionInput inp = executionInput input ∧
              (fun i => TM.transitionTape (work i)) = work₁ ∧
              TM.transitionTape out = out₀) := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
          (executionInput_parked input).read_ne_start
          (fun i => (hready₁.parked i).read_ne_start)
          houtput.read_ne_start
        exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
      have hseq := TM.seqTM_hoareTime
        (TM.resetBinaryWorkTM (selectorTape spec))
        (fallbackReadTreeBranchTM spec) hreset htransition hfallback
      have hrouted :
          routedRead input snapshot spec.registerBound address =
            RAM.initRegs input address := by
        simp [routedRead, readRoute, Nat.not_lt.mpr hge]
      simpa [readDispatchTreeTM, readDispatchTreeTime, work₁, hrouted]
        using hseq
  | succ remaining ih =>
      have hbaseLt : base < spec.registerBound := by omega
      let bounded : Fin spec.registerBound := ⟨base, hbaseLt⟩
      by_cases heq : address = base
      · subst address
        have hselectorZero : work₀ (selectorTape spec) = natTape 0 :=
          hasBinaryNat_eq_natTape (by simpa using hready.selector)
        have hdirect :=
          directReadTreeBranchTM_hoareTime_internal spec input snapshot
            bounded work₀ out₀ (by simpa [bounded] using hready) houtput
        intro inp work out hpre
        obtain ⟨directDone, time, htime, hreach, hhalt,
            hpost⟩ := hdirect inp work out hpre
        have hblank : (work (selectorTape spec)).read = Γ.blank := by
          rw [hpre.2.1]
          exact hready.selector.read_eq_blank_iff.mpr (by simp)
        have hinputRead : inp.read ≠ Γ.start := by
          rw [hpre.1]
          exact (executionInput_parked input).read_ne_start
        have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
          intro i
          rw [hpre.2.1]
          exact (hready.parked i).read_ne_start
        have houtRead : out.read ≠ Γ.start := by
          rw [hpre.2.2]
          exact houtput.read_ne_start
        obtain ⟨done, hreach', hhalt', hdoneInput, hdoneWork,
            hdoneOutput⟩ :=
          TM.branchWorkBlankTM_reachesIn_blank_frame
            (selectorTape spec)
            (directReadTreeBranchTM spec bounded)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (readDispatchTreeTM spec remaining (base + 1) (by omega)))
            inp work out hblank hinputRead hworkRead houtRead hreach hhalt
        refine ⟨done, time + 1, ?_, ?_, hhalt', ?_⟩
        · simpa [readDispatchTreeTime] using
            Nat.add_le_add_right htime 1
        · simpa [readDispatchTreeTM] using hreach'
        · rcases hpost with ⟨hinp, hwork, hout⟩
          rw [hdoneInput, hdoneWork, hdoneOutput, hinp, hwork, hout]
          have hroute :
              routedRead input snapshot spec.registerBound base =
                DenseOverlay.read input snapshot.overlay base := by
            simp [routedRead, readRoute, hbaseLt]
          rw [hroute]
          simp only [true_and]
          rw [← hselectorZero, Function.update_eq_self]
          simp [bounded]
      · have hbaseStrict : base < address := by omega
        let predecessor := address - base - 1
        have hselectorValue : address - base = predecessor + 1 := by
          dsimp [predecessor]
          omega
        have hpredRaw := TM.binaryPredTM_hoareTime_frame
          (selectorTape spec) predecessor
          (executionInput input) work₀ out₀
          (by simpa [hselectorValue] using hready.selector)
          (executionInput_parked input).read_ne_start
          (fun i _ => (hready.parked i).read_ne_start)
          houtput.read_ne_start
        let work₁ :=
          Function.update work₀ (selectorTape spec)
            (natTape predecessor)
        have hpred :
            (TM.binaryPredTM (selectorTape spec)).HoareTime
              (fun inp work out =>
                inp = executionInput input ∧ work = work₀ ∧ out = out₀)
              (fun inp work out =>
                inp = executionInput input ∧ work = work₁ ∧ out = out₀)
              (TM.binaryPredTime predecessor) := by
          apply hpredRaw.consequence
          · exact fun _ _ _ h => h
          · rintro inp work out ⟨hinp, hframe, hvalue, hout⟩
            refine ⟨hinp, ?_, hout⟩
            funext i
            by_cases hi : i = selectorTape spec
            · subst i
              simp only [work₁, Function.update_self]
              exact hasBinaryNat_eq_natTape hvalue
            · simp only [work₁, Function.update_of_ne hi]
              exact hframe i hi
          · exact le_rfl
        have hready₁ :
            ReadTreeReady spec input snapshot address (base + 1) work₁ := by
          apply readTreeReady_update_selector spec input snapshot address base
            (base + 1) predecessor work₀ hready
          dsimp [predecessor]
          omega
        have hrecursive := ih (base + 1) (by omega) (by omega)
          work₁ hready₁
        have htransition :
            ∀ inp work out,
              (inp = executionInput input ∧ work = work₁ ∧ out = out₀) →
              (TM.transitionInput inp = executionInput input ∧
                (fun i => TM.transitionTape (work i)) = work₁ ∧
                TM.transitionTape out = out₀) := by
          rintro inp work out ⟨rfl, rfl, rfl⟩
          have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
            (executionInput_parked input).read_ne_start
            (fun i => (hready₁.parked i).read_ne_start)
            houtput.read_ne_start
          exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
        have hseqRaw := TM.seqTM_hoareTime
          (TM.binaryPredTM (selectorTape spec))
          (readDispatchTreeTM spec remaining (base + 1) (by omega))
          hpred htransition hrecursive
        have hseq :
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (readDispatchTreeTM spec remaining (base + 1)
                (by omega))).HoareTime
              (fun inp work out =>
                inp = executionInput input ∧ work = work₀ ∧ out = out₀)
              (fun inp work out =>
                inp = executionInput input ∧
                work =
                  Function.update
                    (Function.update work₀ (selectorTape spec) (natTape 0))
                    (resultTape spec)
                    (natTape
                      (routedRead input snapshot spec.registerBound address)) ∧
                out = out₀)
              (TM.binaryPredTime predecessor + 1 +
                readDispatchTreeTime spec input snapshot address remaining
                  (base + 1)) := by
          apply hseqRaw.consequence
          · exact fun _ _ _ h => h
          · rintro inp work out ⟨hinp, hwork, hout⟩
            refine ⟨hinp, ?_, hout⟩
            simpa [work₁, Function.update_idem] using hwork
          · exact le_rfl
        intro inp work out hpre
        obtain ⟨branchDone, time, htime, hreach, hhalt,
            hpost⟩ := hseq inp work out hpre
        have hnonblank : (work (selectorTape spec)).read ≠ Γ.blank := by
          intro hblank
          have hzero := hready.selector.read_eq_blank_iff.mp (by
            rw [← hpre.2.1]
            exact hblank)
          omega
        have hinputRead : inp.read ≠ Γ.start := by
          rw [hpre.1]
          exact (executionInput_parked input).read_ne_start
        have hworkRead : ∀ i, (work i).read ≠ Γ.start := by
          intro i
          rw [hpre.2.1]
          exact (hready.parked i).read_ne_start
        have houtRead : out.read ≠ Γ.start := by
          rw [hpre.2.2]
          exact houtput.read_ne_start
        obtain ⟨done, hreach', hhalt', hdoneInput, hdoneWork,
            hdoneOutput⟩ :=
          TM.branchWorkBlankTM_reachesIn_nonblank_frame
            (selectorTape spec)
            (directReadTreeBranchTM spec bounded)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (readDispatchTreeTM spec remaining (base + 1) (by omega)))
            inp work out hnonblank hinputRead hworkRead houtRead hreach hhalt
        refine ⟨done, time + 1, ?_, ?_, hhalt', ?_⟩
        · simpa [readDispatchTreeTime, heq, predecessor] using
            Nat.add_le_add_right htime 1
        · simpa [readDispatchTreeTM] using hreach'
        · rw [hdoneInput, hdoneWork, hdoneOutput]
          exact hpost

theorem readDispatchTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address : ℕ)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (hready : ReadTreeReady spec input snapshot address address work₀)
    (houtput : TM.Parked out₀) :
    (readDispatchTM spec).HoareTime
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work =
          Function.update
            (Function.update work₀ (selectorTape spec) (natTape 0))
            (resultTape spec)
            (natTape
              (routedRead input snapshot spec.registerBound address)) ∧
        out = out₀)
      (readDispatchTime spec input snapshot address) := by
  have hlhsSelector : lhsTape spec ≠ selectorTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hlhsScratch : lhsTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hselectorScratch : selectorTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcopyRaw := TM.binaryCopyIntoTM_hoareTime_frame
    (lhsTape spec) (selectorTape spec) (copyScratchTape spec)
    hlhsSelector hlhsScratch hselectorScratch
    address 0 (executionInput input) work₀ out₀
    hready.query (by simpa using hready.selector) hready.copyScratch
    (executionInput_parked input)
    (fun i _ _ _ => hready.parked i) houtput
  let work₁ :=
    Function.update work₀ (selectorTape spec) (natTape address)
  have hcopy :
      (TM.binaryCopyIntoTM
        (lhsTape spec) (selectorTape spec)
        (copyScratchTape spec)).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = executionInput input ∧ work = work₁ ∧ out = out₀)
        (TM.binaryCopyTime address 0) := by
    simpa [work₁, natTape] using hcopyRaw
  have hready₁ :
      ReadTreeReady spec input snapshot address 0 work₁ := by
    exact readTreeReady_update_selector spec input snapshot address address
      0 address work₀ hready (by simp)
  have htree :=
    readDispatchTreeTM_hoareTime_internal spec input snapshot address
      spec.registerBound 0 (by omega) (by omega) work₁ out₀
      hready₁ houtput
  have htransition :
      ∀ inp work out,
        (inp = executionInput input ∧ work = work₁ ∧ out = out₀) →
        (TM.transitionInput inp = executionInput input ∧
          (fun i => TM.transitionTape (work i)) = work₁ ∧
          TM.transitionTape out = out₀) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
      (executionInput_parked input).read_ne_start
      (fun i => (hready₁.parked i).read_ne_start)
      houtput.read_ne_start
    exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
  have hseq := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM
      (lhsTape spec) (selectorTape spec) (copyScratchTape spec))
    (readDispatchTreeTM spec spec.registerBound 0 (by omega))
    hcopy htransition htree
  simpa [readDispatchTM, readDispatchTime, work₁,
    Function.update_idem] using hseq

private theorem seqTM_hoareTime_exact_internal {n : ℕ}
    (first second : TM n)
    (inp₀ : Tape)
    (work₀ work₁ work₂ : Fin n → Tape) (out₀ : Tape)
    (firstTime secondTime : ℕ)
    (hfirst : first.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      firstTime)
    (hsecond : second.HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      secondTime)
    (hinput : TM.Parked inp₀)
    (hwork₁ : ∀ i, TM.Parked (work₁ i))
    (houtput : TM.Parked out₀) :
    (TM.seqTM first second).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      (firstTime + 1 + secondTime) := by
  have htransition :
      ∀ inp work out,
        (inp = inp₀ ∧ work = work₁ ∧ out = out₀) →
        (TM.transitionInput inp = inp₀ ∧
          (fun i => TM.transitionTape (work i)) = work₁ ∧
          TM.transitionTape out = out₀) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start (fun i => (hwork₁ i).read_ne_start)
      houtput.read_ne_start
    exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
  exact TM.seqTM_hoareTime first second hfirst htransition hsecond

private theorem seqTM_hoareTimeSpace_exact_internal {n : ℕ}
    (first second : TM n)
    (inp₀ : Tape)
    (work₀ work₁ work₂ : Fin n → Tape) (out₀ : Tape)
    (firstTime secondTime inputLength space : ℕ)
    (hfirst : first.HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      firstTime inputLength space)
    (hsecond : second.HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      secondTime inputLength space)
    (hinput : TM.Parked inp₀)
    (hwork₁ : ∀ i, TM.Parked (work₁ i))
    (houtput : TM.Parked out₀) :
    (TM.seqTM first second).HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      (firstTime + 1 + secondTime) inputLength space := by
  have htransition :
      ∀ inp work out,
        (inp = inp₀ ∧ work = work₁ ∧ out = out₀) →
        (TM.transitionInput inp = inp₀ ∧
          (fun i => TM.transitionTape (work i)) = work₁ ∧
          TM.transitionTape out = out₀) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start (fun i => (hwork₁ i).read_ne_start)
      houtput.read_ne_start
    exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
  simpa using TM.seqTM_hoareTimeSpace first second
    hfirst htransition hsecond

private theorem binaryCopyIntoTM_hoareTime_exact_internal {n : ℕ}
    (src dst counter : Fin n)
    (hsrcDst : src ≠ dst) (hsrcCounter : src ≠ counter)
    (hdstCounter : dst ≠ counter)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ src).HasBinaryNat srcValue)
    (hdst : (work₀ dst).HasBinaryNat dstValue)
    (hcounter : (work₀ counter).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (TM.binaryCopyIntoTM src dst counter).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dst (natTape srcValue) ∧
        out = out₀)
      (TM.binaryCopyTime srcValue dstValue) := by
  simpa [natTape] using TM.binaryCopyIntoTM_hoareTime_frame
    src dst counter hsrcDst hsrcCounter hdstCounter srcValue dstValue
    inp₀ work₀ out₀ hsrc hdst hcounter hinput
    (fun i _ _ _ => hwork i) houtput

private theorem resetBinaryWorkTM_hoareTime_exact_internal {n : ℕ}
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (TM.resetBinaryWorkTM idx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (natTape 0) ∧
        out = out₀)
      (TM.resetBinaryWorkTime 1 value.bits.length) := by
  have hraw := TM.resetBinaryWorkTM_hoareTime_frame
    idx value.bits 1 inp₀ work₀ out₀
    hvalue.2.hasBinaryContent hvalue.1
    ⟨by rw [hvalue.2.1], by rw [hvalue.2.1]⟩
    hinput (fun i _ => hwork i) houtput
  simpa [natTape] using hraw

private theorem update_natTape_parked_internal {n : ℕ}
    (work : Fin n → Tape) (idx : Fin n) (value : ℕ)
    (hwork : ∀ i, TM.Parked (work i)) :
    ∀ i, TM.Parked (Function.update work idx (natTape value) i) := by
  intro i
  by_cases hi : i = idx
  · subst i
    simp [natTape_parked_internal]
  · simpa [hi] using hwork i

private theorem setNatTM_hoareTime_internal {n : ℕ}
    (idx : Fin n) (oldValue value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hold : (work₀ idx).HasBinaryNat oldValue)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∃ time,
      (setNatTM idx value).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ idx (natTape value) ∧
          out = out₀)
        time := by
  let work₁ := Function.update work₀ idx (natTape 0)
  have hresetRaw := TM.resetBinaryWorkTM_hoareTime_frame
    idx oldValue.bits 1 inp₀ work₀ out₀
    hold.2.hasBinaryContent hold.1
    ⟨by rw [hold.2.1], by rw [hold.2.1]⟩
    hinput (fun i _ => hwork i) houtput
  have hreset :
      (TM.resetBinaryWorkTM idx).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧ work = work₁ ∧ out = out₀)
        (TM.resetBinaryWorkTime 1 oldValue.bits.length) := by
    simpa [work₁, natTape] using hresetRaw
  have hwork₁ : ∀ i, TM.Parked (work₁ i) := by
    intro i
    by_cases hi : i = idx
    · subst i
      simp [work₁, natTape_parked_internal]
    · simpa [work₁, hi] using hwork i
  have haddRaw := TM.binaryAddConstTM_hoareTime_frame
    idx value 0 inp₀ work₁ out₀
    (by
      simp [work₁]
      exact natTape_hasBinaryNat_internal 0)
    hinput (fun i _ => hwork₁ i) houtput
  have hadd :
      (TM.binaryAddConstTM idx value).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = work₁ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ idx (natTape value) ∧
          out = out₀)
        (TM.binaryAddConstTime value 0) := by
    apply haddRaw.consequence
    · exact fun _ _ _ h => h
    · rintro inp work out ⟨hinp, hworkEq, hout⟩
      refine ⟨hinp, ?_, hout⟩
      simpa [work₁, natTape, Function.update_idem] using hworkEq
    · exact le_rfl
  have htransition :
      ∀ inp work out,
        (inp = inp₀ ∧ work = work₁ ∧ out = out₀) →
        (TM.transitionInput inp = inp₀ ∧
          (fun i => TM.transitionTape (work i)) = work₁ ∧
          TM.transitionTape out = out₀) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start (fun i => (hwork₁ i).read_ne_start)
      houtput.read_ne_start
    exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
  exact ⟨_, by
    simpa [setNatTM] using TM.seqTM_hoareTime
      (TM.resetBinaryWorkTM idx) (TM.binaryAddConstTM idx value)
      hreset htransition hadd⟩

private theorem binarySuccTM_hoareTime_exact_internal {n : ℕ}
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (TM.binarySuccTM idx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (natTape (value + 1)) ∧
        out = out₀)
      (TM.binarySuccTime value) := by
  have hraw := TM.binarySuccTM_hoareTime_frame
    idx value inp₀ work₀ out₀ hvalue hinput.read_ne_start
    (fun i _ => (hwork i).read_ne_start) houtput.read_ne_start
  apply hraw.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hframe, hnew, hout⟩
    refine ⟨hinp, ?_, hout⟩
    funext i
    by_cases hi : i = idx
    · subst i
      rw [Function.update_self]
      exact hasBinaryNat_eq_natTape hnew
    · rw [Function.update_of_ne hi]
      exact hframe i hi
  · exact le_rfl

private theorem binaryPredTM_hoareTime_exact_internal {n : ℕ}
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (TM.binaryPredTM idx).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (natTape value) ∧
        out = out₀)
      (TM.binaryPredTime value) := by
  have hraw := TM.binaryPredTM_hoareTime_frame
    idx value inp₀ work₀ out₀ hvalue hinput.read_ne_start
    (fun i _ => (hwork i).read_ne_start) houtput.read_ne_start
  apply hraw.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hframe, hnew, hout⟩
    refine ⟨hinp, ?_, hout⟩
    funext i
    by_cases hi : i = idx
    · subst i
      rw [Function.update_self]
      exact hasBinaryNat_eq_natTape hnew
    · rw [Function.update_of_ne hi]
      exact hframe i hi
  · exact le_rfl

private theorem binaryArithmeticTM_hoareTime_exact_internal
    {program : Program} (spec : Spec program)
    (op : BinaryOp) (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin (workTapeCount spec) → Tape)
    (out₀ : Tape)
    (hlhs : (work₀ (lhsTape spec)).HasBinaryNat lhs)
    (hrhs : (work₀ (rhsTape spec)).HasBinaryNat rhs)
    (hresult : (work₀ (resultTape spec)).HasBinaryNat 0)
    (hshift : (work₀ (shiftTape spec)).HasBinaryNat 0)
    (htmp : (work₀ (tmpTape spec)).HasBinaryNat 0)
    (hdbl : (work₀ (dblTape spec)).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∃ (value time : ℕ),
      value = (
        match op with
        | .add => lhs + rhs
        | .sub => lhs - rhs
        | .mul => lhs * rhs) ∧
      (binaryArithmeticTM spec op).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work =
            Function.update work₀ (resultTape spec)
              (natTape value) ∧
          out = out₀)
        time := by
  have hlhsRhs : lhsTape spec ≠ rhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hlhsResult : lhsTape spec ≠ resultTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hrhsResult : rhsTape spec ≠ resultTape spec :=
    scratchTape_ne_internal spec (by decide)
  let distinctAdd : TM.BinaryRippleAddDistinct
      (lhsTape spec) (rhsTape spec) (resultTape spec) :=
    ⟨hlhsRhs, hlhsResult, hrhsResult⟩
  let distinctSub : TM.BinaryRippleSubDistinct
      (lhsTape spec) (rhsTape spec) (resultTape spec) :=
    ⟨hlhsRhs, hlhsResult, hrhsResult⟩
  cases op with
  | add =>
      have hraw := TM.binaryRippleAddTM_hoareTime_frame
        (lhsTape spec) (rhsTape spec) (resultTape spec)
        distinctAdd lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult
        hinput (fun i _ _ _ => hwork i) houtput
      refine ⟨lhs + rhs, TM.binaryRippleAddTime lhs rhs, rfl, ?_⟩
      apply hraw.consequence
      · exact fun _ _ _ h => h
      · rintro inp work out
          ⟨hinp, hlhsNew, hrhsNew, hresultNew, hframe, hout⟩
        refine ⟨hinp, ?_, hout⟩
        funext i
        by_cases hiResult : i = resultTape spec
        · subst i
          rw [Function.update_self]
          exact hasBinaryNat_eq_natTape hresultNew
        · rw [Function.update_of_ne hiResult]
          by_cases hiLhs : i = lhsTape spec
          · subst i
            rw [hasBinaryNat_eq_natTape hlhsNew,
              hasBinaryNat_eq_natTape hlhs]
          by_cases hiRhs : i = rhsTape spec
          · subst i
            rw [hasBinaryNat_eq_natTape hrhsNew,
              hasBinaryNat_eq_natTape hrhs]
          · exact hframe i hiLhs hiRhs hiResult
      · exact le_rfl
  | sub =>
      have hraw := TM.binaryRippleSubTM_hoareTime_frame
        (lhsTape spec) (rhsTape spec) (resultTape spec)
        distinctSub lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult
        hinput (fun i _ _ _ => hwork i) houtput
      refine ⟨lhs - rhs, TM.binaryRippleSubTime lhs rhs, rfl, ?_⟩
      apply hraw.consequence
      · exact fun _ _ _ h => h
      · rintro inp work out
          ⟨hinp, hlhsNew, hrhsNew, hresultNew, hframe, hout⟩
        refine ⟨hinp, ?_, hout⟩
        funext i
        by_cases hiResult : i = resultTape spec
        · subst i
          rw [Function.update_self]
          exact hasBinaryNat_eq_natTape hresultNew
        · rw [Function.update_of_ne hiResult]
          by_cases hiLhs : i = lhsTape spec
          · subst i
            rw [hasBinaryNat_eq_natTape hlhsNew,
              hasBinaryNat_eq_natTape hlhs]
          by_cases hiRhs : i = rhsTape spec
          · subst i
            rw [hasBinaryNat_eq_natTape hrhsNew,
              hasBinaryNat_eq_natTape hrhs]
          · exact hframe i hiLhs hiRhs hiResult
      · exact le_rfl
  | mul =>
      have hraw := TM.binaryShiftMulTM_hoareTime_frame
        (multiplicationABI spec) lhs rhs inp₀ work₀ out₀
        (by simpa [multiplicationABI] using hlhs)
        (by simpa [multiplicationABI] using hrhs)
        (by simpa [multiplicationABI] using hresult)
        (by simpa [multiplicationABI] using hshift)
        (by simpa [multiplicationABI] using htmp)
        (by simpa [multiplicationABI] using hdbl)
        hinput hwork houtput
      refine ⟨lhs * rhs, TM.binaryShiftMulTime lhs rhs, rfl, ?_⟩
      apply hraw.consequence
      · exact fun _ _ _ h => h
      · rintro inp work out
          ⟨hinp, hlhsNew, hrhsNew, hresultNew, hshiftNew,
            htmpNew, hdblNew, hframe, hout⟩
        refine ⟨hinp, ?_, hout⟩
        funext i
        by_cases hiResult : i = resultTape spec
        · subst i
          rw [Function.update_self]
          exact hasBinaryNat_eq_natTape
            (by simpa [multiplicationABI] using hresultNew)
        · rw [Function.update_of_ne hiResult]
          by_cases hiLhs : i = lhsTape spec
          · subst i
            calc
              work (lhsTape spec) = natTape lhs :=
                hasBinaryNat_eq_natTape
                  (by simpa [multiplicationABI] using hlhsNew)
              _ = work₀ (lhsTape spec) :=
                (hasBinaryNat_eq_natTape hlhs).symm
          by_cases hiRhs : i = rhsTape spec
          · subst i
            calc
              work (rhsTape spec) = natTape rhs :=
                hasBinaryNat_eq_natTape
                  (by simpa [multiplicationABI] using hrhsNew)
              _ = work₀ (rhsTape spec) :=
                (hasBinaryNat_eq_natTape hrhs).symm
          by_cases hiShift : i = shiftTape spec
          · subst i
            calc
              work (shiftTape spec) = natTape 0 :=
                hasBinaryNat_eq_natTape
                  (by simpa [multiplicationABI] using hshiftNew)
              _ = work₀ (shiftTape spec) :=
                (hasBinaryNat_eq_natTape hshift).symm
          by_cases hiTmp : i = tmpTape spec
          · subst i
            calc
              work (tmpTape spec) = natTape 0 :=
                hasBinaryNat_eq_natTape
                  (by simpa [multiplicationABI] using htmpNew)
              _ = work₀ (tmpTape spec) :=
                (hasBinaryNat_eq_natTape htmp).symm
          by_cases hiDbl : i = dblTape spec
          · subst i
            calc
              work (dblTape spec) = natTape 0 :=
                hasBinaryNat_eq_natTape
                  (by simpa [multiplicationABI] using hdblNew)
              _ = work₀ (dblTape spec) :=
                (hasBinaryNat_eq_natTape hdbl).symm
          · exact hframe i
              (by simpa [multiplicationABI] using hiLhs)
              (by simpa [multiplicationABI] using hiRhs)
              (by simpa [multiplicationABI] using hiResult)
              (by simpa [multiplicationABI] using hiShift)
              (by simpa [multiplicationABI] using hiTmp)
              (by simpa [multiplicationABI] using hiDbl)
      · exact le_rfl

private theorem exactStart_withinAuxSpace_one_internal {n inputLength : ℕ}
    (tm : TM n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    ({ state := tm.qstart, input := inp₀, work := work₀, output := out₀ } :
      Complexity.Cfg n tm.Q).WithinAuxSpace inputLength 1 := by
  constructor
  · intro i
    rw [hworkHead i]
  · rw [hinputHead]
    omega

private theorem update_natTape_head_internal {n : ℕ}
    (work : Fin n → Tape) (idx : Fin n) (value : ℕ)
    (hwork : ∀ i, (work i).head = 1) :
    ∀ i, (Function.update work idx (natTape value) i).head = 1 := by
  intro i
  by_cases hi : i = idx
  · subst i
    simp [natTape, Tape.move]
  · simpa [hi] using hwork i

private theorem resetBinaryWorkTM_hoareTimeSpace_exact_internal {n : ℕ}
    (idx : Fin n) (value inputLength wordBits : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hvalueWidth : value.size ≤ wordBits)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (TM.resetBinaryWorkTM idx).HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (natTape 0) ∧
        out = out₀)
      (TM.resetBinaryWorkTime 1 value.bits.length)
      inputLength (instructionSpace wordBits) := by
  have htime := resetBinaryWorkTM_hoareTime_exact_internal
    idx value inp₀ work₀ out₀ hvalue hinput hwork houtput
  have hraw := htime.toHoareTimeSpace (inputLength := inputLength)
    (initialSpace := 1) (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      subst inp
      subst work
      subst out
      exact exactStart_withinAuxSpace_one_internal
        (TM.resetBinaryWorkTM idx) inp₀ work₀ out₀ hinputHead hworkHead)
  apply hraw.consequence
  · exact fun _ _ _ h => h
  · exact fun _ _ _ h => h
  · exact le_rfl
  · exact le_rfl
  · simp only [TM.resetBinaryWorkTime, TM.clearWorkTimeBound,
      Nat.size_eq_bits_len] at ⊢
    simp only [instructionSpace]
    omega

private theorem binaryCopyIntoTM_hoareTimeSpace_exact_internal {n : ℕ}
    (src dst counter : Fin n)
    (hsrcDst : src ≠ dst) (hsrcCounter : src ≠ counter)
    (hdstCounter : dst ≠ counter)
    (srcValue dstValue inputLength wordBits : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ src).HasBinaryNat srcValue)
    (hdst : (work₀ dst).HasBinaryNat dstValue)
    (hcounter : (work₀ counter).HasBinaryNat 0)
    (hsrcWidth : srcValue.size ≤ wordBits)
    (hdstWidth : dstValue.size ≤ wordBits)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (TM.binaryCopyIntoTM src dst counter).HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dst (natTape srcValue) ∧
        out = out₀)
      (TM.binaryCopyTime srcValue dstValue)
      inputLength (instructionSpace wordBits) := by
  have htime := binaryCopyIntoTM_hoareTime_exact_internal
    src dst counter hsrcDst hsrcCounter hdstCounter srcValue dstValue
    inp₀ work₀ out₀ hsrc hdst hcounter hinput hwork houtput
  have hraw := TM.binaryCopyIntoTM_hoareTimeSpace_frame
    src dst counter hsrcDst hsrcCounter hdstCounter
    srcValue dstValue inputLength 1 inp₀ work₀ out₀
    hsrc hdst hcounter hinput (fun i _ _ _ => hwork i) houtput
    (fun i => by rw [hworkHead i])
    (by rw [hinputHead]; omega)
  exact htime.and_hoareSpace
    (hraw.2.mono le_rfl
      (binaryCopySpace_le_instructionSpace hsrcWidth hdstWidth))

private theorem binarySuccTM_hoareTimeSpace_exact_internal {n : ℕ}
    (idx : Fin n) (value inputLength wordBits : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hvalueWidth : value.size ≤ wordBits)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (TM.binarySuccTM idx).HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (natTape (value + 1)) ∧
        out = out₀)
      (TM.binarySuccTime value) inputLength
      (instructionSpace wordBits) := by
  have htime := binarySuccTM_hoareTime_exact_internal
    idx value inp₀ work₀ out₀ hvalue hinput hwork houtput
  have hraw := TM.binarySuccTM_hoareTimeSpace_frame
    idx value inputLength 1 inp₀ work₀ out₀ hvalue
    hinput.read_ne_start (fun i _ => (hwork i).read_ne_start)
    houtput.read_ne_start
    (exactStart_withinAuxSpace_one_internal
      (TM.binarySuccTM idx) inp₀ work₀ out₀ hinputHead hworkHead)
  exact htime.and_hoareSpace
    (hraw.2.mono le_rfl
      (binarySuccSpace_le_instructionSpace hvalueWidth))

private theorem binaryPredTM_hoareTimeSpace_exact_internal {n : ℕ}
    (idx : Fin n) (value inputLength wordBits : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hvalueWidth : (value + 1).size ≤ wordBits)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (TM.binaryPredTM idx).HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (natTape value) ∧
        out = out₀)
      (TM.binaryPredTime value) inputLength
      (instructionSpace wordBits) := by
  have htime := binaryPredTM_hoareTime_exact_internal
    idx value inp₀ work₀ out₀ hvalue hinput hwork houtput
  have hraw := TM.binaryPredTM_hoareTimeSpace_frame
    idx value inputLength 1 inp₀ work₀ out₀ hvalue
    hinput.read_ne_start (fun i _ => (hwork i).read_ne_start)
    houtput.read_ne_start
    (exactStart_withinAuxSpace_one_internal
      (TM.binaryPredTM idx) inp₀ work₀ out₀ hinputHead hworkHead)
  exact htime.and_hoareSpace
    (hraw.2.mono le_rfl
      (by
        have hspace :=
          binaryPredSpace_le_instructionSpace
            (value := value + 1) hvalueWidth
        simpa using hspace))

private theorem binaryAddConstTM_hoareTimeSpace_exact_internal {n : ℕ}
    (idx : Fin n) (constant dstValue inputLength wordBits : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hfinalWidth : (dstValue + constant).size ≤ wordBits)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (TM.binaryAddConstTM idx constant).HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          (natTape (dstValue + constant)) ∧ out = out₀)
      (TM.binaryAddConstTime constant dstValue) inputLength
      (instructionSpace wordBits) := by
  have hrawTime := TM.binaryAddConstTM_hoareTime_frame
    idx constant dstValue inp₀ work₀ out₀ hdst hinput
    (fun i _ => hwork i) houtput
  have htime :
      (TM.binaryAddConstTM idx constant).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ idx
            (natTape (dstValue + constant)) ∧ out = out₀)
        (TM.binaryAddConstTime constant dstValue) := by
    simpa [natTape] using hrawTime
  have hrawSpace := TM.binaryAddConstTM_hoareTimeSpace_frame
    idx constant dstValue inputLength 1 inp₀ work₀ out₀
    hdst hinput (fun i _ => hwork i) houtput
    (fun i => by rw [hworkHead i])
    (by rw [hinputHead]; omega)
  have hspaceBound :
      TM.binaryAddConstSpace 1 constant dstValue ≤
        instructionSpace wordBits := by
    simp only [TM.binaryAddConstSpace, instructionSpace]
    have hsize := hfinalWidth
    omega
  exact htime.and_hoareSpace
    (hrawSpace.2.mono le_rfl hspaceBound)

private theorem setNatTM_hoareTimeSpace_internal {n : ℕ}
    (idx : Fin n) (oldValue value inputLength wordBits : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hold : (work₀ idx).HasBinaryNat oldValue)
    (holdWidth : oldValue.size ≤ wordBits)
    (hvalueWidth : value.size ≤ wordBits)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    ∃ time,
      (setNatTM idx value).HoareTimeSpace
        (fun inp work out =>
          inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work = Function.update work₀ idx (natTape value) ∧
          out = out₀)
        time inputLength (instructionSpace wordBits) := by
  let work₁ := Function.update work₀ idx (natTape 0)
  have hreset := resetBinaryWorkTM_hoareTimeSpace_exact_internal
    idx oldValue inputLength wordBits inp₀ work₀ out₀
    hold holdWidth hinput hwork houtput hinputHead hworkHead
  have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
    update_natTape_parked_internal work₀ idx 0 hwork
  have hwork₁Head : ∀ i, (work₁ i).head = 1 :=
    update_natTape_head_internal work₀ idx 0 hworkHead
  have hadd := binaryAddConstTM_hoareTimeSpace_exact_internal
    idx value 0 inputLength wordBits inp₀ work₁ out₀
    (by
      simp only [work₁, Function.update_self]
      exact natTape_hasBinaryNat_internal 0)
    (by simpa using hvalueWidth)
    hinput hwork₁Parked houtput hinputHead hwork₁Head
  have hseq := seqTM_hoareTimeSpace_exact_internal
    (TM.resetBinaryWorkTM idx) (TM.binaryAddConstTM idx value)
    inp₀ work₀ work₁
    (Function.update work₀ idx (natTape value)) out₀
    (TM.resetBinaryWorkTime 1 oldValue.bits.length)
    (TM.binaryAddConstTime value 0)
    inputLength (instructionSpace wordBits)
    hreset (by simpa [work₁, Function.update_idem] using hadd)
    hinput hwork₁Parked houtput
  exact ⟨_, by simpa [setNatTM] using hseq⟩

private theorem fallbackReadTreeBranchTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address base wordBits : ℕ)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (haddress : address ≠ 0)
    (haddressWidth : address.size ≤ wordBits)
    (hready : ReadTreeReady spec input snapshot address base work₀)
    (houtput : TM.Parked out₀)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (fallbackReadTreeBranchTM spec).HoareTimeSpace
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work = Function.update work₀ (resultTape spec)
          (natTape (RAM.initRegs input address)) ∧
        out = out₀)
      (Machine.denseInputLookupTime input.length address)
      input.length (instructionSpace wordBits) := by
  have hqc : lhsTape spec ≠ counterTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hqr : lhsTape spec ≠ resultTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hqs : lhsTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcr : counterTape spec ≠ resultTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcs : counterTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hrs : resultTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  let inp₀ := executionInput input
  let copiedWork :=
    Function.update work₀ (counterTape spec) (natTape address)
  have hinput : TM.Parked inp₀ := by
    simpa only [inp₀] using executionInput_parked input
  have hinputHead : inp₀.head = 1 := by
    simp [inp₀, executionInput, Tape.move]
  have hcopiedCounter :
      (copiedWork (counterTape spec)).HasBinaryNat address := by
    simp only [copiedWork, Function.update_self]
    exact natTape_hasBinaryNat_internal address
  have hcopiedResult :
      copiedWork (resultTape spec) = TM.resetBinaryBlank := by
    dsimp only [copiedWork]
    rw [Function.update_of_ne hcr.symm]
    exact (hasBinaryNat_eq_natTape hready.result).trans (by
      rfl)
  have hcopiedParked : ∀ i, TM.Parked (copiedWork i) :=
    update_natTape_parked_internal work₀ (counterTape spec)
      address hready.parked
  have hcopiedHead : ∀ i, (copiedWork i).head = 1 :=
    update_natTape_head_internal work₀ (counterTape spec)
      address hworkHead
  have hcopy := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (lhsTape spec) (counterTape spec) (copyScratchTape spec)
    hqc hqs hcs address 0 input.length wordBits
    inp₀ work₀ out₀ hready.query hready.counter hready.copyScratch
    haddressWidth (by simp) hinput hready.parked houtput
    hinputHead hworkHead
  let scannedPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp.head = input.length + 1 ∧
      inp.cells = inp₀.cells ∧
      (work (counterTape spec)).HasBinaryNat
        (address - input.length) ∧
      (work (resultTape spec)).HasBinaryNat
        (RAM.initRegs input address) ∧
      (∀ i, i ≠ counterTape spec → i ≠ resultTape spec →
        work i = copiedWork i) ∧
      (∀ i, TM.Parked (work i)) ∧ out = out₀
  have hscanTime :
      (Machine.denseInputScanTM
        (counterTape spec) (resultTape spec)).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
        scannedPost
        (Machine.denseInputScanTime input.length address) := by
    rintro inp work out ⟨hinp, hworkEq, hout⟩
    subst inp
    subst work
    subst out
    obtain ⟨done, hreach, hhalt, hdoneHead, hdoneCells,
        hdoneCounter, hdoneResult, hdoneOther, hdoneOutput⟩ :=
      Machine.denseInputScanTM_reachesIn_frame
        (counterTape spec) (resultTape spec) hcr input address
        copiedWork out₀ haddress hcopiedCounter hcopiedResult
        hcopiedParked houtput
    have hdoneParked : ∀ i, TM.Parked (done.work i) := by
      intro i
      by_cases hic : i = counterTape spec
      · subst i
        exact ⟨by rw [hdoneCounter.2.1],
          hdoneCounter.2.hasBinaryContent.cells_ne_start⟩
      · by_cases hir : i = resultTape spec
        · subst i
          exact ⟨by rw [hdoneResult.2.1],
            hdoneResult.2.hasBinaryContent.cells_ne_start⟩
        · rw [hdoneOther i hic hir]
          exact hcopiedParked i
    refine
      ⟨done, Machine.denseInputScanTime input.length address,
        le_rfl, ?_, hhalt, hdoneHead, ?_, hdoneCounter,
        hdoneResult, hdoneOther, hdoneParked, hdoneOutput⟩
    · simpa [inp₀, executionInput] using hreach
    · simpa [inp₀, executionInput] using hdoneCells
  have hscanSpace :
      (Machine.denseInputScanTM
        (counterTape spec) (resultTape spec)).HoareSpace
        (fun inp work out =>
          inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
        input.length (instructionSpace wordBits) := by
    rintro inp work out ⟨hinp, hworkEq, hout⟩ current hreach
    subst inp
    subst work
    subst out
    obtain ⟨time, hreachIn⟩ :=
      (Machine.denseInputScanTM
        (counterTape spec) (resultTape spec)).reaches_to_reachesIn hreach
    obtain ⟨done, hdoneReach, hdoneHalted, _⟩ :=
      Machine.denseInputScanTM_reachesIn_frame
        (counterTape spec) (resultTape spec) hcr input address
        copiedWork out₀ haddress hcopiedCounter hcopiedResult
        hcopiedParked houtput
    have htime :
        time ≤ Machine.denseInputScanTime input.length address :=
      (Machine.denseInputScanTM
        (counterTape spec) (resultTape spec)).reachesIn_le_halt
          hreachIn (by simpa [inp₀, executionInput] using hdoneReach)
          hdoneHalted
    have hprefix :=
      Machine.denseInputScanTM_prefix_withinAuxSpace
        (counterTape spec) (resultTape spec) hcr input address 1
        copiedWork out₀ haddress hcopiedCounter hcopiedResult
        hcopiedParked houtput (fun i => by rw [hcopiedHead i])
        time current (by simpa [inp₀, executionInput] using hreachIn)
        htime
    exact hprefix.mono le_rfl
      (denseInputScanSpace_le_instructionSpace haddressWidth)
  have hscan := hscanTime.and_hoareSpace hscanSpace
  let stablePost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp.cells = inp₀.cells ∧
      (work (counterTape spec)).HasBinaryNat
        (address - input.length) ∧
      (work (resultTape spec)).HasBinaryNat
        (RAM.initRegs input address) ∧
      (∀ i, i ≠ counterTape spec → i ≠ resultTape spec →
        work i = copiedWork i) ∧
      (∀ i, TM.Parked (work i)) ∧ out = out₀
  let rewoundPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out => inp.head = 1 ∧ stablePost inp work out
  have hrewindTime :
      (TM.rewindInputTM (n := workTapeCount spec)).HoareTime
        scannedPost rewoundPost (input.length + 3) := by
    have hraw := TM.rewindInputTM_hoareTime_frame
      (n := workTapeCount spec) (input.length + 1) (P := stablePost)
      (by
        intro inp work out inp' work' out' hstable hcells _hhead
          hworkEq hout
        subst work'
        subst out'
        exact ⟨hcells.trans hstable.1, hstable.2⟩)
    intro inp work out hscanned
    rcases hscanned with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    have hstart : inp.cells 0 = Γ.start := by
      rw [hcells]
      simp [inp₀, executionInput, Tape.move]
    have hnostart : ∀ j, j ≥ 1 → inp.cells j ≠ Γ.start := by
      intro j hj
      rw [hcells]
      simpa [inp₀, executionInput] using
        Tape.init_ofBool_move_right_cells_ne_start input j hj
    exact hraw inp work out
      ⟨hstart, hnostart, by omega,
        hout ▸ houtput.read_ne_start, hout ▸ houtput.1,
        fun i => ⟨(hparked i).read_ne_start, (hparked i).1⟩,
        hcells, hcounter, hresult, hother, hparked, hout⟩
  have hrewindSpace :
      (TM.rewindInputTM (n := workTapeCount spec)).HoareSpace
        scannedPost input.length (instructionSpace wordBits) := by
    apply (rewindInputTM_hoareSpace_internal
      (n := workTapeCount spec)
      (inputLength := input.length)
      (space := instructionSpace wordBits)).weaken_pre
    intro inp work out hscanned
    rcases hscanned with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    refine ⟨?_, by omega, hparked, ?_, by simpa [hout] using houtput⟩
    · constructor
      · rw [hcells]
        simp [inp₀, executionInput, Tape.move]
      · intro j hj
        rw [hcells]
        simpa [inp₀, executionInput] using
          Tape.init_ofBool_move_right_cells_ne_start input j hj
    · intro i
      have hheadOne : (work i).head = 1 := by
        by_cases hic : i = counterTape spec
        · subst i
          exact hcounter.2.1
        · by_cases hir : i = resultTape spec
          · subst i
            exact hresult.2.1
          · rw [hother i hic hir, hcopiedHead i]
      rw [hheadOne]
      exact one_le_instructionSpace wordBits
  have hrewind := hrewindTime.and_hoareSpace hrewindSpace
  have hremainingWidth :
      (address - input.length).size ≤ wordBits :=
    (Nat.size_le_size (Nat.sub_le address input.length)).trans
      haddressWidth
  have hresetTime :
      (TM.resetBinaryWorkTM (counterTape spec)).HoareTime
        rewoundPost (fun _ _ _ => True)
        (TM.resetBinaryWorkTime 1
          (address - input.length).bits.length) := by
    intro inp work out hrewound
    rcases hrewound with ⟨_hhead, hcells, hcounter, _hresult,
      _hother, hparked, hout⟩
    have hrun := TM.resetBinaryWorkTM_hoareTime_frame
      (counterTape spec) (address - input.length).bits 1
      inp work out hcounter.2.hasBinaryContent hcounter.1
      ⟨by rw [hcounter.2.1], by rw [hcounter.2.1]⟩
      (by
        constructor
        · omega
        · intro j hj
          rw [hcells]
          simpa [inp₀, executionInput] using
            Tape.init_ofBool_move_right_cells_ne_start input j hj)
      (fun i _ => hparked i) (by simpa [hout] using houtput)
    obtain ⟨done, time, htime, hreach, hhalt, _⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨done, time, htime, hreach, hhalt, trivial⟩
  have hresetRaw := hresetTime.toHoareTimeSpace
    (inputLength := input.length) (initialSpace := 1) (by
      intro inp work out hrewound
      rcases hrewound with ⟨hhead, _hcells, hcounter, hresult,
        hother, _hparked, _hout⟩
      apply exactStart_withinAuxSpace_one_internal
        (TM.resetBinaryWorkTM (counterTape spec)) inp work out hhead
      intro i
      by_cases hic : i = counterTape spec
      · subst i
        exact hcounter.2.1
      · by_cases hir : i = resultTape spec
        · subst i
          exact hresult.2.1
        · rw [hother i hic hir, hcopiedHead i])
  have hresetSpaceBound :
      1 + TM.resetBinaryWorkTime 1
          (address - input.length).bits.length ≤
        instructionSpace wordBits := by
    simp only [TM.resetBinaryWorkTime, TM.clearWorkTimeBound,
      Nat.size_eq_bits_len] at ⊢
    simp only [instructionSpace]
    omega
  have hreset := hresetRaw.consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) le_rfl le_rfl
      hresetSpaceBound
  have hscanTransition :
      ∀ inp work out, scannedPost inp work out →
        scannedPost (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out hscanned
    rcases hscanned with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    have hinpParked : TM.Parked inp := by
      refine ⟨by omega, ?_⟩
      intro j hj
      rw [hcells]
      simpa [inp₀, executionInput] using
        Tape.init_ofBool_move_right_cells_ne_start input j hj
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinpParked.read_ne_start (fun i => (hparked i).read_ne_start)
      (hout ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hhead, hcells, hcounter, hresult, hother, hparked, hout⟩
  have hrewindTransition :
      ∀ inp work out, rewoundPost inp work out →
        rewoundPost (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    intro inp work out hrewound
    rcases hrewound with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    have hinpParked : TM.Parked inp := by
      refine ⟨by omega, ?_⟩
      intro j hj
      rw [hcells]
      simpa [inp₀, executionInput] using
        Tape.init_ofBool_move_right_cells_ne_start input j hj
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinpParked.read_ne_start (fun i => (hparked i).read_ne_start)
      (hout ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hhead, hcells, hcounter, hresult, hother, hparked, hout⟩
  have hrewindReset := TM.seqTM_hoareTimeSpace
    (TM.rewindInputTM (n := workTapeCount spec))
    (TM.resetBinaryWorkTM (counterTape spec))
    hrewind hrewindTransition hreset
  have hscanTail := TM.seqTM_hoareTimeSpace
    (Machine.denseInputScanTM (counterTape spec) (resultTape spec))
    (TM.seqTM (TM.rewindInputTM (n := workTapeCount spec))
      (TM.resetBinaryWorkTM (counterTape spec)))
    hscan hscanTransition hrewindReset
  have hcopyTransition :
      ∀ inp work out,
        (inp = inp₀ ∧ work = copiedWork ∧ out = out₀) →
        (TM.transitionInput inp = inp₀ ∧
          (fun i => TM.transitionTape (work i)) = copiedWork ∧
          TM.transitionTape out = out₀) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start (fun i => (hcopiedParked i).read_ne_start)
      houtput.read_ne_start
    exact ⟨hi, hw, ho⟩
  have hall := TM.seqTM_hoareTimeSpace
    (TM.binaryCopyIntoTM
      (lhsTape spec) (counterTape spec) (copyScratchTape spec))
    (TM.seqTM
      (Machine.denseInputScanTM (counterTape spec) (resultTape spec))
      (TM.seqTM (TM.rewindInputTM (n := workTapeCount spec))
        (TM.resetBinaryWorkTM (counterTape spec))))
    hcopy hcopyTransition hscanTail
  have htime := fallbackReadTreeBranchTM_hoareTime_internal
    spec input snapshot address base work₀ out₀ haddress hready houtput
  have hspace :
      (fallbackReadTreeBranchTM spec).HoareSpace
        (fun inp work out =>
          inp = executionInput input ∧ work = work₀ ∧ out = out₀)
        input.length (instructionSpace wordBits) := by
    simpa [fallbackReadTreeBranchTM, Machine.denseInputLookupTM,
      inp₀, copiedWork] using hall.2
  exact htime.and_hoareSpace hspace

private theorem false_hoareTimeSpace_internal {n : ℕ}
    (tm : TM n) (time inputLength space : ℕ) :
    tm.HoareTimeSpace
      (fun _ _ _ => False) (fun _ _ _ => False)
      time inputLength space := by
  constructor
  · intro _inp _work _out hfalse
    exact hfalse.elim
  · intro _inp _work _out hfalse
    exact hfalse.elim

private theorem directReadTreeBranchTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (bounded : Fin spec.registerBound) (wordBits : ℕ)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (hvalueWidth :
      (DenseOverlay.read input snapshot.overlay bounded.val).size ≤ wordBits)
    (hready : ReadTreeReady spec input snapshot bounded.val bounded.val work₀)
    (houtput : TM.Parked out₀)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (directReadTreeBranchTM spec bounded).HoareTimeSpace
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work = Function.update work₀ (resultTape spec)
          (natTape
            (DenseOverlay.read input snapshot.overlay bounded.val)) ∧
        out = out₀)
      (TM.binaryCopyTime
        (DenseOverlay.read input snapshot.overlay bounded.val) 0)
      input.length (instructionSpace wordBits) := by
  have hsrcResult :
      registerTape spec bounded.val bounded.isLt ≠ resultTape spec :=
    registerTape_ne_scratchTape_internal spec bounded.val bounded.isLt 2
  have hsrcScratch :
      registerTape spec bounded.val bounded.isLt ≠ copyScratchTape spec :=
    registerTape_ne_scratchTape_internal spec bounded.val bounded.isLt 9
  have hresultScratch : resultTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  simpa [directReadTreeBranchTM] using
    binaryCopyIntoTM_hoareTimeSpace_exact_internal
      (registerTape spec bounded.val bounded.isLt)
      (resultTape spec) (copyScratchTape spec)
      hsrcResult hsrcScratch hresultScratch
      (DenseOverlay.read input snapshot.overlay bounded.val) 0
      input.length wordBits (executionInput input) work₀ out₀
      (hready.register bounded) hready.result hready.copyScratch
      hvalueWidth (by simp) (executionInput_parked input)
      hready.parked houtput (by simp [executionInput, Tape.move])
      hworkHead

private theorem readDispatchTreeTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address remaining base : ℕ)
    (hbound : base + remaining = spec.registerBound)
    (hbase : base ≤ address)
    (wordBits : ℕ)
    (haddressWidth : address.size ≤ wordBits)
    (hroutedWidth :
      (routedRead input snapshot spec.registerBound address).size ≤
        wordBits)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (hready : ReadTreeReady spec input snapshot address base work₀)
    (houtput : TM.Parked out₀)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (readDispatchTreeTM spec remaining base hbound).HoareTimeSpace
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work =
          Function.update
            (Function.update work₀ (selectorTape spec) (natTape 0))
            (resultTape spec)
            (natTape
              (routedRead input snapshot spec.registerBound address)) ∧
        out = out₀)
      (readDispatchTreeTime spec input snapshot address remaining base)
      input.length (instructionSpace wordBits) := by
  have htime := readDispatchTreeTM_hoareTime_internal
    spec input snapshot address remaining base hbound hbase work₀ out₀
      hready houtput
  induction remaining generalizing base work₀ with
  | zero =>
      have hge : spec.registerBound ≤ address := by omega
      have haddress : address ≠ 0 := by
        have hpositive := registerBound_pos_internal spec
        omega
      let work₁ :=
        Function.update work₀ (selectorTape spec) (natTape 0)
      have hselectorWidth :
          (address - base).size ≤ wordBits :=
        (Nat.size_le_size (Nat.sub_le address base)).trans haddressWidth
      have hreset := resetBinaryWorkTM_hoareTimeSpace_exact_internal
        (selectorTape spec) (address - base) input.length wordBits
        (executionInput input) work₀ out₀ hready.selector
        hselectorWidth (executionInput_parked input) hready.parked houtput
        (by simp [executionInput, Tape.move]) hworkHead
      have hready₁ :
          ReadTreeReady spec input snapshot address address work₁ :=
        readTreeReady_update_selector spec input snapshot address base
          address 0 work₀ hready (by simp)
      have hwork₁Head : ∀ i, (work₁ i).head = 1 :=
        update_natTape_head_internal work₀ (selectorTape spec) 0 hworkHead
      have hfallback :=
        fallbackReadTreeBranchTM_hoareTimeSpace_internal
          spec input snapshot address address wordBits work₁ out₀
          haddress haddressWidth hready₁ houtput hwork₁Head
      have hseq := seqTM_hoareTimeSpace_exact_internal
        (TM.resetBinaryWorkTM (selectorTape spec))
        (fallbackReadTreeBranchTM spec)
        (executionInput input) work₀ work₁
        (Function.update work₁ (resultTape spec)
          (natTape (RAM.initRegs input address)))
        out₀
        (TM.resetBinaryWorkTime 1 (address - base).bits.length)
        (Machine.denseInputLookupTime input.length address)
        input.length (instructionSpace wordBits)
        hreset hfallback (executionInput_parked input)
        hready₁.parked houtput
      have hrouted :
          routedRead input snapshot spec.registerBound address =
            RAM.initRegs input address := by
        simp [routedRead, readRoute, Nat.not_lt.mpr hge]
      have hspace :
          (readDispatchTreeTM spec 0 base hbound).HoareSpace
            (fun inp work out =>
              inp = executionInput input ∧ work = work₀ ∧ out = out₀)
            input.length (instructionSpace wordBits) := by
        simpa [readDispatchTreeTM, work₁, hrouted,
          Function.update_idem] using hseq.2
      exact htime.and_hoareSpace hspace
  | succ remaining ih =>
      have hbaseLt : base < spec.registerBound := by omega
      let bounded : Fin spec.registerBound := ⟨base, hbaseLt⟩
      let pre : TM.TapePred (workTapeCount spec) :=
        fun inp work out =>
          inp = executionInput input ∧ work = work₀ ∧ out = out₀
      have hframe :
          ∀ inp work out, pre inp work out →
            inp.read ≠ Γ.start ∧
              (∀ i, (work i).read ≠ Γ.start) ∧
              out.read ≠ Γ.start := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        exact ⟨(executionInput_parked input).read_ne_start,
          fun i => (hready.parked i).read_ne_start,
          houtput.read_ne_start⟩
      by_cases heq : address = base
      · subst address
        have hdirect :=
          directReadTreeBranchTM_hoareTimeSpace_internal
            spec input snapshot bounded wordBits work₀ out₀
            (by
              simpa [bounded, routedRead, readRoute, hbaseLt] using
                hroutedWidth)
            (by simpa [bounded] using hready) houtput hworkHead
        have hfalse := false_hoareTimeSpace_internal
          (TM.seqTM (TM.binaryPredTM (selectorTape spec))
            (readDispatchTreeTM spec remaining (base + 1) (by omega)))
          0 input.length (instructionSpace wordBits)
        have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
          (selectorTape spec) (directReadTreeBranchTM spec bounded)
          (TM.seqTM (TM.binaryPredTM (selectorTape spec))
            (readDispatchTreeTM spec remaining (base + 1) (by omega)))
          (pre := pre)
          (blankPre := pre)
          (nonblankPre := fun _ _ _ => False)
          hframe
          (by
            intro _inp _work _out hpre _hblank
            exact hpre)
          (by
            rintro inp work out ⟨_hinp, hworkEq, _hout⟩ hnonblank
            exact hnonblank (by
              rw [hworkEq]
              exact hready.selector.read_eq_blank_iff.mpr (by simp)))
          hdirect hfalse
        have hspace :
            (readDispatchTreeTM spec (remaining + 1) base hbound).HoareSpace
              pre input.length (instructionSpace wordBits) := by
          simpa [readDispatchTreeTM, pre] using hbranch.2
        exact htime.and_hoareSpace hspace
      · have hbaseStrict : base < address := by omega
        let predecessor := address - base - 1
        have hselectorValue : address - base = predecessor + 1 := by
          dsimp [predecessor]
          omega
        have hselectorWidth :
            (predecessor + 1).size ≤ wordBits := by
          rw [← hselectorValue]
          exact (Nat.size_le_size (Nat.sub_le address base)).trans
            haddressWidth
        let work₁ :=
          Function.update work₀ (selectorTape spec)
            (natTape predecessor)
        have hpred := binaryPredTM_hoareTimeSpace_exact_internal
          (selectorTape spec) predecessor input.length wordBits
          (executionInput input) work₀ out₀
          (by simpa [hselectorValue] using hready.selector)
          hselectorWidth (executionInput_parked input) hready.parked houtput
          (by simp [executionInput, Tape.move]) hworkHead
        have hready₁ :
            ReadTreeReady spec input snapshot address (base + 1) work₁ := by
          apply readTreeReady_update_selector spec input snapshot address
            base (base + 1) predecessor work₀ hready
          dsimp [predecessor]
          omega
        have hwork₁Head : ∀ i, (work₁ i).head = 1 :=
          update_natTape_head_internal work₀ (selectorTape spec)
            predecessor hworkHead
        have hrecursiveTime := readDispatchTreeTM_hoareTime_internal
          spec input snapshot address remaining (base + 1)
          (by omega) (by omega) work₁ out₀ hready₁ houtput
        have hrecursive :=
          (ih (base + 1) (by omega) (by omega)
            work₁ hready₁ hwork₁Head) hrecursiveTime
        have hseq := seqTM_hoareTimeSpace_exact_internal
          (TM.binaryPredTM (selectorTape spec))
          (readDispatchTreeTM spec remaining (base + 1) (by omega))
          (executionInput input) work₀ work₁
          (Function.update
            (Function.update work₀ (selectorTape spec) (natTape 0))
            (resultTape spec)
            (natTape
              (routedRead input snapshot spec.registerBound address)))
          out₀ (TM.binaryPredTime predecessor)
          (readDispatchTreeTime spec input snapshot address remaining
            (base + 1))
          input.length (instructionSpace wordBits)
          hpred (by
            apply hrecursive.consequence
            · exact fun _ _ _ h => h
            · intro inp work out hpost
              simpa [work₁, Function.update_idem] using hpost
            · exact le_rfl
            · exact le_rfl
            · exact le_rfl)
          (executionInput_parked input) hready₁.parked houtput
        have hfalse := false_hoareTimeSpace_internal
          (directReadTreeBranchTM spec bounded)
          0 input.length (instructionSpace wordBits)
        have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
          (selectorTape spec) (directReadTreeBranchTM spec bounded)
          (TM.seqTM (TM.binaryPredTM (selectorTape spec))
            (readDispatchTreeTM spec remaining (base + 1) (by omega)))
          (pre := pre)
          (blankPre := fun _ _ _ => False)
          (nonblankPre := pre)
          hframe
          (by
            rintro inp work out ⟨_hinp, hworkEq, _hout⟩ hblank
            have hzero := hready.selector.read_eq_blank_iff.mp (by
              rw [← hworkEq]
              exact hblank)
            omega)
          (by
            intro _inp _work _out hpre _hnonblank
            exact hpre)
          hfalse hseq
        have hspace :
            (readDispatchTreeTM spec (remaining + 1) base hbound).HoareSpace
              pre input.length (instructionSpace wordBits) := by
          simpa [readDispatchTreeTM, pre] using hbranch.2
        exact htime.and_hoareSpace hspace

private theorem readDispatchTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (address wordBits : ℕ)
    (haddressWidth : address.size ≤ wordBits)
    (hroutedWidth :
      (routedRead input snapshot spec.registerBound address).size ≤
        wordBits)
    (work₀ : Fin (workTapeCount spec) → Tape) (out₀ : Tape)
    (hready : ReadTreeReady spec input snapshot address address work₀)
    (houtput : TM.Parked out₀)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (readDispatchTM spec).HoareTimeSpace
      (fun inp work out =>
        inp = executionInput input ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = executionInput input ∧
        work =
          Function.update
            (Function.update work₀ (selectorTape spec) (natTape 0))
            (resultTape spec)
            (natTape
              (routedRead input snapshot spec.registerBound address)) ∧
        out = out₀)
      (readDispatchTime spec input snapshot address)
      input.length (instructionSpace wordBits) := by
  let work₁ :=
    Function.update work₀ (selectorTape spec) (natTape address)
  have hcopy := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (lhsTape spec) (selectorTape spec) (copyScratchTape spec)
    (scratchTape_ne_internal spec (by decide))
    (scratchTape_ne_internal spec (by decide))
    (scratchTape_ne_internal spec (by decide))
    address 0 input.length wordBits (executionInput input) work₀ out₀
    hready.query (by simpa using hready.selector) hready.copyScratch
    haddressWidth (by simp) (executionInput_parked input)
    hready.parked houtput (by simp [executionInput, Tape.move]) hworkHead
  have hready₁ :
      ReadTreeReady spec input snapshot address 0 work₁ :=
    readTreeReady_update_selector spec input snapshot address address
      0 address work₀ hready (by simp)
  have hwork₁Head : ∀ i, (work₁ i).head = 1 :=
    update_natTape_head_internal work₀ (selectorTape spec)
      address hworkHead
  have htree := readDispatchTreeTM_hoareTimeSpace_internal
    spec input snapshot address spec.registerBound 0 (by omega) (by omega)
    wordBits haddressWidth hroutedWidth work₁ out₀ hready₁ houtput
    hwork₁Head
  have hseq := seqTM_hoareTimeSpace_exact_internal
    (TM.binaryCopyIntoTM
      (lhsTape spec) (selectorTape spec) (copyScratchTape spec))
    (readDispatchTreeTM spec spec.registerBound 0 (by omega))
    (executionInput input) work₀ work₁
    (Function.update
      (Function.update work₀ (selectorTape spec) (natTape 0))
      (resultTape spec)
      (natTape
        (routedRead input snapshot spec.registerBound address)))
    out₀ (TM.binaryCopyTime address 0)
    (readDispatchTreeTime spec input snapshot address
      spec.registerBound 0)
    input.length (instructionSpace wordBits)
    hcopy (by
      apply htree.consequence
      · exact fun _ _ _ h => h
      · intro inp work out hpost
        simpa [work₁, Function.update_idem] using hpost
      · exact le_rfl
      · exact le_rfl
      · exact le_rfl)
    (executionInput_parked input) hready₁.parked houtput
  simpa [readDispatchTM, readDispatchTime, work₁,
    Function.update_idem] using hseq

private theorem binaryArithmeticTM_hoareTimeSpace_exact_internal
    {program : Program} (spec : Spec program)
    (op : BinaryOp) (lhs rhs inputLength wordBits : ℕ)
    (inp₀ : Tape) (work₀ : Fin (workTapeCount spec) → Tape)
    (out₀ : Tape)
    (hlhs : (work₀ (lhsTape spec)).HasBinaryNat lhs)
    (hrhs : (work₀ (rhsTape spec)).HasBinaryNat rhs)
    (hresult : (work₀ (resultTape spec)).HasBinaryNat 0)
    (hshift : (work₀ (shiftTape spec)).HasBinaryNat 0)
    (htmp : (work₀ (tmpTape spec)).HasBinaryNat 0)
    (hdbl : (work₀ (dblTape spec)).HasBinaryNat 0)
    (hlhsWidth : lhs.size ≤ wordBits)
    (hrhsWidth : rhs.size ≤ wordBits)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀)
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    ∃ (value time : ℕ),
      value = (
        match op with
        | .add => lhs + rhs
        | .sub => lhs - rhs
        | .mul => lhs * rhs) ∧
      (binaryArithmeticTM spec op).HoareTimeSpace
        (fun inp work out =>
          inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          work =
            Function.update work₀ (resultTape spec)
              (natTape value) ∧
          out = out₀)
        time inputLength (instructionSpace wordBits) := by
  obtain ⟨value, time, hvalue, htime⟩ :=
    binaryArithmeticTM_hoareTime_exact_internal spec op lhs rhs
      inp₀ work₀ out₀ hlhs hrhs hresult hshift htmp hdbl
      hinput hwork houtput
  refine ⟨value, time, hvalue, htime.and_hoareSpace ?_⟩
  cases op with
  | add =>
      let distinct : TM.BinaryRippleAddDistinct
          (lhsTape spec) (rhsTape spec) (resultTape spec) :=
        ⟨scratchTape_ne_internal spec (by decide),
          scratchTape_ne_internal spec (by decide),
          scratchTape_ne_internal spec (by decide)⟩
      have hraw := TM.binaryRippleAddTM_hoareTimeSpace_frame
        (lhsTape spec) (rhsTape spec) (resultTape spec)
        distinct lhs rhs inputLength 1 inp₀ work₀ out₀
        hlhs hrhs hresult hinput (fun i _ _ _ => hwork i) houtput
        (exactStart_withinAuxSpace_one_internal
          (TM.binaryRippleAddTM
            (lhsTape spec) (rhsTape spec) (resultTape spec))
          inp₀ work₀ out₀ hinputHead hworkHead)
      simpa [binaryArithmeticTM] using
        hraw.2.mono le_rfl
          (binaryRippleAddSpace_le_instructionSpace hlhsWidth hrhsWidth)
  | sub =>
      let distinct : TM.BinaryRippleSubDistinct
          (lhsTape spec) (rhsTape spec) (resultTape spec) :=
        ⟨scratchTape_ne_internal spec (by decide),
          scratchTape_ne_internal spec (by decide),
          scratchTape_ne_internal spec (by decide)⟩
      have hraw := TM.binaryRippleSubTM_hoareTimeSpace_frame
        (lhsTape spec) (rhsTape spec) (resultTape spec)
        distinct lhs rhs inputLength 1 inp₀ work₀ out₀
        hlhs hrhs hresult hinput (fun i _ _ _ => hwork i) houtput
        (exactStart_withinAuxSpace_one_internal
          (TM.binaryRippleSubTM
            (lhsTape spec) (rhsTape spec) (resultTape spec))
          inp₀ work₀ out₀ hinputHead hworkHead)
      simpa [binaryArithmeticTM] using
        hraw.2.mono le_rfl
          (binaryRippleSubSpace_le_instructionSpace hlhsWidth hrhsWidth)
  | mul =>
      have hraw := TM.binaryShiftMulTM_hoareTimeSpace_linear_frame
        (multiplicationABI spec) lhs rhs inputLength 1
        inp₀ work₀ out₀
        (by simpa [multiplicationABI] using hlhs)
        (by simpa [multiplicationABI] using hrhs)
        (by simpa [multiplicationABI] using hresult)
        (by simpa [multiplicationABI] using hshift)
        (by simpa [multiplicationABI] using htmp)
        (by simpa [multiplicationABI] using hdbl)
        hinput hwork houtput
        (exactStart_withinAuxSpace_one_internal
          (TM.binaryShiftMulTM (multiplicationABI spec))
          inp₀ work₀ out₀ hinputHead hworkHead)
      simpa [binaryArithmeticTM] using
        hraw.2.mono le_rfl
          (binaryShiftMulSpace_le_instructionSpace hlhsWidth hrhsWidth)

private def binaryOpValue (op : BinaryOp) (lhs rhs : ℕ) : ℕ :=
  match op with
  | .add => lhs + rhs
  | .sub => lhs - rhs
  | .mul => lhs * rhs

private theorem binaryInstructionTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (op : BinaryOp)
    (destination source₀ source₁ : ℕ)
    (hdestination : destination < spec.registerBound)
    (hsource₀ : source₀ < spec.registerBound)
    (hsource₁ : source₁ < spec.registerBound)
    (wordBits : ℕ)
    (hsource₀Width :
      (DenseOverlay.read input snapshot.overlay source₀).size ≤ wordBits)
    (hsource₁Width :
      (DenseOverlay.read input snapshot.overlay source₁).size ≤ wordBits)
    (hdestinationWidth :
      (DenseOverlay.read input snapshot.overlay destination).size ≤ wordBits)
    (hresultWidth :
      (binaryOpValue op
        (DenseOverlay.read input snapshot.overlay source₀)
        (DenseOverlay.read input snapshot.overlay source₁)).size ≤ wordBits) :
    ∃ (value time : ℕ),
      value = binaryOpValue op
        (DenseOverlay.read input snapshot.overlay source₀)
        (DenseOverlay.read input snapshot.overlay source₁) ∧
      (binaryInstructionTM spec op destination source₀ source₁
        hdestination hsource₀ hsource₁).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape value) ∧
          out = natTape 0)
        time input.length (instructionSpace wordBits) := by
  let initialWork := executionWork spec input snapshot
  let lhsValue := DenseOverlay.read input snapshot.overlay source₀
  let rhsValue := DenseOverlay.read input snapshot.overlay source₁
  let work₁ :=
    Function.update initialWork (lhsTape spec) (natTape lhsValue)
  let work₂ :=
    Function.update work₁ (rhsTape spec) (natTape rhsValue)
  have hinput := executionInput_parked input
  have houtput := natTape_parked_internal 0
  have hinitialParked : ∀ i, TM.Parked (initialWork i) :=
    executionWork_parked_internal spec input snapshot
  have hinputHead : (executionInput input).head = 1 := by
    simp [executionInput, Tape.move]
  have hinitialHead : ∀ i, (initialWork i).head = 1 := by
    intro i
    exact executionWork_head_internal spec input snapshot i
  have hinitialRegister
      (address : ℕ) (haddress : address < spec.registerBound) :
      (initialWork
        (registerTape spec address haddress)).HasBinaryNat
          (DenseOverlay.read input snapshot.overlay address) := by
    change
      (executionWork spec input snapshot
        (registerTape spec address haddress)).HasBinaryNat _
    rw [executionWork_register_internal]
    exact natTape_hasBinaryNat_internal _
  have hinitialScratch
      (slot : Fin scratchCount) (hne : slot ≠ 10) :
      (initialWork (scratchTape spec slot)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec slot)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot slot hne]
    exact natTape_hasBinaryNat_internal 0
  have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
    update_natTape_parked_internal initialWork (lhsTape spec)
      lhsValue hinitialParked
  have hwork₁Head : ∀ i, (work₁ i).head = 1 :=
    update_natTape_head_internal initialWork (lhsTape spec)
      lhsValue hinitialHead
  have hwork₂Parked : ∀ i, TM.Parked (work₂ i) :=
    update_natTape_parked_internal work₁ (rhsTape spec)
      rhsValue hwork₁Parked
  have hwork₂Head : ∀ i, (work₂ i).head = 1 :=
    update_natTape_head_internal work₁ (rhsTape spec)
      rhsValue hwork₁Head
  have hsource₀Lhs :
      registerTape spec source₀ hsource₀ ≠ lhsTape spec :=
    registerTape_ne_scratchTape_internal spec source₀ hsource₀ 0
  have hsource₀Copy :
      registerTape spec source₀ hsource₀ ≠ copyScratchTape spec :=
    registerTape_ne_scratchTape_internal spec source₀ hsource₀ 9
  have hlhsCopy : lhsTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcopy₀ := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (registerTape spec source₀ hsource₀)
    (lhsTape spec) (copyScratchTape spec)
    hsource₀Lhs hsource₀Copy hlhsCopy lhsValue 0 input.length wordBits
    (executionInput input) initialWork (natTape 0)
    (by simpa [lhsValue] using hinitialRegister source₀ hsource₀)
    (by simpa [lhsTape] using hinitialScratch 0 (by decide))
    (by simpa [copyScratchTape] using
      hinitialScratch 9 (by decide))
    (by simpa [lhsValue] using hsource₀Width)
    (by simp)
    hinput hinitialParked houtput hinputHead hinitialHead
  have hsource₁Rhs :
      registerTape spec source₁ hsource₁ ≠ rhsTape spec :=
    registerTape_ne_scratchTape_internal spec source₁ hsource₁ 1
  have hsource₁Copy :
      registerTape spec source₁ hsource₁ ≠ copyScratchTape spec :=
    registerTape_ne_scratchTape_internal spec source₁ hsource₁ 9
  have hrhsCopy : rhsTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hwork₁Source₁ :
      (work₁
        (registerTape spec source₁ hsource₁)).HasBinaryNat rhsValue := by
    dsimp only [work₁]
    unfold lhsTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec source₁ hsource₁ 0)]
    simpa [rhsValue] using hinitialRegister source₁ hsource₁
  have hwork₁Rhs : (work₁ (rhsTape spec)).HasBinaryNat 0 := by
    dsimp only [work₁]
    unfold lhsTape rhsTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 1) (second := 0)
        (by decide))]
    simpa [rhsTape] using hinitialScratch 1 (by decide)
  have hwork₁Copy : (work₁ (copyScratchTape spec)).HasBinaryNat 0 := by
    dsimp only [work₁]
    unfold lhsTape copyScratchTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 9) (second := 0)
        (by decide))]
    simpa [copyScratchTape] using hinitialScratch 9 (by decide)
  have hcopy₁ := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (registerTape spec source₁ hsource₁)
    (rhsTape spec) (copyScratchTape spec)
    hsource₁Rhs hsource₁Copy hrhsCopy rhsValue 0 input.length wordBits
    (executionInput input) work₁ (natTape 0)
    hwork₁Source₁ hwork₁Rhs hwork₁Copy
    (by simpa [rhsValue] using hsource₁Width)
    (by simp)
    hinput hwork₁Parked houtput hinputHead hwork₁Head
  have hlhsRhs : lhsTape spec ≠ rhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hresultRhs : resultTape spec ≠ rhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hresultLhs : resultTape spec ≠ lhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hshiftRhs : shiftTape spec ≠ rhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hshiftLhs : shiftTape spec ≠ lhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have htmpRhs : tmpTape spec ≠ rhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have htmpLhs : tmpTape spec ≠ lhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hdblRhs : dblTape spec ≠ rhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hdblLhs : dblTape spec ≠ lhsTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hwork₂Lhs : (work₂ (lhsTape spec)).HasBinaryNat lhsValue := by
    dsimp only [work₂]
    rw [Function.update_of_ne hlhsRhs]
    dsimp only [work₁]
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal lhsValue
  have hwork₂Rhs : (work₂ (rhsTape spec)).HasBinaryNat rhsValue := by
    dsimp only [work₂]
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal rhsValue
  have hwork₂Result : (work₂ (resultTape spec)).HasBinaryNat 0 := by
    dsimp only [work₂]
    rw [Function.update_of_ne hresultRhs]
    dsimp only [work₁]
    rw [Function.update_of_ne hresultLhs]
    simpa [resultTape] using hinitialScratch 2 (by decide)
  have hwork₂Shift : (work₂ (shiftTape spec)).HasBinaryNat 0 := by
    dsimp only [work₂]
    rw [Function.update_of_ne hshiftRhs]
    dsimp only [work₁]
    rw [Function.update_of_ne hshiftLhs]
    simpa [shiftTape] using hinitialScratch 3 (by decide)
  have hwork₂Tmp : (work₂ (tmpTape spec)).HasBinaryNat 0 := by
    dsimp only [work₂]
    rw [Function.update_of_ne htmpRhs]
    dsimp only [work₁]
    rw [Function.update_of_ne htmpLhs]
    simpa [tmpTape] using hinitialScratch 4 (by decide)
  have hwork₂Dbl : (work₂ (dblTape spec)).HasBinaryNat 0 := by
    dsimp only [work₂]
    rw [Function.update_of_ne hdblRhs]
    dsimp only [work₁]
    rw [Function.update_of_ne hdblLhs]
    simpa [dblTape] using hinitialScratch 5 (by decide)
  have harithmeticRaw :=
    binaryArithmeticTM_hoareTimeSpace_exact_internal spec op
      lhsValue rhsValue input.length wordBits
      (executionInput input) work₂ (natTape 0)
      hwork₂Lhs hwork₂Rhs hwork₂Result hwork₂Shift hwork₂Tmp hwork₂Dbl
      (by simpa [lhsValue] using hsource₀Width)
      (by simpa [rhsValue] using hsource₁Width)
      hinput hwork₂Parked houtput hinputHead hwork₂Head
  obtain ⟨value, arithmeticTime, hvalue, harithmetic⟩ :=
    harithmeticRaw
  have hvalueOp : value = binaryOpValue op lhsValue rhsValue := by
    simpa [binaryOpValue] using hvalue
  have hvalueWidth : value.size ≤ wordBits := by
    rw [hvalueOp]
    simpa [lhsValue, rhsValue] using hresultWidth
  let work₃ :=
    Function.update work₂ (resultTape spec) (natTape value)
  have hwork₃Parked : ∀ i, TM.Parked (work₃ i) :=
    update_natTape_parked_internal work₂ (resultTape spec)
      value hwork₂Parked
  have hwork₃Head : ∀ i, (work₃ i).head = 1 :=
    update_natTape_head_internal work₂ (resultTape spec)
      value hwork₂Head
  have hresultDestination :
      resultTape spec ≠
        registerTape spec destination hdestination :=
    (registerTape_ne_scratchTape_internal spec destination
      hdestination 2).symm
  have hresultCopy : resultTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hdestinationCopy :
      registerTape spec destination hdestination ≠
        copyScratchTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 9
  let destinationValue :=
    DenseOverlay.read input snapshot.overlay destination
  have hwork₃Result :
      (work₃ (resultTape spec)).HasBinaryNat value := by
    dsimp only [work₃]
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal value
  have hwork₃Destination :
      (work₃
        (registerTape spec destination hdestination)).HasBinaryNat
          destinationValue := by
    dsimp only [work₃]
    rw [Function.update_of_ne hresultDestination.symm]
    dsimp only [work₂]
    unfold rhsTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 1)]
    dsimp only [work₁]
    unfold lhsTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 0)]
    simpa [destinationValue] using
      hinitialRegister destination hdestination
  have hwork₃Copy :
      (work₃ (copyScratchTape spec)).HasBinaryNat 0 := by
    dsimp only [work₃]
    unfold resultTape copyScratchTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 9) (second := 2)
        (by decide))]
    dsimp only [work₂]
    unfold rhsTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 9) (second := 1)
        (by decide))]
    dsimp only [work₁]
    unfold lhsTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 9) (second := 0)
        (by decide))]
    simpa [copyScratchTape] using hinitialScratch 9 (by decide)
  have hcopyResult := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (resultTape spec)
    (registerTape spec destination hdestination)
    (copyScratchTape spec)
    hresultDestination hresultCopy hdestinationCopy
    value destinationValue input.length wordBits
    (executionInput input) work₃ (natTape 0)
    hwork₃Result hwork₃Destination hwork₃Copy
    hvalueWidth (by simpa [destinationValue] using hdestinationWidth)
    hinput hwork₃Parked houtput hinputHead hwork₃Head
  let work₄ :=
    Function.update work₃
      (registerTape spec destination hdestination) (natTape value)
  have hwork₄Parked : ∀ i, TM.Parked (work₄ i) :=
    update_natTape_parked_internal work₃
      (registerTape spec destination hdestination)
      value hwork₃Parked
  have hwork₄Head : ∀ i, (work₄ i).head = 1 :=
    update_natTape_head_internal work₃
      (registerTape spec destination hdestination)
      value hwork₃Head
  have hwork₄Lhs : (work₄ (lhsTape spec)).HasBinaryNat lhsValue := by
    dsimp only [work₄]
    unfold lhsTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 0).symm]
    dsimp only [work₃]
    unfold resultTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 0) (second := 2)
        (by decide))]
    dsimp only [work₂]
    unfold rhsTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 0) (second := 1)
        (by decide))]
    dsimp only [work₁]
    unfold lhsTape
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal lhsValue
  have hresetLhs := resetBinaryWorkTM_hoareTimeSpace_exact_internal
    (lhsTape spec) lhsValue input.length wordBits
    (executionInput input) work₄ (natTape 0)
    hwork₄Lhs (by simpa [lhsValue] using hsource₀Width)
    hinput hwork₄Parked houtput hinputHead hwork₄Head
  let work₅ :=
    Function.update work₄ (lhsTape spec) (natTape 0)
  have hwork₅Parked : ∀ i, TM.Parked (work₅ i) :=
    update_natTape_parked_internal work₄ (lhsTape spec) 0 hwork₄Parked
  have hwork₅Head : ∀ i, (work₅ i).head = 1 :=
    update_natTape_head_internal work₄ (lhsTape spec) 0 hwork₄Head
  have hwork₅Rhs : (work₅ (rhsTape spec)).HasBinaryNat rhsValue := by
    dsimp only [work₅]
    rw [Function.update_of_ne hlhsRhs.symm]
    dsimp only [work₄]
    unfold rhsTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 1).symm]
    dsimp only [work₃]
    unfold resultTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec (first := 1) (second := 2)
        (by decide))]
    dsimp only [work₂]
    unfold rhsTape
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal rhsValue
  have hresetRhs := resetBinaryWorkTM_hoareTimeSpace_exact_internal
    (rhsTape spec) rhsValue input.length wordBits
    (executionInput input) work₅ (natTape 0)
    hwork₅Rhs (by simpa [rhsValue] using hsource₁Width)
    hinput hwork₅Parked houtput hinputHead hwork₅Head
  let work₆ :=
    Function.update work₅ (rhsTape spec) (natTape 0)
  have hwork₆Parked : ∀ i, TM.Parked (work₆ i) :=
    update_natTape_parked_internal work₅ (rhsTape spec) 0 hwork₅Parked
  have hwork₆Head : ∀ i, (work₆ i).head = 1 :=
    update_natTape_head_internal work₅ (rhsTape spec) 0 hwork₅Head
  have hwork₆Result :
      (work₆ (resultTape spec)).HasBinaryNat value := by
    dsimp only [work₆]
    rw [Function.update_of_ne hresultRhs]
    dsimp only [work₅]
    rw [Function.update_of_ne hresultLhs]
    dsimp only [work₄]
    rw [Function.update_of_ne hresultDestination]
    dsimp only [work₃]
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal value
  have hresetResult := resetBinaryWorkTM_hoareTimeSpace_exact_internal
    (resultTape spec) value input.length wordBits
    (executionInput input) work₆ (natTape 0)
    hwork₆Result hvalueWidth
    hinput hwork₆Parked houtput hinputHead hwork₆Head
  let work₇ :=
    Function.update work₆ (resultTape spec) (natTape 0)
  have hwork₇Parked : ∀ i, TM.Parked (work₇ i) :=
    update_natTape_parked_internal work₆ (resultTape spec) 0 hwork₆Parked
  have htail₆ := seqTM_hoareTimeSpace_exact_internal
    (TM.resetBinaryWorkTM (rhsTape spec))
    (TM.resetBinaryWorkTM (resultTape spec))
    (executionInput input) work₅ work₆ work₇ (natTape 0)
    (TM.resetBinaryWorkTime 1 rhsValue.bits.length)
    (TM.resetBinaryWorkTime 1 value.bits.length)
    input.length (instructionSpace wordBits)
    hresetRhs hresetResult hinput hwork₆Parked houtput
  have htail₅ := seqTM_hoareTimeSpace_exact_internal
    (TM.resetBinaryWorkTM (lhsTape spec))
    (TM.seqTM (TM.resetBinaryWorkTM (rhsTape spec))
      (TM.resetBinaryWorkTM (resultTape spec)))
    (executionInput input) work₄ work₅ work₇ (natTape 0)
    (TM.resetBinaryWorkTime 1 lhsValue.bits.length)
    _ input.length (instructionSpace wordBits)
    hresetLhs htail₆ hinput hwork₅Parked houtput
  have htail₄ := seqTM_hoareTimeSpace_exact_internal
    (TM.binaryCopyIntoTM
      (resultTape spec)
      (registerTape spec destination hdestination)
      (copyScratchTape spec))
    (TM.seqTM (TM.resetBinaryWorkTM (lhsTape spec))
      (TM.seqTM (TM.resetBinaryWorkTM (rhsTape spec))
        (TM.resetBinaryWorkTM (resultTape spec))))
    (executionInput input) work₃ work₄ work₇ (natTape 0)
    (TM.binaryCopyTime value destinationValue)
    _ input.length (instructionSpace wordBits)
    hcopyResult htail₅ hinput hwork₄Parked houtput
  have htail₃ := seqTM_hoareTimeSpace_exact_internal
    (binaryArithmeticTM spec op)
    (TM.seqTM
      (TM.binaryCopyIntoTM
        (resultTape spec)
        (registerTape spec destination hdestination)
        (copyScratchTape spec))
      (TM.seqTM (TM.resetBinaryWorkTM (lhsTape spec))
        (TM.seqTM (TM.resetBinaryWorkTM (rhsTape spec))
          (TM.resetBinaryWorkTM (resultTape spec)))))
    (executionInput input) work₂ work₃ work₇ (natTape 0)
    arithmeticTime _ input.length (instructionSpace wordBits)
    harithmetic htail₄ hinput hwork₃Parked houtput
  have htail₂ := seqTM_hoareTimeSpace_exact_internal
    (TM.binaryCopyIntoTM
      (registerTape spec source₁ hsource₁)
      (rhsTape spec) (copyScratchTape spec))
    (TM.seqTM (binaryArithmeticTM spec op)
      (TM.seqTM
        (TM.binaryCopyIntoTM
          (resultTape spec)
          (registerTape spec destination hdestination)
          (copyScratchTape spec))
        (TM.seqTM (TM.resetBinaryWorkTM (lhsTape spec))
          (TM.seqTM (TM.resetBinaryWorkTM (rhsTape spec))
            (TM.resetBinaryWorkTM (resultTape spec))))))
    (executionInput input) work₁ work₂ work₇ (natTape 0)
    (TM.binaryCopyTime rhsValue 0) _
    input.length (instructionSpace wordBits)
    hcopy₁ htail₃ hinput hwork₂Parked houtput
  have hfull := seqTM_hoareTimeSpace_exact_internal
    (TM.binaryCopyIntoTM
      (registerTape spec source₀ hsource₀)
      (lhsTape spec) (copyScratchTape spec))
    (TM.seqTM
      (TM.binaryCopyIntoTM
        (registerTape spec source₁ hsource₁)
        (rhsTape spec) (copyScratchTape spec))
      (TM.seqTM (binaryArithmeticTM spec op)
        (TM.seqTM
          (TM.binaryCopyIntoTM
            (resultTape spec)
            (registerTape spec destination hdestination)
            (copyScratchTape spec))
          (TM.seqTM (TM.resetBinaryWorkTM (lhsTape spec))
            (TM.seqTM (TM.resetBinaryWorkTM (rhsTape spec))
              (TM.resetBinaryWorkTM (resultTape spec)))))))
    (executionInput input) initialWork work₁ work₇ (natTape 0)
    (TM.binaryCopyTime lhsValue 0) _
    input.length (instructionSpace wordBits)
    hcopy₀ htail₂ hinput hwork₁Parked houtput
  have hinitialLhsEq :
      initialWork (lhsTape spec) = natTape 0 :=
    hasBinaryNat_eq_natTape
      (by simpa [lhsTape] using hinitialScratch 0 (by decide))
  have hinitialRhsEq :
      initialWork (rhsTape spec) = natTape 0 :=
    hasBinaryNat_eq_natTape
      (by simpa [rhsTape] using hinitialScratch 1 (by decide))
  have hinitialResultEq :
      initialWork (resultTape spec) = natTape 0 :=
    hasBinaryNat_eq_natTape
      (by simpa [resultTape] using hinitialScratch 2 (by decide))
  have hdestinationLhs :
      registerTape spec destination hdestination ≠ lhsTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 0
  have hdestinationRhs :
      registerTape spec destination hdestination ≠ rhsTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 1
  have hdestinationResult :
      registerTape spec destination hdestination ≠ resultTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 2
  have hfinal :
      work₇ =
        Function.update initialWork
          (registerTape spec destination hdestination)
          (natTape value) := by
    funext i
    by_cases hiDestination :
        i = registerTape spec destination hdestination
    · subst i
      dsimp only [work₇]
      rw [Function.update_of_ne hdestinationResult]
      dsimp only [work₆]
      rw [Function.update_of_ne hdestinationRhs]
      dsimp only [work₅]
      rw [Function.update_of_ne hdestinationLhs]
      dsimp only [work₄]
      rw [Function.update_self, Function.update_self]
    by_cases hiLhs : i = lhsTape spec
    · subst i
      dsimp only [work₇]
      rw [Function.update_of_ne hresultLhs.symm]
      dsimp only [work₆]
      rw [Function.update_of_ne hlhsRhs]
      dsimp only [work₅]
      rw [Function.update_self,
        Function.update_of_ne hdestinationLhs.symm]
      exact hinitialLhsEq.symm
    by_cases hiRhs : i = rhsTape spec
    · subst i
      dsimp only [work₇]
      rw [Function.update_of_ne hresultRhs.symm]
      dsimp only [work₆]
      rw [Function.update_self,
        Function.update_of_ne hdestinationRhs.symm]
      exact hinitialRhsEq.symm
    by_cases hiResult : i = resultTape spec
    · subst i
      dsimp only [work₇]
      rw [Function.update_self,
        Function.update_of_ne hdestinationResult.symm]
      exact hinitialResultEq.symm
    · dsimp only [work₇]
      rw [Function.update_of_ne hiResult]
      dsimp only [work₆]
      rw [Function.update_of_ne hiRhs]
      dsimp only [work₅]
      rw [Function.update_of_ne hiLhs]
      dsimp only [work₄]
      rw [Function.update_of_ne hiDestination]
      dsimp only [work₃]
      rw [Function.update_of_ne hiResult]
      dsimp only [work₂]
      rw [Function.update_of_ne hiRhs]
      dsimp only [work₁]
      rw [Function.update_of_ne hiLhs,
        Function.update_of_ne hiDestination]
  have hfullFinal :
      (TM.seqTM
        (TM.binaryCopyIntoTM
          (registerTape spec source₀ hsource₀)
          (lhsTape spec) (copyScratchTape spec))
        (TM.seqTM
          (TM.binaryCopyIntoTM
            (registerTape spec source₁ hsource₁)
            (rhsTape spec) (copyScratchTape spec))
          (TM.seqTM (binaryArithmeticTM spec op)
            (TM.seqTM
              (TM.binaryCopyIntoTM
                (resultTape spec)
                (registerTape spec destination hdestination)
                (copyScratchTape spec))
              (TM.seqTM (TM.resetBinaryWorkTM (lhsTape spec))
                (TM.seqTM (TM.resetBinaryWorkTM (rhsTape spec))
              (TM.resetBinaryWorkTM
                    (resultTape spec)))))))).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape value) ∧
          out = natTape 0)
        (TM.binaryCopyTime lhsValue 0 + 1 +
          (TM.binaryCopyTime rhsValue 0 + 1 +
            (arithmeticTime + 1 +
              (TM.binaryCopyTime value destinationValue + 1 +
                (TM.resetBinaryWorkTime 1 lhsValue.bits.length + 1 +
                  (TM.resetBinaryWorkTime 1 rhsValue.bits.length + 1 +
                    TM.resetBinaryWorkTime 1
                      value.bits.length))))))
        input.length (instructionSpace wordBits) := by
    apply hfull.consequence
    · intro inp work out hpre
      simpa [initialWork] using hpre
    · rintro inp work out ⟨hinp, hworkEq, hout⟩
      refine ⟨hinp, ?_, hout⟩
      rw [hworkEq, hfinal]
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
  refine ⟨value,
    TM.binaryCopyTime lhsValue 0 + 1 +
      (TM.binaryCopyTime rhsValue 0 + 1 +
        (arithmeticTime + 1 +
          (TM.binaryCopyTime value destinationValue + 1 +
            (TM.resetBinaryWorkTime 1 lhsValue.bits.length + 1 +
              (TM.resetBinaryWorkTime 1 rhsValue.bits.length + 1 +
                TM.resetBinaryWorkTime 1 value.bits.length))))),
    (by simpa [lhsValue, rhsValue] using hvalueOp), ?_⟩
  simpa only [binaryInstructionTM] using hfullFinal

private theorem binaryInstructionTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (op : BinaryOp)
    (destination source₀ source₁ : ℕ)
    (hdestination : destination < spec.registerBound)
    (hsource₀ : source₀ < spec.registerBound)
    (hsource₁ : source₁ < spec.registerBound) :
    ∃ (value time : ℕ),
      value = (
        match op with
        | .add =>
            DenseOverlay.read input snapshot.overlay source₀ +
              DenseOverlay.read input snapshot.overlay source₁
        | .sub =>
            DenseOverlay.read input snapshot.overlay source₀ -
              DenseOverlay.read input snapshot.overlay source₁
        | .mul =>
            DenseOverlay.read input snapshot.overlay source₀ *
              DenseOverlay.read input snapshot.overlay source₁) ∧
      (binaryInstructionTM spec op destination source₀ source₁
        hdestination hsource₀ hsource₁).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape value) ∧
          out = natTape 0)
        time := by
  let lhsValue := DenseOverlay.read input snapshot.overlay source₀
  let rhsValue := DenseOverlay.read input snapshot.overlay source₁
  let destinationValue :=
    DenseOverlay.read input snapshot.overlay destination
  let resultValue := binaryOpValue op lhsValue rhsValue
  let wordBits :=
    lhsValue.size + rhsValue.size + destinationValue.size +
      resultValue.size
  obtain ⟨value, time, hvalue, hcontract⟩ :=
    binaryInstructionTM_hoareTimeSpace_internal spec input snapshot op
      destination source₀ source₁ hdestination hsource₀ hsource₁ wordBits
      (by
        dsimp [wordBits, resultValue, lhsValue, rhsValue,
          destinationValue]
        omega)
      (by
        dsimp [wordBits, resultValue, lhsValue, rhsValue,
          destinationValue]
        omega)
      (by
        dsimp [wordBits, resultValue, lhsValue, rhsValue,
          destinationValue]
        omega)
      (by
        dsimp [wordBits, resultValue, lhsValue, rhsValue,
          destinationValue]
        omega)
  exact ⟨value, time, by simpa [binaryOpValue] using hvalue, hcontract.1⟩

private theorem loadInstructionTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (destination addressRegister : ℕ)
    (hdestination : destination < spec.registerBound)
    (haddressRegister : addressRegister < spec.registerBound)
    (wordBits : ℕ)
    (haddressWidth :
      (DenseOverlay.read input snapshot.overlay addressRegister).size ≤
        wordBits)
    (hroutedWidth :
      (routedRead input snapshot spec.registerBound
        (DenseOverlay.read input snapshot.overlay addressRegister)).size ≤
          wordBits)
    (hdestinationWidth :
      (DenseOverlay.read input snapshot.overlay destination).size ≤
        wordBits) :
    ∃ time,
      (loadInstructionTM spec destination addressRegister
        hdestination haddressRegister).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape
                (DenseOverlay.read input snapshot.overlay
                  (DenseOverlay.read input snapshot.overlay
                    addressRegister))) ∧
          out = natTape 0)
        time input.length (instructionSpace wordBits) := by
  let initialWork := executionWork spec input snapshot
  let address :=
    DenseOverlay.read input snapshot.overlay addressRegister
  let routedValue :=
    routedRead input snapshot spec.registerBound address
  let work₁ :=
    Function.update initialWork (lhsTape spec) (natTape address)
  have hinput := executionInput_parked input
  have houtput := natTape_parked_internal 0
  have hinitialParked : ∀ i, TM.Parked (initialWork i) :=
    executionWork_parked_internal spec input snapshot
  have hinputHead : (executionInput input).head = 1 := by
    simp [executionInput, Tape.move]
  have hinitialHead : ∀ i, (initialWork i).head = 1 := by
    intro i
    exact executionWork_head_internal spec input snapshot i
  have hinitialRegister
      (register : ℕ) (hregister : register < spec.registerBound) :
      (initialWork
        (registerTape spec register hregister)).HasBinaryNat
          (DenseOverlay.read input snapshot.overlay register) := by
    change
      (executionWork spec input snapshot
        (registerTape spec register hregister)).HasBinaryNat _
    rw [executionWork_register_internal]
    exact natTape_hasBinaryNat_internal _
  have hinitialScratch
      (slot : Fin scratchCount) (hne : slot ≠ 10) :
      (initialWork (scratchTape spec slot)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec slot)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot slot hne]
    exact natTape_hasBinaryNat_internal 0
  have haddressLhs :
      registerTape spec addressRegister haddressRegister ≠ lhsTape spec :=
    registerTape_ne_scratchTape_internal spec addressRegister
      haddressRegister 0
  have haddressCopy :
      registerTape spec addressRegister haddressRegister ≠
        copyScratchTape spec :=
    registerTape_ne_scratchTape_internal spec addressRegister
      haddressRegister 9
  have hlhsCopy : lhsTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hcopyAddress := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (registerTape spec addressRegister haddressRegister)
    (lhsTape spec) (copyScratchTape spec)
    haddressLhs haddressCopy hlhsCopy address 0 input.length wordBits
    (executionInput input) initialWork (natTape 0)
    (by simpa [address] using
      hinitialRegister addressRegister haddressRegister)
    (by simpa [lhsTape] using hinitialScratch 0 (by decide))
    (by simpa [copyScratchTape] using
      hinitialScratch 9 (by decide))
    (by simpa [address] using haddressWidth) (by simp)
    hinput hinitialParked houtput hinputHead hinitialHead
  have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
    update_natTape_parked_internal initialWork (lhsTape spec)
      address hinitialParked
  have hwork₁Head : ∀ i, (work₁ i).head = 1 :=
    update_natTape_head_internal initialWork (lhsTape spec)
      address hinitialHead
  have hready : ReadTreeReady spec input snapshot address address work₁ := by
    refine
      { query := by
          dsimp only [work₁]
          rw [Function.update_self]
          exact natTape_hasBinaryNat_internal address
        selector := by
          dsimp only [work₁]
          unfold lhsTape selectorTape
          rw [Function.update_of_ne
            (scratchTape_ne_internal spec
              (first := 11) (second := 0) (by decide))]
          simpa [selectorTape] using hinitialScratch 11 (by decide)
        result := by
          dsimp only [work₁]
          unfold lhsTape resultTape
          rw [Function.update_of_ne
            (scratchTape_ne_internal spec
              (first := 2) (second := 0) (by decide))]
          simpa [resultTape] using hinitialScratch 2 (by decide)
        counter := by
          dsimp only [work₁]
          unfold lhsTape counterTape
          rw [Function.update_of_ne
            (scratchTape_ne_internal spec
              (first := 8) (second := 0) (by decide))]
          simpa [counterTape] using hinitialScratch 8 (by decide)
        copyScratch := by
          dsimp only [work₁]
          unfold lhsTape copyScratchTape
          rw [Function.update_of_ne
            (scratchTape_ne_internal spec
              (first := 9) (second := 0) (by decide))]
          simpa [copyScratchTape] using
            hinitialScratch 9 (by decide)
        register := by
          intro bounded
          dsimp only [work₁]
          unfold lhsTape
          rw [Function.update_of_ne
            (registerTape_ne_scratchTape_internal spec
              bounded.val bounded.isLt 0)]
          exact hinitialRegister bounded.val bounded.isLt
        parked := hwork₁Parked }
  have hdispatch := readDispatchTM_hoareTimeSpace_internal
    spec input snapshot address wordBits
      (by simpa [address] using haddressWidth)
      (by simpa [address, routedValue] using hroutedWidth)
      work₁ (natTape 0) hready houtput hwork₁Head
  let work₂ :=
    Function.update
      (Function.update work₁ (selectorTape spec) (natTape 0))
      (resultTape spec) (natTape routedValue)
  have hdispatchExact :
      (readDispatchTM spec).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧ work = work₁ ∧ out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧ work = work₂ ∧ out = natTape 0)
        (readDispatchTime spec input snapshot address)
        input.length (instructionSpace wordBits) := by
    simpa [work₂, routedValue] using hdispatch
  have hwork₂Parked : ∀ i, TM.Parked (work₂ i) := by
    apply update_natTape_parked_internal
    apply update_natTape_parked_internal
    exact hwork₁Parked
  have hwork₂Head : ∀ i, (work₂ i).head = 1 := by
    apply update_natTape_head_internal
    apply update_natTape_head_internal
    exact hwork₁Head
  have hresultDestination :
      resultTape spec ≠ registerTape spec destination hdestination :=
    (registerTape_ne_scratchTape_internal spec destination
      hdestination 2).symm
  have hresultCopy : resultTape spec ≠ copyScratchTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hdestinationCopy :
      registerTape spec destination hdestination ≠
        copyScratchTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 9
  let destinationValue :=
    DenseOverlay.read input snapshot.overlay destination
  have hwork₂Result :
      (work₂ (resultTape spec)).HasBinaryNat routedValue := by
    dsimp only [work₂]
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal routedValue
  have hwork₂Destination :
      (work₂
        (registerTape spec destination hdestination)).HasBinaryNat
          destinationValue := by
    dsimp only [work₂]
    unfold resultTape selectorTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 2)]
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 11)]
    dsimp only [work₁]
    unfold lhsTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 0)]
    simpa [destinationValue] using
      hinitialRegister destination hdestination
  have hwork₂Copy :
      (work₂ (copyScratchTape spec)).HasBinaryNat 0 := by
    dsimp only [work₂]
    unfold copyScratchTape resultTape selectorTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec
        (first := 9) (second := 2) (by decide))]
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec
        (first := 9) (second := 11) (by decide))]
    dsimp only [work₁]
    unfold lhsTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec
        (first := 9) (second := 0) (by decide))]
    simpa [copyScratchTape] using hinitialScratch 9 (by decide)
  have hcopyResult := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (resultTape spec)
    (registerTape spec destination hdestination)
    (copyScratchTape spec)
    hresultDestination hresultCopy hdestinationCopy
    routedValue destinationValue input.length wordBits
    (executionInput input) work₂ (natTape 0)
    hwork₂Result hwork₂Destination hwork₂Copy
    (by simpa [routedValue, address] using hroutedWidth)
    (by simpa [destinationValue] using hdestinationWidth)
    hinput hwork₂Parked houtput hinputHead hwork₂Head
  let work₃ :=
    Function.update work₂
      (registerTape spec destination hdestination)
      (natTape routedValue)
  have hwork₃Parked : ∀ i, TM.Parked (work₃ i) :=
    update_natTape_parked_internal work₂
      (registerTape spec destination hdestination)
      routedValue hwork₂Parked
  have hwork₃Head : ∀ i, (work₃ i).head = 1 :=
    update_natTape_head_internal work₂
      (registerTape spec destination hdestination)
      routedValue hwork₂Head
  have hwork₃Lhs : (work₃ (lhsTape spec)).HasBinaryNat address := by
    dsimp only [work₃]
    unfold lhsTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 0).symm]
    dsimp only [work₂]
    unfold resultTape selectorTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec
        (first := 0) (second := 2) (by decide))]
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec
        (first := 0) (second := 11) (by decide))]
    dsimp only [work₁]
    unfold lhsTape
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal address
  have hresetLhs := resetBinaryWorkTM_hoareTimeSpace_exact_internal
    (lhsTape spec) address input.length wordBits
    (executionInput input) work₃ (natTape 0)
    hwork₃Lhs (by simpa [address] using haddressWidth)
    hinput hwork₃Parked houtput hinputHead hwork₃Head
  let work₄ :=
    Function.update work₃ (lhsTape spec) (natTape 0)
  have hwork₄Parked : ∀ i, TM.Parked (work₄ i) :=
    update_natTape_parked_internal work₃ (lhsTape spec) 0 hwork₃Parked
  have hwork₄Head : ∀ i, (work₄ i).head = 1 :=
    update_natTape_head_internal work₃ (lhsTape spec) 0 hwork₃Head
  have hwork₄Result :
      (work₄ (resultTape spec)).HasBinaryNat routedValue := by
    dsimp only [work₄]
    unfold resultTape lhsTape
    rw [Function.update_of_ne
      (scratchTape_ne_internal spec
        (first := 2) (second := 0) (by decide))]
    dsimp only [work₃]
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 2).symm]
    dsimp only [work₂]
    unfold resultTape
    rw [Function.update_self]
    exact natTape_hasBinaryNat_internal routedValue
  have hresetResult := resetBinaryWorkTM_hoareTimeSpace_exact_internal
    (resultTape spec) routedValue input.length wordBits
    (executionInput input) work₄ (natTape 0)
    hwork₄Result (by simpa [routedValue, address] using hroutedWidth)
    hinput hwork₄Parked houtput hinputHead hwork₄Head
  let work₅ :=
    Function.update work₄ (resultTape spec) (natTape 0)
  have hwork₅Parked : ∀ i, TM.Parked (work₅ i) :=
    update_natTape_parked_internal work₄ (resultTape spec) 0 hwork₄Parked
  have htailReset := seqTM_hoareTimeSpace_exact_internal
    (TM.resetBinaryWorkTM (lhsTape spec))
    (TM.resetBinaryWorkTM (resultTape spec))
    (executionInput input) work₃ work₄ work₅ (natTape 0)
    (TM.resetBinaryWorkTime 1 address.bits.length)
    (TM.resetBinaryWorkTime 1 routedValue.bits.length)
    input.length (instructionSpace wordBits)
    hresetLhs hresetResult hinput hwork₄Parked houtput
  have htailCopy := seqTM_hoareTimeSpace_exact_internal
    (TM.binaryCopyIntoTM
      (resultTape spec)
      (registerTape spec destination hdestination)
      (copyScratchTape spec))
    (TM.seqTM
      (TM.resetBinaryWorkTM (lhsTape spec))
      (TM.resetBinaryWorkTM (resultTape spec)))
    (executionInput input) work₂ work₃ work₅ (natTape 0)
    (TM.binaryCopyTime routedValue destinationValue) _
    input.length (instructionSpace wordBits)
    hcopyResult htailReset hinput hwork₃Parked houtput
  have htailDispatch := seqTM_hoareTimeSpace_exact_internal
    (readDispatchTM spec)
    (TM.seqTM
      (TM.binaryCopyIntoTM
        (resultTape spec)
        (registerTape spec destination hdestination)
        (copyScratchTape spec))
      (TM.seqTM
        (TM.resetBinaryWorkTM (lhsTape spec))
        (TM.resetBinaryWorkTM (resultTape spec))))
    (executionInput input) work₁ work₂ work₅ (natTape 0)
    (readDispatchTime spec input snapshot address) _
    input.length (instructionSpace wordBits)
    hdispatchExact htailCopy hinput hwork₂Parked houtput
  have hfull := seqTM_hoareTimeSpace_exact_internal
    (TM.binaryCopyIntoTM
      (registerTape spec addressRegister haddressRegister)
      (lhsTape spec) (copyScratchTape spec))
    (TM.seqTM
      (readDispatchTM spec)
      (TM.seqTM
        (TM.binaryCopyIntoTM
          (resultTape spec)
          (registerTape spec destination hdestination)
          (copyScratchTape spec))
        (TM.seqTM
          (TM.resetBinaryWorkTM (lhsTape spec))
          (TM.resetBinaryWorkTM (resultTape spec)))))
    (executionInput input) initialWork work₁ work₅ (natTape 0)
    (TM.binaryCopyTime address 0) _
    input.length (instructionSpace wordBits)
    hcopyAddress htailDispatch hinput hwork₁Parked houtput
  have hroute :
      routedValue =
        DenseOverlay.read input snapshot.overlay address := by
    exact routedRead_eq_denseRead_internal
      spec input snapshot hcovered address
  have hinitialLhsEq : initialWork (lhsTape spec) = natTape 0 :=
    hasBinaryNat_eq_natTape
      (by simpa [lhsTape] using hinitialScratch 0 (by decide))
  have hinitialResultEq :
      initialWork (resultTape spec) = natTape 0 :=
    hasBinaryNat_eq_natTape
      (by simpa [resultTape] using hinitialScratch 2 (by decide))
  have hinitialSelectorEq :
      initialWork (selectorTape spec) = natTape 0 :=
    hasBinaryNat_eq_natTape
      (by simpa [selectorTape] using hinitialScratch 11 (by decide))
  have hdestinationLhs :
      registerTape spec destination hdestination ≠ lhsTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 0
  have hdestinationResult :
      registerTape spec destination hdestination ≠ resultTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 2
  have hdestinationSelector :
      registerTape spec destination hdestination ≠ selectorTape spec :=
    registerTape_ne_scratchTape_internal spec destination hdestination 11
  have hlhsResult : lhsTape spec ≠ resultTape spec :=
    scratchTape_ne_internal spec (by decide)
  have hfinal :
      work₅ =
        Function.update initialWork
          (registerTape spec destination hdestination)
          (natTape routedValue) := by
    funext i
    by_cases hiDestination :
        i = registerTape spec destination hdestination
    · subst i
      dsimp only [work₅, work₄, work₃]
      rw [Function.update_of_ne hdestinationResult]
      rw [Function.update_of_ne hdestinationLhs]
      rw [Function.update_self, Function.update_self]
    by_cases hiLhs : i = lhsTape spec
    · subst i
      dsimp only [work₅, work₄]
      rw [Function.update_of_ne hlhsResult]
      rw [Function.update_self]
      rw [Function.update_of_ne hiDestination, hinitialLhsEq]
    by_cases hiResult : i = resultTape spec
    · subst i
      dsimp only [work₅]
      rw [Function.update_self]
      rw [Function.update_of_ne hiDestination, hinitialResultEq]
    by_cases hiSelector : i = selectorTape spec
    · subst i
      dsimp only [work₅, work₄, work₃, work₂]
      rw [Function.update_of_ne hiResult]
      rw [Function.update_of_ne hiLhs]
      rw [Function.update_of_ne hiDestination]
      rw [Function.update_of_ne hiResult]
      rw [Function.update_self]
      rw [Function.update_of_ne hiDestination, hinitialSelectorEq]
    · dsimp only [work₅, work₄, work₃, work₂, work₁]
      rw [Function.update_of_ne hiResult]
      rw [Function.update_of_ne hiLhs]
      rw [Function.update_of_ne hiDestination]
      rw [Function.update_of_ne hiResult]
      rw [Function.update_of_ne hiSelector]
      rw [Function.update_of_ne hiLhs]
      rw [Function.update_of_ne hiDestination]
  have hfullFinal :
      (loadInstructionTM spec destination addressRegister
        hdestination haddressRegister).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape
                (DenseOverlay.read input snapshot.overlay
                  (DenseOverlay.read input snapshot.overlay
                    addressRegister))) ∧
          out = natTape 0)
        (TM.binaryCopyTime address 0 + 1 +
          (readDispatchTime spec input snapshot address + 1 +
            (TM.binaryCopyTime routedValue destinationValue + 1 +
              (TM.resetBinaryWorkTime 1 address.bits.length + 1 +
                TM.resetBinaryWorkTime 1
                  routedValue.bits.length))))
        input.length (instructionSpace wordBits) := by
    simpa only [loadInstructionTM] using hfull.consequence
      (fun inp work out hpre => by simpa [initialWork] using hpre)
      (fun inp work out hpost => by
        rcases hpost with ⟨hinp, hworkEq, hout⟩
        refine ⟨hinp, ?_, hout⟩
        rw [hworkEq, hfinal, hroute])
      le_rfl le_rfl le_rfl
  exact ⟨
    TM.binaryCopyTime address 0 + 1 +
      (readDispatchTime spec input snapshot address + 1 +
        (TM.binaryCopyTime routedValue destinationValue + 1 +
          (TM.resetBinaryWorkTime 1 address.bits.length + 1 +
            TM.resetBinaryWorkTime 1 routedValue.bits.length))),
    hfullFinal⟩

private theorem loadInstructionTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (destination addressRegister : ℕ)
    (hdestination : destination < spec.registerBound)
    (haddressRegister : addressRegister < spec.registerBound) :
    ∃ time,
      (loadInstructionTM spec destination addressRegister
        hdestination haddressRegister).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape
                (DenseOverlay.read input snapshot.overlay
                  (DenseOverlay.read input snapshot.overlay
                    addressRegister))) ∧
          out = natTape 0)
        time := by
  let address :=
    DenseOverlay.read input snapshot.overlay addressRegister
  let routedValue :=
    routedRead input snapshot spec.registerBound address
  let destinationValue :=
    DenseOverlay.read input snapshot.overlay destination
  let wordBits :=
    address.size + routedValue.size + destinationValue.size
  obtain ⟨time, hcontract⟩ :=
    loadInstructionTM_hoareTimeSpace_internal spec input snapshot hcovered
      destination addressRegister hdestination haddressRegister wordBits
      (by dsimp [wordBits, address, routedValue, destinationValue]; omega)
      (by dsimp [wordBits, address, routedValue, destinationValue]; omega)
      (by dsimp [wordBits, address, routedValue, destinationValue]; omega)
  exact ⟨time, hcontract.1⟩

private theorem setPCTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (target : ℕ) :
    ∃ time,
      (setNatTM (pcTape spec) target).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input { snapshot with pc := target } ∧
          out = natTape 0)
        time := by
  have hpc :
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc := by
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  obtain ⟨time, hset⟩ := setNatTM_hoareTime_internal
    (pcTape spec) snapshot.pc target
    (executionInput input) (executionWork spec input snapshot)
    (natTape 0) hpc (executionInput_parked input)
    (executionWork_parked_internal spec input snapshot)
    (natTape_parked_internal 0)
  refine ⟨time, hset.consequence (fun _ _ _ h => h) ?_ le_rfl⟩
  rintro inp work out ⟨hinp, hwork, hout⟩
  refine ⟨hinp, ?_, hout⟩
  rw [hwork, executionWork_setPC_internal]

private theorem setPCTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (target wordBits : ℕ)
    (hpcWidth : snapshot.pc.size ≤ wordBits)
    (htargetWidth : target.size ≤ wordBits) :
    ∃ time,
      (setNatTM (pcTape spec) target).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input { snapshot with pc := target } ∧
          out = natTape 0)
        time input.length (instructionSpace wordBits) := by
  have hpc :
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc := by
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  obtain ⟨time, hset⟩ := setNatTM_hoareTimeSpace_internal
    (pcTape spec) snapshot.pc target input.length wordBits
    (executionInput input) (executionWork spec input snapshot)
    (natTape 0) hpc hpcWidth htargetWidth
    (executionInput_parked input)
    (executionWork_parked_internal spec input snapshot)
    (natTape_parked_internal 0)
    (by simp [executionInput, Tape.move])
    (executionWork_head_internal spec input snapshot)
  refine ⟨time, hset.consequence (fun _ _ _ h => h) ?_
    le_rfl le_rfl le_rfl⟩
  rintro inp work out ⟨hinp, hwork, hout⟩
  refine ⟨hinp, ?_, hout⟩
  rw [hwork, executionWork_setPC_internal]

private theorem succPCTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot) :
    (TM.binarySuccTM (pcTape spec)).HoareTime
      (fun inp work out =>
        inp = executionInput input ∧
        work = executionWork spec input snapshot ∧
        out = natTape 0)
      (fun inp work out =>
        inp = executionInput input ∧
        work =
          executionWork spec input
            { snapshot with pc := snapshot.pc + 1 } ∧
        out = natTape 0)
      (TM.binarySuccTime snapshot.pc) := by
  have hpc :
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc := by
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hsucc := binarySuccTM_hoareTime_exact_internal
    (pcTape spec) snapshot.pc
    (executionInput input) (executionWork spec input snapshot)
    (natTape 0) hpc (executionInput_parked input)
    (executionWork_parked_internal spec input snapshot)
    (natTape_parked_internal 0)
  apply hsucc.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hwork, hout⟩
    refine ⟨hinp, ?_, hout⟩
    rw [hwork, executionWork_setPC_internal]
  · exact le_rfl

private theorem succPCTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (wordBits : ℕ) (hpcWidth : snapshot.pc.size ≤ wordBits) :
    (TM.binarySuccTM (pcTape spec)).HoareTimeSpace
      (fun inp work out =>
        inp = executionInput input ∧
        work = executionWork spec input snapshot ∧
        out = natTape 0)
      (fun inp work out =>
        inp = executionInput input ∧
        work =
          executionWork spec input
            { snapshot with pc := snapshot.pc + 1 } ∧
        out = natTape 0)
      (TM.binarySuccTime snapshot.pc) input.length
      (instructionSpace wordBits) := by
  have hpc :
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc := by
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hsucc := binarySuccTM_hoareTimeSpace_exact_internal
    (pcTape spec) snapshot.pc input.length wordBits
    (executionInput input) (executionWork spec input snapshot)
    (natTape 0) hpc hpcWidth (executionInput_parked input)
    (executionWork_parked_internal spec input snapshot)
    (natTape_parked_internal 0)
    (by simp [executionInput, Tape.move])
    (executionWork_head_internal spec input snapshot)
  apply hsucc.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hwork, hout⟩
    refine ⟨hinp, ?_, hout⟩
    rw [hwork, executionWork_setPC_internal]
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

private theorem writeThenSuccTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (machine : TM (workTapeCount spec))
    (destination value : ℕ)
    (hdestination : destination < spec.registerBound)
    (machineTime : ℕ)
    (hmachine :
      machine.HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape value) ∧
          out = natTape 0)
        machineTime) :
    ∃ time,
      (TM.seqTM machine
        (TM.binarySuccTM (pcTape spec))).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              { pc := snapshot.pc + 1
                overlay :=
                  DenseOverlay.write snapshot.overlay destination value } ∧
          out = natTape 0)
        time := by
  let work₁ :=
    Function.update (executionWork spec input snapshot)
      (registerTape spec destination hdestination) (natTape value)
  let work₂ :=
    Function.update work₁ (pcTape spec) (natTape (snapshot.pc + 1))
  have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
    update_natTape_parked_internal
      (executionWork spec input snapshot)
      (registerTape spec destination hdestination) value
      (executionWork_parked_internal spec input snapshot)
  have hwork₁PC :
      (work₁ (pcTape spec)).HasBinaryNat snapshot.pc := by
    dsimp only [work₁]
    unfold pcTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 10).symm]
    change
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hsucc := binarySuccTM_hoareTime_exact_internal
    (pcTape spec) snapshot.pc
    (executionInput input) work₁ (natTape 0)
    hwork₁PC (executionInput_parked input) hwork₁Parked
    (natTape_parked_internal 0)
  have hmachineExact :
      machine.HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧ work = work₁ ∧
          out = natTape 0)
        machineTime := by
    simpa only [work₁] using hmachine
  have hseq := seqTM_hoareTime_exact_internal
    machine (TM.binarySuccTM (pcTape spec))
    (executionInput input) (executionWork spec input snapshot)
    work₁ work₂ (natTape 0)
    machineTime (TM.binarySuccTime snapshot.pc)
    hmachineExact hsucc (executionInput_parked input)
    hwork₁Parked
    (natTape_parked_internal 0)
  have hfinal :
      work₂ =
        executionWork spec input
          { pc := snapshot.pc + 1
            overlay :=
              DenseOverlay.write snapshot.overlay destination value } := by
    dsimp only [work₂, work₁]
    exact executionWork_write_internal spec input snapshot hcanonical
      destination value (snapshot.pc + 1) hdestination
  refine ⟨machineTime + 1 + TM.binarySuccTime snapshot.pc, ?_⟩
  apply hseq.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hwork, hout⟩
    exact ⟨hinp, hwork.trans hfinal, hout⟩
  · exact le_rfl

private theorem writeThenSuccTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (machine : TM (workTapeCount spec))
    (destination value : ℕ)
    (hdestination : destination < spec.registerBound)
    (machineTime wordBits : ℕ)
    (hpcWidth : snapshot.pc.size ≤ wordBits)
    (hmachine :
      machine.HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (registerTape spec destination hdestination)
              (natTape value) ∧
          out = natTape 0)
        machineTime input.length (instructionSpace wordBits)) :
    ∃ time,
      (TM.seqTM machine
        (TM.binarySuccTM (pcTape spec))).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              { pc := snapshot.pc + 1
                overlay :=
                  DenseOverlay.write snapshot.overlay destination value } ∧
          out = natTape 0)
        time input.length (instructionSpace wordBits) := by
  let work₁ :=
    Function.update (executionWork spec input snapshot)
      (registerTape spec destination hdestination) (natTape value)
  let work₂ :=
    Function.update work₁ (pcTape spec) (natTape (snapshot.pc + 1))
  have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
    update_natTape_parked_internal
      (executionWork spec input snapshot)
      (registerTape spec destination hdestination) value
      (executionWork_parked_internal spec input snapshot)
  have hwork₁Head : ∀ i, (work₁ i).head = 1 :=
    update_natTape_head_internal
      (executionWork spec input snapshot)
      (registerTape spec destination hdestination) value
      (executionWork_head_internal spec input snapshot)
  have hwork₁PC :
      (work₁ (pcTape spec)).HasBinaryNat snapshot.pc := by
    dsimp only [work₁]
    unfold pcTape
    rw [Function.update_of_ne
      (registerTape_ne_scratchTape_internal spec destination
        hdestination 10).symm]
    change
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hsucc := binarySuccTM_hoareTimeSpace_exact_internal
    (pcTape spec) snapshot.pc input.length wordBits
    (executionInput input) work₁ (natTape 0)
    hwork₁PC hpcWidth (executionInput_parked input) hwork₁Parked
    (natTape_parked_internal 0)
    (by simp [executionInput, Tape.move]) hwork₁Head
  have hmachineExact :
      machine.HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧ work = work₁ ∧
          out = natTape 0)
        machineTime input.length (instructionSpace wordBits) := by
    simpa only [work₁] using hmachine
  have hseq := seqTM_hoareTimeSpace_exact_internal
    machine (TM.binarySuccTM (pcTape spec))
    (executionInput input) (executionWork spec input snapshot)
    work₁ work₂ (natTape 0)
    machineTime (TM.binarySuccTime snapshot.pc)
    input.length (instructionSpace wordBits)
    hmachineExact hsucc (executionInput_parked input)
    hwork₁Parked (natTape_parked_internal 0)
  have hfinal :
      work₂ =
        executionWork spec input
          { pc := snapshot.pc + 1
            overlay :=
              DenseOverlay.write snapshot.overlay destination value } := by
    dsimp only [work₂, work₁]
    exact executionWork_write_internal spec input snapshot hcanonical
      destination value (snapshot.pc + 1) hdestination
  refine ⟨machineTime + 1 + TM.binarySuccTime snapshot.pc, ?_⟩
  apply hseq.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hwork, hout⟩
    exact ⟨hinp, hwork.trans hfinal, hout⟩
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

private theorem executeInstructionTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (instruction : Instr)
    (hregisters :
      InstrRegistersBelow spec.registerBound instruction)
    (hnostore : InstrNoStore instruction) :
    ∃ time,
      (executeInstructionTM spec instruction).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (snapshot.stepInstr input instruction) ∧
          out = natTape 0)
        time := by
  cases instruction with
  | imm destination value =>
      simp only [InstrRegistersBelow] at hregisters
      have hold :
          (executionWork spec input snapshot
            (registerTape spec destination hregisters)).HasBinaryNat
              (DenseOverlay.read input snapshot.overlay destination) := by
        rw [executionWork_register_internal]
        exact natTape_hasBinaryNat_internal _
      obtain ⟨setTime, hset⟩ := setNatTM_hoareTime_internal
        (registerTape spec destination hregisters)
        (DenseOverlay.read input snapshot.overlay destination) value
        (executionInput input) (executionWork spec input snapshot)
        (natTape 0) hold (executionInput_parked input)
        (executionWork_parked_internal spec input snapshot)
        (natTape_parked_internal 0)
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTime_internal spec input snapshot
          hcanonical
          (setNatTM (registerTape spec destination hregisters) value)
          destination value hregisters setTime hset
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hregisters,
        DenseOverlay.Snapshot.stepInstr] using hfull
  | add destination source₀ source₁ =>
      rcases hregisters with ⟨hdestination, hsource₀, hsource₁⟩
      obtain ⟨value, instructionTime, hvalue, hinstruction⟩ :=
        binaryInstructionTM_hoareTime_internal spec input snapshot
          .add destination source₀ source₁ hdestination hsource₀ hsource₁
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTime_internal spec input snapshot
          hcanonical
          (binaryInstructionTM spec .add destination source₀ source₁
            hdestination hsource₀ hsource₁)
          destination value hdestination instructionTime hinstruction
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, hsource₀, hsource₁,
        DenseOverlay.Snapshot.stepInstr, hvalue] using hfull
  | sub destination source₀ source₁ =>
      rcases hregisters with ⟨hdestination, hsource₀, hsource₁⟩
      obtain ⟨value, instructionTime, hvalue, hinstruction⟩ :=
        binaryInstructionTM_hoareTime_internal spec input snapshot
          .sub destination source₀ source₁ hdestination hsource₀ hsource₁
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTime_internal spec input snapshot
          hcanonical
          (binaryInstructionTM spec .sub destination source₀ source₁
            hdestination hsource₀ hsource₁)
          destination value hdestination instructionTime hinstruction
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, hsource₀, hsource₁,
        DenseOverlay.Snapshot.stepInstr, hvalue] using hfull
  | mul destination source₀ source₁ =>
      rcases hregisters with ⟨hdestination, hsource₀, hsource₁⟩
      obtain ⟨value, instructionTime, hvalue, hinstruction⟩ :=
        binaryInstructionTM_hoareTime_internal spec input snapshot
          .mul destination source₀ source₁ hdestination hsource₀ hsource₁
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTime_internal spec input snapshot
          hcanonical
          (binaryInstructionTM spec .mul destination source₀ source₁
            hdestination hsource₀ hsource₁)
          destination value hdestination instructionTime hinstruction
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, hsource₀, hsource₁,
        DenseOverlay.Snapshot.stepInstr, hvalue] using hfull
  | load destination addressRegister =>
      rcases hregisters with ⟨hdestination, haddressRegister⟩
      obtain ⟨instructionTime, hinstruction⟩ :=
        loadInstructionTM_hoareTime_internal spec input snapshot hcovered
          destination addressRegister hdestination haddressRegister
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTime_internal spec input snapshot
          hcanonical
          (loadInstructionTM spec destination addressRegister
            hdestination haddressRegister)
          destination
          (DenseOverlay.read input snapshot.overlay
            (DenseOverlay.read input snapshot.overlay addressRegister))
          hdestination instructionTime hinstruction
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, haddressRegister,
        DenseOverlay.Snapshot.stepInstr] using hfull
  | store addressRegister source =>
      simp [InstrNoStore] at hnostore
  | jz source target =>
      simp only [InstrRegistersBelow] at hregisters
      let sourceValue :=
        DenseOverlay.read input snapshot.overlay source
      let post :=
        fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (snapshot.stepInstr input (.jz source target)) ∧
          out = natTape 0
      have hsource :
          (executionWork spec input snapshot
            (registerTape spec source hregisters)).HasBinaryNat
              sourceValue := by
        rw [executionWork_register_internal]
        exact natTape_hasBinaryNat_internal sourceValue
      have hframe :
          ∀ inp work out,
            (inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0) →
            inp.read ≠ Γ.start ∧
              (∀ i, (work i).read ≠ Γ.start) ∧
              out.read ≠ Γ.start := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        exact
          ⟨(executionInput_parked input).read_ne_start,
            fun i =>
              (executionWork_parked_internal spec input snapshot i).read_ne_start,
            (natTape_parked_internal 0).read_ne_start⟩
      by_cases hzero : sourceValue = 0
      · obtain ⟨blankTime, hblankRaw⟩ :=
          setPCTM_hoareTime_internal spec input snapshot target
        have hblank :
            (setNatTM (pcTape spec) target).HoareTime
              (fun inp work out =>
                inp = executionInput input ∧
                work = executionWork spec input snapshot ∧
                out = natTape 0)
              post blankTime := by
          simpa [post, DenseOverlay.Snapshot.stepInstr, sourceValue,
            hzero] using hblankRaw
        have hnonblank :
            (TM.binarySuccTM (pcTape spec)).HoareTime
              (fun _ _ _ => False) post 0 := by
          intro inp work out hfalse
          exact hfalse.elim
        have hbranch := TM.branchWorkBlankTM_hoareTime
          (registerTape spec source hregisters)
          (setNatTM (pcTape spec) target)
          (TM.binarySuccTM (pcTape spec))
          hframe
          (fun _ _ _ hpre _ => hpre)
          (fun inp work out hpre hnonblankRead => by
            rcases hpre with ⟨rfl, rfl, rfl⟩
            exact hnonblankRead
              (hsource.read_eq_blank_iff.mpr hzero))
          hblank hnonblank
        refine ⟨TM.branchWorkBlankTime blankTime 0, ?_⟩
        have hbranchFinal := hbranch.consequence
          (fun _ _ _ h => h)
          (fun _ _ _ h => h.elim (fun hp => hp) (fun hp => hp))
          le_rfl
        simpa [executeInstructionTM, hregisters, post] using hbranchFinal
      · have hblank :
            (setNatTM (pcTape spec) target).HoareTime
              (fun _ _ _ => False) post 0 := by
          intro inp work out hfalse
          exact hfalse.elim
        have hnonblankRaw :=
          succPCTM_hoareTime_internal spec input snapshot
        have hnonblank :
            (TM.binarySuccTM (pcTape spec)).HoareTime
              (fun inp work out =>
                inp = executionInput input ∧
                work = executionWork spec input snapshot ∧
                out = natTape 0)
              post (TM.binarySuccTime snapshot.pc) := by
          simpa [post, DenseOverlay.Snapshot.stepInstr, sourceValue,
            hzero] using hnonblankRaw
        have hbranch := TM.branchWorkBlankTM_hoareTime
          (registerTape spec source hregisters)
          (setNatTM (pcTape spec) target)
          (TM.binarySuccTM (pcTape spec))
          hframe
          (fun inp work out hpre hblankRead => by
            rcases hpre with ⟨rfl, rfl, rfl⟩
            exact hzero (hsource.read_eq_blank_iff.mp hblankRead))
          (fun _ _ _ hpre _ => hpre)
          hblank hnonblank
        refine
          ⟨TM.branchWorkBlankTime 0
            (TM.binarySuccTime snapshot.pc), ?_⟩
        have hbranchFinal := hbranch.consequence
          (fun _ _ _ h => h)
          (fun _ _ _ h => h.elim (fun hp => hp) (fun hp => hp))
          le_rfl
        simpa [executeInstructionTM, hregisters, post] using hbranchFinal
  | jmp target =>
      obtain ⟨time, hset⟩ :=
        setPCTM_hoareTime_internal spec input snapshot target
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM,
        DenseOverlay.Snapshot.stepInstr] using hset
  | halt =>
      have hskip := TM.skipTM_hoareTime_frame
        (executionInput input) (executionWork spec input snapshot)
        (natTape 0) (executionInput_parked input)
        (executionWork_parked_internal spec input snapshot)
        (natTape_parked_internal 0)
      refine ⟨1, ?_⟩
      simpa [executeInstructionTM,
        DenseOverlay.Snapshot.stepInstr] using hskip

private theorem executeInstructionTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (instruction : Instr)
    (hregisters :
      InstrRegistersBelow spec.registerBound instruction)
    (hnostore : InstrNoStore instruction)
    (wordBits : ℕ)
    (hcurrent : SnapshotBound spec input snapshot wordBits)
    (hnext :
      SnapshotBound spec input
        (snapshot.stepInstr input instruction) wordBits)
    (hpcWidth : snapshot.pc.size ≤ wordBits)
    (hnextPCWidth :
      (snapshot.stepInstr input instruction).pc.size ≤ wordBits) :
    ∃ time,
      (executeInstructionTM spec instruction).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (snapshot.stepInstr input instruction) ∧
          out = natTape 0)
        time input.length (instructionSpace wordBits) := by
  cases instruction with
  | imm destination value =>
      simp only [InstrRegistersBelow] at hregisters
      have hold :
          (executionWork spec input snapshot
            (registerTape spec destination hregisters)).HasBinaryNat
              (DenseOverlay.read input snapshot.overlay destination) := by
        rw [executionWork_register_internal]
        exact natTape_hasBinaryNat_internal _
      have holdWidth :
          (DenseOverlay.read input snapshot.overlay destination).size ≤
            wordBits := by
        simpa [bitlen] using hcurrent destination hregisters
      have hvalueWidth : value.size ≤ wordBits := by
        have hwidth := hnext destination hregisters
        simp only [DenseOverlay.Snapshot.stepInstr] at hwidth
        rw [DenseOverlay.read_write input snapshot.overlay hcanonical
          destination value] at hwidth
        simpa [bitlen] using hwidth
      obtain ⟨setTime, hset⟩ := setNatTM_hoareTimeSpace_internal
        (registerTape spec destination hregisters)
        (DenseOverlay.read input snapshot.overlay destination) value
        input.length wordBits
        (executionInput input) (executionWork spec input snapshot)
        (natTape 0) hold holdWidth hvalueWidth
        (executionInput_parked input)
        (executionWork_parked_internal spec input snapshot)
        (natTape_parked_internal 0)
        (by simp [executionInput, Tape.move])
        (executionWork_head_internal spec input snapshot)
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTimeSpace_internal spec input snapshot
          hcanonical
          (setNatTM (registerTape spec destination hregisters) value)
          destination value hregisters setTime wordBits hpcWidth hset
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hregisters,
        DenseOverlay.Snapshot.stepInstr] using hfull
  | add destination source₀ source₁ =>
      rcases hregisters with ⟨hdestination, hsource₀, hsource₁⟩
      let lhsValue :=
        DenseOverlay.read input snapshot.overlay source₀
      let rhsValue :=
        DenseOverlay.read input snapshot.overlay source₁
      let destinationValue :=
        DenseOverlay.read input snapshot.overlay destination
      let value := lhsValue + rhsValue
      have hlhsWidth : lhsValue.size ≤ wordBits := by
        simpa [lhsValue, bitlen] using hcurrent source₀ hsource₀
      have hrhsWidth : rhsValue.size ≤ wordBits := by
        simpa [rhsValue, bitlen] using hcurrent source₁ hsource₁
      have hdestinationWidth : destinationValue.size ≤ wordBits := by
        simpa [destinationValue, bitlen] using
          hcurrent destination hdestination
      have hvalueWidth : value.size ≤ wordBits := by
        have hwidth := hnext destination hdestination
        simp only [DenseOverlay.Snapshot.stepInstr] at hwidth
        rw [DenseOverlay.read_write input snapshot.overlay hcanonical
          destination
          (DenseOverlay.read input snapshot.overlay source₀ +
            DenseOverlay.read input snapshot.overlay source₁)] at hwidth
        simpa [value, lhsValue, rhsValue, bitlen] using hwidth
      obtain ⟨computed, instructionTime, hvalue, hinstruction⟩ :=
        binaryInstructionTM_hoareTimeSpace_internal spec input snapshot
          .add destination source₀ source₁ hdestination hsource₀ hsource₁
          wordBits hlhsWidth hrhsWidth hdestinationWidth hvalueWidth
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTimeSpace_internal spec input snapshot
          hcanonical
          (binaryInstructionTM spec .add destination source₀ source₁
            hdestination hsource₀ hsource₁)
          destination computed hdestination instructionTime wordBits
          hpcWidth hinstruction
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, hsource₀, hsource₁,
        DenseOverlay.Snapshot.stepInstr, hvalue] using hfull
  | sub destination source₀ source₁ =>
      rcases hregisters with ⟨hdestination, hsource₀, hsource₁⟩
      let lhsValue :=
        DenseOverlay.read input snapshot.overlay source₀
      let rhsValue :=
        DenseOverlay.read input snapshot.overlay source₁
      let destinationValue :=
        DenseOverlay.read input snapshot.overlay destination
      let value := lhsValue - rhsValue
      have hlhsWidth : lhsValue.size ≤ wordBits := by
        simpa [lhsValue, bitlen] using hcurrent source₀ hsource₀
      have hrhsWidth : rhsValue.size ≤ wordBits := by
        simpa [rhsValue, bitlen] using hcurrent source₁ hsource₁
      have hdestinationWidth : destinationValue.size ≤ wordBits := by
        simpa [destinationValue, bitlen] using
          hcurrent destination hdestination
      have hvalueWidth : value.size ≤ wordBits := by
        have hwidth := hnext destination hdestination
        simp only [DenseOverlay.Snapshot.stepInstr] at hwidth
        rw [DenseOverlay.read_write input snapshot.overlay hcanonical
          destination
          (DenseOverlay.read input snapshot.overlay source₀ -
            DenseOverlay.read input snapshot.overlay source₁)] at hwidth
        simpa [value, lhsValue, rhsValue, bitlen] using hwidth
      obtain ⟨computed, instructionTime, hvalue, hinstruction⟩ :=
        binaryInstructionTM_hoareTimeSpace_internal spec input snapshot
          .sub destination source₀ source₁ hdestination hsource₀ hsource₁
          wordBits hlhsWidth hrhsWidth hdestinationWidth hvalueWidth
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTimeSpace_internal spec input snapshot
          hcanonical
          (binaryInstructionTM spec .sub destination source₀ source₁
            hdestination hsource₀ hsource₁)
          destination computed hdestination instructionTime wordBits
          hpcWidth hinstruction
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, hsource₀, hsource₁,
        DenseOverlay.Snapshot.stepInstr, hvalue] using hfull
  | mul destination source₀ source₁ =>
      rcases hregisters with ⟨hdestination, hsource₀, hsource₁⟩
      let lhsValue :=
        DenseOverlay.read input snapshot.overlay source₀
      let rhsValue :=
        DenseOverlay.read input snapshot.overlay source₁
      let destinationValue :=
        DenseOverlay.read input snapshot.overlay destination
      let value := lhsValue * rhsValue
      have hlhsWidth : lhsValue.size ≤ wordBits := by
        simpa [lhsValue, bitlen] using hcurrent source₀ hsource₀
      have hrhsWidth : rhsValue.size ≤ wordBits := by
        simpa [rhsValue, bitlen] using hcurrent source₁ hsource₁
      have hdestinationWidth : destinationValue.size ≤ wordBits := by
        simpa [destinationValue, bitlen] using
          hcurrent destination hdestination
      have hvalueWidth : value.size ≤ wordBits := by
        have hwidth := hnext destination hdestination
        simp only [DenseOverlay.Snapshot.stepInstr] at hwidth
        rw [DenseOverlay.read_write input snapshot.overlay hcanonical
          destination
          (DenseOverlay.read input snapshot.overlay source₀ *
            DenseOverlay.read input snapshot.overlay source₁)] at hwidth
        simpa [value, lhsValue, rhsValue, bitlen] using hwidth
      obtain ⟨computed, instructionTime, hvalue, hinstruction⟩ :=
        binaryInstructionTM_hoareTimeSpace_internal spec input snapshot
          .mul destination source₀ source₁ hdestination hsource₀ hsource₁
          wordBits hlhsWidth hrhsWidth hdestinationWidth hvalueWidth
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTimeSpace_internal spec input snapshot
          hcanonical
          (binaryInstructionTM spec .mul destination source₀ source₁
            hdestination hsource₀ hsource₁)
          destination computed hdestination instructionTime wordBits
          hpcWidth hinstruction
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, hsource₀, hsource₁,
        DenseOverlay.Snapshot.stepInstr, hvalue] using hfull
  | load destination addressRegister =>
      rcases hregisters with ⟨hdestination, haddressRegister⟩
      let address :=
        DenseOverlay.read input snapshot.overlay addressRegister
      let loadedValue :=
        DenseOverlay.read input snapshot.overlay address
      have haddressWidth : address.size ≤ wordBits := by
        simpa [address, bitlen] using
          hcurrent addressRegister haddressRegister
      have hdestinationWidth :
          (DenseOverlay.read input snapshot.overlay destination).size ≤
            wordBits := by
        simpa [bitlen] using hcurrent destination hdestination
      have hloadedWidth : loadedValue.size ≤ wordBits := by
        have hwidth := hnext destination hdestination
        simp only [DenseOverlay.Snapshot.stepInstr] at hwidth
        rw [DenseOverlay.read_write input snapshot.overlay hcanonical
          destination
          (DenseOverlay.read input snapshot.overlay
            (DenseOverlay.read input snapshot.overlay
              addressRegister))] at hwidth
        simpa [loadedValue, address, bitlen] using hwidth
      have hroutedWidth :
          (routedRead input snapshot spec.registerBound address).size ≤
            wordBits := by
        rw [routedRead_eq_denseRead_internal
          spec input snapshot hcovered address]
        exact hloadedWidth
      obtain ⟨instructionTime, hinstruction⟩ :=
        loadInstructionTM_hoareTimeSpace_internal spec input snapshot
          hcovered destination addressRegister hdestination
          haddressRegister wordBits haddressWidth hroutedWidth
          hdestinationWidth
      obtain ⟨time, hfull⟩ :=
        writeThenSuccTM_hoareTimeSpace_internal spec input snapshot
          hcanonical
          (loadInstructionTM spec destination addressRegister
            hdestination haddressRegister)
          destination loadedValue hdestination instructionTime wordBits
          hpcWidth (by simpa [loadedValue, address] using hinstruction)
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM, hdestination, haddressRegister,
        DenseOverlay.Snapshot.stepInstr, loadedValue, address] using hfull
  | store addressRegister source =>
      simp [InstrNoStore] at hnostore
  | jz source target =>
      simp only [InstrRegistersBelow] at hregisters
      let sourceValue :=
        DenseOverlay.read input snapshot.overlay source
      let post :=
        fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (snapshot.stepInstr input (.jz source target)) ∧
          out = natTape 0
      have hsource :
          (executionWork spec input snapshot
            (registerTape spec source hregisters)).HasBinaryNat
              sourceValue := by
        rw [executionWork_register_internal]
        exact natTape_hasBinaryNat_internal sourceValue
      have hframe :
          ∀ inp work out,
            (inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0) →
            inp.read ≠ Γ.start ∧
              (∀ i, (work i).read ≠ Γ.start) ∧
              out.read ≠ Γ.start := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        exact
          ⟨(executionInput_parked input).read_ne_start,
            fun i =>
              (executionWork_parked_internal spec input snapshot i).read_ne_start,
            (natTape_parked_internal 0).read_ne_start⟩
      by_cases hzero : sourceValue = 0
      · have htargetWidth : target.size ≤ wordBits := by
          simpa [DenseOverlay.Snapshot.stepInstr, sourceValue, hzero] using
            hnextPCWidth
        obtain ⟨blankTime, hblankRaw⟩ :=
          setPCTM_hoareTimeSpace_internal spec input snapshot target
            wordBits hpcWidth htargetWidth
        have hblank :
            (setNatTM (pcTape spec) target).HoareTimeSpace
              (fun inp work out =>
                inp = executionInput input ∧
                work = executionWork spec input snapshot ∧
                out = natTape 0)
              post blankTime input.length (instructionSpace wordBits) := by
          simpa [post, DenseOverlay.Snapshot.stepInstr, sourceValue,
            hzero] using hblankRaw
        have hnonblank :
            (TM.binarySuccTM (pcTape spec)).HoareTimeSpace
              (fun _ _ _ => False) post 0 input.length
              (instructionSpace wordBits) := by
          constructor
          · intro inp work out hfalse
            exact hfalse.elim
          · intro inp work out hfalse
            exact hfalse.elim
        have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
          (registerTape spec source hregisters)
          (setNatTM (pcTape spec) target)
          (TM.binarySuccTM (pcTape spec))
          hframe
          (fun _ _ _ hpre _ => hpre)
          (fun inp work out hpre hnonblankRead => by
            rcases hpre with ⟨rfl, rfl, rfl⟩
            exact hnonblankRead
              (hsource.read_eq_blank_iff.mpr hzero))
          hblank hnonblank
        refine ⟨TM.branchWorkBlankTime blankTime 0, ?_⟩
        have hbranchFinal :
            (TM.branchWorkBlankTM
              (registerTape spec source hregisters)
              (setNatTM (pcTape spec) target)
              (TM.binarySuccTM (pcTape spec))).HoareTimeSpace
              (fun inp work out =>
                inp = executionInput input ∧
                work = executionWork spec input snapshot ∧
                out = natTape 0)
              post (TM.branchWorkBlankTime blankTime 0)
              input.length (instructionSpace wordBits) := by
          simpa using hbranch
        simpa [executeInstructionTM, hregisters, post] using hbranchFinal
      · have hblank :
            (setNatTM (pcTape spec) target).HoareTimeSpace
              (fun _ _ _ => False) post 0 input.length
              (instructionSpace wordBits) := by
          constructor
          · intro inp work out hfalse
            exact hfalse.elim
          · intro inp work out hfalse
            exact hfalse.elim
        have hnonblankRaw :=
          succPCTM_hoareTimeSpace_internal spec input snapshot
            wordBits hpcWidth
        have hnonblank :
            (TM.binarySuccTM (pcTape spec)).HoareTimeSpace
              (fun inp work out =>
                inp = executionInput input ∧
                work = executionWork spec input snapshot ∧
                out = natTape 0)
              post (TM.binarySuccTime snapshot.pc)
              input.length (instructionSpace wordBits) := by
          simpa [post, DenseOverlay.Snapshot.stepInstr, sourceValue,
            hzero] using hnonblankRaw
        have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
          (registerTape spec source hregisters)
          (setNatTM (pcTape spec) target)
          (TM.binarySuccTM (pcTape spec))
          hframe
          (fun inp work out hpre hblankRead => by
            rcases hpre with ⟨rfl, rfl, rfl⟩
            exact hzero (hsource.read_eq_blank_iff.mp hblankRead))
          (fun _ _ _ hpre _ => hpre)
          hblank hnonblank
        refine
          ⟨TM.branchWorkBlankTime 0
            (TM.binarySuccTime snapshot.pc), ?_⟩
        have hbranchFinal :
            (TM.branchWorkBlankTM
              (registerTape spec source hregisters)
              (setNatTM (pcTape spec) target)
              (TM.binarySuccTM (pcTape spec))).HoareTimeSpace
              (fun inp work out =>
                inp = executionInput input ∧
                work = executionWork spec input snapshot ∧
                out = natTape 0)
              post
              (TM.branchWorkBlankTime 0
                (TM.binarySuccTime snapshot.pc))
              input.length (instructionSpace wordBits) := by
          simpa using hbranch
        simpa [executeInstructionTM, hregisters, post] using hbranchFinal
  | jmp target =>
      have htargetWidth : target.size ≤ wordBits := by
        simpa [DenseOverlay.Snapshot.stepInstr] using hnextPCWidth
      obtain ⟨time, hset⟩ :=
        setPCTM_hoareTimeSpace_internal spec input snapshot target
          wordBits hpcWidth htargetWidth
      refine ⟨time, ?_⟩
      simpa [executeInstructionTM,
        DenseOverlay.Snapshot.stepInstr] using hset
  | halt =>
      have hskip := TM.skipTM_hoareTime_frame
        (executionInput input) (executionWork spec input snapshot)
        (natTape 0) (executionInput_parked input)
        (executionWork_parked_internal spec input snapshot)
        (natTape_parked_internal 0)
      have hspace := hskip.toHoareTimeSpace
        (inputLength := input.length) (initialSpace := 1)
        (by
          rintro inp work out ⟨rfl, rfl, rfl⟩
          exact exactStart_withinAuxSpace_one_internal
            TM.skipTM (executionInput input)
            (executionWork spec input snapshot) (natTape 0)
            (by simp [executionInput, Tape.move])
            (executionWork_head_internal spec input snapshot))
      refine ⟨1, ?_⟩
      have hbounded :
          TM.skipTM.HoareTimeSpace
            (fun inp work out =>
              inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0)
            (fun inp work out =>
              inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0)
            1 input.length (instructionSpace wordBits) :=
        hspace.consequence
          (fun _ _ _ h => h) (fun _ _ _ h => h)
          le_rfl le_rfl (by
            unfold instructionSpace
            omega)
      simpa [executeInstructionTM,
        DenseOverlay.Snapshot.stepInstr] using hbounded

private theorem selectedInstruction_eq_getD_internal
    (program : Program) (selector : ℕ) :
    selectedInstruction program selector =
      (program[selector]?).getD .halt := by
  induction program generalizing selector with
  | nil => simp [selectedInstruction]
  | cons instruction tail ih =>
      cases selector with
      | zero => simp [selectedInstruction]
      | succ selector =>
          simpa [selectedInstruction] using ih selector

private theorem dispatchProgramTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (remaining : Program) (selector : ℕ)
    (hregisters : ∀ index,
      InstrRegistersBelow spec.registerBound
        (selectedInstruction remaining index))
    (hnostore : ∀ index,
      InstrNoStore (selectedInstruction remaining index)) :
    ∃ time,
      (dispatchProgramTM spec remaining).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector) ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (snapshot.stepInstr input
                (selectedInstruction remaining selector)) ∧
          out = natTape 0)
        time := by
  induction remaining generalizing selector with
  | nil =>
      let work₀ :=
        Function.update (executionWork spec input snapshot)
          (selectorTape spec) (natTape selector)
      have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
        update_natTape_parked_internal
          (executionWork spec input snapshot)
          (selectorTape spec) selector
          (executionWork_parked_internal spec input snapshot)
      have hselector :
          (work₀ (selectorTape spec)).HasBinaryNat selector := by
        dsimp only [work₀]
        rw [Function.update_self]
        exact natTape_hasBinaryNat_internal selector
      have hreset := resetBinaryWorkTM_hoareTime_exact_internal
        (selectorTape spec) selector
        (executionInput input) work₀ (natTape 0)
        hselector (executionInput_parked input) hwork₀Parked
        (natTape_parked_internal 0)
      have hbaseSelector :
          executionWork spec input snapshot (selectorTape spec) =
            natTape 0 := by
        exact hasBinaryNat_eq_natTape
          (by
            change
              (executionWork spec input snapshot
                (scratchTape spec 11)).HasBinaryNat 0
            rw [executionWork_scratch_internal spec input snapshot
              11 (by decide)]
            exact natTape_hasBinaryNat_internal 0)
      have hresetFinal :
          (TM.resetBinaryWorkTM (selectorTape spec)).HoareTime
            (fun inp work out =>
              inp = executionInput input ∧ work = work₀ ∧
              out = natTape 0)
            (fun inp work out =>
              inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0)
            (TM.resetBinaryWorkTime 1 selector.bits.length) := by
        apply hreset.consequence
        · exact fun _ _ _ h => h
        · rintro inp work out ⟨hinp, hwork, hout⟩
          refine ⟨hinp, ?_, hout⟩
          rw [hwork]
          simp [work₀, Function.update_idem, hbaseSelector]
        · exact le_rfl
      obtain ⟨haltTime, hhalt⟩ :=
        executeInstructionTM_hoareTime_internal spec input snapshot
          hcanonical hcovered .halt
          (by simp [InstrRegistersBelow])
          (by simp [InstrNoStore])
      have hseq := seqTM_hoareTime_exact_internal
        (TM.resetBinaryWorkTM (selectorTape spec))
        (executeInstructionTM spec .halt)
        (executionInput input) work₀
        (executionWork spec input snapshot)
        (executionWork spec input snapshot) (natTape 0)
        (TM.resetBinaryWorkTime 1 selector.bits.length) haltTime
        hresetFinal hhalt (executionInput_parked input)
        (executionWork_parked_internal spec input snapshot)
        (natTape_parked_internal 0)
      refine
        ⟨TM.resetBinaryWorkTime 1 selector.bits.length + 1 +
          haltTime, ?_⟩
      simpa [dispatchProgramTM, selectedInstruction,
        DenseOverlay.Snapshot.stepInstr, work₀] using hseq
  | cons instruction tail ih =>
      have hinstructionRegisters :
          InstrRegistersBelow spec.registerBound instruction := by
        simpa [selectedInstruction] using hregisters 0
      have hinstructionNoStore : InstrNoStore instruction := by
        simpa [selectedInstruction] using hnostore 0
      have htailRegisters :
          ∀ index,
            InstrRegistersBelow spec.registerBound
              (selectedInstruction tail index) := by
        intro index
        simpa [selectedInstruction] using hregisters (index + 1)
      have htailNoStore :
          ∀ index, InstrNoStore (selectedInstruction tail index) := by
        intro index
        simpa [selectedInstruction] using hnostore (index + 1)
      cases selector with
      | zero =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape 0)
          have hbaseSelector :
              executionWork spec input snapshot (selectorTape spec) =
                natTape 0 := by
            exact hasBinaryNat_eq_natTape
              (by
                change
                  (executionWork spec input snapshot
                    (scratchTape spec 11)).HasBinaryNat 0
                rw [executionWork_scratch_internal spec input snapshot
                  11 (by decide)]
                exact natTape_hasBinaryNat_internal 0)
          have hwork₀Eq :
              work₀ = executionWork spec input snapshot := by
            dsimp only [work₀]
            rw [← hbaseSelector, Function.update_eq_self]
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
            rw [hwork₀Eq]
            exact executionWork_parked_internal spec input snapshot
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat 0 := by
            rw [hwork₀Eq, hbaseSelector]
            exact natTape_hasBinaryNat_internal 0
          obtain ⟨instructionTime, hinstruction⟩ :=
            executeInstructionTM_hoareTime_internal spec input snapshot
              hcanonical hcovered instruction hinstructionRegisters
              hinstructionNoStore
          have hblank :
              (executeInstructionTM spec instruction).HoareTime
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) 0)) ∧
                  out = natTape 0)
                instructionTime := by
            simpa [hwork₀Eq, selectedInstruction] using hinstruction
          have hnonblank :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchProgramTM spec tail)).HoareTime
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) 0)) ∧
                  out = natTape 0)
                0 := by
            intro inp work out hfalse
            exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTime
            (selectorTape spec)
            (executeInstructionTM spec instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchProgramTM spec tail))
            hframe
            (fun _ _ _ hpre _ => hpre)
            (fun inp work out hpre hnonblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              exact hnonblankRead
                (hselector.read_eq_blank_iff.mpr rfl))
            hblank hnonblank
          refine
            ⟨TM.branchWorkBlankTime instructionTime 0, ?_⟩
          have hbranchFinal := hbranch.consequence
            (fun _ _ _ h => h)
            (fun _ _ _ h => h.elim (fun hp => hp) (fun hp => hp))
            le_rfl
          simpa [dispatchProgramTM, work₀] using hbranchFinal
      | succ selector =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape (selector + 1))
          let work₁ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector)
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) (selector + 1)
              (executionWork_parked_internal spec input snapshot)
          have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) selector
              (executionWork_parked_internal spec input snapshot)
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat
                (selector + 1) := by
            dsimp only [work₀]
            rw [Function.update_self]
            exact natTape_hasBinaryNat_internal (selector + 1)
          have hpredRaw := binaryPredTM_hoareTime_exact_internal
            (selectorTape spec) selector
            (executionInput input) work₀ (natTape 0)
            hselector (executionInput_parked input) hwork₀Parked
            (natTape_parked_internal 0)
          have hpred :
              (TM.binaryPredTM (selectorTape spec)).HoareTime
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₁ ∧
                  out = natTape 0)
                (TM.binaryPredTime selector) := by
            simpa [work₀, work₁, Function.update_idem] using hpredRaw
          obtain ⟨recursiveTime, hrecursive⟩ :=
            ih selector htailRegisters htailNoStore
          have hseqRaw := seqTM_hoareTime_exact_internal
            (TM.binaryPredTM (selectorTape spec))
            (dispatchProgramTM spec tail)
            (executionInput input) work₀ work₁
            (executionWork spec input
              (snapshot.stepInstr input
                (selectedInstruction tail selector)))
            (natTape 0) (TM.binaryPredTime selector) recursiveTime
            hpred hrecursive (executionInput_parked input)
            hwork₁Parked (natTape_parked_internal 0)
          have hseq :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchProgramTM spec tail)).HoareTime
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) (selector + 1))) ∧
                  out = natTape 0)
                (TM.binaryPredTime selector + 1 +
                  recursiveTime) := by
            simpa [selectedInstruction] using hseqRaw
          have hblank :
              (executeInstructionTM spec instruction).HoareTime
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) (selector + 1))) ∧
                  out = natTape 0)
                0 := by
            intro inp work out hfalse
            exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTime
            (selectorTape spec)
            (executeInstructionTM spec instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchProgramTM spec tail))
            hframe
            (fun inp work out hpre hblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              have hzero :=
                hselector.read_eq_blank_iff.mp hblankRead
              omega)
            (fun _ _ _ hpre _ => hpre)
            hblank hseq
          refine
            ⟨TM.branchWorkBlankTime 0
              (TM.binaryPredTime selector + 1 + recursiveTime), ?_⟩
          have hbranchFinal := hbranch.consequence
            (fun _ _ _ h => h)
            (fun _ _ _ h => h.elim (fun hp => hp) (fun hp => hp))
            le_rfl
          simpa [dispatchProgramTM, work₀] using hbranchFinal

private theorem dispatchProgramTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (remaining : Program) (selector wordBits : ℕ)
    (hregisters : ∀ index,
      InstrRegistersBelow spec.registerBound
        (selectedInstruction remaining index))
    (hnostore : ∀ index,
      InstrNoStore (selectedInstruction remaining index))
    (hselectorWidth : selector.size ≤ wordBits)
    (hcurrent : SnapshotBound spec input snapshot wordBits)
    (hnext :
      SnapshotBound spec input
        (snapshot.stepInstr input
          (selectedInstruction remaining selector)) wordBits)
    (hpcWidth : snapshot.pc.size ≤ wordBits)
    (hnextPCWidth :
      (snapshot.stepInstr input
        (selectedInstruction remaining selector)).pc.size ≤ wordBits) :
    ∃ time,
      (dispatchProgramTM spec remaining).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector) ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (snapshot.stepInstr input
                (selectedInstruction remaining selector)) ∧
          out = natTape 0)
        time input.length (instructionSpace wordBits) := by
  induction remaining generalizing selector with
  | nil =>
      let work₀ :=
        Function.update (executionWork spec input snapshot)
          (selectorTape spec) (natTape selector)
      have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
        update_natTape_parked_internal
          (executionWork spec input snapshot)
          (selectorTape spec) selector
          (executionWork_parked_internal spec input snapshot)
      have hwork₀Head : ∀ i, (work₀ i).head = 1 :=
        update_natTape_head_internal
          (executionWork spec input snapshot)
          (selectorTape spec) selector
          (executionWork_head_internal spec input snapshot)
      have hselector :
          (work₀ (selectorTape spec)).HasBinaryNat selector := by
        dsimp only [work₀]
        rw [Function.update_self]
        exact natTape_hasBinaryNat_internal selector
      have hreset := resetBinaryWorkTM_hoareTimeSpace_exact_internal
        (selectorTape spec) selector input.length wordBits
        (executionInput input) work₀ (natTape 0)
        hselector hselectorWidth (executionInput_parked input)
        hwork₀Parked (natTape_parked_internal 0)
        (by simp [executionInput, Tape.move]) hwork₀Head
      have hbaseSelector :
          executionWork spec input snapshot (selectorTape spec) =
            natTape 0 := by
        exact hasBinaryNat_eq_natTape
          (by
            change
              (executionWork spec input snapshot
                (scratchTape spec 11)).HasBinaryNat 0
            rw [executionWork_scratch_internal spec input snapshot
              11 (by decide)]
            exact natTape_hasBinaryNat_internal 0)
      have hresetFinal :
          (TM.resetBinaryWorkTM (selectorTape spec)).HoareTimeSpace
            (fun inp work out =>
              inp = executionInput input ∧ work = work₀ ∧
              out = natTape 0)
            (fun inp work out =>
              inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0)
            (TM.resetBinaryWorkTime 1 selector.bits.length)
            input.length (instructionSpace wordBits) := by
        apply hreset.consequence
        · exact fun _ _ _ h => h
        · rintro inp work out ⟨hinp, hwork, hout⟩
          refine ⟨hinp, ?_, hout⟩
          rw [hwork]
          simp [work₀, Function.update_idem, hbaseSelector]
        · exact le_rfl
        · exact le_rfl
        · exact le_rfl
      obtain ⟨haltTime, hhalt⟩ :=
        executeInstructionTM_hoareTimeSpace_internal spec input snapshot
          hcanonical hcovered .halt
          (by simp [InstrRegistersBelow])
          (by simp [InstrNoStore]) wordBits hcurrent
          (by simpa [selectedInstruction] using hnext)
          hpcWidth
          (by simpa [selectedInstruction] using hnextPCWidth)
      have hseq := seqTM_hoareTimeSpace_exact_internal
        (TM.resetBinaryWorkTM (selectorTape spec))
        (executeInstructionTM spec .halt)
        (executionInput input) work₀
        (executionWork spec input snapshot)
        (executionWork spec input snapshot) (natTape 0)
        (TM.resetBinaryWorkTime 1 selector.bits.length) haltTime
        input.length (instructionSpace wordBits)
        hresetFinal
        (by simpa [DenseOverlay.Snapshot.stepInstr] using hhalt)
        (executionInput_parked input)
        (executionWork_parked_internal spec input snapshot)
        (natTape_parked_internal 0)
      refine
        ⟨TM.resetBinaryWorkTime 1 selector.bits.length + 1 +
          haltTime, ?_⟩
      simpa [dispatchProgramTM, selectedInstruction,
        DenseOverlay.Snapshot.stepInstr, work₀] using hseq
  | cons instruction tail ih =>
      have hinstructionRegisters :
          InstrRegistersBelow spec.registerBound instruction := by
        simpa [selectedInstruction] using hregisters 0
      have hinstructionNoStore : InstrNoStore instruction := by
        simpa [selectedInstruction] using hnostore 0
      have htailRegisters :
          ∀ index,
            InstrRegistersBelow spec.registerBound
              (selectedInstruction tail index) := by
        intro index
        simpa [selectedInstruction] using hregisters (index + 1)
      have htailNoStore :
          ∀ index, InstrNoStore (selectedInstruction tail index) := by
        intro index
        simpa [selectedInstruction] using hnostore (index + 1)
      cases selector with
      | zero =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape 0)
          have hbaseSelector :
              executionWork spec input snapshot (selectorTape spec) =
                natTape 0 := by
            exact hasBinaryNat_eq_natTape
              (by
                change
                  (executionWork spec input snapshot
                    (scratchTape spec 11)).HasBinaryNat 0
                rw [executionWork_scratch_internal spec input snapshot
                  11 (by decide)]
                exact natTape_hasBinaryNat_internal 0)
          have hwork₀Eq :
              work₀ = executionWork spec input snapshot := by
            dsimp only [work₀]
            rw [← hbaseSelector, Function.update_eq_self]
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
            rw [hwork₀Eq]
            exact executionWork_parked_internal spec input snapshot
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat 0 := by
            rw [hwork₀Eq, hbaseSelector]
            exact natTape_hasBinaryNat_internal 0
          obtain ⟨instructionTime, hinstruction⟩ :=
            executeInstructionTM_hoareTimeSpace_internal spec input snapshot
              hcanonical hcovered instruction hinstructionRegisters
              hinstructionNoStore wordBits hcurrent
              (by simpa [selectedInstruction] using hnext)
              hpcWidth
              (by simpa [selectedInstruction] using hnextPCWidth)
          have hblank :
              (executeInstructionTM spec instruction).HoareTimeSpace
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) 0)) ∧
                  out = natTape 0)
                instructionTime input.length
                (instructionSpace wordBits) := by
            simpa [hwork₀Eq, selectedInstruction] using hinstruction
          have hnonblank :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchProgramTM spec tail)).HoareTimeSpace
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) 0)) ∧
                  out = natTape 0)
                0 input.length (instructionSpace wordBits) := by
            constructor
            · intro inp work out hfalse
              exact hfalse.elim
            · intro inp work out hfalse
              exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
            (selectorTape spec)
            (executeInstructionTM spec instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchProgramTM spec tail))
            hframe
            (fun _ _ _ hpre _ => hpre)
            (fun inp work out hpre hnonblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              exact hnonblankRead
                (hselector.read_eq_blank_iff.mpr rfl))
            hblank hnonblank
          refine
            ⟨TM.branchWorkBlankTime instructionTime 0, ?_⟩
          simpa [dispatchProgramTM, work₀] using hbranch
      | succ selector =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape (selector + 1))
          let work₁ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector)
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) (selector + 1)
              (executionWork_parked_internal spec input snapshot)
          have hwork₀Head : ∀ i, (work₀ i).head = 1 :=
            update_natTape_head_internal
              (executionWork spec input snapshot)
              (selectorTape spec) (selector + 1)
              (executionWork_head_internal spec input snapshot)
          have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) selector
              (executionWork_parked_internal spec input snapshot)
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat
                (selector + 1) := by
            dsimp only [work₀]
            rw [Function.update_self]
            exact natTape_hasBinaryNat_internal (selector + 1)
          have hselectorPredWidth : selector.size ≤ wordBits := by
            exact (Nat.size_le_size (by omega)).trans hselectorWidth
          have hpredRaw := binaryPredTM_hoareTimeSpace_exact_internal
            (selectorTape spec) selector input.length wordBits
            (executionInput input) work₀ (natTape 0)
            hselector hselectorWidth (executionInput_parked input)
            hwork₀Parked (natTape_parked_internal 0)
            (by simp [executionInput, Tape.move]) hwork₀Head
          have hpred :
              (TM.binaryPredTM (selectorTape spec)).HoareTimeSpace
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₁ ∧
                  out = natTape 0)
                (TM.binaryPredTime selector) input.length
                (instructionSpace wordBits) := by
            simpa [work₀, work₁, Function.update_idem] using hpredRaw
          obtain ⟨recursiveTime, hrecursive⟩ :=
            ih selector htailRegisters htailNoStore hselectorPredWidth
              (by simpa [selectedInstruction] using hnext)
              (by simpa [selectedInstruction] using hnextPCWidth)
          have hseqRaw := seqTM_hoareTimeSpace_exact_internal
            (TM.binaryPredTM (selectorTape spec))
            (dispatchProgramTM spec tail)
            (executionInput input) work₀ work₁
            (executionWork spec input
              (snapshot.stepInstr input
                (selectedInstruction tail selector)))
            (natTape 0) (TM.binaryPredTime selector) recursiveTime
            input.length (instructionSpace wordBits)
            hpred hrecursive (executionInput_parked input)
            hwork₁Parked (natTape_parked_internal 0)
          have hseq :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchProgramTM spec tail)).HoareTimeSpace
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) (selector + 1))) ∧
                  out = natTape 0)
                (TM.binaryPredTime selector + 1 +
                  recursiveTime) input.length
                (instructionSpace wordBits) := by
            simpa [selectedInstruction] using hseqRaw
          have hblank :
              (executeInstructionTM spec instruction).HoareTimeSpace
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work =
                    executionWork spec input
                      (snapshot.stepInstr input
                        (selectedInstruction
                          (instruction :: tail) (selector + 1))) ∧
                  out = natTape 0)
                0 input.length (instructionSpace wordBits) := by
            constructor
            · intro inp work out hfalse
              exact hfalse.elim
            · intro inp work out hfalse
              exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
            (selectorTape spec)
            (executeInstructionTM spec instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchProgramTM spec tail))
            hframe
            (fun inp work out hpre hblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              have hzero :=
                hselector.read_eq_blank_iff.mp hblankRead
              omega)
            (fun _ _ _ hpre _ => hpre)
            hblank hseq
          refine
            ⟨TM.branchWorkBlankTime 0
              (TM.binaryPredTime selector + 1 + recursiveTime), ?_⟩
          simpa [dispatchProgramTM, work₀] using hbranch

private theorem programStepTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed) :
    ∃ time,
      (programStepTM spec).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (DenseOverlay.Snapshot.step program input snapshot) ∧
          out = natTape 0)
        time := by
  let initialWork := executionWork spec input snapshot
  let dispatchWork :=
    Function.update initialWork (selectorTape spec)
      (natTape snapshot.pc)
  have hinput := executionInput_parked input
  have houtput := natTape_parked_internal 0
  have hinitialParked : ∀ i, TM.Parked (initialWork i) :=
    executionWork_parked_internal spec input snapshot
  have hpc :
      (initialWork (pcTape spec)).HasBinaryNat snapshot.pc := by
    change
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hselector :
      (initialWork (selectorTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 11)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 11 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopyScratch :
      (initialWork (copyScratchTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 9)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 9 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopy := binaryCopyIntoTM_hoareTime_exact_internal
    (pcTape spec) (selectorTape spec) (copyScratchTape spec)
    (scratchTape_ne_internal spec (first := 10) (second := 11)
      (by decide))
    (scratchTape_ne_internal spec (first := 10) (second := 9)
      (by decide))
    (scratchTape_ne_internal spec (first := 11) (second := 9)
      (by decide))
    snapshot.pc 0 (executionInput input) initialWork (natTape 0)
    hpc hselector hcopyScratch hinput hinitialParked houtput
  have hcopyExact :
      (TM.binaryCopyIntoTM
        (pcTape spec) (selectorTape spec)
        (copyScratchTape spec)).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧ work = initialWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (TM.binaryCopyTime snapshot.pc 0) := by
    simpa only [dispatchWork] using hcopy
  have hregisters :
      ∀ index,
        InstrRegistersBelow spec.registerBound
          (selectedInstruction program index) := by
    intro index
    rw [selectedInstruction_eq_getD_internal]
    exact spec.registersBelow index
  have hnostore :
      ∀ index, InstrNoStore (selectedInstruction program index) := by
    intro index
    rw [selectedInstruction_eq_getD_internal]
    exact spec.noStore index
  obtain ⟨dispatchTime, hdispatch⟩ :=
    dispatchProgramTM_hoareTime_internal spec input snapshot
      hcanonical hcovered program snapshot.pc hregisters hnostore
  have hdispatchFinal :
      (dispatchProgramTM spec program).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (DenseOverlay.Snapshot.step program input snapshot) ∧
          out = natTape 0)
        dispatchTime := by
    simpa [dispatchWork, DenseOverlay.Snapshot.step,
      DenseOverlay.Snapshot.curInstr,
      selectedInstruction_eq_getD_internal] using hdispatch
  have hseq := seqTM_hoareTime_exact_internal
    (TM.binaryCopyIntoTM
      (pcTape spec) (selectorTape spec) (copyScratchTape spec))
    (dispatchProgramTM spec program)
    (executionInput input) initialWork dispatchWork
    (executionWork spec input
      (DenseOverlay.Snapshot.step program input snapshot))
    (natTape 0) (TM.binaryCopyTime snapshot.pc 0) dispatchTime
    hcopyExact hdispatchFinal hinput
    (update_natTape_parked_internal initialWork
      (selectorTape spec) snapshot.pc hinitialParked)
    houtput
  refine
    ⟨TM.binaryCopyTime snapshot.pc 0 + 1 + dispatchTime, ?_⟩
  simpa only [programStepTM, initialWork] using hseq

private theorem programStepTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (wordBits : ℕ)
    (hcurrent : SnapshotBound spec input snapshot wordBits)
    (hnext :
      SnapshotBound spec input
        (DenseOverlay.Snapshot.step program input snapshot) wordBits)
    (hpcWidth : snapshot.pc.size ≤ wordBits)
    (hnextPCWidth :
      (DenseOverlay.Snapshot.step program input snapshot).pc.size ≤
        wordBits) :
    ∃ time,
      (programStepTM spec).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (DenseOverlay.Snapshot.step program input snapshot) ∧
          out = natTape 0)
        time input.length (instructionSpace wordBits) := by
  let initialWork := executionWork spec input snapshot
  let dispatchWork :=
    Function.update initialWork (selectorTape spec)
      (natTape snapshot.pc)
  have hinput := executionInput_parked input
  have houtput := natTape_parked_internal 0
  have hinitialParked : ∀ i, TM.Parked (initialWork i) :=
    executionWork_parked_internal spec input snapshot
  have hinitialHead : ∀ i, (initialWork i).head = 1 :=
    executionWork_head_internal spec input snapshot
  have hpc :
      (initialWork (pcTape spec)).HasBinaryNat snapshot.pc := by
    change
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hselector :
      (initialWork (selectorTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 11)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 11 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopyScratch :
      (initialWork (copyScratchTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 9)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 9 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopy := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (pcTape spec) (selectorTape spec) (copyScratchTape spec)
    (scratchTape_ne_internal spec (first := 10) (second := 11)
      (by decide))
    (scratchTape_ne_internal spec (first := 10) (second := 9)
      (by decide))
    (scratchTape_ne_internal spec (first := 11) (second := 9)
      (by decide))
    snapshot.pc 0 input.length wordBits
    (executionInput input) initialWork (natTape 0)
    hpc hselector hcopyScratch hpcWidth (by simp)
    hinput hinitialParked houtput
    (by simp [executionInput, Tape.move]) hinitialHead
  have hcopyExact :
      (TM.binaryCopyIntoTM
        (pcTape spec) (selectorTape spec)
        (copyScratchTape spec)).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧ work = initialWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (TM.binaryCopyTime snapshot.pc 0)
        input.length (instructionSpace wordBits) := by
    simpa only [dispatchWork] using hcopy
  have hregisters :
      ∀ index,
        InstrRegistersBelow spec.registerBound
          (selectedInstruction program index) := by
    intro index
    rw [selectedInstruction_eq_getD_internal]
    exact spec.registersBelow index
  have hnostore :
      ∀ index, InstrNoStore (selectedInstruction program index) := by
    intro index
    rw [selectedInstruction_eq_getD_internal]
    exact spec.noStore index
  obtain ⟨dispatchTime, hdispatch⟩ :=
    dispatchProgramTM_hoareTimeSpace_internal spec input snapshot
      hcanonical hcovered program snapshot.pc wordBits
      hregisters hnostore hpcWidth hcurrent
      (by
        simpa [DenseOverlay.Snapshot.step,
          DenseOverlay.Snapshot.curInstr,
          selectedInstruction_eq_getD_internal] using hnext)
      hpcWidth
      (by
        simpa [DenseOverlay.Snapshot.step,
          DenseOverlay.Snapshot.curInstr,
          selectedInstruction_eq_getD_internal] using hnextPCWidth)
  have hdispatchFinal :
      (dispatchProgramTM spec program).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            executionWork spec input
              (DenseOverlay.Snapshot.step program input snapshot) ∧
          out = natTape 0)
        dispatchTime input.length (instructionSpace wordBits) := by
    simpa [dispatchWork, DenseOverlay.Snapshot.step,
      DenseOverlay.Snapshot.curInstr,
      selectedInstruction_eq_getD_internal] using hdispatch
  have hdispatchWorkParked : ∀ i, TM.Parked (dispatchWork i) :=
    update_natTape_parked_internal initialWork
      (selectorTape spec) snapshot.pc hinitialParked
  have hseq := seqTM_hoareTimeSpace_exact_internal
    (TM.binaryCopyIntoTM
      (pcTape spec) (selectorTape spec) (copyScratchTape spec))
    (dispatchProgramTM spec program)
    (executionInput input) initialWork dispatchWork
    (executionWork spec input
      (DenseOverlay.Snapshot.step program input snapshot))
    (natTape 0) (TM.binaryCopyTime snapshot.pc 0) dispatchTime
    input.length (instructionSpace wordBits)
    hcopyExact hdispatchFinal hinput hdispatchWorkParked houtput
  refine
    ⟨TM.binaryCopyTime snapshot.pc 0 + 1 + dispatchTime, ?_⟩
  simpa only [programStepTM, initialWork] using hseq

private theorem instructionHaltVerdictTM_hoareTime_internal
    {n : ℕ} (instruction : Instr)
    (inp₀ : Tape) (work₀ : Fin n → Tape)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i)) :
    (instructionHaltVerdictTM instruction).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = natTape 0)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = natTape (if instruction = .halt then 1 else 0))
      1 := by
  intro inp work out hpre
  obtain ⟨rfl, rfl, rfl⟩ := hpre
  have hinp := hinput.move_idle
  have hworkEq :
      (fun i => (work i).writeAndMove
        (TM.readBackWrite (work i).read)
        (TM.idleDir (work i).read)) = work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have hout :
      (natTape 0).writeAndMove
          (if instruction = .halt then Γw.one else Γw.blank).toΓ
          (TM.idleDir (natTape 0).read) =
        natTape (if instruction = .halt then 1 else 0) := by
    by_cases hhalt : instruction = .halt
    · subst instruction
      simp only [ite_true]
      have hread : (natTape 0).read = Γ.blank := by
        simp [natTape, Tape.read, Tape.move, Tape.init]
      rw [hread]
      simp only [TM.idleDir, reduceCtorEq, ↓reduceIte]
      apply Tape.ext
      · simp [natTape, Tape.writeAndMove, Tape.write,
          Tape.move, Tape.init]
      · funext j
        by_cases hj0 : j = 0
        · subst j
          simp [natTape, Tape.writeAndMove, Tape.write,
            Tape.move, Tape.init]
        · by_cases hj1 : j = 1
          · subst j
            simp [natTape, Tape.writeAndMove, Tape.write,
              Tape.move, Tape.init, Γ.ofBool]
          · have hnone : [Γ.one][j - 1]? = none := by
              apply List.getElem?_eq_none
              simp
              omega
            simp [natTape, Tape.writeAndMove, Tape.write,
              Tape.move, Tape.init, hj0, hj1, hnone, Γ.ofBool]
    · rw [if_neg hhalt, if_neg hhalt]
      have hread : (natTape 0).read = Γ.blank := by
        simp [natTape, Tape.read, Tape.move, Tape.init]
      simpa [hread] using
        (natTape_parked_internal 0).writeAndMove_readBack_idle
  let final : Complexity.Cfg n
      (instructionHaltVerdictTM (n := n) instruction).Q :=
    { state := .done
      input := inp
      work := work
      output := natTape (if instruction = .halt then 1 else 0) }
  have hstep :
      (instructionHaltVerdictTM instruction).step
        { state := (instructionHaltVerdictTM instruction).qstart
          input := inp
          work := work
          output := natTape 0 } = some final := by
    simp only [TM.step, instructionHaltVerdictTM, reduceCtorEq,
      ↓reduceIte, final]
    rw [hinp, hworkEq, hout]
  exact
    ⟨final, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

private theorem instructionHaltVerdictTM_hoareTimeSpace_internal
    {n : ℕ} (instruction : Instr)
    (inp₀ : Tape) (work₀ : Fin n → Tape)
    (inputLength wordBits : ℕ)
    (hinput : TM.Parked inp₀)
    (hwork : ∀ i, TM.Parked (work₀ i))
    (hinputHead : inp₀.head = 1)
    (hworkHead : ∀ i, (work₀ i).head = 1) :
    (instructionHaltVerdictTM instruction).HoareTimeSpace
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = natTape 0)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out = natTape (if instruction = .halt then 1 else 0))
      1 inputLength (instructionSpace wordBits) := by
  have htime := instructionHaltVerdictTM_hoareTime_internal
    instruction inp₀ work₀ hinput hwork
  have hspace := htime.toHoareTimeSpace
    (inputLength := inputLength) (initialSpace := 1)
    (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      subst inp
      subst work
      subst out
      exact exactStart_withinAuxSpace_one_internal
        (instructionHaltVerdictTM instruction)
        inp₀ work₀ (natTape 0) hinputHead hworkHead)
  apply hspace.consequence
  · exact fun _ _ _ h => h
  · exact fun _ _ _ h => h
  · exact le_rfl
  · exact le_rfl
  · unfold instructionSpace
    omega

private theorem dispatchHaltTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (remaining : Program) (selector : ℕ) :
    ∃ time,
      (dispatchHaltTM spec remaining).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector) ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out =
            natTape
              (if selectedInstruction remaining selector = .halt then
                1
              else 0))
        time := by
  induction remaining generalizing selector with
  | nil =>
      let work₀ :=
        Function.update (executionWork spec input snapshot)
          (selectorTape spec) (natTape selector)
      have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
        update_natTape_parked_internal
          (executionWork spec input snapshot)
          (selectorTape spec) selector
          (executionWork_parked_internal spec input snapshot)
      have hselector :
          (work₀ (selectorTape spec)).HasBinaryNat selector := by
        dsimp only [work₀]
        rw [Function.update_self]
        exact natTape_hasBinaryNat_internal selector
      have hreset := resetBinaryWorkTM_hoareTime_exact_internal
        (selectorTape spec) selector
        (executionInput input) work₀ (natTape 0)
        hselector (executionInput_parked input) hwork₀Parked
        (natTape_parked_internal 0)
      have hbaseSelector :
          executionWork spec input snapshot (selectorTape spec) =
            natTape 0 := by
        exact hasBinaryNat_eq_natTape
          (by
            change
              (executionWork spec input snapshot
                (scratchTape spec 11)).HasBinaryNat 0
            rw [executionWork_scratch_internal spec input snapshot
              11 (by decide)]
            exact natTape_hasBinaryNat_internal 0)
      have hresetFinal :
          (TM.resetBinaryWorkTM (selectorTape spec)).HoareTime
            (fun inp work out =>
              inp = executionInput input ∧ work = work₀ ∧
              out = natTape 0)
            (fun inp work out =>
              inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0)
            (TM.resetBinaryWorkTime 1 selector.bits.length) := by
        apply hreset.consequence
        · exact fun _ _ _ h => h
        · rintro inp work out ⟨hinp, hwork, hout⟩
          refine ⟨hinp, ?_, hout⟩
          rw [hwork]
          simp [work₀, Function.update_idem, hbaseSelector]
        · exact le_rfl
      have hhalt := instructionHaltVerdictTM_hoareTime_internal
        (n := workTapeCount spec) .halt
        (executionInput input) (executionWork spec input snapshot)
        (executionInput_parked input)
        (executionWork_parked_internal spec input snapshot)
      have htransition :
          ∀ inp work out,
            (inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0) →
            (TM.transitionInput inp = executionInput input ∧
              (fun i => TM.transitionTape (work i)) =
                executionWork spec input snapshot ∧
              TM.transitionTape out = natTape 0) := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
          (executionInput_parked input).read_ne_start
          (fun i =>
            (executionWork_parked_internal spec input snapshot i).read_ne_start)
          (natTape_parked_internal 0).read_ne_start
        exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
      have hseq := TM.seqTM_hoareTime
        (TM.resetBinaryWorkTM (selectorTape spec))
        (instructionHaltVerdictTM .halt)
        hresetFinal htransition hhalt
      refine
        ⟨TM.resetBinaryWorkTime 1 selector.bits.length + 1 + 1, ?_⟩
      simpa [dispatchHaltTM, selectedInstruction, work₀] using hseq
  | cons instruction tail ih =>
      cases selector with
      | zero =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape 0)
          have hbaseSelector :
              executionWork spec input snapshot (selectorTape spec) =
                natTape 0 := by
            exact hasBinaryNat_eq_natTape
              (by
                change
                  (executionWork spec input snapshot
                    (scratchTape spec 11)).HasBinaryNat 0
                rw [executionWork_scratch_internal spec input snapshot
                  11 (by decide)]
                exact natTape_hasBinaryNat_internal 0)
          have hwork₀Eq :
              work₀ = executionWork spec input snapshot := by
            dsimp only [work₀]
            rw [← hbaseSelector, Function.update_eq_self]
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
            rw [hwork₀Eq]
            exact executionWork_parked_internal spec input snapshot
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat 0 := by
            rw [hwork₀Eq, hbaseSelector]
            exact natTape_hasBinaryNat_internal 0
          have hblankRaw := instructionHaltVerdictTM_hoareTime_internal
            (n := workTapeCount spec) instruction
            (executionInput input) (executionWork spec input snapshot)
            (executionInput_parked input)
            (executionWork_parked_internal spec input snapshot)
          have hblank :
              (instructionHaltVerdictTM instruction).HoareTime
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) 0 = .halt then
                        1
                      else 0))
                1 := by
            simpa [hwork₀Eq, selectedInstruction] using hblankRaw
          have hnonblank :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchHaltTM spec tail)).HoareTime
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) 0 = .halt then
                        1
                      else 0))
                0 := by
            intro inp work out hfalse
            exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTime
            (selectorTape spec)
            (instructionHaltVerdictTM instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchHaltTM spec tail))
            hframe
            (fun _ _ _ hpre _ => hpre)
            (fun inp work out hpre hnonblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              exact hnonblankRead
                (hselector.read_eq_blank_iff.mpr rfl))
            hblank hnonblank
          refine ⟨TM.branchWorkBlankTime 1 0, ?_⟩
          have hbranchFinal := hbranch.consequence
            (fun _ _ _ h => h)
            (fun _ _ _ h => h.elim (fun hp => hp) (fun hp => hp))
            le_rfl
          simpa [dispatchHaltTM, work₀] using hbranchFinal
      | succ selector =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape (selector + 1))
          let work₁ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector)
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) (selector + 1)
              (executionWork_parked_internal spec input snapshot)
          have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) selector
              (executionWork_parked_internal spec input snapshot)
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat
                (selector + 1) := by
            dsimp only [work₀]
            rw [Function.update_self]
            exact natTape_hasBinaryNat_internal (selector + 1)
          have hpredRaw := binaryPredTM_hoareTime_exact_internal
            (selectorTape spec) selector
            (executionInput input) work₀ (natTape 0)
            hselector (executionInput_parked input) hwork₀Parked
            (natTape_parked_internal 0)
          have hpred :
              (TM.binaryPredTM (selectorTape spec)).HoareTime
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₁ ∧
                  out = natTape 0)
                (TM.binaryPredTime selector) := by
            simpa [work₀, work₁, Function.update_idem] using hpredRaw
          obtain ⟨recursiveTime, hrecursive⟩ := ih selector
          have htransition :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₁ ∧
                  out = natTape 0) →
                (TM.transitionInput inp = executionInput input ∧
                  (fun i => TM.transitionTape (work i)) = work₁ ∧
                  TM.transitionTape out = natTape 0) := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
              (executionInput_parked input).read_ne_start
              (fun i => (hwork₁Parked i).read_ne_start)
              (natTape_parked_internal 0).read_ne_start
            exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
          have hseqRaw := TM.seqTM_hoareTime
            (TM.binaryPredTM (selectorTape spec))
            (dispatchHaltTM spec tail)
            hpred htransition hrecursive
          have hseq :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchHaltTM spec tail)).HoareTime
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) (selector + 1) = .halt then
                        1
                      else 0))
                (TM.binaryPredTime selector + 1 +
                  recursiveTime) := by
            simpa [selectedInstruction] using hseqRaw
          have hblank :
              (instructionHaltVerdictTM instruction).HoareTime
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) (selector + 1) = .halt then
                        1
                      else 0))
                0 := by
            intro inp work out hfalse
            exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTime
            (selectorTape spec)
            (instructionHaltVerdictTM instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchHaltTM spec tail))
            hframe
            (fun inp work out hpre hblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              have hzero :=
                hselector.read_eq_blank_iff.mp hblankRead
              omega)
            (fun _ _ _ hpre _ => hpre)
            hblank hseq
          refine
            ⟨TM.branchWorkBlankTime 0
              (TM.binaryPredTime selector + 1 + recursiveTime), ?_⟩
          have hbranchFinal := hbranch.consequence
            (fun _ _ _ h => h)
            (fun _ _ _ h => h.elim (fun hp => hp) (fun hp => hp))
            le_rfl
          simpa [dispatchHaltTM, work₀] using hbranchFinal

private theorem dispatchHaltTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (remaining : Program) (selector wordBits : ℕ)
    (hselectorWidth : selector.size ≤ wordBits) :
    ∃ time,
      (dispatchHaltTM spec remaining).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work =
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector) ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out =
            natTape
              (if selectedInstruction remaining selector = .halt then
                1
              else 0))
        time input.length (instructionSpace wordBits) := by
  induction remaining generalizing selector with
  | nil =>
      let work₀ :=
        Function.update (executionWork spec input snapshot)
          (selectorTape spec) (natTape selector)
      have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
        update_natTape_parked_internal
          (executionWork spec input snapshot)
          (selectorTape spec) selector
          (executionWork_parked_internal spec input snapshot)
      have hwork₀Head : ∀ i, (work₀ i).head = 1 :=
        update_natTape_head_internal
          (executionWork spec input snapshot)
          (selectorTape spec) selector
          (executionWork_head_internal spec input snapshot)
      have hselector :
          (work₀ (selectorTape spec)).HasBinaryNat selector := by
        dsimp only [work₀]
        rw [Function.update_self]
        exact natTape_hasBinaryNat_internal selector
      have hreset := resetBinaryWorkTM_hoareTimeSpace_exact_internal
        (selectorTape spec) selector input.length wordBits
        (executionInput input) work₀ (natTape 0)
        hselector hselectorWidth (executionInput_parked input)
        hwork₀Parked (natTape_parked_internal 0)
        (by simp [executionInput, Tape.move]) hwork₀Head
      have hbaseSelector :
          executionWork spec input snapshot (selectorTape spec) =
            natTape 0 := by
        exact hasBinaryNat_eq_natTape
          (by
            change
              (executionWork spec input snapshot
                (scratchTape spec 11)).HasBinaryNat 0
            rw [executionWork_scratch_internal spec input snapshot
              11 (by decide)]
            exact natTape_hasBinaryNat_internal 0)
      have hresetFinal :
          (TM.resetBinaryWorkTM (selectorTape spec)).HoareTimeSpace
            (fun inp work out =>
              inp = executionInput input ∧ work = work₀ ∧
              out = natTape 0)
            (fun inp work out =>
              inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0)
            (TM.resetBinaryWorkTime 1 selector.bits.length)
            input.length (instructionSpace wordBits) := by
        apply hreset.consequence
        · exact fun _ _ _ h => h
        · rintro inp work out ⟨hinp, hwork, hout⟩
          refine ⟨hinp, ?_, hout⟩
          rw [hwork]
          simp [work₀, Function.update_idem, hbaseSelector]
        · exact le_rfl
        · exact le_rfl
        · exact le_rfl
      have hhalt :=
        instructionHaltVerdictTM_hoareTimeSpace_internal
          (n := workTapeCount spec) .halt
          (executionInput input) (executionWork spec input snapshot)
          input.length wordBits
          (executionInput_parked input)
          (executionWork_parked_internal spec input snapshot)
          (by simp [executionInput, Tape.move])
          (executionWork_head_internal spec input snapshot)
      have htransition :
          ∀ inp work out,
            (inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 0) →
            (TM.transitionInput inp = executionInput input ∧
              (fun i => TM.transitionTape (work i)) =
                executionWork spec input snapshot ∧
              TM.transitionTape out = natTape 0) := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
          (executionInput_parked input).read_ne_start
          (fun i =>
            (executionWork_parked_internal spec input snapshot i).read_ne_start)
          (natTape_parked_internal 0).read_ne_start
        exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
      have hseqRaw := TM.seqTM_hoareTimeSpace
        (TM.resetBinaryWorkTM (selectorTape spec))
        (instructionHaltVerdictTM .halt)
        hresetFinal htransition hhalt
      have hseq :
          (TM.seqTM (TM.resetBinaryWorkTM (selectorTape spec))
            (instructionHaltVerdictTM .halt)).HoareTimeSpace
            (fun inp work out =>
              inp = executionInput input ∧ work = work₀ ∧
              out = natTape 0)
            (fun inp work out =>
              inp = executionInput input ∧
              work = executionWork spec input snapshot ∧
              out = natTape 1)
            (TM.resetBinaryWorkTime 1 selector.bits.length + 1 + 1)
            input.length (instructionSpace wordBits) := by
        simpa using hseqRaw
      refine
        ⟨TM.resetBinaryWorkTime 1 selector.bits.length + 1 + 1, ?_⟩
      simpa [dispatchHaltTM, selectedInstruction, work₀] using hseq
  | cons instruction tail ih =>
      cases selector with
      | zero =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape 0)
          have hbaseSelector :
              executionWork spec input snapshot (selectorTape spec) =
                natTape 0 := by
            exact hasBinaryNat_eq_natTape
              (by
                change
                  (executionWork spec input snapshot
                    (scratchTape spec 11)).HasBinaryNat 0
                rw [executionWork_scratch_internal spec input snapshot
                  11 (by decide)]
                exact natTape_hasBinaryNat_internal 0)
          have hwork₀Eq :
              work₀ = executionWork spec input snapshot := by
            dsimp only [work₀]
            rw [← hbaseSelector, Function.update_eq_self]
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
            rw [hwork₀Eq]
            exact executionWork_parked_internal spec input snapshot
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat 0 := by
            rw [hwork₀Eq, hbaseSelector]
            exact natTape_hasBinaryNat_internal 0
          have hblankRaw :=
            instructionHaltVerdictTM_hoareTimeSpace_internal
              (n := workTapeCount spec) instruction
              (executionInput input)
              (executionWork spec input snapshot)
              input.length wordBits
              (executionInput_parked input)
              (executionWork_parked_internal spec input snapshot)
              (by simp [executionInput, Tape.move])
              (executionWork_head_internal spec input snapshot)
          have hblank :
              (instructionHaltVerdictTM instruction).HoareTimeSpace
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) 0 = .halt then
                        1
                      else 0))
                1 input.length (instructionSpace wordBits) := by
            simpa [hwork₀Eq, selectedInstruction] using hblankRaw
          have hnonblank :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchHaltTM spec tail)).HoareTimeSpace
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) 0 = .halt then
                        1
                      else 0))
                0 input.length (instructionSpace wordBits) := by
            constructor
            · intro inp work out hfalse
              exact hfalse.elim
            · intro inp work out hfalse
              exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
            (selectorTape spec)
            (instructionHaltVerdictTM instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchHaltTM spec tail))
            hframe
            (fun _ _ _ hpre _ => hpre)
            (fun inp work out hpre hnonblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              exact hnonblankRead
                (hselector.read_eq_blank_iff.mpr rfl))
            hblank hnonblank
          refine ⟨TM.branchWorkBlankTime 1 0, ?_⟩
          simpa [dispatchHaltTM, work₀] using hbranch
      | succ selector =>
          let work₀ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape (selector + 1))
          let work₁ :=
            Function.update (executionWork spec input snapshot)
              (selectorTape spec) (natTape selector)
          have hwork₀Parked : ∀ i, TM.Parked (work₀ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) (selector + 1)
              (executionWork_parked_internal spec input snapshot)
          have hwork₀Head : ∀ i, (work₀ i).head = 1 :=
            update_natTape_head_internal
              (executionWork spec input snapshot)
              (selectorTape spec) (selector + 1)
              (executionWork_head_internal spec input snapshot)
          have hwork₁Parked : ∀ i, TM.Parked (work₁ i) :=
            update_natTape_parked_internal
              (executionWork spec input snapshot)
              (selectorTape spec) selector
              (executionWork_parked_internal spec input snapshot)
          have hselector :
              (work₀ (selectorTape spec)).HasBinaryNat
                (selector + 1) := by
            dsimp only [work₀]
            rw [Function.update_self]
            exact natTape_hasBinaryNat_internal (selector + 1)
          have hselectorPredWidth : selector.size ≤ wordBits :=
            (Nat.size_le_size (by omega)).trans hselectorWidth
          have hpredRaw := binaryPredTM_hoareTimeSpace_exact_internal
            (selectorTape spec) selector input.length wordBits
            (executionInput input) work₀ (natTape 0)
            hselector hselectorWidth (executionInput_parked input)
            hwork₀Parked (natTape_parked_internal 0)
            (by simp [executionInput, Tape.move]) hwork₀Head
          have hpred :
              (TM.binaryPredTM (selectorTape spec)).HoareTimeSpace
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₁ ∧
                  out = natTape 0)
                (TM.binaryPredTime selector) input.length
                (instructionSpace wordBits) := by
            simpa [work₀, work₁, Function.update_idem] using hpredRaw
          obtain ⟨recursiveTime, hrecursive⟩ :=
            ih selector hselectorPredWidth
          have htransition :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₁ ∧
                  out = natTape 0) →
                (TM.transitionInput inp = executionInput input ∧
                  (fun i => TM.transitionTape (work i)) = work₁ ∧
                  TM.transitionTape out = natTape 0) := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
              (executionInput_parked input).read_ne_start
              (fun i => (hwork₁Parked i).read_ne_start)
              (natTape_parked_internal 0).read_ne_start
            exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
          have hseqRaw := TM.seqTM_hoareTimeSpace
            (TM.binaryPredTM (selectorTape spec))
            (dispatchHaltTM spec tail)
            hpred htransition hrecursive
          have hseq :
              (TM.seqTM (TM.binaryPredTM (selectorTape spec))
                (dispatchHaltTM spec tail)).HoareTimeSpace
                (fun inp work out =>
                  inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) (selector + 1) = .halt then
                        1
                      else 0))
                (TM.binaryPredTime selector + 1 +
                  recursiveTime) input.length
                (instructionSpace wordBits) := by
            simpa [selectedInstruction] using hseqRaw
          have hblank :
              (instructionHaltVerdictTM instruction).HoareTimeSpace
                (fun _ _ _ => False)
                (fun inp work out =>
                  inp = executionInput input ∧
                  work = executionWork spec input snapshot ∧
                  out =
                    natTape
                      (if selectedInstruction
                          (instruction :: tail) (selector + 1) = .halt then
                        1
                      else 0))
                0 input.length (instructionSpace wordBits) := by
            constructor
            · intro inp work out hfalse
              exact hfalse.elim
            · intro inp work out hfalse
              exact hfalse.elim
          have hframe :
              ∀ inp work out,
                (inp = executionInput input ∧ work = work₀ ∧
                  out = natTape 0) →
                inp.read ≠ Γ.start ∧
                  (∀ i, (work i).read ≠ Γ.start) ∧
                  out.read ≠ Γ.start := by
            rintro inp work out ⟨rfl, rfl, rfl⟩
            exact
              ⟨(executionInput_parked input).read_ne_start,
                fun i => (hwork₀Parked i).read_ne_start,
                (natTape_parked_internal 0).read_ne_start⟩
          have hbranch := TM.branchWorkBlankTM_hoareTimeSpace
            (selectorTape spec)
            (instructionHaltVerdictTM instruction)
            (TM.seqTM (TM.binaryPredTM (selectorTape spec))
              (dispatchHaltTM spec tail))
            hframe
            (fun inp work out hpre hblankRead => by
              rcases hpre with ⟨rfl, rfl, rfl⟩
              have hzero :=
                hselector.read_eq_blank_iff.mp hblankRead
              omega)
            (fun _ _ _ hpre _ => hpre)
            hblank hseq
          refine
            ⟨TM.branchWorkBlankTime 0
              (TM.binaryPredTime selector + 1 + recursiveTime), ?_⟩
          simpa [dispatchHaltTM, work₀] using hbranch

private theorem programHaltTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot) :
    ∃ time,
      (programHaltTM spec).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape (if snapshot.Halted program then 1 else 0))
        time := by
  let initialWork := executionWork spec input snapshot
  let dispatchWork :=
    Function.update initialWork (selectorTape spec)
      (natTape snapshot.pc)
  have hinput := executionInput_parked input
  have houtput := natTape_parked_internal 0
  have hinitialParked : ∀ i, TM.Parked (initialWork i) :=
    executionWork_parked_internal spec input snapshot
  have hpc :
      (initialWork (pcTape spec)).HasBinaryNat snapshot.pc := by
    change
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hselector :
      (initialWork (selectorTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 11)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 11 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopyScratch :
      (initialWork (copyScratchTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 9)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 9 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopy := binaryCopyIntoTM_hoareTime_exact_internal
    (pcTape spec) (selectorTape spec) (copyScratchTape spec)
    (scratchTape_ne_internal spec (first := 10) (second := 11)
      (by decide))
    (scratchTape_ne_internal spec (first := 10) (second := 9)
      (by decide))
    (scratchTape_ne_internal spec (first := 11) (second := 9)
      (by decide))
    snapshot.pc 0 (executionInput input) initialWork (natTape 0)
    hpc hselector hcopyScratch hinput hinitialParked houtput
  have hcopyExact :
      (TM.binaryCopyIntoTM
        (pcTape spec) (selectorTape spec)
        (copyScratchTape spec)).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧ work = initialWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (TM.binaryCopyTime snapshot.pc 0) := by
    simpa only [dispatchWork] using hcopy
  obtain ⟨dispatchTime, hdispatch⟩ :=
    dispatchHaltTM_hoareTime_internal spec input snapshot
      program snapshot.pc
  have hdispatchFinal :
      (dispatchHaltTM spec program).HoareTime
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape (if snapshot.Halted program then 1 else 0))
        dispatchTime := by
    simpa [dispatchWork, DenseOverlay.Snapshot.Halted,
      DenseOverlay.Snapshot.curInstr,
      selectedInstruction_eq_getD_internal] using hdispatch
  have hdispatchWorkParked : ∀ i, TM.Parked (dispatchWork i) :=
    update_natTape_parked_internal initialWork
      (selectorTape spec) snapshot.pc hinitialParked
  have htransition :
      ∀ inp work out,
        (inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0) →
        (TM.transitionInput inp = executionInput input ∧
          (fun i => TM.transitionTape (work i)) = dispatchWork ∧
          TM.transitionTape out = natTape 0) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start
      (fun i => (hdispatchWorkParked i).read_ne_start)
      houtput.read_ne_start
    exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
  have hseq := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM
      (pcTape spec) (selectorTape spec) (copyScratchTape spec))
    (dispatchHaltTM spec program)
    hcopyExact htransition hdispatchFinal
  refine
    ⟨TM.binaryCopyTime snapshot.pc 0 + 1 + dispatchTime, ?_⟩
  simpa only [programHaltTM, initialWork] using hseq

private theorem programHaltTM_hoareTimeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (wordBits : ℕ) (hpcWidth : snapshot.pc.size ≤ wordBits) :
    ∃ time,
      (programHaltTM spec).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape (if snapshot.Halted program then 1 else 0))
        time input.length (instructionSpace wordBits) := by
  let initialWork := executionWork spec input snapshot
  let dispatchWork :=
    Function.update initialWork (selectorTape spec)
      (natTape snapshot.pc)
  have hinput := executionInput_parked input
  have houtput := natTape_parked_internal 0
  have hinitialParked : ∀ i, TM.Parked (initialWork i) :=
    executionWork_parked_internal spec input snapshot
  have hinitialHead : ∀ i, (initialWork i).head = 1 :=
    executionWork_head_internal spec input snapshot
  have hpc :
      (initialWork (pcTape spec)).HasBinaryNat snapshot.pc := by
    change
      (executionWork spec input snapshot
        (pcTape spec)).HasBinaryNat snapshot.pc
    rw [executionWork_pc_internal]
    exact natTape_hasBinaryNat_internal snapshot.pc
  have hselector :
      (initialWork (selectorTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 11)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 11 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopyScratch :
      (initialWork (copyScratchTape spec)).HasBinaryNat 0 := by
    change
      (executionWork spec input snapshot
        (scratchTape spec 9)).HasBinaryNat 0
    rw [executionWork_scratch_internal spec input snapshot 9 (by decide)]
    exact natTape_hasBinaryNat_internal 0
  have hcopy := binaryCopyIntoTM_hoareTimeSpace_exact_internal
    (pcTape spec) (selectorTape spec) (copyScratchTape spec)
    (scratchTape_ne_internal spec (first := 10) (second := 11)
      (by decide))
    (scratchTape_ne_internal spec (first := 10) (second := 9)
      (by decide))
    (scratchTape_ne_internal spec (first := 11) (second := 9)
      (by decide))
    snapshot.pc 0 input.length wordBits
    (executionInput input) initialWork (natTape 0)
    hpc hselector hcopyScratch hpcWidth (by simp)
    hinput hinitialParked houtput
    (by simp [executionInput, Tape.move]) hinitialHead
  have hcopyExact :
      (TM.binaryCopyIntoTM
        (pcTape spec) (selectorTape spec)
        (copyScratchTape spec)).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧ work = initialWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (TM.binaryCopyTime snapshot.pc 0)
        input.length (instructionSpace wordBits) := by
    simpa only [dispatchWork] using hcopy
  obtain ⟨dispatchTime, hdispatch⟩ :=
    dispatchHaltTM_hoareTimeSpace_internal spec input snapshot
      program snapshot.pc wordBits hpcWidth
  have hdispatchFinal :
      (dispatchHaltTM spec program).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape (if snapshot.Halted program then 1 else 0))
        dispatchTime input.length (instructionSpace wordBits) := by
    simpa [dispatchWork, DenseOverlay.Snapshot.Halted,
      DenseOverlay.Snapshot.curInstr,
      selectedInstruction_eq_getD_internal] using hdispatch
  have hdispatchWorkParked : ∀ i, TM.Parked (dispatchWork i) :=
    update_natTape_parked_internal initialWork
      (selectorTape spec) snapshot.pc hinitialParked
  have htransition :
      ∀ inp work out,
        (inp = executionInput input ∧ work = dispatchWork ∧
          out = natTape 0) →
        (TM.transitionInput inp = executionInput input ∧
          (fun i => TM.transitionTape (work i)) = dispatchWork ∧
          TM.transitionTape out = natTape 0) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htrans := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start
      (fun i => (hdispatchWorkParked i).read_ne_start)
      houtput.read_ne_start
    exact ⟨htrans.1, htrans.2.1, htrans.2.2⟩
  have hseqRaw := TM.seqTM_hoareTimeSpace
    (TM.binaryCopyIntoTM
      (pcTape spec) (selectorTape spec) (copyScratchTape spec))
    (dispatchHaltTM spec program)
    hcopyExact htransition hdispatchFinal
  have hseq :
      (TM.seqTM
        (TM.binaryCopyIntoTM
          (pcTape spec) (selectorTape spec) (copyScratchTape spec))
        (dispatchHaltTM spec program)).HoareTimeSpace
        (fun inp work out =>
          inp = executionInput input ∧ work = initialWork ∧
          out = natTape 0)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape (if snapshot.Halted program then 1 else 0))
        (TM.binaryCopyTime snapshot.pc 0 + 1 + dispatchTime)
        input.length (instructionSpace wordBits) := by
    simpa using hseqRaw
  exact ⟨_, by simpa only [programHaltTM, initialWork] using hseq⟩

private theorem programLoopTM_iteration_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed) :
    let next := snapshot.step program input
    ∃ time,
      ((next.Halted program ∧
          (programLoopTM spec).reachesIn time
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input snapshot
              output := natTape 0 }
            { state := Sum.inr (Sum.inl TM.LoopPhase.done)
              input := executionInput input
              work := executionWork spec input next
              output := natTape 1 }) ∨
        (¬next.Halted program ∧
          (programLoopTM spec).reachesIn time
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input snapshot
              output := natTape 0 }
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input next
              output := natTape 0 })) := by
  let next := snapshot.step program input
  let body := programStepTM spec
  let test := programHaltTM spec
  have hinput := executionInput_parked input
  obtain ⟨bodyBound, hbody⟩ :=
    programStepTM_hoareTime_internal spec input snapshot
      hcanonical hcovered
  obtain ⟨cbody, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
      hbodyInput, hbodyWork, hbodyOutput⟩ :=
    hbody (executionInput input) (executionWork spec input snapshot)
      (natTape 0) ⟨rfl, rfl, rfl⟩
  have hbodyWorkParked : ∀ i, TM.Parked (cbody.work i) := by
    rw [hbodyWork]
    exact executionWork_parked_internal spec input next
  have hbodyLoop := TM.loopTM_body_simulation body test hbodyReach
  have hbodyTransition :
      (⟨test.qstart, TM.transitionInput cbody.input,
        fun i => TM.transitionTape (cbody.work i),
        TM.transitionTape cbody.output⟩ :
          Complexity.Cfg (workTapeCount spec) test.Q) =
        ⟨test.qstart, executionInput input,
          executionWork spec input next, natTape 0⟩ := by
    have hi : TM.transitionInput cbody.input = executionInput input := by
      rw [hbodyInput]
      exact hinput.transitionInput_eq_self
    have hw :
        (fun i => TM.transitionTape (cbody.work i)) =
          executionWork spec input next :=
      funext fun i => by
        rw [hbodyWork]
        exact
          (executionWork_parked_internal spec input next i
            ).transitionTape_eq_self
    have ho : TM.transitionTape cbody.output = natTape 0 := by
      rw [hbodyOutput]
      exact (natTape_parked_internal 0).transitionTape_eq_self
    rw [hi, hw, ho]
  have hbodyToTest := TM.loopTM_body_to_test body test hbodyHalt
  rw [hbodyTransition] at hbodyToTest
  obtain ⟨testBound, htest⟩ :=
    programHaltTM_hoareTime_internal spec input next
  obtain ⟨ctest, testTime, htestTime, htestReach, htestHalt,
      htestInput, htestWork, htestOutput⟩ :=
    htest (executionInput input) (executionWork spec input next)
      (natTape 0) ⟨rfl, rfl, rfl⟩
  have htestWorkParked : ∀ i, TM.Parked (ctest.work i) := by
    rw [htestWork]
    exact executionWork_parked_internal spec input next
  have htestOutputParked : TM.Parked ctest.output := by
    rw [htestOutput]
    exact natTape_parked_internal _
  have htestTransition :
      (⟨(Sum.inr (Sum.inl TM.LoopPhase.rewindOut) :
          TM.LoopQ body.Q test.Q),
        TM.transitionInput ctest.input,
        fun i => TM.transitionTape (ctest.work i),
        TM.transitionTape ctest.output⟩ :
          Complexity.Cfg (workTapeCount spec)
            (TM.LoopQ body.Q test.Q)) =
        ⟨Sum.inr (Sum.inl TM.LoopPhase.rewindOut),
          executionInput input, executionWork spec input next,
          ctest.output⟩ := by
    have hi : TM.transitionInput ctest.input = executionInput input := by
      rw [htestInput]
      exact hinput.transitionInput_eq_self
    have hw :
        (fun i => TM.transitionTape (ctest.work i)) =
          executionWork spec input next := by
      funext i
      rw [htestWork]
      exact
        (executionWork_parked_internal spec input next i
          ).transitionTape_eq_self
    have ho : TM.transitionTape ctest.output = ctest.output :=
      htestOutputParked.transitionTape_eq_self
    rw [hi, hw, ho]
  have htestToRewind :=
    (TM.loopTM_test_to_rewind body test htestHalt).trans
      (congrArg some htestTransition)
  obtain ⟨ctail, htailReach, htailState, htailInput, htailWork,
      htailOutput⟩ :=
    Machine.programLoop_rewind_check_internal body test
      ⟨Sum.inr (Sum.inl TM.LoopPhase.rewindOut),
        executionInput input, executionWork spec input next,
        ctest.output⟩ rfl hinput.read_ne_start
      (fun i =>
        (executionWork_parked_internal spec input next i).read_ne_start)
      (by
        rw [htestOutput]
        simp [natTape, Tape.move])
      (by
        rw [htestOutput]
        simp [natTape, Tape.init, Tape.move])
      (by
        intro j hj
        exact htestOutputParked.2 j hj)
  have hreach := TM.reachesIn_trans _
    (TM.reachesIn_trans _
      (TM.reachesIn_trans _
        (TM.reachesIn_trans _ hbodyLoop (.step hbodyToTest .zero))
        (TM.loopTM_test_simulation body test htestReach))
      (.step htestToRewind .zero)) htailReach
  refine ⟨bodyTime + 1 + testTime + 1 + 3, ?_⟩
  by_cases hhalted : next.Halted program
  · left
    refine ⟨hhalted, ?_⟩
    have hone : ctest.output.cells 1 = Γ.one := by
      rw [htestOutput]
      simp [hhalted, natTape, Tape.init, Tape.move, Γ.ofBool]
    have htailDone :
        ctail.state = Sum.inr (Sum.inl TM.LoopPhase.done) := by
      simpa [hone] using htailState
    have htailOutputFinal : ctail.output = natTape 1 := by
      rw [htailOutput, htestOutput]
      simp [hhalted]
    have hctail :
        ctail =
          { state := Sum.inr (Sum.inl TM.LoopPhase.done)
            input := executionInput input
            work := executionWork spec input next
            output := natTape 1 } := by
      cases ctail
      simp only [Complexity.Cfg.mk.injEq]
      exact ⟨htailDone, htailInput, htailWork, htailOutputFinal⟩
    simpa [programLoopTM, body, test, hctail, next] using hreach
  · right
    refine ⟨hhalted, ?_⟩
    have hone : ctest.output.cells 1 ≠ Γ.one := by
      rw [htestOutput]
      simp [hhalted, natTape, Tape.init, Tape.move]
    have htailStart : ctail.state = Sum.inl body.qstart := by
      simpa [hone] using htailState
    have htailOutputFinal : ctail.output = natTape 0 := by
      rw [htailOutput, htestOutput]
      simp [hhalted]
    have hctail :
        ctail =
          { state := Sum.inl body.qstart
            input := executionInput input
            work := executionWork spec input next
            output := natTape 0 } := by
      cases ctail
      simp only [Complexity.Cfg.mk.injEq]
      exact ⟨htailStart, htailInput, htailWork, htailOutputFinal⟩
    simpa [programLoopTM, body, test, hctail, next] using hreach

private def HoareOutputHead {n : ℕ} (tm : TM n)
    (pre : TM.TapePred n) (bound : ℕ) : Prop :=
  ∀ inp work out, pre inp work out →
    ∀ cfg, tm.reaches
      { state := tm.qstart, input := inp, work := work, output := out } cfg →
      cfg.output.head ≤ bound

private def HoareSpaceOutput {n : ℕ} (tm : TM n)
    (pre : TM.TapePred n) (inputLength space : ℕ) : Prop :=
  ∀ inp work out, pre inp work out →
    ∀ cfg, tm.reaches
      { state := tm.qstart, input := inp, work := work, output := out } cfg →
      cfg.WithinAuxSpace inputLength space ∧
        cfg.output.head ≤ space + 1

private theorem HoareOutputHead.mono_internal {n : ℕ} {tm : TM n}
    {pre : TM.TapePred n} {bound bound' : ℕ}
    (h : HoareOutputHead tm pre bound) (hle : bound ≤ bound') :
    HoareOutputHead tm pre bound' := by
  intro inp work out hpre cfg hreach
  exact (h inp work out hpre cfg hreach).trans hle

private theorem transducer_output_head_step_le_internal
    {n : ℕ} {tm : TM n} (htrans : tm.IsTransducer)
    {c c' : Complexity.Cfg n tm.Q} (hstep : tm.step c = some c') :
    c.output.head ≤ c'.output.head := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    change c.output.head ≤
      (c.output.writeAndMove
        (tm.δ c.state c.input.read (fun i => (c.work i).read)
          c.output.read).2.2.1.toΓ
        (tm.δ c.state c.input.read (fun i => (c.work i).read)
          c.output.read).2.2.2.2.2).head
    generalize hδ : tm.δ c.state c.input.read
      (fun i => (c.work i).read) c.output.read = transition
    rcases transition with
      ⟨q, workWrite, outputWrite, inputDir, workDir, outputDir⟩
    have hdir := htrans c.state c.input.read
      (fun i => (c.work i).read) c.output.read
    rw [hδ] at hdir
    dsimp only at hdir
    cases outputDir with
    | left => exact (hdir rfl).elim
    | stay => simp [Tape.writeAndMove, Tape.move, Tape.write_head]
    | right => simp [Tape.writeAndMove, Tape.move, Tape.write_head]

private theorem transducer_output_head_reachesIn_le_internal
    {n : ℕ} {tm : TM n} (htrans : tm.IsTransducer)
    {c c' : Complexity.Cfg n tm.Q} {time : ℕ}
    (hreach : tm.reachesIn time c c') :
    c.output.head ≤ c'.output.head := by
  induction hreach with
  | zero => exact le_rfl
  | step hstep _ ih =>
      exact
        (transducer_output_head_step_le_internal htrans hstep).trans ih

private theorem hoareOutputHead_of_transducer_hoareTime_internal
    {n : ℕ} {tm : TM n} {pre post : TM.TapePred n}
    {time bound : ℕ} (htrans : tm.IsTransducer)
    (htime : tm.HoareTime pre post time)
    (hpost : ∀ inp work out, post inp work out → out.head ≤ bound) :
    HoareOutputHead tm pre bound := by
  intro inp work out hpre cfg hreach
  obtain ⟨done, doneTime, _hdoneTime, hdoneReach, hdoneHalted,
      hdonePost⟩ := htime inp work out hpre
  obtain ⟨steps, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  have hsteps : steps ≤ doneTime :=
    tm.reachesIn_le_halt hreachIn hdoneReach hdoneHalted
  obtain ⟨partialCfg, hprefix, hsuffix⟩ :=
    TM.reachesIn_prefix_internal hdoneReach hsteps
  have hcfg : cfg = partialCfg :=
    tm.reachesIn_right_unique hreachIn hprefix
  rw [hcfg]
  exact
    (transducer_output_head_reachesIn_le_internal htrans hsuffix).trans
      (hpost done.input done.work done.output hdonePost)

private theorem seqTM_hoareOutputHead_internal {n : ℕ}
    (tm₁ tm₂ : TM n) {pre mid mid' post : TM.TapePred n}
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
    exact
      (houtput₁ inp work out hpre partialCfg
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
    exact
      (houtput₂ (TM.transitionInput cfg₁.input)
        (fun i => TM.transitionTape (cfg₁.work i))
        (TM.transitionTape cfg₁.output) hmid' partialCfg
        (TM.reaches_of_reachesIn hprefix)).trans (le_max_right _ _)

private theorem skipTM_isTransducer_internal {n : ℕ} :
    (TM.skipTM (n := n)).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> cases oHead <;> simp [TM.skipTM, TM.idleDir]

private theorem rewindInputTM_isTransducer_internal {n : ℕ} :
    (TM.rewindInputTM (n := n)).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> simp only [TM.rewindInputTM]
  · split <;> simp only [TM.idleDir] <;> split <;> decide
  · simp only [TM.idleDir]
    split <;> decide
  · simp only [TM.allIdle, TM.idleDir]
    split <;> decide

private theorem denseInputIdleTM_isTransducer_internal {n : ℕ} :
    (Machine.denseInputIdleTM (n := n)).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> simp only [Machine.denseInputIdleTM, TM.idleDir] <;>
    split <;> decide

private theorem capturePreviousInputBitTM_isTransducer_internal {n : ℕ}
    (result : Fin n) :
    (Machine.capturePreviousInputBitTM result).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> simp only [Machine.capturePreviousInputBitTM,
    TM.allIdle, TM.idleDir] <;> split <;> decide

private theorem denseInputStepTM_isTransducer_internal {n : ℕ}
    (counter result : Fin n) :
    (Machine.denseInputStepTM counter result).IsTransducer := by
  unfold Machine.denseInputStepTM
  exact denseInputIdleTM_isTransducer_internal.branchWorkBlankTM
    ((TM.binaryPredTM_isTransducer counter).seqTM
      ((capturePreviousInputBitTM_isTransducer_internal result
        ).branchWorkBlankTM denseInputIdleTM_isTransducer_internal))

private theorem denseInputScanTM_isTransducer_internal {n : ℕ}
    (counter result : Fin n) :
    (Machine.denseInputScanTM counter result).IsTransducer := by
  unfold Machine.denseInputScanTM
  exact (denseInputStepTM_isTransducer_internal counter result).forInputTM

private theorem denseInputLookupTM_isTransducer_internal {n : ℕ}
    (query counter result scratch : Fin n) :
    (Machine.denseInputLookupTM query counter result scratch
      ).IsTransducer := by
  unfold Machine.denseInputLookupTM
  exact (TM.binaryCopyIntoTM_isTransducer query counter scratch).seqTM
    ((denseInputScanTM_isTransducer_internal counter result).seqTM
      (rewindInputTM_isTransducer_internal.seqTM
        (TM.resetBinaryWorkTM_isTransducer counter)))

private theorem directReadTreeBranchTM_isTransducer_internal
    {program : Program} (spec : Spec program)
    (address : Fin spec.registerBound) :
    (directReadTreeBranchTM spec address).IsTransducer := by
  unfold directReadTreeBranchTM
  exact TM.binaryCopyIntoTM_isTransducer _ _ _

private theorem fallbackReadTreeBranchTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (fallbackReadTreeBranchTM spec).IsTransducer := by
  unfold fallbackReadTreeBranchTM
  exact denseInputLookupTM_isTransducer_internal _ _ _ _

private theorem readDispatchTreeTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    ∀ (remaining base : ℕ)
      (hbound : base + remaining = spec.registerBound),
      (readDispatchTreeTM spec remaining base hbound).IsTransducer
  | 0, base, hbound => by
      simp only [readDispatchTreeTM]
      exact (TM.resetBinaryWorkTM_isTransducer _).seqTM
        (fallbackReadTreeBranchTM_isTransducer_internal spec)
  | remaining + 1, base, hbound => by
      simp only [readDispatchTreeTM]
      exact
        (directReadTreeBranchTM_isTransducer_internal spec _
          ).branchWorkBlankTM
            ((TM.binaryPredTM_isTransducer _).seqTM
              (readDispatchTreeTM_isTransducer_internal spec remaining
                (base + 1) (by omega)))

private theorem readDispatchTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (readDispatchTM spec).IsTransducer := by
  unfold readDispatchTM
  exact (TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
    (readDispatchTreeTM_isTransducer_internal spec _ _ _)

private theorem setNatTM_isTransducer_internal {n : ℕ}
    (idx : Fin n) (value : ℕ) :
    (setNatTM idx value).IsTransducer := by
  unfold setNatTM
  exact (TM.resetBinaryWorkTM_isTransducer idx).seqTM
    (TM.binaryAddConstTM_isTransducer idx value)

private theorem binaryArithmeticTM_isTransducer_internal
    {program : Program} (spec : Spec program) (op : BinaryOp) :
    (binaryArithmeticTM spec op).IsTransducer := by
  cases op <;> simp only [binaryArithmeticTM]
  · exact TM.binaryRippleAddTM_isTransducer _ _ _
  · exact TM.binaryRippleSubTM_isTransducer _ _ _
  · exact TM.binaryShiftMulTM_isTransducer _

private theorem binaryInstructionTM_isTransducer_internal
    {program : Program} (spec : Spec program) (op : BinaryOp)
    (destination source₀ source₁ : ℕ)
    (hdestination : destination < spec.registerBound)
    (hsource₀ : source₀ < spec.registerBound)
    (hsource₁ : source₁ < spec.registerBound) :
    (binaryInstructionTM spec op destination source₀ source₁
      hdestination hsource₀ hsource₁).IsTransducer := by
  unfold binaryInstructionTM
  exact (TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
    ((TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
      ((binaryArithmeticTM_isTransducer_internal spec op).seqTM
        ((TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
          ((TM.resetBinaryWorkTM_isTransducer _).seqTM
            ((TM.resetBinaryWorkTM_isTransducer _).seqTM
              (TM.resetBinaryWorkTM_isTransducer _))))))

private theorem loadInstructionTM_isTransducer_internal
    {program : Program} (spec : Spec program)
    (destination addressRegister : ℕ)
    (hdestination : destination < spec.registerBound)
    (haddressRegister : addressRegister < spec.registerBound) :
    (loadInstructionTM spec destination addressRegister
      hdestination haddressRegister).IsTransducer := by
  unfold loadInstructionTM
  exact (TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
    ((readDispatchTM_isTransducer_internal spec).seqTM
      ((TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
        ((TM.resetBinaryWorkTM_isTransducer _).seqTM
          (TM.resetBinaryWorkTM_isTransducer _))))

private theorem executeInstructionTM_isTransducer_internal
    {program : Program} (spec : Spec program) (instruction : Instr) :
    (executeInstructionTM spec instruction).IsTransducer := by
  cases instruction <;> simp only [executeInstructionTM]
  · split
    · exact (setNatTM_isTransducer_internal _ _).seqTM
        (TM.binarySuccTM_isTransducer _)
    · exact skipTM_isTransducer_internal
  · repeat' first | split
    all_goals first
      | exact
          (binaryInstructionTM_isTransducer_internal spec .add
            _ _ _ _ _ _).seqTM (TM.binarySuccTM_isTransducer _)
      | exact skipTM_isTransducer_internal
  · repeat' first | split
    all_goals first
      | exact
          (binaryInstructionTM_isTransducer_internal spec .sub
            _ _ _ _ _ _).seqTM (TM.binarySuccTM_isTransducer _)
      | exact skipTM_isTransducer_internal
  · repeat' first | split
    all_goals first
      | exact
          (binaryInstructionTM_isTransducer_internal spec .mul
            _ _ _ _ _ _).seqTM (TM.binarySuccTM_isTransducer _)
      | exact skipTM_isTransducer_internal
  · repeat' first | split
    all_goals first
      | exact
          (loadInstructionTM_isTransducer_internal spec _ _ _ _).seqTM
            (TM.binarySuccTM_isTransducer _)
      | exact skipTM_isTransducer_internal
  · exact skipTM_isTransducer_internal
  · split
    · exact (setNatTM_isTransducer_internal _ _).branchWorkBlankTM
        (TM.binarySuccTM_isTransducer _)
    · exact skipTM_isTransducer_internal
  · exact setNatTM_isTransducer_internal _ _
  · exact skipTM_isTransducer_internal

private theorem dispatchProgramTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    ∀ code : Program, (dispatchProgramTM spec code).IsTransducer
  | [] => by
      simp only [dispatchProgramTM]
      exact (TM.resetBinaryWorkTM_isTransducer _).seqTM
        (executeInstructionTM_isTransducer_internal spec .halt)
  | instruction :: tail => by
      simp only [dispatchProgramTM]
      exact
        (executeInstructionTM_isTransducer_internal spec instruction
          ).branchWorkBlankTM
            ((TM.binaryPredTM_isTransducer _).seqTM
              (dispatchProgramTM_isTransducer_internal spec tail))

private theorem programStepTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (programStepTM spec).IsTransducer := by
  unfold programStepTM
  exact (TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
    (dispatchProgramTM_isTransducer_internal spec program)

private theorem instructionHaltVerdictTM_isTransducer_internal
    {n : ℕ} (instruction : Instr) :
    (instructionHaltVerdictTM (n := n) instruction).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> simp only [instructionHaltVerdictTM, TM.allIdle,
    TM.idleDir] <;> split <;> decide

private theorem dispatchHaltTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    ∀ code : Program, (dispatchHaltTM spec code).IsTransducer
  | [] => by
      simp only [dispatchHaltTM]
      exact (TM.resetBinaryWorkTM_isTransducer _).seqTM
        (instructionHaltVerdictTM_isTransducer_internal .halt)
  | instruction :: tail => by
      simp only [dispatchHaltTM]
      exact
        (instructionHaltVerdictTM_isTransducer_internal instruction
          ).branchWorkBlankTM
            ((TM.binaryPredTM_isTransducer _).seqTM
              (dispatchHaltTM_isTransducer_internal spec tail))

private theorem programHaltTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (programHaltTM spec).IsTransducer := by
  unfold programHaltTM
  exact (TM.binaryCopyIntoTM_isTransducer _ _ _).seqTM
    (dispatchHaltTM_isTransducer_internal spec program)

private theorem registerVerdictTM_isTransducer_internal
    {n : ℕ} (idx : Fin n) :
    (Machine.registerVerdictTM idx).IsTransducer := by
  intro state iHead wHeads oHead
  cases state <;> simp only [Machine.registerVerdictTM, TM.allIdle,
    TM.idleDir] <;> split <;> decide

private theorem programOutputTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (programOutputTM spec).IsTransducer := by
  unfold programOutputTM
  exact registerVerdictTM_isTransducer_internal _

private theorem prefixInitTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (prefixInitTM spec).IsTransducer := by
  intro state iHead wHeads oHead
  simp only [prefixInitTM]
  split
  · simp only [TM.idleDir]
    split <;> decide
  · simp only [TM.allIdle, TM.idleDir]
    split <;> decide

private theorem initializeTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (initializeTM spec).IsTransducer := by
  unfold initializeTM
  exact (TM.binaryLengthTM_isTransducer _).seqTM
    (rewindInputTM_isTransducer_internal.seqTM
      (prefixInitTM_isTransducer_internal spec))

private theorem executionInitializeTM_isTransducer_internal
    {program : Program} (spec : Spec program) :
    (executionInitializeTM spec).IsTransducer := by
  unfold executionInitializeTM
  exact (initializeTM_isTransducer_internal spec).seqTM
    rewindInputTM_isTransducer_internal

private theorem programLoopTM_iteration_timeSpace_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (hcanonical : DenseOverlay.Canonical snapshot.overlay)
    (hcovered : Covered snapshot.overlay spec.allowed)
    (wordBits : ℕ)
    (hcurrent : SnapshotBound spec input snapshot wordBits)
    (hnext :
      SnapshotBound spec input
        (snapshot.step program input) wordBits)
    (hpcWidth : snapshot.pc.size ≤ wordBits)
    (hnextPCWidth :
      (snapshot.step program input).pc.size ≤ wordBits) :
    let next := snapshot.step program input
    ∃ time,
      (((next.Halted program ∧
          (programLoopTM spec).reachesIn time
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input snapshot
              output := natTape 0 }
            { state := Sum.inr (Sum.inl TM.LoopPhase.done)
              input := executionInput input
              work := executionWork spec input next
              output := natTape 1 }) ∨
        (¬next.Halted program ∧
          (programLoopTM spec).reachesIn time
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input snapshot
              output := natTape 0 }
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input next
              output := natTape 0 })) ∧
        ∀ steps cfg, steps ≤ time →
          (programLoopTM spec).reachesIn steps
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input snapshot
              output := natTape 0 } cfg →
          cfg.WithinAuxSpace input.length (instructionSpace wordBits) ∧
            cfg.output.head ≤ instructionSpace wordBits + 1) := by
  let next := snapshot.step program input
  let body := programStepTM spec
  let test := programHaltTM spec
  have hinput := executionInput_parked input
  obtain ⟨bodyBound, hbody⟩ :=
    programStepTM_hoareTimeSpace_internal spec input snapshot
      hcanonical hcovered wordBits hcurrent
      (by simpa [next] using hnext) hpcWidth
      (by simpa [next] using hnextPCWidth)
  obtain ⟨cbody, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
      hbodyInput, hbodyWork, hbodyOutput⟩ :=
    hbody.1 (executionInput input) (executionWork spec input snapshot)
      (natTape 0) ⟨rfl, rfl, rfl⟩
  have hbodyWorkParked : ∀ i, TM.Parked (cbody.work i) := by
    rw [hbodyWork]
    exact executionWork_parked_internal spec input next
  have hbodyLoop := TM.loopTM_body_simulation body test hbodyReach
  have hbodyTransition :
      (⟨test.qstart, TM.transitionInput cbody.input,
        fun i => TM.transitionTape (cbody.work i),
        TM.transitionTape cbody.output⟩ :
          Complexity.Cfg (workTapeCount spec) test.Q) =
        ⟨test.qstart, executionInput input,
          executionWork spec input next, natTape 0⟩ := by
    have hi : TM.transitionInput cbody.input = executionInput input := by
      rw [hbodyInput]
      exact hinput.transitionInput_eq_self
    have hw :
        (fun i => TM.transitionTape (cbody.work i)) =
          executionWork spec input next :=
      funext fun i => by
        rw [hbodyWork]
        exact
          (executionWork_parked_internal spec input next i
            ).transitionTape_eq_self
    have ho : TM.transitionTape cbody.output = natTape 0 := by
      rw [hbodyOutput]
      exact (natTape_parked_internal 0).transitionTape_eq_self
    rw [hi, hw, ho]
  have hbodyToTest := TM.loopTM_body_to_test body test hbodyHalt
  rw [hbodyTransition] at hbodyToTest
  obtain ⟨testBound, htest⟩ :=
    programHaltTM_hoareTimeSpace_internal spec input next
      wordBits (by simpa [next] using hnextPCWidth)
  obtain ⟨ctest, testTime, htestTime, htestReach, htestHalt,
      htestInput, htestWork, htestOutput⟩ :=
    htest.1 (executionInput input) (executionWork spec input next)
      (natTape 0) ⟨rfl, rfl, rfl⟩
  have htestWorkParked : ∀ i, TM.Parked (ctest.work i) := by
    rw [htestWork]
    exact executionWork_parked_internal spec input next
  have htestOutputParked : TM.Parked ctest.output := by
    rw [htestOutput]
    exact natTape_parked_internal _
  have htestTransition :
      (⟨(Sum.inr (Sum.inl TM.LoopPhase.rewindOut) :
          TM.LoopQ body.Q test.Q),
        TM.transitionInput ctest.input,
        fun i => TM.transitionTape (ctest.work i),
        TM.transitionTape ctest.output⟩ :
          Complexity.Cfg (workTapeCount spec)
            (TM.LoopQ body.Q test.Q)) =
        ⟨Sum.inr (Sum.inl TM.LoopPhase.rewindOut),
          executionInput input, executionWork spec input next,
          ctest.output⟩ := by
    have hi : TM.transitionInput ctest.input = executionInput input := by
      rw [htestInput]
      exact hinput.transitionInput_eq_self
    have hw :
        (fun i => TM.transitionTape (ctest.work i)) =
          executionWork spec input next := by
      funext i
      rw [htestWork]
      exact
        (executionWork_parked_internal spec input next i
          ).transitionTape_eq_self
    have ho : TM.transitionTape ctest.output = ctest.output :=
      htestOutputParked.transitionTape_eq_self
    rw [hi, hw, ho]
  have htestToRewind :=
    (TM.loopTM_test_to_rewind body test htestHalt).trans
      (congrArg some htestTransition)
  obtain ⟨ctail, htailReach, htailState, htailInput, htailWork,
      htailOutput⟩ :=
    Machine.programLoop_rewind_check_internal body test
      ⟨Sum.inr (Sum.inl TM.LoopPhase.rewindOut),
        executionInput input, executionWork spec input next,
        ctest.output⟩ rfl hinput.read_ne_start
      (fun i =>
        (executionWork_parked_internal spec input next i).read_ne_start)
      (by
        rw [htestOutput]
        simp [natTape, Tape.move])
      (by
        rw [htestOutput]
        simp [natTape, Tape.init, Tape.move])
      (by
        intro j hj
        exact htestOutputParked.2 j hj)
  have htestLoop := TM.loopTM_test_simulation body test htestReach
  have hbodyPhase := TM.reachesIn_trans _ hbodyLoop
    (.step hbodyToTest .zero)
  have htestPhase := TM.reachesIn_trans _ hbodyPhase htestLoop
  have htoRewind := TM.reachesIn_trans _ htestPhase
    (.step htestToRewind .zero)
  have hreach := TM.reachesIn_trans _ htoRewind htailReach
  refine
    ⟨bodyTime + 1 + testTime + 1 + 3, ?_, ?_⟩
  · by_cases hhalted : next.Halted program
    · left
      refine ⟨hhalted, ?_⟩
      have hone : ctest.output.cells 1 = Γ.one := by
        rw [htestOutput]
        simp [hhalted, natTape, Tape.init, Tape.move, Γ.ofBool]
      have htailDone :
          ctail.state = Sum.inr (Sum.inl TM.LoopPhase.done) := by
        simpa [hone] using htailState
      have htailOutputFinal : ctail.output = natTape 1 := by
        rw [htailOutput, htestOutput]
        simp [hhalted]
      have hctail :
          ctail =
            { state := Sum.inr (Sum.inl TM.LoopPhase.done)
              input := executionInput input
              work := executionWork spec input next
              output := natTape 1 } := by
        cases ctail
        simp only [Complexity.Cfg.mk.injEq]
        exact ⟨htailDone, htailInput, htailWork, htailOutputFinal⟩
      simpa [programLoopTM, body, test, hctail, next] using hreach
    · right
      refine ⟨hhalted, ?_⟩
      have hone : ctest.output.cells 1 ≠ Γ.one := by
        rw [htestOutput]
        simp [hhalted, natTape, Tape.init, Tape.move]
      have htailStart : ctail.state = Sum.inl body.qstart := by
        simpa [hone] using htailState
      have htailOutputFinal : ctail.output = natTape 0 := by
        rw [htailOutput, htestOutput]
        simp [hhalted]
      have hctail :
          ctail =
            { state := Sum.inl body.qstart
              input := executionInput input
              work := executionWork spec input next
              output := natTape 0 } := by
        cases ctail
        simp only [Complexity.Cfg.mk.injEq]
        exact ⟨htailStart, htailInput, htailWork, htailOutputFinal⟩
      simpa [programLoopTM, body, test, hctail, next] using hreach
  · intro steps cfg hsteps hprefix
    by_cases hbodyPrefix : steps ≤ bodyTime
    · obtain ⟨partialCfg, hpartial, hsuffix⟩ :=
        TM.reachesIn_prefix_internal hbodyReach hbodyPrefix
      have hlift := TM.loopTM_body_simulation body test hpartial
      have hlift' :
          (programLoopTM spec).reachesIn steps
            { state := (programLoopTM spec).qstart
              input := executionInput input
              work := executionWork spec input snapshot
              output := natTape 0 }
            (TM.loopBodyWrap body test partialCfg) := by
        simpa [programLoopTM, body, test, TM.loopBodyWrap] using hlift
      have hcfg :
          cfg = TM.loopBodyWrap body test partialCfg :=
        (programLoopTM spec).reachesIn_right_unique hprefix hlift'
      have hpartialSpace := hbody.2
        (executionInput input) (executionWork spec input snapshot)
        (natTape 0) ⟨rfl, rfl, rfl⟩ partialCfg
        (TM.reaches_of_reachesIn hpartial)
      rw [hcfg]
      constructor
      · simpa [TM.loopBodyWrap] using hpartialSpace
      · change partialCfg.output.head ≤ instructionSpace wordBits + 1
        have hhead :=
          transducer_output_head_reachesIn_le_internal
            (programStepTM_isTransducer_internal spec) hsuffix
        have hdoneHead : cbody.output.head = 1 := by
          rw [hbodyOutput]
          simp [natTape, Tape.move]
        rw [hdoneHead] at hhead
        have hspacePositive := one_le_instructionSpace wordBits
        omega
    · have hbodyDone : bodyTime + 1 ≤ steps := by omega
      let afterBody := steps - (bodyTime + 1)
      have hstepsBody : bodyTime + 1 + afterBody = steps := by
        dsimp only [afterBody]
        omega
      by_cases htestPrefix : afterBody ≤ testTime
      · obtain ⟨partialCfg, hpartial, hsuffix⟩ :=
          TM.reachesIn_prefix_internal htestReach htestPrefix
        have hlift := TM.loopTM_test_simulation body test hpartial
        have hcombined := TM.reachesIn_trans _ hbodyPhase hlift
        have hcombined' :
            (programLoopTM spec).reachesIn steps
              { state := (programLoopTM spec).qstart
                input := executionInput input
                work := executionWork spec input snapshot
                output := natTape 0 }
              (TM.loopTestWrap body test partialCfg) := by
          rw [hstepsBody] at hcombined
          simpa [programLoopTM, body, test, TM.loopBodyWrap] using hcombined
        have hcfg :
            cfg = TM.loopTestWrap body test partialCfg :=
          (programLoopTM spec).reachesIn_right_unique hprefix hcombined'
        have hpartialSpace := htest.2
          (executionInput input) (executionWork spec input next)
          (natTape 0) ⟨rfl, rfl, rfl⟩ partialCfg
          (TM.reaches_of_reachesIn hpartial)
        rw [hcfg]
        constructor
        · simpa [TM.loopTestWrap] using hpartialSpace
        · change partialCfg.output.head ≤ instructionSpace wordBits + 1
          have hhead :=
            transducer_output_head_reachesIn_le_internal
              (programHaltTM_isTransducer_internal spec) hsuffix
          have hdoneHead : ctest.output.head = 1 := by
            rw [htestOutput]
            simp [natTape, Tape.move]
          rw [hdoneHead] at hhead
          have hspacePositive := one_le_instructionSpace wordBits
          omega
      · have hrewindDone :
            bodyTime + 1 + testTime + 1 ≤ steps := by
          dsimp only [afterBody] at htestPrefix
          omega
        let tailSteps :=
          steps - (bodyTime + 1 + testTime + 1)
        have hstepsTail :
            bodyTime + 1 + testTime + 1 + tailSteps = steps := by
          dsimp only [tailSteps]
          omega
        have hprefixSplit :
            (programLoopTM spec).reachesIn
              (bodyTime + 1 + testTime + 1 + tailSteps)
              { state := (programLoopTM spec).qstart
                input := executionInput input
                work := executionWork spec input snapshot
                output := natTape 0 } cfg := by
          simpa only [hstepsTail] using hprefix
        obtain ⟨boundary, hfirst, htail⟩ :=
          TM.reachesIn_split_internal hprefixSplit
        let rewindStart :
            Complexity.Cfg (workTapeCount spec) (programLoopTM spec).Q :=
          { state := Sum.inr (Sum.inl TM.LoopPhase.rewindOut)
            input := executionInput input
            work := executionWork spec input next
            output := ctest.output }
        have htoRewind' :
            (programLoopTM spec).reachesIn
              (bodyTime + 1 + testTime + 1)
              { state := (programLoopTM spec).qstart
                input := executionInput input
                work := executionWork spec input snapshot
                output := natTape 0 } rewindStart := by
          simpa [programLoopTM, body, test, rewindStart,
            TM.loopBodyWrap] using htoRewind
        have hboundary : boundary = rewindStart :=
          (programLoopTM spec).reachesIn_right_unique hfirst htoRewind'
        subst boundary
        have htailBound : tailSteps ≤ 3 := by
          dsimp only [tailSteps]
          omega
        have hrewindSpace :
            rewindStart.WithinAuxSpace input.length 1 := by
          constructor
          · intro i
            simp only [rewindStart]
            rw [executionWork_head_internal spec input next i]
          · simp [rewindStart, executionInput, Tape.move]
        constructor
        · exact (hrewindSpace.reachesIn htail).mono le_rfl (by
            unfold instructionSpace
            omega)
        · have hhead :=
            (programLoopTM spec).output_head_reachesIn_bound htail
          have hstartHead : rewindStart.output.head = 1 := by
            change ctest.output.head = 1
            rw [htestOutput]
            simp [natTape, Tape.move]
          rw [hstartHead] at hhead
          have hspaceLarge : 3 ≤ instructionSpace wordBits := by
            unfold instructionSpace
            omega
          omega

private theorem snapshot_step_eq_self_of_halted_internal
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hhalted : snapshot.Halted program) :
    snapshot.step program input = snapshot := by
  change snapshot.curInstr program = .halt at hhalted
  rw [DenseOverlay.Snapshot.step, hhalted]
  rfl

private theorem snapshot_run_halted_internal
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hhalted : snapshot.Halted program) :
    ∀ fuel, snapshot.run program input fuel = snapshot
  | 0 => rfl
  | fuel + 1 => by
      rw [DenseOverlay.Snapshot.run, if_pos hhalted]

/-- A halted fuel-bounded semantic run is realized exactly by the direct
fixed-register controller. The controller performs one final iteration to
recognize a snapshot that is already halted. -/
private theorem programLoopTM_reaches_run_internal
    {program : Program} (spec : Spec program) (input : List Bool) :
    ∀ (fuel : ℕ) (snapshot : DenseOverlay.Snapshot),
      DenseOverlay.Canonical snapshot.overlay →
      Covered snapshot.overlay spec.allowed →
      (snapshot.run program input fuel).Halted program →
      ∃ time,
        (programLoopTM spec).reachesIn time
          { state := (programLoopTM spec).qstart
            input := executionInput input
            work := executionWork spec input snapshot
            output := natTape 0 }
          { state := (programLoopTM spec).qhalt
            input := executionInput input
            work :=
              executionWork spec input
                (snapshot.run program input fuel)
            output := natTape 1 } := by
  intro fuel
  induction fuel with
  | zero =>
      intro snapshot hcanonical hcovered hhalted
      have hsnapshotHalted : snapshot.Halted program := by
        simpa [DenseOverlay.Snapshot.run] using hhalted
      have hstepSelf := snapshot_step_eq_self_of_halted_internal
        program input snapshot hsnapshotHalted
      obtain ⟨time, hbranch⟩ :=
        programLoopTM_iteration_internal spec input snapshot
          hcanonical hcovered
      rcases hbranch with ⟨_, hreach⟩ | ⟨hnextRunning, _⟩
      · refine ⟨time, ?_⟩
        simpa [DenseOverlay.Snapshot.run, hstepSelf] using hreach
      · exact (hnextRunning (by simpa only [hstepSelf] using
          hsnapshotHalted)).elim
  | succ fuel ih =>
      intro snapshot hcanonical hcovered hhalted
      by_cases hsnapshotHalted : snapshot.Halted program
      · have hstepSelf := snapshot_step_eq_self_of_halted_internal
          program input snapshot hsnapshotHalted
        obtain ⟨time, hbranch⟩ :=
          programLoopTM_iteration_internal spec input snapshot
            hcanonical hcovered
        rcases hbranch with ⟨_, hreach⟩ | ⟨hnextRunning, _⟩
        · refine ⟨time, ?_⟩
          have hrunSelf :=
            snapshot_run_halted_internal program input snapshot
              hsnapshotHalted (fuel + 1)
          simpa only [hstepSelf, hrunSelf] using hreach
        · exact (hnextRunning (by simpa only [hstepSelf] using
            hsnapshotHalted)).elim
      · have hrunHalted :
            ((snapshot.step program input).run program input fuel).Halted
              program := by
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hhalted
        obtain ⟨time₁, hbranch⟩ :=
          programLoopTM_iteration_internal spec input snapshot
            hcanonical hcovered
        rcases hbranch with ⟨hnextHalted, hreach₁⟩ |
            ⟨hnextRunning, hreach₁⟩
        · have hrunSelf :=
            snapshot_run_halted_internal program input
              (snapshot.step program input) hnextHalted fuel
          refine ⟨time₁, ?_⟩
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted, hrunSelf]
            using hreach₁
        · have hnextCanonical :=
            DenseOverlay.Snapshot.step_canonical program input snapshot
              hcanonical
          have hnextCovered :=
            DenseOverlay.FixedRegisters.Footprint.Snapshot.step_covered
              (input := input) spec.writesWithin hcovered
          obtain ⟨time₂, hreach₂⟩ :=
            ih (snapshot.step program input) hnextCanonical hnextCovered
              hrunHalted
          refine ⟨time₁ + time₂, ?_⟩
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using
            TM.reachesIn_trans _ hreach₁ hreach₂

private theorem programLoopTM_hoareSpaceOutput_from_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (wordBits : ℕ) :
    ∀ (fuel : ℕ) (snapshot : DenseOverlay.Snapshot),
      DenseOverlay.Canonical snapshot.overlay →
      Covered snapshot.overlay spec.allowed →
      (snapshot.run program input fuel).Halted program →
      (∀ k, k ≤ fuel →
        SnapshotBound spec input
          (snapshot.run program input k) wordBits) →
      (∀ k, k ≤ fuel →
        (snapshot.run program input k).pc.size ≤ wordBits) →
      HoareSpaceOutput (programLoopTM spec)
        (fun inp work out =>
          inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = natTape 0)
        input.length (instructionSpace wordBits) := by
  intro fuel
  induction fuel with
  | zero =>
      intro snapshot hcanonical hcovered hhalted htrace hpctrace
        inp work out hpre cfg hreach
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      have hsnapshotHalted : snapshot.Halted program := by
        simpa [DenseOverlay.Snapshot.run] using hhalted
      have hstepSelf := snapshot_step_eq_self_of_halted_internal
        program input snapshot hsnapshotHalted
      have hcurrent :
          SnapshotBound spec input snapshot wordBits := by
        simpa [DenseOverlay.Snapshot.run] using htrace 0 (by omega)
      have hpcWidth : snapshot.pc.size ≤ wordBits := by
        simpa [DenseOverlay.Snapshot.run] using hpctrace 0 (by omega)
      obtain ⟨time, hbranch, hprefixSpace⟩ :=
        programLoopTM_iteration_timeSpace_internal spec input snapshot
          hcanonical hcovered wordBits hcurrent
          (by simpa [hstepSelf] using hcurrent)
          hpcWidth (by simpa [hstepSelf] using hpcWidth)
      rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
          ⟨hnextRunning, _hsegment⟩
      · obtain ⟨steps, hreachIn⟩ :=
          (programLoopTM spec).reaches_to_reachesIn hreach
        have hsegmentHalted :
            (programLoopTM spec).halted
              { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                input := executionInput input
                work := executionWork spec input snapshot
                output := natTape 1 } := by
          rfl
        have hsteps : steps ≤ time :=
          (programLoopTM spec).reachesIn_le_halt
            hreachIn (by simpa [hstepSelf] using hsegment)
            hsegmentHalted
        exact hprefixSpace steps cfg hsteps hreachIn
      · exact (hnextRunning (by simpa only [hstepSelf] using
          hsnapshotHalted)).elim
  | succ fuel ih =>
      intro snapshot hcanonical hcovered hhalted htrace hpctrace
        inp work out hpre cfg hreach
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      by_cases hsnapshotHalted : snapshot.Halted program
      · have hstepSelf := snapshot_step_eq_self_of_halted_internal
          program input snapshot hsnapshotHalted
        have hcurrent :
            SnapshotBound spec input snapshot wordBits := by
          simpa [DenseOverlay.Snapshot.run] using htrace 0 (by omega)
        have hpcWidth : snapshot.pc.size ≤ wordBits := by
          simpa [DenseOverlay.Snapshot.run] using hpctrace 0 (by omega)
        obtain ⟨time, hbranch, hprefixSpace⟩ :=
          programLoopTM_iteration_timeSpace_internal spec input snapshot
            hcanonical hcovered wordBits hcurrent
            (by simpa [hstepSelf] using hcurrent)
            hpcWidth (by simpa [hstepSelf] using hpcWidth)
        rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
            ⟨hnextRunning, _hsegment⟩
        · obtain ⟨steps, hreachIn⟩ :=
            (programLoopTM spec).reaches_to_reachesIn hreach
          have hsegmentHalted :
              (programLoopTM spec).halted
                { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                  input := executionInput input
                  work := executionWork spec input snapshot
                  output := natTape 1 } := by
            rfl
          have hsteps : steps ≤ time :=
            (programLoopTM spec).reachesIn_le_halt
              hreachIn (by simpa [hstepSelf] using hsegment)
              hsegmentHalted
          exact hprefixSpace steps cfg hsteps hreachIn
        · exact (hnextRunning (by simpa only [hstepSelf] using
            hsnapshotHalted)).elim
      · have hrunHalted :
            ((snapshot.step program input).run program input fuel).Halted
              program := by
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hhalted
        have hcurrent :
            SnapshotBound spec input snapshot wordBits := by
          simpa [DenseOverlay.Snapshot.run] using htrace 0 (by omega)
        have hpcWidth : snapshot.pc.size ≤ wordBits := by
          simpa [DenseOverlay.Snapshot.run] using hpctrace 0 (by omega)
        have hnext :
            SnapshotBound spec input
              (snapshot.step program input) wordBits := by
          have hbound := htrace 1 (by omega)
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hbound
        have hnextPCWidth :
            (snapshot.step program input).pc.size ≤ wordBits := by
          have hbound := hpctrace 1 (by omega)
          simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hbound
        obtain ⟨time, hbranch, hprefixSpace⟩ :=
          programLoopTM_iteration_timeSpace_internal spec input snapshot
            hcanonical hcovered wordBits hcurrent hnext
            hpcWidth hnextPCWidth
        obtain ⟨steps, hreachIn⟩ :=
          (programLoopTM spec).reaches_to_reachesIn hreach
        rcases hbranch with ⟨_hnextHalted, hsegment⟩ |
            ⟨_hnextRunning, hsegment⟩
        · have hsegmentHalted :
              (programLoopTM spec).halted
                { state := Sum.inr (Sum.inl TM.LoopPhase.done)
                  input := executionInput input
                  work :=
                    executionWork spec input
                      (snapshot.step program input)
                  output := natTape 1 } := by
            rfl
          have hsteps : steps ≤ time :=
            (programLoopTM spec).reachesIn_le_halt
              hreachIn hsegment hsegmentHalted
          exact hprefixSpace steps cfg hsteps hreachIn
        · by_cases hprefix : steps ≤ time
          · exact hprefixSpace steps cfg hprefix hreachIn
          · have htimeSteps : time ≤ steps := by omega
            let tailTime := steps - time
            have htimeEq : time + tailTime = steps :=
              Nat.add_sub_of_le htimeSteps
            have hreachSplit :
                (programLoopTM spec).reachesIn (time + tailTime)
                  { state := (programLoopTM spec).qstart
                    input := executionInput input
                    work := executionWork spec input snapshot
                    output := natTape 0 } cfg := by
              simpa only [htimeEq] using hreachIn
            obtain ⟨boundary, hfirst, htail⟩ :=
              TM.reachesIn_split_internal hreachSplit
            have hboundary :
                boundary =
                  { state := (programLoopTM spec).qstart
                    input := executionInput input
                    work :=
                      executionWork spec input
                        (snapshot.step program input)
                    output := natTape 0 } :=
              (programLoopTM spec).reachesIn_right_unique
                hfirst hsegment
            subst boundary
            have hnextCanonical :=
              DenseOverlay.Snapshot.step_canonical program input snapshot
                hcanonical
            have hnextCovered :=
              DenseOverlay.FixedRegisters.Footprint.Snapshot.step_covered
                (input := input) spec.writesWithin hcovered
            have htailTrace :
                ∀ k, k ≤ fuel →
                  SnapshotBound spec input
                    ((snapshot.step program input).run program input k)
                    wordBits := by
              intro k hk
              have hk' : k + 1 ≤ fuel + 1 := by omega
              have hbound := htrace (k + 1) hk'
              simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hbound
            have htailPCTrace :
                ∀ k, k ≤ fuel →
                  ((snapshot.step program input).run program input k
                    ).pc.size ≤ wordBits := by
              intro k hk
              have hk' : k + 1 ≤ fuel + 1 := by omega
              have hbound := hpctrace (k + 1) hk'
              simpa [DenseOverlay.Snapshot.run, hsnapshotHalted] using hbound
            have hrecursive := ih (snapshot.step program input)
              hnextCanonical hnextCovered hrunHalted
              htailTrace htailPCTrace
            exact hrecursive _ _ _ ⟨rfl, rfl, rfl⟩ cfg
              (TM.reaches_of_reachesIn htail)

private theorem registerRead_nonzero_mem_internal
    (overlay : RegisterStore.Store) (address : ℕ)
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

private theorem bitlen_pred_le_internal (value : ℕ) :
    bitlen (value - 1) ≤ bitlen value := by
  unfold bitlen
  exact Nat.size_le_size (Nat.sub_le value 1)

private theorem denseSnapshotBound_one_le_wordBits_internal
    {snapshot : DenseOverlay.Snapshot} {entryBudget wordBits : ℕ}
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    1 ≤ wordBits := by
  have hread := hvalid.2
  change RegisterStore.read snapshot.overlay 0 ≠ 0 at hread
  have hmem :=
    registerRead_nonzero_mem_internal snapshot.overlay 0 hread
  have hwidth :
      bitlen (RegisterStore.read snapshot.overlay 0) ≤ wordBits := by
    simpa using (hbound.entries
      (0, RegisterStore.read snapshot.overlay 0) hmem).2
  have hpositive :
      1 ≤ bitlen (RegisterStore.read snapshot.overlay 0) := by
    unfold bitlen
    exact Nat.size_pos.mpr (Nat.pos_of_ne_zero hread)
  omega

private theorem denseSnapshotBound_read_bitlen_le_internal
    {input : List Bool} {snapshot : DenseOverlay.Snapshot}
    {entryBudget wordBits address : ℕ}
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    bitlen (DenseOverlay.read input snapshot.overlay address) ≤ wordBits := by
  have hone :=
    denseSnapshotBound_one_le_wordBits_internal hvalid hbound
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
        (registerRead_nonzero_mem_internal snapshot.overlay address htag)).2
    exact (bitlen_pred_le_internal _).trans hwidth

private theorem programOutputTM_hoareTime_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (snapshot : DenseOverlay.Snapshot) :
    (programOutputTM spec).HoareTime
      (fun inp work out =>
        inp = executionInput input ∧
          work = executionWork spec input snapshot ∧ out = natTape 1)
      (fun inp work out =>
        inp = executionInput input ∧
          work = executionWork spec input snapshot ∧
          out = Machine.registerVerdictOutput
            (DenseOverlay.read input snapshot.overlay 0))
      1 := by
  let idx :=
    registerTape spec 0 (spec.allowed_lt 0 spec.zero_mem)
  have hvalue :
      (executionWork spec input snapshot idx).HasBinaryNat
        (DenseOverlay.read input snapshot.overlay 0) := by
    rw [show idx =
      registerTape spec 0 (spec.allowed_lt 0 spec.zero_mem) from rfl,
      executionWork_register_internal]
    exact
      natTape_hasBinaryNat_internal
        (DenseOverlay.read input snapshot.overlay 0)
  have hresult :=
    Machine.registerVerdictTM_hoareTime_haltOutput_internal
      idx (DenseOverlay.read input snapshot.overlay 0)
      (executionInput input) (executionWork spec input snapshot)
      hvalue (executionInput_parked input)
      (executionWork_parked_internal spec input snapshot)
  have hout :
      Machine.instructionHaltOutput .halt = natTape 1 := by
    apply Tape.ext
    · simp [Machine.instructionHaltOutput,
        Machine.instructionHaltVerdict, natTape, Tape.writeAndMove,
        Tape.move, Tape.write, Tape.read, Tape.init, TM.idleDir]
    · funext j
      by_cases hzero : j = 0
      · subst j
        simp [Machine.instructionHaltOutput,
          Machine.instructionHaltVerdict, natTape, Tape.writeAndMove,
          Tape.move, Tape.write, Tape.read, Tape.init, TM.idleDir]
      · by_cases hone : j = 1
        · subst j
          simp [Machine.instructionHaltOutput,
            Machine.instructionHaltVerdict, natTape, Tape.writeAndMove,
            Tape.move, Tape.write, Tape.read, Tape.init, TM.idleDir,
            Γ.ofBool]
        · have hlarge : 1 < j := by omega
          simp [Machine.instructionHaltOutput,
            Machine.instructionHaltVerdict, natTape, Tape.writeAndMove,
            Tape.move, Tape.write, Tape.read, Tape.init, TM.idleDir,
            hzero, hone, show j - 1 ≠ 0 by omega]
  rw [hout] at hresult
  simpa [programOutputTM, idx] using hresult

/-- Semantic correctness of the complete direct compiler on one halted
fuel-bounded run. The result exposes an exact reusable final snapshot and the
Boolean output tape obtained from its R0 value. -/
private theorem programTM_hoareTime_run_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (fuel : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program) :
    ∃ time,
      (programTM spec).HoareTime
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
            work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (fun inp work out =>
          let final :=
            (DenseOverlay.Snapshot.initial input).run program input fuel
          inp = executionInput input ∧
            work = executionWork spec input final ∧
            out = Machine.registerVerdictOutput
              (DenseOverlay.read input final.overlay 0))
        time := by
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  have hcanonical := DenseOverlay.Snapshot.initial_canonical input
  have hcovered :=
    DenseOverlay.FixedRegisters.Footprint.Snapshot.initial_covered
      (input := input) spec.zero_mem
  obtain ⟨loopTime, hloopReach⟩ :=
    programLoopTM_reaches_run_internal spec input fuel initial
      hcanonical hcovered hhalted
  let initPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = executionInput input ∧ work = executionWork spec input initial ∧
        out = natTape 0
  let loopPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = executionInput input ∧ work = executionWork spec input final ∧
        out = natTape 1
  let outputPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = executionInput input ∧ work = executionWork spec input final ∧
        out = Machine.registerVerdictOutput
          (DenseOverlay.read input final.overlay 0)
  have hloop :
      (programLoopTM spec).HoareTime initPost loopPost loopTime := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    let done :
        Complexity.Cfg (workTapeCount spec) (programLoopTM spec).Q :=
      { state := (programLoopTM spec).qhalt
        input := executionInput input
        work := executionWork spec input final
        output := natTape 1 }
    refine ⟨done, loopTime, le_rfl, ?_, rfl, rfl, rfl, rfl⟩
    simpa [initial, final, done] using hloopReach
  have houtput := programOutputTM_hoareTime_internal spec input final
  have hloopTransition :
      ∀ inp work out, loopPost inp work out →
        loopPost (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
      (executionInput_parked input).read_ne_start
      (fun i =>
        (executionWork_parked_internal spec input final i).read_ne_start)
      (natTape_parked_internal 1).read_ne_start
    rw [htransition.1, htransition.2.1, htransition.2.2]
    exact ⟨rfl, rfl, rfl⟩
  have htail := TM.seqTM_hoareTime
    (programLoopTM spec) (programOutputTM spec)
    hloop hloopTransition houtput
  have hinitialize :=
    (executionInitializeTM_hoareTimeSpace_internal spec input).1
  have hinitTransition :
      ∀ inp work out, initPost inp work out →
        initPost (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
      (executionInput_parked input).read_ne_start
      (fun i =>
        (executionWork_parked_internal spec input initial i).read_ne_start)
      (natTape_parked_internal 0).read_ne_start
    rw [htransition.1, htransition.2.1, htransition.2.2]
    exact ⟨rfl, rfl, rfl⟩
  have hfull := TM.seqTM_hoareTime
    (executionInitializeTM spec)
    (TM.seqTM (programLoopTM spec) (programOutputTM spec))
    hinitialize hinitTransition htail
  refine
    ⟨(initializeTime spec input.length + 1 + (input.length + 3)) + 1 +
        (loopTime + 1 + 1), ?_⟩
  simpa [programTM, initial, final, initPost, loopPost, outputPost] using
    hfull

/-- A dense fixed-register trace bound supplies both the direct compiler's
all-prefix auxiliary-space contract and the separately charged output-head
bound. -/
private theorem programTM_contract_traceBound_internal
    {program : Program} (spec : Spec program)
    (input : List Bool) (fuel wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel spec.allowed.card wordBits) :
    ∃ time,
      (programTM spec).HoareTimeSpace
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
            work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (fun inp work out =>
          let final :=
            (DenseOverlay.Snapshot.initial input).run program input fuel
          inp = executionInput input ∧
            work = executionWork spec input final ∧
            out = Machine.registerVerdictOutput
              (DenseOverlay.read input final.overlay 0))
        time input.length
        (max (initializeSpace spec input.length)
          (instructionSpace wordBits)) ∧
      HoareOutputHead (programTM spec)
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
            work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (max (initializeSpace spec input.length)
          (instructionSpace wordBits) + 1) := by
  let initial := DenseOverlay.Snapshot.initial input
  let final := initial.run program input fuel
  let initPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = executionInput input ∧ work = executionWork spec input initial ∧
        out = natTape 0
  let loopPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = executionInput input ∧ work = executionWork spec input final ∧
        out = natTape 1
  let outputPost : TM.TapePred (workTapeCount spec) :=
    fun inp work out =>
      inp = executionInput input ∧ work = executionWork spec input final ∧
        out = Machine.registerVerdictOutput
          (DenseOverlay.read input final.overlay 0)
  have hcanonical := DenseOverlay.Snapshot.initial_canonical input
  have hcovered :=
    DenseOverlay.FixedRegisters.Footprint.Snapshot.initial_covered
      (input := input) spec.zero_mem
  have htrace :
      ∀ k, k ≤ fuel →
        SnapshotBound spec input (initial.run program input k) wordBits := by
    intro k hk address haddress
    have hvalid := DenseOverlay.Snapshot.run_valid program input k initial
      (by simpa only [initial] using
        DenseOverlay.Snapshot.initial_valid input)
    have hdense := hbound k hk
    exact denseSnapshotBound_read_bitlen_le_internal hvalid hdense
  have hpctrace :
      ∀ k, k ≤ fuel →
        (initial.run program input k).pc.size ≤ wordBits := by
    intro k hk
    exact (hbound k hk).pcWidth
  have hloopCombined :=
    programLoopTM_hoareSpaceOutput_from_internal spec input wordBits
      fuel initial hcanonical hcovered
      (by simpa only [initial] using hhalted) htrace hpctrace
  have hloopSpace :
      (programLoopTM spec).HoareSpace initPost input.length
        (instructionSpace wordBits) := by
    intro inp work out hpre cfg hreach
    exact
      (hloopCombined inp work out (by simpa [initPost] using hpre)
        cfg hreach).1
  have hloopOutput :
      HoareOutputHead (programLoopTM spec) initPost
        (instructionSpace wordBits + 1) := by
    intro inp work out hpre cfg hreach
    exact
      (hloopCombined inp work out (by simpa [initPost] using hpre)
        cfg hreach).2
  obtain ⟨loopTime, hloopReach⟩ :=
    programLoopTM_reaches_run_internal spec input fuel initial
      hcanonical hcovered (by simpa only [initial] using hhalted)
  have hloopTime :
      (programLoopTM spec).HoareTime initPost loopPost loopTime := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    let done :
        Complexity.Cfg (workTapeCount spec) (programLoopTM spec).Q :=
      { state := (programLoopTM spec).qhalt
        input := executionInput input
        work := executionWork spec input final
        output := natTape 1 }
    refine ⟨done, loopTime, le_rfl, ?_, rfl, rfl, rfl, rfl⟩
    simpa [initial, final, done] using hloopReach
  have hloop := hloopTime.and_hoareSpace hloopSpace
  have houtputTime :=
    programOutputTM_hoareTime_internal spec input final
  have houtputBase := houtputTime.toHoareTimeSpace
    (inputLength := input.length) (initialSpace := 1) (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      constructor
      · intro i
        rw [executionWork_head_internal spec input final i]
      · simp [executionInput, Tape.move])
  have houtput :
      (programOutputTM spec).HoareTimeSpace loopPost outputPost 1
        input.length (instructionSpace wordBits) := by
    apply houtputBase.consequence
    · exact fun _ _ _ hpre => by simpa [loopPost] using hpre
    · exact fun _ _ _ hpost => by simpa [outputPost] using hpost
    · exact le_rfl
    · exact le_rfl
    · unfold instructionSpace
      omega
  have hloopTransition :
      ∀ inp work out, loopPost inp work out →
        loopPost (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
      (executionInput_parked input).read_ne_start
      (fun i =>
        (executionWork_parked_internal spec input final i).read_ne_start)
      (natTape_parked_internal 1).read_ne_start
    rw [htransition.1, htransition.2.1, htransition.2.2]
    exact ⟨rfl, rfl, rfl⟩
  have htail := TM.seqTM_hoareTimeSpace
    (programLoopTM spec) (programOutputTM spec)
    hloop hloopTransition houtput
  have houtputOutput :
      HoareOutputHead (programOutputTM spec) loopPost 1 := by
    apply hoareOutputHead_of_transducer_hoareTime_internal
      (programOutputTM_isTransducer_internal spec) houtputTime
    intro inp work out hpost
    rw [hpost.2.2]
    simp [Machine.registerVerdictOutput, Tape.move, Tape.writeAndMove,
      Tape.write_head, TM.idleDir, Tape.read, Tape.init]
  have htailOutputRaw := seqTM_hoareOutputHead_internal
    (programLoopTM spec) (programOutputTM spec)
    hloopTime hloopTransition houtputTime hloopOutput houtputOutput
  have hone : 1 ≤ instructionSpace wordBits + 1 := by omega
  have htailOutput :
      HoareOutputHead
        (TM.seqTM (programLoopTM spec) (programOutputTM spec))
        initPost (instructionSpace wordBits + 1) := by
    simpa [max_eq_left hone] using htailOutputRaw
  have hinitialize :=
    executionInitializeTM_hoareTimeSpace_internal spec input
  have hinitTransition :
      ∀ inp work out, initPost inp work out →
        initPost (TM.transitionInput inp)
          (fun i => TM.transitionTape (work i))
          (TM.transitionTape out) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
      (executionInput_parked input).read_ne_start
      (fun i =>
        (executionWork_parked_internal spec input initial i).read_ne_start)
      (natTape_parked_internal 0).read_ne_start
    rw [htransition.1, htransition.2.1, htransition.2.2]
    exact ⟨rfl, rfl, rfl⟩
  have hfull := TM.seqTM_hoareTimeSpace
    (executionInitializeTM spec)
    (TM.seqTM (programLoopTM spec) (programOutputTM spec))
    hinitialize hinitTransition htail
  have hinitOutput :
      HoareOutputHead (executionInitializeTM spec)
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
            work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        1 := by
    apply hoareOutputHead_of_transducer_hoareTime_internal
      (executionInitializeTM_isTransducer_internal spec) hinitialize.1
    intro inp work out hpost
    rw [hpost.2.2]
    simp [natTape, Tape.move]
  have hfullOutputRaw := seqTM_hoareOutputHead_internal
    (executionInitializeTM spec)
    (TM.seqTM (programLoopTM spec) (programOutputTM spec))
    hinitialize.1 hinitTransition htail.1 hinitOutput htailOutput
  have hfullOutputSmall :
      HoareOutputHead (programTM spec)
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
            work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (instructionSpace wordBits + 1) := by
    simpa [programTM, max_eq_right hone] using hfullOutputRaw
  have hfullOutput := hfullOutputSmall.mono_internal
    (Nat.add_le_add_right (le_max_right
      (initializeSpace spec input.length) (instructionSpace wordBits)) 1)
  refine
    ⟨(initializeTime spec input.length + 1 + (input.length + 3)) + 1 +
        (loopTime + 1 + 1), ?_, hfullOutput⟩
  simpa [programTM, initial, final, initPost, loopPost, outputPost] using
    hfull

/-- A fixed direct-register compiler decides every language whose dense
execution has a length-uniform word-width trace bound. -/
theorem programTM_decidesInSpace_traceBound_internal
    {program : Program} (spec : Spec program) (L : Language)
    (wordBits : ℕ → ℕ)
    (hrun : ∀ input, ∃ fuel,
      let final :=
        (DenseOverlay.Snapshot.initial input).run program input fuel
      final.Halted program ∧
      DenseOverlay.FixedRegisters.TraceBound
        program input fuel spec.allowed.card (wordBits input.length) ∧
      (input ∈ L → DenseOverlay.read input final.overlay 0 = 1) ∧
      (input ∉ L → DenseOverlay.read input final.overlay 0 = 0)) :
    (programTM spec).DecidesInSpace L
      (fun n => max (initializeSpace spec n)
        (instructionSpace (wordBits n))) := by
  apply TM.decidesInSpace_of_hoareSpace
  · intro input
    obtain ⟨fuel, hhalted, hbound, _hyes, _hno⟩ := hrun input
    obtain ⟨_time, hcontract, _houtput⟩ :=
      programTM_contract_traceBound_internal spec input fuel
        (wordBits input.length) hhalted hbound
    exact hcontract.2
  · intro input
    obtain ⟨fuel, hhalted, _hbound, hyes, hno⟩ := hrun input
    obtain ⟨_time, htime⟩ :=
      programTM_hoareTime_run_internal spec input fuel hhalted
    obtain ⟨cfg, _steps, _hsteps, hreach, hhalt, hpost⟩ :=
      htime _ _ _ ⟨rfl, rfl, rfl⟩
    refine
      ⟨cfg, TM.reaches_of_reachesIn hreach, hhalt, ?_, ?_⟩
    · intro hmem
      rw [hpost.2.2,
        Machine.registerVerdictOutput_cell_one_internal, hyes hmem]
      decide
    · intro hnotmem
      rw [hpost.2.2,
        Machine.registerVerdictOutput_cell_one_internal, hno hnotmem]
      rfl
  · intro input cfg hreach
    obtain ⟨fuel, hhalted, hbound, _hyes, _hno⟩ := hrun input
    obtain ⟨_time, _hcontract, houtput⟩ :=
      programTM_contract_traceBound_internal spec input fuel
        (wordBits input.length) hhalted hbound
    exact houtput _ _ _ ⟨rfl, rfl, rfl⟩ cfg hreach

theorem controlPC_val_of_lt_internal {program : Program} {pc : ℕ}
    (hpc : pc < program.length) :
    (controlPC program pc).val = pc := by
  simp [controlPC, Nat.min_eq_left (Nat.le_of_lt hpc)]

theorem controlPC_val_of_ge_internal {program : Program} {pc : ℕ}
    (hpc : program.length ≤ pc) :
    (controlPC program pc).val = program.length := by
  simp [controlPC, Nat.min_eq_right hpc]

end Internal

end FixedRegisterMachine
end RAM
end Complexity
