/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInitDefs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Internal
import Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength

/-!
# Dense-overlay public-input initialization -- proofs
-/

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem parked_of_binaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem resetBinaryBlank_hasBinaryNat_zero :
    TM.resetBinaryBlank.HasBinaryNat 0 := by
  simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0

private theorem resetBinaryBlank_parked : TM.Parked TM.resetBinaryBlank :=
  parked_of_binaryNat resetBinaryBlank_hasBinaryNat_zero

private theorem denseProgramInitialStore_eq (input : List Bool) :
    denseProgramInitialStore input = [(0, input.length + 1)] := by
  simp [denseProgramInitialStore, DenseOverlay.Snapshot.initial,
    DenseOverlay.write, RegisterStore.write]

private theorem rewindInputTM_step_preserves_space
    {inputLength space : ℕ}
    {c c' : Complexity.Cfg n (TM.rewindInputTM (n := n)).Q}
    (hstep : (TM.rewindInputTM (n := n)).step c = some c')
    (hspace : c.WithinAuxSpace inputLength space)
    (hinput : c.input.StartInvariant)
    (hwork : ∀ i, TM.Parked (c.work i))
    (houtput : TM.Parked c.output) :
    c'.WithinAuxSpace inputLength space ∧
      c'.input.StartInvariant ∧
      (∀ i, TM.Parked (c'.work i)) ∧ TM.Parked c'.output := by
  have hne := TM.state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg hne] at hstep
  cases hstate : c.state with
  | moveLeft =>
      simp only [TM.rewindInputTM, hstate] at hstep
      split at hstep <;> rename_i hread
      · cases Option.some.inj hstep
        have hhead : c.input.head = 0 := by
          by_contra h
          exact hinput.2 c.input.head (by omega)
            (by rwa [Tape.read] at hread)
        have hworkEq :
            (fun i => (c.work i).writeAndMove
              (TM.readBackWrite (c.work i).read).toΓ
              (TM.idleDir (c.work i).read)) = c.work := by
          funext i
          exact (hwork i).writeAndMove_readBack_idle
        have houtputEq := houtput.writeAndMove_readBack_idle
        rw [hworkEq, houtputEq]
        refine ⟨⟨hspace.1, ?_⟩, hinput.move Dir3.right,
          hwork, houtput⟩
        simp [Tape.move, hhead]
      · cases Option.some.inj hstep
        have hworkEq :
            (fun i => (c.work i).writeAndMove
              (TM.readBackWrite (c.work i).read).toΓ
              (TM.idleDir (c.work i).read)) = c.work := by
          funext i
          exact (hwork i).writeAndMove_readBack_idle
        have houtputEq := houtput.writeAndMove_readBack_idle
        rw [hworkEq, houtputEq]
        refine ⟨⟨hspace.1, ?_⟩,
          hinput.move (TM.moveLeftDir c.input.read), hwork, houtput⟩
        simpa [TM.moveLeftDir, hread, Tape.move] using
          le_trans (Nat.sub_le c.input.head 1) hspace.2
  | moveRight =>
      simp only [TM.rewindInputTM, hstate] at hstep
      cases Option.some.inj hstep
      have hworkEq :
          (fun i => (c.work i).writeAndMove
            (TM.readBackWrite (c.work i).read).toΓ
            (TM.idleDir (c.work i).read)) = c.work := by
        funext i
        exact (hwork i).writeAndMove_readBack_idle
      have houtputEq := houtput.writeAndMove_readBack_idle
      rw [hworkEq, houtputEq]
      refine ⟨⟨hspace.1, ?_⟩,
        hinput.move (TM.idleDir c.input.read), hwork, houtput⟩
      by_cases hread : c.input.read = Γ.start
      · have hhead : c.input.head = 0 := by
          by_contra h
          exact hinput.2 c.input.head (by omega)
            (by rwa [Tape.read] at hread)
        simp [TM.idleDir, hread, Tape.move, hhead]
      · simpa [TM.idleDir, hread, Tape.move] using hspace.2
  | done => exact (hne hstate).elim

private theorem rewindInputTM_reachesIn_withinAuxSpace
    {inputLength space time : ℕ}
    {start current : Complexity.Cfg n (TM.rewindInputTM (n := n)).Q}
    (hspace : start.WithinAuxSpace inputLength space)
    (hinput : start.input.StartInvariant)
    (hwork : ∀ i, TM.Parked (start.work i))
    (houtput : TM.Parked start.output)
    (hreach : (TM.rewindInputTM (n := n)).reachesIn time start current) :
    current.WithinAuxSpace inputLength space := by
  induction hreach with
  | zero => exact hspace
  | step hstep _hrest ih =>
      have hnext := rewindInputTM_step_preserves_space hstep hspace
        hinput hwork houtput
      exact ih hnext.1 hnext.2.1 hnext.2.2.1 hnext.2.2.2

private def denseLengthPost (tapes : ControlInstructionTapes n)
    (input : List Bool) : TapePred (n + 1) :=
  fun inp work out =>
    inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
    inp.head = input.length + 1 ∧
    (work tapes.liftedLhs).HasBinaryNat input.length ∧
    (∀ i, i ≠ tapes.liftedLhs → work i = TM.resetBinaryBlank) ∧
    out = TM.resetBinaryBlank

private def denseTagPost (tapes : ControlInstructionTapes n)
    (input : List Bool) : TapePred (n + 1) :=
  fun inp work out =>
    inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
    inp.head = input.length + 1 ∧
    (work tapes.liftedLhs).HasBinaryNat (input.length + 1) ∧
    (∀ i, i ≠ tapes.liftedLhs → work i = TM.resetBinaryBlank) ∧
    out = TM.resetBinaryBlank

private def denseEmitPre (tapes : ControlInstructionTapes n)
    (input : List Bool) : TapePred (n + 1) :=
  fun inp work out =>
    inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
    inp.head = input.length + 1 ∧
    InitialLoopReady tapes (input.length + 1) 0 [] work ∧
    (work tapes.buffer).cells 0 = Γ.start ∧
    out = TM.resetBinaryBlank

private def denseAbiPre (tapes : ControlInstructionTapes n)
    (input : List Bool) : TapePred (n + 1) :=
  fun inp work out =>
    inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
    inp.head = input.length + 1 ∧
    InitialLoopReady tapes (input.length + 1)
      (denseProgramInitialStore input).length
      (denseProgramInitialStore input) work ∧
    (work tapes.buffer).cells 0 = Γ.start ∧
    out = TM.resetBinaryBlank

private def denseRewindPre (tapes : ControlInstructionTapes n)
    (input : List Bool) : TapePred (n + 1) :=
  fun inp work out =>
    inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
    inp.head = input.length + 1 ∧
    work = denseProgramSnapshotWork tapes
      (DenseOverlay.Snapshot.initial input) ∧
    out = TM.resetBinaryBlank

private def denseInitPost (tapes : ControlInstructionTapes n)
    (input : List Bool) : TapePred (n + 1) :=
  fun inp work out =>
    inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
    work = denseProgramSnapshotWork tapes
      (DenseOverlay.Snapshot.initial input) ∧
    out = TM.resetBinaryBlank

private theorem denseProgramInitSpace_one (inputLength : ℕ) :
    1 ≤ denseProgramInitSpace inputLength := by
  unfold denseProgramInitSpace
  omega

private theorem denseProgramInitSpace_three (inputLength : ℕ) :
    3 ≤ denseProgramInitSpace inputLength := by
  unfold denseProgramInitSpace
  omega

private theorem binaryLengthSpace_le_denseProgramInitSpace
    (inputLength : ℕ) :
    TM.binaryLengthSpace inputLength ≤
      denseProgramInitSpace inputLength := by
  have hsize : inputLength.size ≤ (inputLength + 1).size :=
    Nat.size_le_size (by omega)
  unfold TM.binaryLengthSpace denseProgramInitSpace bitlen
  omega

private theorem binarySuccSpace_le_denseProgramInitSpace
    (inputLength : ℕ) :
    1 + TM.binarySuccTime inputLength ≤
      denseProgramInitSpace inputLength := by
  have htime := TM.binarySuccTime_le inputLength
  have hsize : inputLength.size ≤ (inputLength + 1).size :=
    Nat.size_le_size (by omega)
  unfold denseProgramInitSpace bitlen
  omega

private theorem denseLengthEmitSpace_le (input : List Bool) :
    1 + (rewindEntryEncodeRestoreTime (0, input.length + 1) + 1 +
      TM.binarySuccTime 0) ≤ denseProgramInitSpace input.length := by
  simp [denseProgramInitSpace, rewindEntryEncodeRestoreTime,
    rewindEntryEncodeTime, rewindWordEncodeTime, wordEncodeTime,
    TM.binarySuccTime, BinarySucc.steps, bitlen,
    ← Nat.size_eq_bits_len]
  ring_nf
  have hpos : 0 < (input.length + 1).bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_pos.mpr (by omega)
  have hpos' : 0 < (1 + input.length).bits.length := by
    simpa [Nat.add_comm] using hpos
  omega

private theorem denseAbiInstallSpace_le
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    ((denseProgramInitialStore input).flatMap Entry.encode).length + 1 +
        initialAbiInstallTime tapes (denseProgramInitialStore input)
          (input.length + 1) ≤
      denseProgramInitSpace input.length := by
  have hne : tapes.lifted.data.rhs ≠ tapes.liftedLhs :=
    tapes.lifted.data.ne (by decide)
  simp [denseProgramInitSpace, initialAbiInstallTime,
    denseProgramInitialStore, DenseOverlay.Snapshot.initial,
    DenseOverlay.write, RegisterStore.write, TM.binaryCopyTime,
    TM.clearWorkTimeBound, TM.binaryRippleAddTime,
    TM.resetBinaryWorkTime, TM.resetBinaryWorkManyTime,
    initialCleanupBits, initialCleanupTargets, Entry.encode,
    WordCode.encode, Nat.length_toBitsLE, bitlen, hne,
    ← Nat.size_eq_bits_len]
  clear hne tapes
  ring_nf
  have hpos : 0 < (input.length + 1).bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_pos.mpr (by omega)
  have hpos' : 0 < (1 + input.length).bits.length := by
    simpa [Nat.add_comm] using hpos
  omega

/-- Any all-prefix serialized trace budget already dominates the width needed
to install the initial dense snapshot, up to a fixed factor. -/
theorem denseProgramInitSpace_le_of_traceFits_internal
    {program : Program} {input : List Bool} {fuel bound : ℕ}
    (hfits : DenseOverlay.TraceFits program input fuel bound) :
    denseProgramInitSpace input.length ≤ 32 * bound := by
  have hwidth := hfits.initial_width
  unfold denseProgramInitSpace
  omega

private theorem initialLoopReady_withinAuxSpace
    {Q : Type} (tapes : ControlInstructionTapes n)
    {address count inputLength space : ℕ} {entries : Store}
    {inp : Tape} {work : Fin (n + 1) → Tape} {out : Tape} {state : Q}
    (hready : InitialLoopReady tapes address count entries work)
    (hone : 1 ≤ space)
    (hbuffer : (entries.flatMap Entry.encode).length + 1 ≤ space)
    (hinput : inp.head ≤ inputLength + space + 1) :
    ({ state := state, input := inp, work := work, output := out } :
      Complexity.Cfg (n + 1) Q).WithinAuxSpace inputLength space := by
  refine ⟨?_, hinput⟩
  intro i
  by_cases hlhs : i = tapes.liftedLhs
  · subst i
    rw [hready.address.2.1]
    exact hone
  by_cases hrhs : i = tapes.lifted.data.rhs
  · subst i
    rw [hready.value.2.1]
    exact hone
  by_cases hcount : i = tapes.lifted.data.update.remaining
  · subst i
    rw [hready.count.2.1]
    exact hone
  by_cases hbuf : i = tapes.buffer
  · subst i
    rw [hready.buffer.1]
    exact hbuffer
  change (work i).head ≤ space
  rw [hready.frame i hlhs hrhs hcount hbuf]
  simpa [TM.resetBinaryBlank, Tape.move] using hone

private theorem denseProgramSnapshotWork_parked
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    ∀ i, TM.Parked
      (denseProgramSnapshotWork tapes
        (DenseOverlay.Snapshot.initial input) i) := by
  let sparseInitial : Snapshot :=
    { pc := 0, store := denseProgramInitialStore input }
  have hsparseCanonical : Canonical sparseInitial.store := by
    simpa [sparseInitial, denseProgramInitialStore] using
      DenseOverlay.Snapshot.initial_canonical input
  have hready : InstructionExecutionReady tapes sparseInitial.store 0
      (programSnapshotWork tapes sparseInitial) :=
    programSnapshotWork_ready_internal tapes sparseInitial hsparseCanonical
  intro i
  simpa [denseProgramSnapshotWork, sparseInitial] using
    hready.control.lookup.scanner.parked i

private theorem denseProgramSnapshotWork_head_le
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    ∀ i, (denseProgramSnapshotWork tapes
      (DenseOverlay.Snapshot.initial input) i).head ≤
        denseProgramInitSpace input.length := by
  intro i
  have hhead :
      (denseProgramSnapshotWork tapes
        (DenseOverlay.Snapshot.initial input) i).head = 1 := by
    unfold denseProgramSnapshotWork programSnapshotWork
    by_cases hpc : i = tapes.liftedPC
    · subst i
      rw [Function.update_self]
      simp [programBinaryTape, Tape.move]
    rw [Function.update_of_ne hpc]
    by_cases hresult : i = tapes.lifted.data.update.resultCount
    · subst i
      rw [Function.update_self]
      simp [programBinaryTape, Tape.move]
    rw [Function.update_of_ne hresult]
    by_cases hremaining : i = tapes.lifted.data.update.remaining
    · subst i
      rw [Function.update_self]
      simp [programBinaryTape, Tape.move]
    rw [Function.update_of_ne hremaining]
    by_cases hsource : i = tapes.liftedSource
    · subst i
      rw [Function.update_self]
      simp [programBinaryTape, Tape.move]
    rw [Function.update_of_ne hsource]
    simp [TM.resetBinaryBlank, Tape.move]
  rw [hhead]
  exact denseProgramInitSpace_one input.length

private theorem denseTagTM_hoareTime
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (TM.binarySuccTM tapes.liftedLhs).HoareTime
      (denseLengthPost tapes input) (denseTagPost tapes input)
      (TM.binarySuccTime input.length) := by
  intro inp work out hpre
  have hinputRead : inp.read ≠ Γ.start := by
    rw [Tape.read, hpre.2.1, hpre.1]
    exact Tape.init_ofBool_cells_ne_start input (input.length + 1)
      (by omega)
  have hotherParked :
      ∀ i, i ≠ tapes.liftedLhs → TM.Parked (work i) := by
    intro i hi
    rw [hpre.2.2.2.1 i hi]
    exact resetBinaryBlank_parked
  have houtputParked : TM.Parked out := by
    rw [hpre.2.2.2.2]
    exact resetBinaryBlank_parked
  have hframe := TM.binarySuccTM_hoareTime_frame tapes.liftedLhs
    input.length inp work out hpre.2.2.1 hinputRead
    (fun i hi => (hotherParked i hi).read_ne_start)
    houtputParked.read_ne_start
  obtain ⟨done, time, htime, hreach, hhalt, hinput, hwork,
      hvalue, houtput⟩ := hframe inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, time, htime, hreach, hhalt, ?_⟩
  refine ⟨?_, ?_, hvalue, ?_, ?_⟩
  · rw [hinput]
    exact hpre.1
  · rw [hinput]
    exact hpre.2.1
  · intro i hi
    rw [hwork i hi]
    exact hpre.2.2.2.1 i hi
  · exact houtput.trans hpre.2.2.2.2

private theorem denseSeedTM_hoareTime
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (TM.binarySuccTM tapes.lifted.data.rhs).HoareTime
      (denseTagPost tapes input) (denseEmitPre tapes input)
      (TM.binarySuccTime 0) := by
  intro inp work out hpre
  have hrhsLhs : tapes.lifted.data.rhs ≠ tapes.liftedLhs :=
    tapes.lifted.data.ne (by decide)
  have hrhsZero :
      (work tapes.lifted.data.rhs).HasBinaryNat 0 := by
    rw [hpre.2.2.2.1 _ hrhsLhs]
    exact resetBinaryBlank_hasBinaryNat_zero
  have hinputRead : inp.read ≠ Γ.start := by
    rw [Tape.read, hpre.2.1, hpre.1]
    exact Tape.init_ofBool_cells_ne_start input (input.length + 1)
      (by omega)
  have hotherParked :
      ∀ i, i ≠ tapes.lifted.data.rhs → TM.Parked (work i) := by
    intro i hi
    by_cases hilhs : i = tapes.liftedLhs
    · subst i
      exact parked_of_binaryNat hpre.2.2.1
    · rw [hpre.2.2.2.1 i hilhs]
      exact resetBinaryBlank_parked
  have houtputParked : TM.Parked out := by
    rw [hpre.2.2.2.2]
    exact resetBinaryBlank_parked
  have hframe := TM.binarySuccTM_hoareTime_frame
    tapes.lifted.data.rhs 0 inp work out hrhsZero hinputRead
    (fun i hi => (hotherParked i hi).read_ne_start)
    houtputParked.read_ne_start
  obtain ⟨done, time, htime, hreach, hhalt, hinput, hwork,
      hvalue, houtput⟩ := hframe inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, time, htime, hreach, hhalt, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hinput]
    exact hpre.1
  · rw [hinput]
    exact hpre.2.1
  · have hlhsRhs : tapes.liftedLhs ≠ tapes.lifted.data.rhs :=
      Ne.symm hrhsLhs
    have hlhs :
        (done.work tapes.liftedLhs).HasBinaryNat
          (input.length + 1) := by
      rw [hwork _ hlhsRhs]
      exact hpre.2.2.1
    have hcountLhs :
        tapes.lifted.data.update.remaining ≠ tapes.liftedLhs :=
      tapes.lifted.data.ne (by decide)
    have hcountRhs :
        tapes.lifted.data.update.remaining ≠
          tapes.lifted.data.rhs :=
      tapes.lifted.data.ne (by decide)
    have hbufferLhs : tapes.buffer ≠ tapes.liftedLhs :=
      Ne.symm (tapes.liftedData_ne_buffer 13)
    have hbufferRhs :
        tapes.buffer ≠ tapes.lifted.data.rhs :=
      Ne.symm (tapes.liftedData_ne_buffer 14)
    refine
      { address := hlhs
        value := hvalue
        count := ?_
        buffer := ?_
        parked := ?_
        frame := ?_ }
    · rw [hwork _ hcountRhs, hpre.2.2.2.1 _ hcountLhs]
      exact resetBinaryBlank_hasBinaryNat_zero
    · rw [hwork _ hbufferRhs, hpre.2.2.2.1 _ hbufferLhs]
      simp [TM.resetBinaryBlank, Tape.HasBinaryPrefix, Tape.init,
        Tape.move]
    · intro i
      by_cases hirhs : i = tapes.lifted.data.rhs
      · subst i
        exact parked_of_binaryNat hvalue
      · rw [hwork i hirhs]
        by_cases hilhs : i = tapes.liftedLhs
        · subst i
          exact parked_of_binaryNat hpre.2.2.1
        · rw [hpre.2.2.2.1 i hilhs]
          exact resetBinaryBlank_parked
    · intro i hilhs hirhs _hcount hbuffer
      rw [hwork i hirhs, hpre.2.2.2.1 i hilhs]
  · have hbufferLhs : tapes.buffer ≠ tapes.liftedLhs :=
      Ne.symm (tapes.liftedData_ne_buffer 13)
    have hbufferRhs :
        tapes.buffer ≠ tapes.lifted.data.rhs :=
      Ne.symm (tapes.liftedData_ne_buffer 14)
    rw [hwork _ hbufferRhs, hpre.2.2.2.1 _ hbufferLhs]
    simp [TM.resetBinaryBlank, Tape.move, Tape.init]
  · exact houtput.trans hpre.2.2.2.2

private theorem denseEmitTM_hoareTime
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (initialLengthEmitTM tapes).HoareTime
      (denseEmitPre tapes input) (denseAbiPre tapes input)
      (rewindEntryEncodeRestoreTime (0, input.length + 1) + 1 +
        TM.binarySuccTime 0) := by
  intro inp work out hpre
  have hinputParked : TM.Parked inp := by
    refine ⟨by rw [hpre.2.1]; omega, ?_⟩
    intro j hj
    rw [hpre.1]
    exact Tape.init_ofBool_cells_ne_start input j hj
  have htime := initialLengthEmitTM_hoareTime_internal tapes
    (input.length + 1) 0 [] inp work out hpre.2.2.1
    hinputParked hpre.2.2.2.2
  obtain ⟨done, time, htimeLe, hreach, hhalt, hinput, hready,
      houtput⟩ := htime inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, time, htimeLe, hreach, hhalt, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hinput]
    exact hpre.1
  · rw [hinput]
    exact hpre.2.1
  · rw [denseProgramInitialStore_eq]
    simpa using hready
  · exact TM.work_cells_zero_eq_start_of_reachesIn tapes.buffer
      hreach hpre.2.2.2.1
  · exact houtput.trans hpre.2.2.2.2

private theorem denseAbiTM_hoareTime
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (initialAbiInstallTM tapes).HoareTime
      (denseAbiPre tapes input) (denseRewindPre tapes input)
      (initialAbiInstallTime tapes (denseProgramInitialStore input)
        (input.length + 1)) := by
  intro inp work out hpre
  have hinputParked : TM.Parked inp := by
    refine ⟨by rw [hpre.2.1]; omega, ?_⟩
    intro j hj
    rw [hpre.1]
    exact Tape.init_ofBool_cells_ne_start input j hj
  have htime := initialAbiInstallTM_hoareTime_internal tapes
    (denseProgramInitialStore input) (input.length + 1) inp work out
    hpre.2.2.1 hpre.2.2.2.1 hinputParked hpre.2.2.2.2
  obtain ⟨done, time, htimeLe, hreach, hhalt, hinput, hwork,
      houtput⟩ := htime inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, time, htimeLe, hreach, hhalt, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hinput]
    exact hpre.1
  · rw [hinput]
    exact hpre.2.1
  · simpa [denseProgramSnapshotWork, denseProgramInitialStore] using
      hwork
  · exact houtput.trans hpre.2.2.2.2

private theorem denseRewindTM_hoareTime
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (TM.rewindInputTM (n := n + 1)).HoareTime
      (denseRewindPre tapes input) (denseInitPost tapes input)
      (input.length + 1 + 2) := by
  intro inp work out hpre
  let sparseInitial : Snapshot :=
    { pc := 0, store := denseProgramInitialStore input }
  have hsparseCanonical : Canonical sparseInitial.store := by
    simpa [sparseInitial, denseProgramInitialStore] using
      DenseOverlay.Snapshot.initial_canonical input
  have habiReady : InstructionExecutionReady tapes sparseInitial.store 0
      (programSnapshotWork tapes sparseInitial) :=
    programSnapshotWork_ready_internal tapes sparseInitial
      hsparseCanonical
  have hworkEq :
      work = programSnapshotWork tapes sparseInitial := by
    simpa [denseProgramSnapshotWork, sparseInitial] using
      hpre.2.2.1
  have houtputParked : TM.Parked out := by
    rw [hpre.2.2.2]
    exact resetBinaryBlank_parked
  have hframe := TM.rewindInputTM_hoareTime_frame
    (n := n + 1) (input.length + 1)
    (P := fun inp work out =>
      inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
      work = denseProgramSnapshotWork tapes
        (DenseOverlay.Snapshot.initial input) ∧
      out = TM.resetBinaryBlank)
    (by
      intro inp work out inp' work' out' hP hcells _hhead hwork' hout'
      exact ⟨hcells.trans hP.1,
        hwork'.trans hP.2.1, hout'.trans hP.2.2⟩)
  have hframePre :
      inp.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
      inp.head ≤ input.length + 1 ∧
      out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
      (∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
      (inp.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
        work = denseProgramSnapshotWork tapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = TM.resetBinaryBlank) := by
    refine ⟨?_, ?_, by rw [hpre.2.1],
      houtputParked.read_ne_start, houtputParked.1, ?_,
      hpre.1, hpre.2.2.1, hpre.2.2.2⟩
    · rw [hpre.1]
      simp [Tape.init]
    · intro j hj
      rw [hpre.1]
      exact Tape.init_ofBool_cells_ne_start input j hj
    · intro i
      rw [hworkEq]
      have hi := habiReady.control.lookup.scanner.parked i
      exact ⟨hi.read_ne_start, hi.1⟩
  obtain ⟨done, time, htime, hreach, hhalt, hhead, hP⟩ :=
    hframe inp work out hframePre
  refine ⟨done, time, htime, hreach, hhalt, ?_⟩
  refine ⟨?_, hP.2.1, hP.2.2⟩
  exact Tape.ext (by simpa [Tape.move] using hhead)
    (by simpa [Tape.move] using hP.1)

private theorem phaseTransition_preserves_of_parked
    {P : TapePred n}
    (hparked : ∀ inp work out, P inp work out →
      TM.Parked inp ∧ (∀ i, TM.Parked (work i)) ∧ TM.Parked out) :
    ∀ inp work out, P inp work out →
      P (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i))
        (TM.transitionTape out) := by
  intro inp work out hpre
  obtain ⟨hinputParked, hworkParked, houtputParked⟩ :=
    hparked inp work out hpre
  obtain ⟨hinput, hwork, houtput⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hinputParked.read_ne_start
      (fun i => (hworkParked i).read_ne_start)
      houtputParked.read_ne_start
  simpa only [hinput, hwork, houtput] using hpre

/-- Dense public-input initialization satisfies its exact endpoint contract
and an honest all-reachable width bound. -/
theorem denseProgramInitTM_hoareTimeSpace_internal
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (denseProgramInitTM tapes).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork tapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = TM.resetBinaryBlank)
      (denseProgramInitTime tapes input) input.length
      (denseProgramInitSpace input.length) := by
  have hlengthBase :=
    TM.binaryLengthTM_hoareTimeSpace tapes.liftedLhs input
  have hlength :
      (TM.binaryLengthTM tapes.liftedLhs).HoareTimeSpace
        (fun inp work out =>
          inp = Tape.init (input.map Γ.ofBool) ∧
          work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (denseLengthPost tapes input)
        (TM.binaryLengthTime input.length) input.length
        (denseProgramInitSpace input.length) := by
    apply hlengthBase.consequence
    · intro inp work out hpre
      exact hpre
    · intro inp work out hpost
      simpa [denseLengthPost, TM.resetBinaryBlank] using hpost
    · exact le_rfl
    · exact le_rfl
    · exact binaryLengthSpace_le_denseProgramInitSpace input.length
  have htagBase :
      (TM.binarySuccTM tapes.liftedLhs).HoareTimeSpace
        (denseLengthPost tapes input) (denseTagPost tapes input)
        (TM.binarySuccTime input.length) input.length
        (1 + TM.binarySuccTime input.length) := by
    apply (denseTagTM_hoareTime tapes input).toHoareTimeSpace
    intro inp work out hpre
    refine ⟨?_, ?_⟩
    · intro i
      change (work i).head ≤ 1
      by_cases hi : i = tapes.liftedLhs
      · subst i
        rw [hpre.2.2.1.2.1]
      · rw [hpre.2.2.2.1 i hi]
        simp [TM.resetBinaryBlank, Tape.move]
    · rw [hpre.2.1]
      omega
  have htag :
      (TM.binarySuccTM tapes.liftedLhs).HoareTimeSpace
        (denseLengthPost tapes input) (denseTagPost tapes input)
        (TM.binarySuccTime input.length) input.length
        (denseProgramInitSpace input.length) := by
    exact htagBase.consequence
      (fun _ _ _ hpre => hpre) (fun _ _ _ hpost => hpost)
      le_rfl le_rfl
      (binarySuccSpace_le_denseProgramInitSpace input.length)
  have hseedBase :
      (TM.binarySuccTM tapes.lifted.data.rhs).HoareTimeSpace
        (denseTagPost tapes input) (denseEmitPre tapes input)
        (TM.binarySuccTime 0) input.length
        (1 + TM.binarySuccTime 0) := by
    apply (denseSeedTM_hoareTime tapes input).toHoareTimeSpace
    intro inp work out hpre
    refine ⟨?_, ?_⟩
    · intro i
      change (work i).head ≤ 1
      by_cases hi : i = tapes.liftedLhs
      · subst i
        rw [hpre.2.2.1.2.1]
      · rw [hpre.2.2.2.1 i hi]
        simp [TM.resetBinaryBlank, Tape.move]
    · rw [hpre.2.1]
      omega
  have hseedSpace :
      1 + TM.binarySuccTime 0 ≤
        denseProgramInitSpace input.length := by
    have htime := TM.binarySuccTime_le 0
    have hthree := denseProgramInitSpace_three input.length
    simp at htime
    omega
  have hseed :
      (TM.binarySuccTM tapes.lifted.data.rhs).HoareTimeSpace
        (denseTagPost tapes input) (denseEmitPre tapes input)
        (TM.binarySuccTime 0) input.length
        (denseProgramInitSpace input.length) := by
    exact hseedBase.consequence
      (fun _ _ _ hpre => hpre) (fun _ _ _ hpost => hpost)
      le_rfl le_rfl hseedSpace
  have hemitBase :
      (initialLengthEmitTM tapes).HoareTimeSpace
        (denseEmitPre tapes input) (denseAbiPre tapes input)
        (rewindEntryEncodeRestoreTime (0, input.length + 1) + 1 +
          TM.binarySuccTime 0)
        input.length
        (1 + (rewindEntryEncodeRestoreTime
          (0, input.length + 1) + 1 + TM.binarySuccTime 0)) := by
    apply (denseEmitTM_hoareTime tapes input).toHoareTimeSpace
    intro inp work out hpre
    apply initialLoopReady_withinAuxSpace tapes hpre.2.2.1
    · exact le_rfl
    · simp
    · rw [hpre.2.1]
      omega
  have hemit :
      (initialLengthEmitTM tapes).HoareTimeSpace
        (denseEmitPre tapes input) (denseAbiPre tapes input)
        (rewindEntryEncodeRestoreTime (0, input.length + 1) + 1 +
          TM.binarySuccTime 0)
        input.length (denseProgramInitSpace input.length) := by
    exact hemitBase.consequence
      (fun _ _ _ hpre => hpre) (fun _ _ _ hpost => hpost)
      le_rfl le_rfl (denseLengthEmitSpace_le input)
  have habiBase :
      (initialAbiInstallTM tapes).HoareTimeSpace
        (denseAbiPre tapes input) (denseRewindPre tapes input)
        (initialAbiInstallTime tapes (denseProgramInitialStore input)
          (input.length + 1))
        input.length
        (((denseProgramInitialStore input).flatMap Entry.encode).length +
          1 + initialAbiInstallTime tapes
            (denseProgramInitialStore input) (input.length + 1)) := by
    apply (denseAbiTM_hoareTime tapes input).toHoareTimeSpace
    intro inp work out hpre
    apply initialLoopReady_withinAuxSpace tapes hpre.2.2.1
    · omega
    · exact le_rfl
    · rw [hpre.2.1]
      omega
  have habi :
      (initialAbiInstallTM tapes).HoareTimeSpace
        (denseAbiPre tapes input) (denseRewindPre tapes input)
        (initialAbiInstallTime tapes (denseProgramInitialStore input)
          (input.length + 1))
        input.length (denseProgramInitSpace input.length) := by
    exact habiBase.consequence
      (fun _ _ _ hpre => hpre) (fun _ _ _ hpost => hpost)
      le_rfl le_rfl (denseAbiInstallSpace_le tapes input)
  have hrewindSpace :
      (TM.rewindInputTM (n := n + 1)).HoareSpace
        (denseRewindPre tapes input) input.length
        (denseProgramInitSpace input.length) := by
    intro inp work out hpre current hreach
    have hstart :
        ({ state := (TM.rewindInputTM (n := n + 1)).qstart,
           input := inp, work := work, output := out } :
          Complexity.Cfg (n + 1)
            (TM.rewindInputTM (n := n + 1)).Q).WithinAuxSpace
          input.length (denseProgramInitSpace input.length) := by
      refine ⟨?_, ?_⟩
      · intro i
        rw [hpre.2.2.1]
        exact denseProgramSnapshotWork_head_le tapes input i
      · rw [hpre.2.1]
        have hone := denseProgramInitSpace_one input.length
        omega
    have hinput : inp.StartInvariant := by
      refine ⟨?_, ?_⟩
      · rw [hpre.1]
        simp [Tape.init]
      · intro j hj
        rw [hpre.1]
        exact Tape.init_ofBool_cells_ne_start input j hj
    have hwork : ∀ i, TM.Parked (work i) := by
      intro i
      rw [hpre.2.2.1]
      exact denseProgramSnapshotWork_parked tapes input i
    have houtput : TM.Parked out := by
      rw [hpre.2.2.2]
      exact resetBinaryBlank_parked
    obtain ⟨time, hreachIn⟩ :=
      (TM.rewindInputTM (n := n + 1)).reaches_to_reachesIn hreach
    exact rewindInputTM_reachesIn_withinAuxSpace
      hstart hinput hwork houtput hreachIn
  have hrewind :
      (TM.rewindInputTM (n := n + 1)).HoareTimeSpace
        (denseRewindPre tapes input) (denseInitPost tapes input)
        (input.length + 1 + 2) input.length
        (denseProgramInitSpace input.length) :=
    (denseRewindTM_hoareTime tapes input).and_hoareSpace
      hrewindSpace
  have htransitionLength :=
    phaseTransition_preserves_of_parked
      (P := denseLengthPost tapes input) (by
        intro inp work out hpre
        refine ⟨?_, ?_, ?_⟩
        · refine ⟨by rw [hpre.2.1]; omega, ?_⟩
          intro j hj
          rw [hpre.1]
          exact Tape.init_ofBool_cells_ne_start input j hj
        · intro i
          by_cases hi : i = tapes.liftedLhs
          · subst i
            exact parked_of_binaryNat hpre.2.2.1
          · rw [hpre.2.2.2.1 i hi]
            exact resetBinaryBlank_parked
        · rw [hpre.2.2.2.2]
          exact resetBinaryBlank_parked)
  have htransitionTag :=
    phaseTransition_preserves_of_parked
      (P := denseTagPost tapes input) (by
        intro inp work out hpre
        refine ⟨?_, ?_, ?_⟩
        · refine ⟨by rw [hpre.2.1]; omega, ?_⟩
          intro j hj
          rw [hpre.1]
          exact Tape.init_ofBool_cells_ne_start input j hj
        · intro i
          by_cases hi : i = tapes.liftedLhs
          · subst i
            exact parked_of_binaryNat hpre.2.2.1
          · rw [hpre.2.2.2.1 i hi]
            exact resetBinaryBlank_parked
        · rw [hpre.2.2.2.2]
          exact resetBinaryBlank_parked)
  have htransitionEmit :=
    phaseTransition_preserves_of_parked
      (P := denseEmitPre tapes input) (by
        intro inp work out hpre
        refine ⟨?_, hpre.2.2.1.parked, ?_⟩
        · refine ⟨by rw [hpre.2.1]; omega, ?_⟩
          intro j hj
          rw [hpre.1]
          exact Tape.init_ofBool_cells_ne_start input j hj
        · rw [hpre.2.2.2.2]
          exact resetBinaryBlank_parked)
  have htransitionAbi :=
    phaseTransition_preserves_of_parked
      (P := denseAbiPre tapes input) (by
        intro inp work out hpre
        refine ⟨?_, hpre.2.2.1.parked, ?_⟩
        · refine ⟨by rw [hpre.2.1]; omega, ?_⟩
          intro j hj
          rw [hpre.1]
          exact Tape.init_ofBool_cells_ne_start input j hj
        · rw [hpre.2.2.2.2]
          exact resetBinaryBlank_parked)
  have htransitionRewind :=
    phaseTransition_preserves_of_parked
      (P := denseRewindPre tapes input) (by
        intro inp work out hpre
        refine ⟨?_, ?_, ?_⟩
        · refine ⟨by rw [hpre.2.1]; omega, ?_⟩
          intro j hj
          rw [hpre.1]
          exact Tape.init_ofBool_cells_ne_start input j hj
        · intro i
          rw [hpre.2.2.1]
          exact denseProgramSnapshotWork_parked tapes input i
        · rw [hpre.2.2.2]
          exact resetBinaryBlank_parked)
  have habiRewind := TM.seqTM_hoareTimeSpace
    (initialAbiInstallTM tapes) (TM.rewindInputTM (n := n + 1))
    habi htransitionRewind hrewind
  have hemitTail := TM.seqTM_hoareTimeSpace
    (initialLengthEmitTM tapes)
    (TM.seqTM (initialAbiInstallTM tapes)
      (TM.rewindInputTM (n := n + 1)))
    hemit htransitionAbi habiRewind
  have hseedTail := TM.seqTM_hoareTimeSpace
    (TM.binarySuccTM tapes.lifted.data.rhs)
    (TM.seqTM (initialLengthEmitTM tapes)
      (TM.seqTM (initialAbiInstallTM tapes)
        (TM.rewindInputTM (n := n + 1))))
    hseed htransitionEmit hemitTail
  have htagTail := TM.seqTM_hoareTimeSpace
    (TM.binarySuccTM tapes.liftedLhs)
    (TM.seqTM (TM.binarySuccTM tapes.lifted.data.rhs)
      (TM.seqTM (initialLengthEmitTM tapes)
        (TM.seqTM (initialAbiInstallTM tapes)
          (TM.rewindInputTM (n := n + 1)))))
    htag htransitionTag hseedTail
  have hfull := TM.seqTM_hoareTimeSpace
    (TM.binaryLengthTM tapes.liftedLhs)
    (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
      (TM.seqTM (TM.binarySuccTM tapes.lifted.data.rhs)
        (TM.seqTM (initialLengthEmitTM tapes)
          (TM.seqTM (initialAbiInstallTM tapes)
            (TM.rewindInputTM (n := n + 1))))))
    hlength htransitionLength htagTail
  simpa only [denseProgramInitTM, denseProgramInitTime, denseInitPost,
    max_self] using hfull

/-- Forgetting the all-prefix space component recovers the exact initializer
time contract. -/
theorem denseProgramInitTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (denseProgramInitTM tapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork tapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = TM.resetBinaryBlank)
      (denseProgramInitTime tapes input) :=
  (denseProgramInitTM_hoareTimeSpace_internal tapes input).toHoareTime

end Machine
end RegisterStore
end RAM
end Complexity
