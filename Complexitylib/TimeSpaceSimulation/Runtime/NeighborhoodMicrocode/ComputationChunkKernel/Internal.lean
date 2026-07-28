/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ComputationChunkKernel.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineBranch
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedComputationKernel

/-!
# Fixed computation-chunk provider -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ComputationChunkKernel
namespace Internal

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

private theorem digitBase_eq_two_pow_chunkBits
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Representation.digitBase instanceData =
      2 ^
        PrimeGrouped.Logarithmic.chunkBits
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) := by
  unfold Representation.digitBase CandidateParameters.domainSize
    PrimeGrouped.Logarithmic.domainSize
  rw [Representation.payloadWidth_eq_booleanWidth instanceData]
  rfl

private theorem assignmentCount_eq_power
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    CombineValue.assignmentCount
        (NeighborhoodExecutableEvaluation.payloadWidth
          tm instanceData.blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) =
      Representation.digitBase instanceData ^
        assignmentDigitCount instanceData := by
  rw [digitBase_eq_two_pow_chunkBits instanceData]
  unfold CombineValue.assignmentCount assignmentDigitCount
  rw [← Nat.pow_mul]
  congr 1
  ac_rfl

private theorem countLoop_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base exponent accumulator : ℕ)
    (hbase : store (Layout.chunkRadix regs) = base)
    (hexponent :
      store (rangeRegisters regs).remaining = exponent)
    (haccumulator :
      store (rangeRegisters regs).count = accumulator)
    (hone : store (rangeRegisters regs).one = 1) :
    ∃ final,
      Runs
          (.whileNonzero (rangeRegisters regs).remaining
            (countBody regs))
          store final ∧
      final (rangeRegisters regs).count =
        accumulator * base ^ exponent ∧
      final (rangeRegisters regs).remaining = 0 ∧
      final (Layout.chunkRadix regs) = base ∧
      final (rangeRegisters regs).one = 1 := by
  induction exponent generalizing store accumulator with
  | zero =>
      refine ⟨store, Runs.whileZero hexponent, ?_, hexponent,
        hbase, hone⟩
      simpa using haccumulator
  | succ exponent ih =>
      let multiplied :=
        Basic.exec
          (.mul (rangeRegisters regs).count
            (rangeRegisters regs).count (Layout.chunkRadix regs))
          store
      have hmultiply :
          Runs
            (.basic
              (.mul (rangeRegisters regs).count
                (rangeRegisters regs).count
                (Layout.chunkRadix regs)))
            store multiplied :=
        Runs.basic _ _
      have hmultipliedCount :
          multiplied (rangeRegisters regs).count =
            accumulator * base := by
        simp [multiplied, Basic.exec, haccumulator, hbase]
      have hmultipliedRemaining :
          multiplied (rangeRegisters regs).remaining =
            exponent + 1 := by
        simpa [multiplied, Basic.exec, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hexponent
      have hmultipliedBase :
          multiplied (Layout.chunkRadix regs) = base := by
        simpa [multiplied, Basic.exec, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hbase
      have hmultipliedOne :
          multiplied (rangeRegisters regs).one = 1 := by
        simpa [multiplied, Basic.exec, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hone
      let decremented :=
        Basic.exec
          (.sub (rangeRegisters regs).remaining
            (rangeRegisters regs).remaining (rangeRegisters regs).one)
          multiplied
      have hdecrement :
          Runs
            (.basic
              (.sub (rangeRegisters regs).remaining
                (rangeRegisters regs).remaining
                (rangeRegisters regs).one))
            multiplied decremented :=
        Runs.basic _ _
      have hdecrementedCount :
          decremented (rangeRegisters regs).count =
            accumulator * base := by
        simpa [decremented, Basic.exec, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hmultipliedCount
      have hdecrementedRemaining :
          decremented (rangeRegisters regs).remaining = exponent := by
        simp [decremented, Basic.exec, hmultipliedRemaining,
          hmultipliedOne]
      have hdecrementedBase :
          decremented (Layout.chunkRadix regs) = base := by
        simpa [decremented, Basic.exec, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hmultipliedBase
      have hdecrementedOne :
          decremented (rangeRegisters regs).one = 1 := by
        simpa [decremented, Basic.exec, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hmultipliedOne
      obtain ⟨final, hloop, hfinalCount, hfinalRemaining,
          hfinalBase, hfinalOne⟩ :=
        ih decremented (accumulator * base)
          hdecrementedBase hdecrementedRemaining
          hdecrementedCount hdecrementedOne
      refine
        ⟨final,
          Runs.whileNonzero (by omega)
            (by
              simpa [countBody] using
                Runs.seq hmultiply hdecrement)
            hloop,
          ?_, hfinalRemaining, hfinalBase, hfinalOne⟩
      calc
        final (rangeRegisters regs).count =
            (accumulator * base) * base ^ exponent :=
          hfinalCount
        _ = accumulator * base ^ (exponent + 1) := by
          rw [pow_succ]
          ring

private theorem restoreCountLoop_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base exponent accumulator : ℕ)
    (hbase : store (Layout.chunkRadix regs) = base)
    (hexponent : store (countExponent regs) = exponent)
    (haccumulator :
      store (rangeRegisters regs).count = accumulator)
    (hone : store (rangeRegisters regs).one = 1) :
    ∃ final,
      Runs
          (.whileNonzero (countExponent regs)
            (restoreCountBody regs))
          store final ∧
      final (rangeRegisters regs).count =
        accumulator * base ^ exponent ∧
      final (countExponent regs) = 0 ∧
      final (Layout.chunkRadix regs) = base ∧
      final (rangeRegisters regs).one = 1 := by
  induction exponent generalizing store accumulator with
  | zero =>
      refine ⟨store, Runs.whileZero hexponent, ?_, hexponent,
        hbase, hone⟩
      simpa using haccumulator
  | succ exponent ih =>
      let multiplied :=
        Basic.exec
          (.mul (rangeRegisters regs).count
            (rangeRegisters regs).count (Layout.chunkRadix regs))
          store
      have hmultiply :
          Runs
            (.basic
              (.mul (rangeRegisters regs).count
                (rangeRegisters regs).count
                (Layout.chunkRadix regs)))
            store multiplied :=
        Runs.basic _ _
      have hmultipliedCount :
          multiplied (rangeRegisters regs).count =
            accumulator * base := by
        simp [multiplied, Basic.exec, haccumulator, hbase]
      have hmultipliedExponent :
          multiplied (countExponent regs) = exponent + 1 := by
        simpa [multiplied, Basic.exec, countExponent, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hexponent
      have hmultipliedBase :
          multiplied (Layout.chunkRadix regs) = base := by
        simpa [multiplied, Basic.exec, countExponent, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hbase
      have hmultipliedOne :
          multiplied (rangeRegisters regs).one = 1 := by
        simpa [multiplied, Basic.exec, countExponent, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hone
      let decremented :=
        Basic.exec
          (.sub (countExponent regs) (countExponent regs)
            (rangeRegisters regs).one)
          multiplied
      have hdecrement :
          Runs
            (.basic
              (.sub (countExponent regs) (countExponent regs)
                (rangeRegisters regs).one))
            multiplied decremented :=
        Runs.basic _ _
      have hdecrementedCount :
          decremented (rangeRegisters regs).count =
            accumulator * base := by
        simpa [decremented, Basic.exec, countExponent, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hmultipliedCount
      have hdecrementedExponent :
          decremented (countExponent regs) = exponent := by
        simp [decremented, Basic.exec, hmultipliedExponent,
          hmultipliedOne]
      have hdecrementedBase :
          decremented (Layout.chunkRadix regs) = base := by
        simpa [decremented, Basic.exec, countExponent, rangeRegisters,
          CombineValue.rangeRegisters, Layout.chunkRadix,
          regs.injective.eq_iff] using hmultipliedBase
      have hdecrementedOne :
          decremented (rangeRegisters regs).one = 1 := by
        simpa [decremented, Basic.exec, countExponent, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hmultipliedOne
      obtain ⟨final, hloop, hfinalCount, hfinalExponent,
          hfinalBase, hfinalOne⟩ :=
        ih decremented (accumulator * base)
          hdecrementedBase hdecrementedExponent
          hdecrementedCount hdecrementedOne
      refine
        ⟨final,
          Runs.whileNonzero (by omega)
            (by
              simpa [restoreCountBody] using
                Runs.seq hmultiply hdecrement)
            hloop,
          ?_, hfinalExponent, hfinalBase, hfinalOne⟩
      calc
        final (rangeRegisters regs).count =
            (accumulator * base) * base ^ exponent :=
          hfinalCount
        _ = accumulator * base ^ (exponent + 1) := by
          rw [pow_succ]
          ring

private theorem initializeAssignmentCount_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store) :
    ∃ final,
      Runs (initializeAssignmentCount regs) store final ∧
      final (rangeRegisters regs).count =
        CombineValue.assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) ∧
      final (rangeRegisters regs).one = 1 := by
  let range := rangeRegisters regs
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let chunks :=
    PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      fanIn
  obtain ⟨copied, hcopy, hcopyValue, hcopyOutside⟩ :=
    CombineTerm.copy_runs_internal range.remaining
      (Layout.bankDigitCount regs) store
      (regs.injective.ne (by decide))
  have hcopiedRemaining :
      copied range.remaining = (fanIn + 1) * chunks := by
    exact hcopyValue.trans (by
      simpa [fanIn, chunks] using hparameters.bankDigitCount_eq)
  have hcopiedChunkCount :
      copied (Layout.chunkCount regs) = chunks := by
    rw [hcopyOutside _]
    · simpa [fanIn, chunks] using hparameters.chunkCount_eq
    · exact regs.injective.ne (by decide)
  have hcopiedBase :
      copied (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    rw [hcopyOutside _]
    · exact hparameters.digitBase_eq
    · exact regs.injective.ne (by decide)
  let subtracted :=
    Basic.exec
      (.sub range.remaining range.remaining (Layout.chunkCount regs))
      copied
  have hsubtract :
      Runs
        (.basic
          (.sub range.remaining range.remaining
            (Layout.chunkCount regs)))
        copied subtracted :=
    Runs.basic _ _
  have hsubtractedRemaining :
      subtracted range.remaining = fanIn * chunks := by
    simp [subtracted, Basic.exec, hcopiedRemaining,
      hcopiedChunkCount, Nat.add_mul]
  have hsubtractedBase :
      subtracted (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    simpa [subtracted, Basic.exec, range, rangeRegisters,
      CombineValue.rangeRegisters, Layout.chunkCount,
      Layout.chunkRadix, regs.injective.eq_iff] using hcopiedBase
  let counted :=
    Basic.exec (.imm range.count 1) subtracted
  have hcount :
      Runs (.basic (.imm range.count 1)) subtracted counted :=
    Runs.basic _ _
  have hcountedRemaining :
      counted range.remaining = fanIn * chunks := by
    simpa [counted, Basic.exec, range, rangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff] using
      hsubtractedRemaining
  have hcountedCount : counted range.count = 1 := by
    simp [counted, Basic.exec]
  have hcountedBase :
      counted (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    simpa [counted, Basic.exec, range, rangeRegisters,
      CombineValue.rangeRegisters, Layout.chunkRadix,
      regs.injective.eq_iff] using hsubtractedBase
  let ready :=
    Basic.exec (.imm range.one 1) counted
  have hone :
      Runs (.basic (.imm range.one 1)) counted ready :=
    Runs.basic _ _
  have hreadyRemaining :
      ready range.remaining = assignmentDigitCount instanceData := by
    simpa [ready, Basic.exec, range, rangeRegisters,
      CombineValue.rangeRegisters, assignmentDigitCount, fanIn, chunks,
      regs.injective.eq_iff] using hcountedRemaining
  have hreadyCount : ready range.count = 1 := by
    simpa [ready, Basic.exec, range, rangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff] using
      hcountedCount
  have hreadyBase :
      ready (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    simpa [ready, Basic.exec, range, rangeRegisters,
      CombineValue.rangeRegisters, Layout.chunkRadix,
      regs.injective.eq_iff] using hcountedBase
  have hreadyOne : ready range.one = 1 := by
    simp [ready, Basic.exec]
  obtain ⟨final, hloop, hfinalCount, _hremaining,
      _hbase, hfinalOne⟩ :=
    countLoop_runs regs ready (Representation.digitBase instanceData)
      (assignmentDigitCount instanceData) 1 hreadyBase
      hreadyRemaining hreadyCount hreadyOne
  refine ⟨final, ?_, ?_, hfinalOne⟩
  · simpa [initializeAssignmentCount, Cmd.seqList, range] using
      Runs.seq hcopy
        (Runs.seq hsubtract
          (Runs.seq hcount (Runs.seq hone hloop)))
  · simpa [assignmentCount_eq_power instanceData] using hfinalCount

private theorem restoreAssignmentCount_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store (rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (restoreAssignmentCount regs) store final ∧
      final (rangeRegisters regs).count =
        CombineValue.assignmentCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) ∧
      ∀ address,
        address ∉
          ({countExponent regs, (rangeRegisters regs).count} :
            Finset ℕ) →
        final address = store address := by
  let range := rangeRegisters regs
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let chunks :=
    PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      fanIn
  obtain ⟨copied, hcopy, hcopyValue, hcopyOutside⟩ :=
    CombineTerm.copy_runs_internal (countExponent regs)
      (Layout.bankDigitCount regs) store
      (regs.injective.ne (by decide))
  have hcopiedExponent :
      copied (countExponent regs) = (fanIn + 1) * chunks := by
    exact hcopyValue.trans (by
      simpa [fanIn, chunks] using hparameters.bankDigitCount_eq)
  have hcopiedChunkCount :
      copied (Layout.chunkCount regs) = chunks := by
    rw [hcopyOutside _ (regs.injective.ne (by decide))]
    simpa [fanIn, chunks] using hparameters.chunkCount_eq
  have hcopiedBase :
      copied (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    rw [hcopyOutside _ (regs.injective.ne (by decide))]
    exact hparameters.digitBase_eq
  have hcopiedOne : copied range.one = 1 := by
    rw [hcopyOutside range.one]
    · exact hone
    · dsimp [range, rangeRegisters, CombineValue.rangeRegisters,
        countExponent]
      exact regs.injective.ne (by decide)
  let subtracted :=
    Basic.exec
      (.sub (countExponent regs) (countExponent regs)
        (Layout.chunkCount regs))
      copied
  have hsubtract :
      Runs
        (.basic
          (.sub (countExponent regs) (countExponent regs)
            (Layout.chunkCount regs)))
        copied subtracted :=
    Runs.basic _ _
  have hsubtractedExponent :
      subtracted (countExponent regs) = fanIn * chunks := by
    simp [subtracted, Basic.exec, hcopiedExponent,
      hcopiedChunkCount, Nat.add_mul]
  have hsubtractedBase :
      subtracted (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    simpa [subtracted, Basic.exec, countExponent,
      Layout.chunkCount, Layout.chunkRadix,
      regs.injective.eq_iff] using hcopiedBase
  have hsubtractedOne : subtracted range.one = 1 := by
    simpa [subtracted, Basic.exec, countExponent, range,
      rangeRegisters, CombineValue.rangeRegisters, Layout.chunkCount,
      regs.injective.eq_iff] using hcopiedOne
  let counted :=
    Basic.exec (.imm range.count 1) subtracted
  have hcount :
      Runs (.basic (.imm range.count 1)) subtracted counted :=
    Runs.basic _ _
  have hcountedExponent :
      counted (countExponent regs) = fanIn * chunks := by
    simpa [counted, Basic.exec, countExponent, range,
      rangeRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hsubtractedExponent
  have hcountedCount : counted range.count = 1 := by
    simp [counted, Basic.exec]
  have hcountedBase :
      counted (Layout.chunkRadix regs) =
        Representation.digitBase instanceData := by
    simpa [counted, Basic.exec, countExponent, range,
      rangeRegisters, CombineValue.rangeRegisters, Layout.chunkRadix,
      regs.injective.eq_iff] using hsubtractedBase
  have hcountedOne : counted range.one = 1 := by
    simpa [counted, Basic.exec, countExponent, range,
      rangeRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff] using hsubtractedOne
  obtain ⟨final, hloop, hfinalCount, _hfinalExponent,
      _hfinalBase, _hfinalOne⟩ :=
    restoreCountLoop_runs regs counted
      (Representation.digitBase instanceData)
      (assignmentDigitCount instanceData) 1 hcountedBase
      (by
        simpa [assignmentDigitCount, fanIn, chunks] using
          hcountedExponent)
      hcountedCount hcountedOne
  have hrun :
      Runs (restoreAssignmentCount regs) store final := by
    simpa [restoreAssignmentCount, Cmd.seqList, range] using
      Runs.seq hcopy (Runs.seq hsubtract (Runs.seq hcount hloop))
  have hwrites :
      Footprint.CmdWritesWithin
        ({countExponent regs, range.count} : Finset ℕ)
        (restoreAssignmentCount regs) := by
    simp [restoreAssignmentCount, restoreCountBody, CombineTerm.copy,
      Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin, range]
  refine ⟨final, hrun, ?_, ?_⟩
  · simpa [assignmentCount_eq_power instanceData] using hfinalCount
  · intro address haddress
    exact Footprint.runs_eq_outside hwrites hrun haddress

private theorem packedContext_transport
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    {initial final : Store}
    (hcontext :
      PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk initial)
    (habi : ControlDecode.PreservesABI regs initial final)
    (hbank : final regs.layout.bank = initial regs.layout.bank)
    (hguess : final controller.guess = initial controller.guess) :
    PackedComputationKernel.Context regs instanceData frame tape slot
      interval logicalBank code outputChunk final := by
  exact
    { computation :=
        CombineTerm.Internal.computationFrameContext_transport_internal
          regs instanceData frame tape slot interval.val logicalBank
          hcontext.computation habi hbank
      guess_eq := hguess.trans hcontext.guess_eq
      cursor_eq := habi.active_eq.trans hcontext.cursor_eq }

private theorem preservesABI_of_workspace_eq
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (heq :
      ∀ physical : Fin 34,
        final (regs.index physical) = initial (regs.index physical)) :
    ControlDecode.PreservesABI regs initial final :=
  { fuel_eq := heq 22
    nodeCode_eq := heq 23
    scalar_eq := heq 25
    out_eq := heq 26
    phaseCode_eq := heq 27
    active_eq := heq 28
    blockLength_eq := heq 2
    horizon_eq := heq 3
    chunkCount_eq := heq 7
    chunkRadix_eq := heq 8
    frameRadix_eq := heq 13
    bankRadix_eq := heq 14
    bankDigitCount_eq := heq 15
    modulusPred_eq := heq 16
    modulus_eq := heq 24 }

private theorem controllerOne_not_mem_combineScratch
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.one ∉ CombineValue.combineScratchFootprint regs := by
  intro hmember
  obtain ⟨slot, _, heq⟩ := Finset.mem_image.mp hmember
  exact regs.index_ne_controller
    (CombineValue.combineScratchMap slot) _ heq

private theorem combineScratch_index_not_mem
    (regs : NeighborhoodTrial.Registers controller)
    (physical : Fin 34)
    (hphysical :
      ∀ scratchSlot : Fin 19,
        CombineValue.combineScratchMap scratchSlot ≠ physical) :
    regs.index physical ∉
      CombineValue.combineScratchFootprint regs := by
  simp only [CombineValue.combineScratchFootprint,
    Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro scratchSlot heq
  exact hphysical scratchSlot (regs.injective heq)

private theorem workspace_index_not_mem_footprint
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (physical : Fin 34)
    (hphysical :
      ∀ scratchSlot : Fin 19,
        CombineValue.combineScratchMap scratchSlot ≠ physical) :
    regs.index physical ∉ footprint controller regs := by
  simp only [footprint, Finset.mem_union, Finset.mem_singleton,
    not_or]
  exact
    ⟨combineScratch_index_not_mem regs physical hphysical,
      by
        change regs.index physical ≠ controller.index 14
        exact
          regs.index_ne_controller physical (14 : Fin 17)⟩

private theorem preservesABI_of_footprint
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (command : Cmd) {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin (footprint controller regs) command)
    (hrun : Runs command initial final) :
    ControlDecode.PreservesABI regs initial final := by
  have hpreserved :
      ∀ physical : Fin 34,
        (∀ scratchSlot : Fin 19,
          CombineValue.combineScratchMap scratchSlot ≠ physical) →
        final (regs.index physical) = initial (regs.index physical) := by
    intro physical hphysical
    exact Footprint.runs_eq_outside hwrites hrun
      (workspace_index_not_mem_footprint
        controller regs physical hphysical)
  exact
    { fuel_eq := hpreserved (22 : Fin 34) (by decide)
      nodeCode_eq := hpreserved (23 : Fin 34) (by decide)
      scalar_eq := hpreserved (25 : Fin 34) (by decide)
      out_eq := hpreserved (26 : Fin 34) (by decide)
      phaseCode_eq := hpreserved (27 : Fin 34) (by decide)
      active_eq := hpreserved (28 : Fin 34) (by decide)
      blockLength_eq := hpreserved (2 : Fin 34) (by decide)
      horizon_eq := hpreserved (3 : Fin 34) (by decide)
      chunkCount_eq := hpreserved (7 : Fin 34) (by decide)
      chunkRadix_eq := hpreserved (8 : Fin 34) (by decide)
      frameRadix_eq := hpreserved (13 : Fin 34) (by decide)
      bankRadix_eq := hpreserved (14 : Fin 34) (by decide)
      bankDigitCount_eq := hpreserved (15 : Fin 34) (by decide)
      modulusPred_eq := hpreserved (16 : Fin 34) (by decide)
      modulus_eq := hpreserved (24 : Fin 34) (by decide) }

private theorem combineScratch_slot
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 19) :
    regs.index (CombineValue.combineScratchMap slot) ∈
      CombineValue.combineScratchFootprint regs :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem copy_writesWithin_combineScratch
    (regs : NeighborhoodTrial.Registers controller)
    (destination source : ℕ)
    (hdestination :
      destination ∈ CombineValue.combineScratchFootprint regs) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (CombineTerm.copy destination source) := by
  simpa [CombineTerm.copy, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin] using
    And.intro hdestination hdestination

private theorem preservesABI_trans
    (regs : NeighborhoodTrial.Registers controller)
    {initial middle final : Store}
    (hfirst : ControlDecode.PreservesABI regs initial middle)
    (hsecond : ControlDecode.PreservesABI regs middle final) :
    ControlDecode.PreservesABI regs initial final :=
  { fuel_eq := hsecond.fuel_eq.trans hfirst.fuel_eq
    nodeCode_eq := hsecond.nodeCode_eq.trans hfirst.nodeCode_eq
    scalar_eq := hsecond.scalar_eq.trans hfirst.scalar_eq
    out_eq := hsecond.out_eq.trans hfirst.out_eq
    phaseCode_eq := hsecond.phaseCode_eq.trans hfirst.phaseCode_eq
    active_eq := hsecond.active_eq.trans hfirst.active_eq
    blockLength_eq :=
      hsecond.blockLength_eq.trans hfirst.blockLength_eq
    horizon_eq := hsecond.horizon_eq.trans hfirst.horizon_eq
    chunkCount_eq :=
      hsecond.chunkCount_eq.trans hfirst.chunkCount_eq
    chunkRadix_eq :=
      hsecond.chunkRadix_eq.trans hfirst.chunkRadix_eq
    frameRadix_eq :=
      hsecond.frameRadix_eq.trans hfirst.frameRadix_eq
    bankRadix_eq := hsecond.bankRadix_eq.trans hfirst.bankRadix_eq
    bankDigitCount_eq :=
      hsecond.bankDigitCount_eq.trans hfirst.bankDigitCount_eq
    modulusPred_eq :=
      hsecond.modulusPred_eq.trans hfirst.modulusPred_eq
    modulus_eq := hsecond.modulus_eq.trans hfirst.modulus_eq }

private theorem parameters_transport
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : Store}
    (hparameters : Representation.Parameters regs instanceData initial)
    (habi : ControlDecode.PreservesABI regs initial final) :
    Representation.Parameters regs instanceData final :=
  { blockLength_eq :=
      habi.blockLength_eq.trans hparameters.blockLength_eq
    horizon_eq := habi.horizon_eq.trans hparameters.horizon_eq
    digitBase_eq := habi.chunkRadix_eq.trans hparameters.digitBase_eq
    bankBase_eq := habi.bankRadix_eq.trans hparameters.bankBase_eq
    frameBase_eq := habi.frameRadix_eq.trans hparameters.frameBase_eq
    chunkCount_eq :=
      habi.chunkCount_eq.trans hparameters.chunkCount_eq
    bankDigitCount_eq :=
      habi.bankDigitCount_eq.trans hparameters.bankDigitCount_eq
    modulus_eq := habi.modulus_eq.trans hparameters.modulus_eq
    modulusPred_eq :=
      habi.modulusPred_eq.trans hparameters.modulusPred_eq }

private theorem restoreAssignmentCount_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (restoreAssignmentCount regs) := by
  have hexponent :
      countExponent regs ∈
        CombineValue.combineScratchFootprint regs := by
    simpa [countExponent] using
      combineScratch_slot regs (5 : Fin 19)
  have hcount :
      (rangeRegisters regs).count ∈
        CombineValue.combineScratchFootprint regs := by
    simpa [rangeRegisters, CombineValue.rangeRegisters] using
      combineScratch_slot regs (6 : Fin 19)
  simp [restoreAssignmentCount, restoreCountBody, CombineTerm.copy,
    Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin, hexponent, hcount]

theorem stackSafePacked_specAt_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (hencoding :
      instanceData.encoding =
        NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    StackSafePackedSpecAt order regs instanceData frame tape slot interval
      logicalBank code outputChunk := by
  intro store assignment hcontext hremaining hmodulus hmodulusPred hone
  let range := rangeRegisters regs
  obtain ⟨saved, hsave, hsaveValue, hsaveOutside⟩ :=
    CombineTerm.copy_runs_internal range.count
      (Layout.frameStackRegisters regs).word store
      (regs.injective.ne (by decide))
  have hsaveWrites :
      Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (CombineTerm.copy range.count
          (Layout.frameStackRegisters regs).word) := by
    have hcount :
        range.count ∈
          CombineValue.combineScratchFootprint regs := by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        combineScratch_slot regs (6 : Fin 19)
    simpa [CombineTerm.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin] using And.intro hcount hcount
  have hsaveABI :
      ControlDecode.PreservesABI regs store saved :=
    CombineValue.preservesABI_of_combineScratch regs hsaveWrites hsave
  have hsaveBank :
      saved regs.layout.bank = store regs.layout.bank := by
    apply hsaveOutside
    change regs.index 33 ≠ regs.index 10
    exact regs.injective.ne (by decide)
  have hsaveGuess :
      saved controller.guess = store controller.guess := by
    apply hsaveOutside
    change controller.index 2 ≠ regs.index 10
    exact (regs.index_ne_controller (10 : Fin 34) (2 : Fin 17)).symm
  have hsavedContext :
      PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk saved :=
    packedContext_transport regs instanceData frame tape slot interval
      logicalBank code outputChunk hcontext.packed hsaveABI hsaveBank
      hsaveGuess
  have hsaveRemaining : saved range.remaining = assignment := by
    rw [hsaveOutside range.remaining]
    · exact hremaining
    · change regs.index 21 ≠ regs.index 10
      exact regs.injective.ne (by decide)
  have hsaveOne : saved range.one = 1 := by
    rw [hsaveOutside range.one]
    · exact hone
    · change regs.index 17 ≠ regs.index 10
      exact regs.injective.ne (by decide)
  have hsaveModulus :
      saved range.modulus =
        NeighborhoodScheduler.fieldModulus instanceData :=
    hsaveABI.modulus_eq.trans hmodulus
  have hsaveModulusPred :
      saved range.modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1 :=
    hsaveABI.modulusPred_eq.trans hmodulusPred
  obtain ⟨afterPacked, hpackedRun, hpackedPost, hpackedWord,
      hpackedContext⟩ :=
    PackedComputationKernel.command_spec order regs instanceData frame tape
      slot interval logicalBank code outputChunk hencoding hguess
      saved assignment hsavedContext hsaveRemaining hsaveModulus
      hsaveModulusPred hsaveOne
  have hpackedBankExact :
      afterPacked regs.layout.bank = saved regs.layout.bank := by
    apply Footprint.runs_eq_outside
      (PackedComputationKernel.command_writesWithin
        tm order controller regs)
      hpackedRun
    change regs.index 33 ∉ PackedLocalStep.footprint regs
    simp only [PackedLocalStep.footprint, Finset.mem_image,
      Finset.mem_univ, true_and, not_exists]
    intro writeSlot heq
    have hslot := regs.injective heq
    fin_cases writeSlot <;>
      simp [PackedLocalStep.writeMap] at hslot
  have hpackedOne : afterPacked range.one = 1 :=
    hpackedPost.one_eq.trans hsaveOne
  obtain ⟨final, hrestore, hrestoreCount, hrestoreOutside⟩ :=
    restoreAssignmentCount_runs regs instanceData afterPacked
      hpackedContext.computation.computation.parameters hpackedOne
  have hrestoreABI :
      ControlDecode.PreservesABI regs afterPacked final :=
    CombineValue.preservesABI_of_combineScratch regs
      (restoreAssignmentCount_writesWithin regs) hrestore
  have hrestoreSlot :
      ∀ (physical : Fin 34),
        physical ≠ 9 →
        physical ≠ 10 →
        final (regs.index physical) =
          afterPacked (regs.index physical) := by
    intro physical hneExponent hneCount
    apply hrestoreOutside
    simp [countExponent, rangeRegisters,
      CombineValue.rangeRegisters, regs.injective.eq_iff,
      hneExponent, hneCount]
  have hrestoreBank :
      final regs.layout.bank = afterPacked regs.layout.bank := by
    simpa [NeighborhoodTrial.Registers.layout] using
      hrestoreSlot (33 : Fin 34) (by decide) (by decide)
  have hrestoreGuess :
      final controller.guess = afterPacked controller.guess := by
    apply hrestoreOutside
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · change controller.index 2 ≠ regs.index 9
      exact
        (regs.index_ne_controller (9 : Fin 34) (2 : Fin 17)).symm
    · change controller.index 2 ≠ regs.index 10
      exact
        (regs.index_ne_controller (10 : Fin 34) (2 : Fin 17)).symm
  have hfinalPackedContext :
      PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk final :=
    packedContext_transport regs instanceData frame tape slot interval
      logicalBank code outputChunk hpackedContext hrestoreABI
      hrestoreBank hrestoreGuess
  have hrestorePacked :
      final (CombineTerm.packedValue regs) =
        afterPacked (CombineTerm.packedValue regs) := by
    simpa [CombineTerm.packedValue] using
      hrestoreSlot (6 : Fin 34) (by decide) (by decide)
  have hrestoreAccumulator :
      final range.accumulator = afterPacked range.accumulator := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hrestoreSlot (18 : Fin 34) (by decide) (by decide)
  have hrestoreRemaining :
      final range.remaining = afterPacked range.remaining := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hrestoreSlot (21 : Fin 34) (by decide) (by decide)
  have hrestoreModulus :
      final range.modulus = afterPacked range.modulus := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hrestoreSlot (24 : Fin 34) (by decide) (by decide)
  have hrestoreModulusPred :
      final range.modulusPred = afterPacked range.modulusPred := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hrestoreSlot (16 : Fin 34) (by decide) (by decide)
  have hrestoreOne :
      final range.one = afterPacked range.one := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hrestoreSlot (17 : Fin 34) (by decide) (by decide)
  have hrestoreStack :
      final (Layout.frameStackRegisters regs).word =
        afterPacked (Layout.frameStackRegisters regs).word := by
    simpa [Layout.frameStackRegisters, Layout.frameStackMap] using
      hrestoreSlot (32 : Fin 34) (by decide) (by decide)
  have hsaveSlot :
      ∀ (physical : Fin 34),
        physical ≠ 10 →
        saved (regs.index physical) = store (regs.index physical) := by
    intro physical hne
    apply hsaveOutside
    exact fun heq => hne (regs.injective heq)
  have hsaveAccumulator :
      saved range.accumulator = store range.accumulator := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hsaveSlot (18 : Fin 34) (by decide)
  have hsaveModulusValue :
      saved range.modulus = store range.modulus := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hsaveSlot (24 : Fin 34) (by decide)
  have hsaveModulusPredValue :
      saved range.modulusPred = store range.modulusPred := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hsaveSlot (16 : Fin 34) (by decide)
  have hsaveOneValue :
      saved range.one = store range.one := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      hsaveSlot (17 : Fin 34) (by decide)
  have hpackedStack :
      afterPacked (Layout.frameStackRegisters regs).word =
        store (Layout.frameStackRegisters regs).word := by
    have hword := hpackedWord.trans hsaveValue
    simpa [PackedComputationKernel.bankRegisters,
      PackedLocalStep.bankRegisters,
      PackedLocalHeadScan.bankRegisters, PackedLocalHeadScan.bankMap,
      Layout.frameStackRegisters, Layout.frameStackMap] using hword
  refine ⟨final, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [stackSafePacked, Cmd.seqList, range] using
      Runs.seq hsave (Runs.seq hpackedRun hrestore)
  · exact
      { packed_eq := hrestorePacked.trans hpackedPost.packed_eq
        accumulator_eq :=
          hrestoreAccumulator.trans
            (hpackedPost.accumulator_eq.trans hsaveAccumulator)
        remaining_eq :=
          hrestoreRemaining.trans hpackedPost.remaining_eq
        modulus_eq :=
          hrestoreModulus.trans
            (hpackedPost.modulus_eq.trans hsaveModulusValue)
        modulusPred_eq :=
          hrestoreModulusPred.trans
            (hpackedPost.modulusPred_eq.trans hsaveModulusPredValue)
        one_eq :=
          hrestoreOne.trans
            (hpackedPost.one_eq.trans hsaveOneValue)
        count_eq := hrestoreCount.trans hcontext.count_eq.symm }
  · exact hrestoreStack.trans hpackedStack
  · exact hrestoreBank.trans (hpackedBankExact.trans hsaveBank)
  · exact
      { packed := hfinalPackedContext
        count_eq := hrestoreCount }

private theorem cmdWritesWithin_mono
    {smaller larger : Finset ℕ}
    (hsubset : smaller ⊆ larger) :
    ∀ command,
      Footprint.CmdWritesWithin smaller command →
      Footprint.CmdWritesWithin larger command := by
  intro command hwrites
  induction command with
  | skip => trivial
  | basic op =>
      cases op <;>
        simp_all [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] <;>
        exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero test onZero onNonzero zeroIH nonzeroIH =>
      exact ⟨zeroIH hwrites.1, nonzeroIH hwrites.2⟩
  | whileNonzero test body bodyIH =>
      exact bodyIH hwrites

private theorem packedFootprint_subset_combineScratch
    (regs : NeighborhoodTrial.Registers controller) :
    PackedComputationKernel.footprint regs ⊆
      CombineValue.combineScratchFootprint regs := by
  intro address haddress
  simp only [PackedComputationKernel.footprint,
    PackedLocalStep.footprint, Finset.mem_image, Finset.mem_univ,
    true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  fin_cases slot
  all_goals
    simp [PackedLocalStep.writeMap,
      CombineValue.combineScratchFootprint,
      CombineValue.combineScratchMap]
  all_goals
    first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩
    | exact ⟨6, rfl⟩
    | exact ⟨7, rfl⟩
    | exact ⟨8, rfl⟩
    | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩
    | exact ⟨11, rfl⟩
    | exact ⟨12, rfl⟩
    | exact ⟨14, rfl⟩
    | exact ⟨15, rfl⟩
    | exact ⟨16, rfl⟩
    | exact ⟨17, rfl⟩

private theorem initializeAssignmentCount_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (initializeAssignmentCount regs) := by
  have hremaining :
      (rangeRegisters regs).remaining ∈
        CombineValue.combineScratchFootprint regs := by
    simpa [rangeRegisters, CombineValue.rangeRegisters] using
      combineScratch_slot regs (13 : Fin 19)
  have hcount :
      (rangeRegisters regs).count ∈
        CombineValue.combineScratchFootprint regs := by
    simpa [rangeRegisters, CombineValue.rangeRegisters] using
      combineScratch_slot regs (6 : Fin 19)
  have hone :
      (rangeRegisters regs).one ∈
        CombineValue.combineScratchFootprint regs := by
    simpa [rangeRegisters, CombineValue.rangeRegisters] using
      combineScratch_slot regs (9 : Fin 19)
  simp [initializeAssignmentCount, countBody, CombineTerm.copy,
    Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin, hremaining, hcount, hone]

private theorem initializeAssignmentCount_preciseWrites
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      ({(rangeRegisters regs).remaining,
        (rangeRegisters regs).count,
        (rangeRegisters regs).one} : Finset ℕ)
      (initializeAssignmentCount regs) := by
  simp [initializeAssignmentCount, countBody, CombineTerm.copy,
    Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]

theorem stackSafePacked_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (stackSafePacked tm order controller regs) := by
  have hcount :
      (rangeRegisters regs).count ∈
        CombineValue.combineScratchFootprint regs := by
    simpa [rangeRegisters, CombineValue.rangeRegisters] using
      combineScratch_slot regs (6 : Fin 19)
  have hsave :
      Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (CombineTerm.copy (rangeRegisters regs).count
          (Layout.frameStackRegisters regs).word) := by
    simpa [CombineTerm.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin] using And.intro hcount hcount
  have hpacked :=
    cmdWritesWithin_mono
      (packedFootprint_subset_combineScratch regs)
      (PackedComputationKernel.command tm order controller regs)
      (PackedComputationKernel.command_writesWithin
        tm order controller regs)
  simpa [stackSafePacked, Cmd.seqList, Footprint.CmdWritesWithin] using
    And.intro hsave
      (And.intro hpacked (restoreAssignmentCount_writesWithin regs))

theorem assignmentTerm_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (footprint controller regs)
      (assignmentTerm tm order controller regs) := by
  let range := rangeRegisters regs
  have hscratch :
      CombineValue.combineScratchFootprint regs ⊆
        footprint controller regs := by
    intro address haddress
    exact Finset.mem_union_left _ haddress
  have hcount :
      range.count ∈ footprint controller regs :=
    hscratch (by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        combineScratch_slot regs (6 : Fin 19))
  have hterm :
      range.term ∈ footprint controller regs :=
    hscratch (by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        combineScratch_slot regs (11 : Fin 19))
  have htest :
      range.test ∈ footprint controller regs :=
    hscratch (by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        combineScratch_slot regs (3 : Fin 19))
  have hstack :
      (Layout.frameStackRegisters regs).word ∈
        footprint controller regs :=
    hscratch (by
      simpa [Layout.frameStackRegisters, Layout.frameStackMap] using
        combineScratch_slot regs (17 : Fin 19))
  have hbank :
      regs.layout.bank ∈ footprint controller regs :=
    hscratch (by
      simpa [NeighborhoodTrial.Registers.layout] using
        combineScratch_slot regs (18 : Fin 19))
  have hcontrollerOne :
      controller.one ∈ footprint controller regs := by
    simp [footprint]
  have hsaveBank :
      Footprint.CmdWritesWithin (footprint controller regs)
        (saveBank controller regs) := by
    simpa [saveBank, CombineTerm.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin] using
      And.intro hcontrollerOne hcontrollerOne
  have hsaveContinuation :
      Footprint.CmdWritesWithin
        (footprint controller regs)
        (saveContinuation regs) := by
    simpa [saveContinuation, CombineTerm.copy,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
      And.intro hcount hcount
  have hsaveBasis :
      Footprint.CmdWritesWithin
        (footprint controller regs)
        (saveBasisFactor regs) := by
    simpa [saveBasisFactor, CombineTerm.copy,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
      And.intro hterm hterm
  have hrestoreContinuation :
      Footprint.CmdWritesWithin
        (footprint controller regs)
        (restoreContinuation regs) := by
    simpa [restoreContinuation, CombineTerm.copy,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
      And.intro hstack hstack
  have hrestoreBank :
      Footprint.CmdWritesWithin (footprint controller regs)
        (restoreBank controller regs) := by
    simpa [restoreBank, CombineTerm.copy, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin] using And.intro hbank hbank
  have hrestoreControllerOne :
      Footprint.CmdWritesWithin (footprint controller regs)
        (restoreControllerOne controller) := by
    simpa [restoreControllerOne, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin] using hcontrollerOne
  have hmultiply :
      Footprint.CmdWritesWithin
        (footprint controller regs)
        (multiplyFactors regs) := by
    have hterm' :
        (CombineValue.rangeRegisters regs).term ∈
          footprint controller regs := by
      simpa [range] using hterm
    have htest' :
        (CombineValue.rangeRegisters regs).test ∈
          footprint controller regs := by
      simpa [range] using htest
    simpa [multiplyFactors, RuntimeArithmetic.mulMod,
      RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      CombineTerm.termReduceRegisters,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
      And.intro hterm'
        (And.intro htest' (And.intro hterm' htest'))
  simpa [assignmentTerm, Cmd.seqList,
    Footprint.CmdWritesWithin] using
    And.intro
      (cmdWritesWithin_mono hscratch _
        (stackSafePacked_writesWithin_internal
          tm order controller regs))
      (And.intro hsaveBank
        (And.intro hsaveContinuation
          (And.intro
            (cmdWritesWithin_mono hscratch _
              (CombineTerm.computationBasisKernel_writesWithin
                workTapeCount regs))
            (And.intro hsaveBasis
              (And.intro hrestoreContinuation
                (And.intro hrestoreBank
                  (And.intro hrestoreControllerOne
                    (And.intro
                      (cmdWritesWithin_mono hscratch _
                        (restoreAssignmentCount_writesWithin regs))
                      hmultiply))))))))

theorem assignmentTerm_specAt_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (stackWord bankWord : ℕ)
    (hencoding :
      instanceData.encoding =
        NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    CombineValue.TermKernelSpecAtContext
      (rangeRegisters regs)
      (assignmentTerm tm order controller regs)
      (NeighborhoodScheduler.fieldModulus instanceData)
      (CombineValue.assignmentTerm
        (NeighborhoodExecutableEvaluation.payloadWidth
          tm instanceData.blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
        (GuessedLocalEvaluation.booleanCombineAtGuess
          tm instanceData.blockLength instanceData.encoding
          instanceData.positive instanceData.guess interval tape slot)
        (CombineTerm.computationArguments frame logicalBank)
        outputChunk)
      (TermContext controller regs instanceData frame tape slot interval
        logicalBank code outputChunk stackWord bankWord) := by
  intro store assignment htermContext hremaining hmodulus
    hmodulusPred hone
  let range := rangeRegisters regs
  obtain ⟨afterPacked, hpackedRun, hpackedPost, hpackedStack,
      hpackedBank, hpackedContext⟩ :=
    stackSafePacked_specAt_internal order regs instanceData frame tape slot
      interval logicalBank code outputChunk hencoding hguess store
      assignment htermContext.context hremaining hmodulus hmodulusPred
      hone
  have hpackedControllerOne :
      afterPacked controller.one = 1 := by
    rw [Footprint.runs_eq_outside
      (stackSafePacked_writesWithin_internal
        tm order controller regs)
      hpackedRun
      (controllerOne_not_mem_combineScratch controller regs)]
    exact htermContext.controllerOne_eq
  obtain ⟨bankSaved, hsaveBankRun, hsaveBankValue,
      hsaveBankOutside⟩ :=
    CombineTerm.copy_runs_internal controller.one regs.layout.bank
      afterPacked
      (by
        change controller.index 14 ≠ regs.index 33
        exact
          (regs.index_ne_controller (33 : Fin 34)
            (14 : Fin 17)).symm)
  have hsaveBankABI :
      ControlDecode.PreservesABI regs afterPacked bankSaved :=
    preservesABI_of_workspace_eq regs (by
      intro physical
      apply hsaveBankOutside
      change regs.index physical ≠ controller.index 14
      exact regs.index_ne_controller physical (14 : Fin 17))
  have hsaveBankBank :
      bankSaved regs.layout.bank = afterPacked regs.layout.bank := by
    apply hsaveBankOutside
    change regs.index 33 ≠ controller.index 14
    exact regs.index_ne_controller (33 : Fin 34) (14 : Fin 17)
  have hsaveBankGuess :
      bankSaved controller.guess = afterPacked controller.guess := by
    apply hsaveBankOutside
    change controller.index 2 ≠ controller.index 14
    exact controller.injective.ne (by decide)
  have hbankSavedContext :
      PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk bankSaved :=
    packedContext_transport regs instanceData frame tape slot interval
      logicalBank code outputChunk hpackedContext.packed hsaveBankABI
      hsaveBankBank hsaveBankGuess
  obtain ⟨continuationSaved, hsaveContinuationRun,
      hsaveContinuationValue, hsaveContinuationOutside⟩ :=
    CombineTerm.copy_runs_internal range.count
      (Layout.frameStackRegisters regs).word bankSaved
      (regs.injective.ne (by decide))
  have hsaveContinuationWrites :
      Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (saveContinuation regs) := by
    have hcount :
        range.count ∈
          CombineValue.combineScratchFootprint regs := by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        combineScratch_slot regs (6 : Fin 19)
    simpa [saveContinuation, CombineTerm.copy,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
      And.intro hcount hcount
  have hsaveContinuationABI :
      ControlDecode.PreservesABI regs bankSaved continuationSaved :=
    CombineValue.preservesABI_of_combineScratch regs
      hsaveContinuationWrites
      (by simpa [saveContinuation] using hsaveContinuationRun)
  have hsaveContinuationBank :
      continuationSaved regs.layout.bank =
        bankSaved regs.layout.bank := by
    apply hsaveContinuationOutside
    change regs.index 33 ≠ regs.index 10
    exact regs.injective.ne (by decide)
  have hsaveContinuationGuess :
      continuationSaved controller.guess =
        bankSaved controller.guess := by
    apply hsaveContinuationOutside
    change controller.index 2 ≠ regs.index 10
    exact
      (regs.index_ne_controller (10 : Fin 34) (2 : Fin 17)).symm
  have hcontinuationSavedContext :
      PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk continuationSaved :=
    packedContext_transport regs instanceData frame tape slot interval
      logicalBank code outputChunk hbankSavedContext
      hsaveContinuationABI hsaveContinuationBank
      hsaveContinuationGuess
  have hcontinuationSavedRemaining :
      continuationSaved range.remaining = assignment := by
    rw [hsaveContinuationOutside range.remaining]
    · rw [hsaveBankOutside range.remaining]
      · exact hpackedPost.remaining_eq
      · change regs.index 21 ≠ controller.index 14
        exact regs.index_ne_controller (21 : Fin 34) (14 : Fin 17)
    · change regs.index 21 ≠ regs.index 10
      exact regs.injective.ne (by decide)
  have hcontinuationSavedModulus :
      continuationSaved range.modulus =
        NeighborhoodScheduler.fieldModulus instanceData := by
    exact hsaveContinuationABI.modulus_eq.trans
      (hsaveBankABI.modulus_eq.trans
        (hpackedPost.modulus_eq.trans hmodulus))
  have hcontinuationSavedModulusPred :
      continuationSaved range.modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1 := by
    exact hsaveContinuationABI.modulusPred_eq.trans
      (hsaveBankABI.modulusPred_eq.trans
        (hpackedPost.modulusPred_eq.trans hmodulusPred))
  have hcontinuationSavedOne :
      continuationSaved range.one = 1 := by
    rw [hsaveContinuationOutside range.one]
    · rw [hsaveBankOutside range.one]
      · exact hpackedPost.one_eq.trans hone
      · change regs.index 17 ≠ controller.index 14
        exact regs.index_ne_controller (17 : Fin 34) (14 : Fin 17)
    · change regs.index 17 ≠ regs.index 10
      exact regs.injective.ne (by decide)
  obtain ⟨afterBasis, hbasisRun, hbasisPost, hbasisContext⟩ :=
    CombineTerm.computationBasisKernel_spec regs instanceData frame tape
      slot interval.val logicalBank continuationSaved assignment
      hcontinuationSavedContext.computation
      hcontinuationSavedRemaining hcontinuationSavedModulus
      hcontinuationSavedModulusPred hcontinuationSavedOne
  have hbasisWrites :=
    CombineTerm.computationBasisKernel_writesWithin
      workTapeCount regs
  have hbasisABI :
      ControlDecode.PreservesABI regs continuationSaved afterBasis :=
    CombineValue.preservesABI_of_combineScratch regs hbasisWrites
      hbasisRun
  have hafterBasisControllerOne :
      afterBasis controller.one =
        afterPacked regs.layout.bank := by
    calc
      afterBasis controller.one =
          continuationSaved controller.one :=
        Footprint.runs_eq_outside hbasisWrites hbasisRun
          (controllerOne_not_mem_combineScratch controller regs)
      _ = bankSaved controller.one := by
        apply hsaveContinuationOutside
        change controller.index 14 ≠ regs.index 10
        exact
          (regs.index_ne_controller
            (10 : Fin 34) (14 : Fin 17)).symm
      _ = afterPacked regs.layout.bank := hsaveBankValue
  obtain ⟨basisSaved, hsaveBasisRun, hsaveBasisValue,
      hsaveBasisOutside⟩ :=
    CombineTerm.copy_runs_internal range.term
      (CombineTerm.basisValue regs) afterBasis
      (regs.injective.ne (by decide))
  have hsaveBasisWrites :
      Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (saveBasisFactor regs) := by
    apply copy_writesWithin_combineScratch
    simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
      combineScratch_slot regs (11 : Fin 19)
  have hsaveBasisABI :
      ControlDecode.PreservesABI regs afterBasis basisSaved :=
    CombineValue.preservesABI_of_combineScratch regs
      hsaveBasisWrites
      (by simpa [saveBasisFactor] using hsaveBasisRun)
  have hbasisSavedControllerOne :
      basisSaved controller.one =
        afterPacked regs.layout.bank := by
    rw [hsaveBasisOutside controller.one]
    · exact hafterBasisControllerOne
    · change controller.index 14 ≠ regs.index 19
      exact
        (regs.index_ne_controller
          (19 : Fin 34) (14 : Fin 17)).symm
  obtain ⟨continuationRestored, hrestoreContinuationRun,
      hrestoreContinuationValue, hrestoreContinuationOutside⟩ :=
    CombineTerm.copy_runs_internal
      (Layout.frameStackRegisters regs).word range.count basisSaved
      (regs.injective.ne (by decide))
  have hrestoreContinuationWrites :
      Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (restoreContinuation regs) := by
    apply copy_writesWithin_combineScratch
    simpa [Layout.frameStackRegisters, Layout.frameStackMap] using
      combineScratch_slot regs (17 : Fin 19)
  have hrestoreContinuationABI :
      ControlDecode.PreservesABI regs basisSaved continuationRestored :=
    CombineValue.preservesABI_of_combineScratch regs
      hrestoreContinuationWrites
      (by
        simpa [restoreContinuation] using
          hrestoreContinuationRun)
  have hcontinuationRestoredControllerOne :
      continuationRestored controller.one =
        afterPacked regs.layout.bank := by
    rw [hrestoreContinuationOutside controller.one]
    · exact hbasisSavedControllerOne
    · change controller.index 14 ≠ regs.index 32
      exact
        (regs.index_ne_controller
          (32 : Fin 34) (14 : Fin 17)).symm
  obtain ⟨bankRestored, hrestoreBankRun, hrestoreBankValue,
      hrestoreBankOutside⟩ :=
    CombineTerm.copy_runs_internal regs.layout.bank controller.one
      continuationRestored
      (by
        change regs.index 33 ≠ controller.index 14
        exact
          regs.index_ne_controller (33 : Fin 34) (14 : Fin 17))
  have hrestoreBankWrites :
      Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (restoreBank controller regs) := by
    apply copy_writesWithin_combineScratch
    simpa [NeighborhoodTrial.Registers.layout] using
      combineScratch_slot regs (18 : Fin 19)
  have hrestoreBankABI :
      ControlDecode.PreservesABI regs continuationRestored bankRestored :=
    CombineValue.preservesABI_of_combineScratch regs
      hrestoreBankWrites
      (by simpa [restoreBank] using hrestoreBankRun)
  have hbankRestoredBank :
      bankRestored regs.layout.bank =
        afterPacked regs.layout.bank :=
    hrestoreBankValue.trans hcontinuationRestoredControllerOne
  have hbankRestoredControllerOne :
      bankRestored controller.one =
        afterPacked regs.layout.bank := by
    rw [hrestoreBankOutside controller.one]
    · exact hcontinuationRestoredControllerOne
    · change controller.index 14 ≠ regs.index 33
      exact
        (regs.index_ne_controller
          (33 : Fin 34) (14 : Fin 17)).symm
  let controllerRestored :=
    Basic.exec (.imm controller.one 1) bankRestored
  have hrestoreControllerRun :
      Runs (restoreControllerOne controller)
        bankRestored controllerRestored := by
    simpa [restoreControllerOne, controllerRestored] using
      Runs.basic (.imm controller.one 1) bankRestored
  have hrestoreControllerWorkspace :
      ∀ physical : Fin 34,
        controllerRestored (regs.index physical) =
          bankRestored (regs.index physical) := by
    intro physical
    simp only [controllerRestored, Basic.exec]
    rw [Function.update_of_ne]
    change regs.index physical ≠ controller.index 14
    exact regs.index_ne_controller physical (14 : Fin 17)
  have hrestoreControllerABI :
      ControlDecode.PreservesABI regs bankRestored controllerRestored :=
    preservesABI_of_workspace_eq regs hrestoreControllerWorkspace
  have hcontrollerRestoredBank :
      controllerRestored regs.layout.bank =
        afterPacked regs.layout.bank := by
    rw [show controllerRestored regs.layout.bank =
        bankRestored regs.layout.bank by
      simpa [NeighborhoodTrial.Registers.layout] using
        hrestoreControllerWorkspace (33 : Fin 34)]
    exact hbankRestoredBank
  have hcontrollerRestoredOne :
      controllerRestored controller.one = 1 := by
    simp [controllerRestored, Basic.exec]
  have hafterBasisToControllerABI :
      ControlDecode.PreservesABI regs afterBasis controllerRestored :=
    preservesABI_trans regs hsaveBasisABI
      (preservesABI_trans regs hrestoreContinuationABI
        (preservesABI_trans regs hrestoreBankABI
          hrestoreControllerABI))
  have hcontrollerParameters :
      Representation.Parameters regs instanceData controllerRestored :=
    parameters_transport regs instanceData
      hbasisContext.computation.parameters
      hafterBasisToControllerABI
  have hcontrollerRangeOne :
      controllerRestored range.one = 1 := by
    have honeBasis :
        afterBasis range.one = 1 :=
      hbasisPost.one_eq.trans hcontinuationSavedOne
    rw [show controllerRestored range.one =
        bankRestored range.one by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        hrestoreControllerWorkspace (17 : Fin 34)]
    rw [hrestoreBankOutside range.one]
    · rw [hrestoreContinuationOutside range.one]
      · rw [hsaveBasisOutside range.one]
        · exact honeBasis
        · change regs.index 17 ≠ regs.index 19
          exact regs.injective.ne (by decide)
      · change regs.index 17 ≠ regs.index 32
        exact regs.injective.ne (by decide)
    · change regs.index 17 ≠ regs.index 33
      exact regs.injective.ne (by decide)
  obtain ⟨countRestored, hrestoreCountRun, hrestoreCountValue,
      hrestoreCountOutside⟩ :=
    restoreAssignmentCount_runs regs instanceData controllerRestored
      hcontrollerParameters hcontrollerRangeOne
  have hrestoreCountABI :
      ControlDecode.PreservesABI regs controllerRestored countRestored :=
    CombineValue.preservesABI_of_combineScratch regs
      (restoreAssignmentCount_writesWithin regs) hrestoreCountRun
  have hcountRestoredFromBasis :
      ∀ physical : Fin 34,
        physical ≠ 9 →
        physical ≠ 10 →
        physical ≠ 19 →
        physical ≠ 32 →
        physical ≠ 33 →
        countRestored (regs.index physical) =
          afterBasis (regs.index physical) := by
    intro physical hneExponent hneCount hneTerm hneStack hneBank
    rw [hrestoreCountOutside (regs.index physical)]
    · rw [hrestoreControllerWorkspace physical]
      rw [hrestoreBankOutside (regs.index physical)]
      · rw [hrestoreContinuationOutside (regs.index physical)]
        · rw [hsaveBasisOutside (regs.index physical)]
          exact fun heq => hneTerm (regs.injective heq)
        · exact fun heq => hneStack (regs.injective heq)
      · exact fun heq => hneBank (regs.injective heq)
    · simp [countExponent, rangeRegisters,
        CombineValue.rangeRegisters, regs.injective.eq_iff,
        hneExponent, hneCount]
  have hafterBasisPacked :
      afterBasis (CombineTerm.packedValue regs) =
        CombineTerm.packedAssignmentValue
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (GuessedLocalEvaluation.booleanCombineAtGuess
            tm instanceData.blockLength instanceData.encoding
            instanceData.positive instanceData.guess interval tape slot)
          outputChunk assignment := by
    calc
      afterBasis (CombineTerm.packedValue regs) =
          continuationSaved (CombineTerm.packedValue regs) :=
        hbasisPost.packed_eq
      _ = bankSaved (CombineTerm.packedValue regs) := by
        apply hsaveContinuationOutside
        change regs.index 6 ≠ regs.index 10
        exact regs.injective.ne (by decide)
      _ = afterPacked (CombineTerm.packedValue regs) := by
        apply hsaveBankOutside
        change regs.index 6 ≠ controller.index 14
        exact
          regs.index_ne_controller (6 : Fin 34) (14 : Fin 17)
      _ = _ := hpackedPost.packed_eq
  have hcountRestoredPacked :
      countRestored (CombineTerm.packedValue regs) =
        CombineTerm.packedAssignmentValue
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (GuessedLocalEvaluation.booleanCombineAtGuess
            tm instanceData.blockLength instanceData.encoding
            instanceData.positive instanceData.guess interval tape slot)
          outputChunk assignment := by
    calc
      countRestored (CombineTerm.packedValue regs) =
          afterBasis (CombineTerm.packedValue regs) := by
        simpa [CombineTerm.packedValue] using
          hcountRestoredFromBasis (6 : Fin 34) (by decide)
            (by decide) (by decide) (by decide) (by decide)
      _ = _ := hafterBasisPacked
  have hcountRestoredBasis :
      countRestored range.term =
        CombineTerm.basisAssignmentValue
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (CombineTerm.computationArguments frame logicalBank)
          assignment := by
    rw [hrestoreCountOutside range.term]
    · rw [show controllerRestored range.term =
          bankRestored range.term by
        simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
          hrestoreControllerWorkspace (19 : Fin 34)]
      rw [hrestoreBankOutside range.term]
      · rw [hrestoreContinuationOutside range.term]
        · exact hsaveBasisValue.trans hbasisPost.basis_eq
        · change regs.index 19 ≠ regs.index 32
          exact regs.injective.ne (by decide)
      · change regs.index 19 ≠ regs.index 33
        exact regs.injective.ne (by decide)
    · simp [countExponent, range, rangeRegisters,
        CombineValue.rangeRegisters, regs.injective.eq_iff]
  have hcountRestoredAccumulator :
      countRestored range.accumulator =
        store range.accumulator := by
    calc
      countRestored range.accumulator =
          afterBasis range.accumulator := by
        simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
          hcountRestoredFromBasis (18 : Fin 34) (by decide)
            (by decide) (by decide) (by decide) (by decide)
      _ = continuationSaved range.accumulator :=
        hbasisPost.accumulator_eq
      _ = bankSaved range.accumulator := by
        apply hsaveContinuationOutside
        change regs.index 18 ≠ regs.index 10
        exact regs.injective.ne (by decide)
      _ = afterPacked range.accumulator := by
        apply hsaveBankOutside
        change regs.index 18 ≠ controller.index 14
        exact
          regs.index_ne_controller (18 : Fin 34) (14 : Fin 17)
      _ = store range.accumulator := hpackedPost.accumulator_eq
  have hcountRestoredRemaining :
      countRestored range.remaining = assignment := by
    calc
      countRestored range.remaining =
          afterBasis range.remaining := by
        simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
          hcountRestoredFromBasis (21 : Fin 34) (by decide)
            (by decide) (by decide) (by decide) (by decide)
      _ = assignment := hbasisPost.remaining_eq
  have hcountRestoredModulus :
      countRestored range.modulus =
        NeighborhoodScheduler.fieldModulus instanceData := by
    calc
      countRestored range.modulus =
          afterBasis range.modulus := by
        simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
          hcountRestoredFromBasis (24 : Fin 34) (by decide)
            (by decide) (by decide) (by decide) (by decide)
      _ = NeighborhoodScheduler.fieldModulus instanceData :=
        hbasisPost.modulus_eq.trans hcontinuationSavedModulus
  have hcountRestoredModulusPred :
      countRestored range.modulusPred =
        NeighborhoodScheduler.fieldModulus instanceData - 1 := by
    calc
      countRestored range.modulusPred =
          afterBasis range.modulusPred := by
        simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
          hcountRestoredFromBasis (16 : Fin 34) (by decide)
            (by decide) (by decide) (by decide) (by decide)
      _ = NeighborhoodScheduler.fieldModulus instanceData - 1 :=
        hbasisPost.modulusPred_eq.trans
          hcontinuationSavedModulusPred
  have hcountRestoredOne :
      countRestored range.one = 1 := by
    calc
      countRestored range.one = afterBasis range.one := by
        simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
          hcountRestoredFromBasis (17 : Fin 34) (by decide)
            (by decide) (by decide) (by decide) (by decide)
      _ = 1 := hbasisPost.one_eq.trans hcontinuationSavedOne
  have hcountRestoredCount :
      countRestored range.count = store range.count :=
    hrestoreCountValue.trans htermContext.context.count_eq.symm
  let payloadWidth :=
    NeighborhoodExecutableEvaluation.payloadWidth
      tm instanceData.blockLength
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let modulus := NeighborhoodScheduler.fieldModulus instanceData
  let packedFactor :=
    CombineTerm.packedAssignmentValue payloadWidth fanIn
      (GuessedLocalEvaluation.booleanCombineAtGuess
        tm instanceData.blockLength instanceData.encoding
        instanceData.positive instanceData.guess interval tape slot)
      outputChunk assignment
  let basisFactor :=
    CombineTerm.basisAssignmentValue payloadWidth fanIn
      (CombineTerm.computationArguments frame logicalBank) assignment
  let termValue :=
    PrimeField.Runtime.mul modulus packedFactor basisFactor
  have hmodulusPos : 0 < modulus := by
    simpa [modulus, NeighborhoodScheduler.fieldModulus, payloadWidth,
      fanIn] using CombineValue.fieldModulus_pos payloadWidth fanIn
  let final :=
    RuntimeArithmetic.reduceResultStore
      (CombineTerm.termReduceRegisters regs) termValue countRestored
  have hmulRun :
      Runs (multiplyFactors regs) countRestored final := by
    simpa [multiplyFactors, final, termValue, packedFactor,
      basisFactor, payloadWidth, fanIn, modulus,
      hcountRestoredPacked, hcountRestoredBasis,
      PrimeField.Runtime.mul, PrimeField.Runtime.mulInput,
      PrimeField.Runtime.normalize, Nat.mul_mod] using
      RuntimeArithmetic.mulMod_runs
        (CombineTerm.termReduceRegisters regs)
        (CombineTerm.packedValue regs) range.term countRestored
        modulus hmodulusPos
        (by simpa [modulus] using hcountRestoredModulus)
        (by simpa [modulus] using hcountRestoredModulusPred)
  have hmulWrites :
      Footprint.CmdWritesWithin
        (CombineValue.combineScratchFootprint regs)
        (multiplyFactors regs) := by
    have hterm :
        range.term ∈
          CombineValue.combineScratchFootprint regs := by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        combineScratch_slot regs (11 : Fin 19)
    have htest :
        range.test ∈
          CombineValue.combineScratchFootprint regs := by
      simpa [range, rangeRegisters, CombineValue.rangeRegisters] using
        combineScratch_slot regs (3 : Fin 19)
    simpa [multiplyFactors, RuntimeArithmetic.mulMod,
      RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      CombineTerm.termReduceRegisters,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin] using
      And.intro hterm
        (And.intro htest (And.intro hterm htest))
  have hmulABI :
      ControlDecode.PreservesABI regs countRestored final :=
    CombineValue.preservesABI_of_combineScratch regs hmulWrites hmulRun
  have hrun :
      Runs (assignmentTerm tm order controller regs) store final := by
    simpa [assignmentTerm, Cmd.seqList, saveBank, saveContinuation,
      saveBasisFactor, restoreContinuation, restoreBank] using
      Runs.seq hpackedRun
        (Runs.seq hsaveBankRun
          (Runs.seq hsaveContinuationRun
            (Runs.seq hbasisRun
              (Runs.seq hsaveBasisRun
                (Runs.seq hrestoreContinuationRun
                  (Runs.seq hrestoreBankRun
                    (Runs.seq hrestoreControllerRun
                      (Runs.seq hrestoreCountRun hmulRun))))))))
  have hafterPackedToFinalABI :
      ControlDecode.PreservesABI regs afterPacked final :=
    preservesABI_trans regs hsaveBankABI
      (preservesABI_trans regs hsaveContinuationABI
        (preservesABI_trans regs hbasisABI
          (preservesABI_trans regs hsaveBasisABI
            (preservesABI_trans regs hrestoreContinuationABI
              (preservesABI_trans regs hrestoreBankABI
                (preservesABI_trans regs hrestoreControllerABI
                  (preservesABI_trans regs hrestoreCountABI
                    hmulABI)))))))
  have hcountRestoredBank :
      countRestored regs.layout.bank =
        afterPacked regs.layout.bank := by
    rw [hrestoreCountOutside regs.layout.bank]
    · exact hcontrollerRestoredBank
    · simp [countExponent, rangeRegisters,
        CombineValue.rangeRegisters,
        NeighborhoodTrial.Registers.layout,
        regs.injective.eq_iff]
  have hfinalBank :
      final regs.layout.bank =
        afterPacked regs.layout.bank := by
    rw [show final regs.layout.bank =
        countRestored regs.layout.bank by
      simp [final, RuntimeArithmetic.reduceResultStore,
        CombineTerm.termReduceRegisters,
        CombineValue.rangeRegisters,
        NeighborhoodTrial.Registers.layout,
        regs.injective.eq_iff]]
    exact hcountRestoredBank
  have hguessNotScratch :
      controller.guess ∉
        CombineValue.combineScratchFootprint regs := by
    intro hmember
    obtain ⟨scratchSlot, _, heq⟩ := Finset.mem_image.mp hmember
    exact regs.index_ne_controller
      (CombineValue.combineScratchMap scratchSlot) (2 : Fin 17)
      heq
  have hguessNotFootprint :
      controller.guess ∉ footprint controller regs := by
    simp only [footprint, Finset.mem_union, Finset.mem_singleton,
      not_or]
    refine ⟨hguessNotScratch, ?_⟩
    change controller.index 2 ≠ controller.index 14
    exact controller.injective.ne (by decide)
  have hfinalGuessStore :
      final controller.guess = store controller.guess :=
    Footprint.runs_eq_outside
      (assignmentTerm_writesWithin_internal
        tm order controller regs)
      hrun hguessNotFootprint
  have hpackedGuessStore :
      afterPacked controller.guess = store controller.guess :=
    Footprint.runs_eq_outside
      (stackSafePacked_writesWithin_internal
        tm order controller regs)
      hpackedRun hguessNotScratch
  have hfinalGuess :
      final controller.guess = afterPacked controller.guess :=
    hfinalGuessStore.trans hpackedGuessStore.symm
  have hfinalPackedContext :
      PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk final :=
    packedContext_transport regs instanceData frame tape slot interval
      logicalBank code outputChunk hpackedContext.packed
      hafterPackedToFinalABI hfinalBank hfinalGuess
  have hcountRestoredControllerOne :
      countRestored controller.one = 1 := by
    rw [hrestoreCountOutside controller.one]
    · exact hcontrollerRestoredOne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · change controller.index 14 ≠ regs.index 9
        exact
          (regs.index_ne_controller
            (9 : Fin 34) (14 : Fin 17)).symm
      · change controller.index 14 ≠ regs.index 10
        exact
          (regs.index_ne_controller
            (10 : Fin 34) (14 : Fin 17)).symm
  have hfinalControllerOne :
      final controller.one = 1 := by
    rw [show final controller.one =
        countRestored controller.one by
      simp only [final, RuntimeArithmetic.reduceResultStore]
      rw [Function.update_of_ne, Function.update_of_ne]
      · change controller.index 14 ≠ regs.index 19
        exact
          (regs.index_ne_controller
            (19 : Fin 34) (14 : Fin 17)).symm
      · change controller.index 14 ≠ regs.index 5
        exact
          (regs.index_ne_controller
            (5 : Fin 34) (14 : Fin 17)).symm]
    exact hcountRestoredControllerOne
  have hfinalCount :
      final range.count =
        CombineValue.assignmentCount payloadWidth fanIn := by
    rw [show final range.count = countRestored range.count by
      simp [final, RuntimeArithmetic.reduceResultStore,
        CombineTerm.termReduceRegisters, range,
        CombineValue.rangeRegisters, regs.injective.eq_iff]]
    simpa [payloadWidth, fanIn] using hrestoreCountValue
  have hcontinuationRestoredStack :
      continuationRestored (Layout.frameStackRegisters regs).word =
        stackWord := by
    calc
      continuationRestored (Layout.frameStackRegisters regs).word =
          basisSaved range.count :=
        hrestoreContinuationValue
      _ = afterBasis range.count := by
        apply hsaveBasisOutside
        change regs.index 10 ≠ regs.index 19
        exact regs.injective.ne (by decide)
      _ = continuationSaved range.count := hbasisPost.count_eq
      _ = bankSaved (Layout.frameStackRegisters regs).word :=
        hsaveContinuationValue
      _ = afterPacked (Layout.frameStackRegisters regs).word := by
        apply hsaveBankOutside
        change regs.index 32 ≠ controller.index 14
        exact
          regs.index_ne_controller (32 : Fin 34) (14 : Fin 17)
      _ = store (Layout.frameStackRegisters regs).word :=
        hpackedStack
      _ = stackWord := htermContext.stack_eq
  have hfinalStackWord :
      final (Layout.frameStackRegisters regs).word = stackWord := by
    calc
      final (Layout.frameStackRegisters regs).word =
          countRestored (Layout.frameStackRegisters regs).word := by
        simp [final, RuntimeArithmetic.reduceResultStore,
          CombineTerm.termReduceRegisters,
          CombineValue.rangeRegisters, Layout.frameStackRegisters,
          Layout.frameStackMap, regs.injective.eq_iff]
      _ = controllerRestored
          (Layout.frameStackRegisters regs).word := by
        apply hrestoreCountOutside
        simp [countExponent, rangeRegisters,
          CombineValue.rangeRegisters, Layout.frameStackRegisters,
          Layout.frameStackMap, regs.injective.eq_iff]
      _ = bankRestored (Layout.frameStackRegisters regs).word := by
        simpa [Layout.frameStackRegisters, Layout.frameStackMap] using
          hrestoreControllerWorkspace (32 : Fin 34)
      _ = continuationRestored
          (Layout.frameStackRegisters regs).word := by
        apply hrestoreBankOutside
        change regs.index 32 ≠ regs.index 33
        exact regs.injective.ne (by decide)
      _ = stackWord := hcontinuationRestoredStack
  have hfinalBankWord :
      final regs.layout.bank = bankWord :=
    hfinalBank.trans (hpackedBank.trans htermContext.bank_eq)
  have hfinalTermContext :
      TermContext controller regs instanceData frame tape slot interval
        logicalBank code outputChunk stackWord bankWord final :=
    { context :=
        { packed := hfinalPackedContext
          count_eq := by
            simpa [payloadWidth, fanIn] using hfinalCount }
      controllerOne_eq := hfinalControllerOne
      stack_eq := hfinalStackWord
      bank_eq := hfinalBankWord }
  have htermValue :
      CombineValue.assignmentTerm payloadWidth fanIn
          (GuessedLocalEvaluation.booleanCombineAtGuess
            tm instanceData.blockLength instanceData.encoding
            instanceData.positive instanceData.guess interval tape slot)
          (CombineTerm.computationArguments frame logicalBank)
          outputChunk assignment =
        termValue := by
    simpa [termValue, modulus, packedFactor, basisFactor,
      NeighborhoodScheduler.fieldModulus] using
      CombineTerm.assignmentTerm_eq_factors payloadWidth fanIn
        (GuessedLocalEvaluation.booleanCombineAtGuess
          tm instanceData.blockLength instanceData.encoding
          instanceData.positive instanceData.guess interval tape slot)
        (CombineTerm.computationArguments frame logicalBank)
        outputChunk assignment
  refine ⟨final, hrun, ?_, hfinalTermContext⟩
  exact
    { term_eq := by
        calc
          final range.term = termValue := by
            simp [final, RuntimeArithmetic.reduceResultStore,
              CombineTerm.termReduceRegisters, range,
              CombineValue.rangeRegisters, regs.injective.eq_iff]
          _ =
              CombineValue.assignmentTerm payloadWidth fanIn
                (GuessedLocalEvaluation.booleanCombineAtGuess
                  tm instanceData.blockLength instanceData.encoding
                  instanceData.positive instanceData.guess interval
                  tape slot)
                (CombineTerm.computationArguments frame logicalBank)
                outputChunk assignment :=
            htermValue.symm
      accumulator_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          CombineTerm.termReduceRegisters, range, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hcountRestoredAccumulator
      remaining_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          CombineTerm.termReduceRegisters, range, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hcountRestoredRemaining
      modulus_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          CombineTerm.termReduceRegisters, range, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hcountRestoredModulus.trans hmodulus.symm
      modulusPred_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          CombineTerm.termReduceRegisters, range, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hcountRestoredModulusPred.trans hmodulusPred.symm
      one_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          CombineTerm.termReduceRegisters, range, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hcountRestoredOne.trans hone.symm
      count_eq := by
        simpa [final, RuntimeArithmetic.reduceResultStore,
          CombineTerm.termReduceRegisters, range, rangeRegisters,
          CombineValue.rangeRegisters, regs.injective.eq_iff] using
          hcountRestoredCount }

private theorem termContext_stableUnderDriverWrites
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (stackWord bankWord : ℕ) :
    CombineValue.StableUnderDriverWrites
      (rangeRegisters regs)
      (TermContext controller regs instanceData frame tape slot interval
        logicalBank code outputChunk stackWord bankWord) := by
  intro initial final hcontext houtside
  have hguess :
      final controller.guess = initial controller.guess := by
    apply houtside
    simp [CombineValue.RangeRegisters.driverWriteFootprint,
      rangeRegisters, CombineValue.rangeRegisters]
    constructor
    · exact
        (regs.index_ne_controller
          (18 : Fin 34) (2 : Fin 17)).symm
    constructor
    · exact
        (regs.index_ne_controller
          (5 : Fin 34) (2 : Fin 17)).symm
    constructor
    · exact
        (regs.index_ne_controller
          (21 : Fin 34) (2 : Fin 17)).symm
    · exact
        (regs.index_ne_controller
          (17 : Fin 34) (2 : Fin 17)).symm
  have hcursor :
      final (Layout.active regs) = initial (Layout.active regs) := by
    apply houtside
    simp [CombineValue.RangeRegisters.driverWriteFootprint,
      rangeRegisters, CombineValue.rangeRegisters, Layout.active,
      regs.injective.eq_iff]
  have hcount :
      final (rangeRegisters regs).count =
        initial (rangeRegisters regs).count := by
    apply houtside
    simp [CombineValue.RangeRegisters.driverWriteFootprint,
      rangeRegisters, CombineValue.rangeRegisters,
      regs.injective.eq_iff]
  have hcontrollerOne :
      final controller.one = initial controller.one := by
    apply houtside
    simp [CombineValue.RangeRegisters.driverWriteFootprint,
      rangeRegisters, CombineValue.rangeRegisters]
    constructor
    · exact
        (regs.index_ne_controller
          (18 : Fin 34) (14 : Fin 17)).symm
    constructor
    · exact
        (regs.index_ne_controller
          (5 : Fin 34) (14 : Fin 17)).symm
    constructor
    · exact
        (regs.index_ne_controller
          (21 : Fin 34) (14 : Fin 17)).symm
    · exact
        (regs.index_ne_controller
          (17 : Fin 34) (14 : Fin 17)).symm
  have hstack :
      final (Layout.frameStackRegisters regs).word =
        initial (Layout.frameStackRegisters regs).word := by
    apply houtside
    simp [CombineValue.RangeRegisters.driverWriteFootprint,
      rangeRegisters, CombineValue.rangeRegisters,
      Layout.frameStackRegisters, Layout.frameStackMap,
      regs.injective.eq_iff]
  have hbank :
      final regs.layout.bank = initial regs.layout.bank := by
    apply houtside
    simp [CombineValue.RangeRegisters.driverWriteFootprint,
      rangeRegisters, CombineValue.rangeRegisters,
      NeighborhoodTrial.Registers.layout, regs.injective.eq_iff]
  have hcomputation :=
    CombineTerm.Internal.computationFrameContext_stableUnderDriverWrites_internal
      regs instanceData frame tape slot interval.val logicalBank
      hcontext.context.packed.computation houtside
  exact
    { context :=
        { packed :=
            { computation := hcomputation
              guess_eq :=
                hguess.trans hcontext.context.packed.guess_eq
              cursor_eq :=
                hcursor.trans hcontext.context.packed.cursor_eq }
          count_eq := hcount.trans hcontext.context.count_eq }
      controllerOne_eq :=
        hcontrollerOne.trans hcontext.controllerOne_eq
      stack_eq := hstack.trans hcontext.stack_eq
      bank_eq := hbank.trans hcontext.bank_eq }

private theorem rangeFold_writesWithin
    (op : CombineValue.FoldOp)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (termKernel : Cmd)
    (hkernel :
      Footprint.CmdWritesWithin
        (footprint controller regs) termKernel) :
    Footprint.CmdWritesWithin
      (footprint controller regs)
      (CombineValue.rangeFold op
        (CombineValue.rangeRegisters regs) termKernel) := by
  have hscratch :
      CombineValue.combineScratchFootprint regs ⊆
        footprint controller regs := by
    intro address haddress
    exact Finset.mem_union_left _ haddress
  have hAccumulator :
      (CombineValue.rangeRegisters regs).accumulator ∈
        footprint controller regs :=
    hscratch (by
      simpa [CombineValue.rangeRegisters] using
        combineScratch_slot regs (10 : Fin 19))
  have hTest :
      (CombineValue.rangeRegisters regs).test ∈
        footprint controller regs :=
    hscratch (by
      simpa [CombineValue.rangeRegisters] using
        combineScratch_slot regs (3 : Fin 19))
  have hRemaining :
      (CombineValue.rangeRegisters regs).remaining ∈
        footprint controller regs :=
    hscratch (by
      simpa [CombineValue.rangeRegisters] using
        combineScratch_slot regs (13 : Fin 19))
  have hOne :
      (CombineValue.rangeRegisters regs).one ∈
        footprint controller regs :=
    hscratch (by
      simpa [CombineValue.rangeRegisters] using
        combineScratch_slot regs (9 : Fin 19))
  cases op <;>
    simp_all [CombineValue.rangeFold, CombineValue.initializeFold,
      CombineValue.rangeFoldFrom, CombineValue.foldBody,
      CombineValue.foldCommand, CombineValue.copy,
      RuntimeArithmetic.addMod, RuntimeArithmetic.mulMod,
      RuntimeArithmetic.reduce, RuntimeArithmetic.reduceBody,
      RuntimeArithmetic.reduceTestOp,
      CombineValue.RangeRegisters.reduceRegisters,
      Cmd.seqList, Footprint.CmdWritesWithin,
      Footprint.BasicWritesWithin]

theorem command_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (footprint controller regs)
      (command tm order controller regs) := by
  have hterm :=
    assignmentTerm_writesWithin_internal
      tm order controller regs
  have hfold :=
    rangeFold_writesWithin .add controller regs
      (assignmentTerm tm order controller regs) hterm
  have hscratch :
      CombineValue.combineScratchFootprint regs ⊆
        footprint controller regs := by
    intro address haddress
    exact Finset.mem_union_left _ haddress
  have hresult :
      CombineBranch.chunkValue regs ∈
        footprint controller regs :=
    hscratch (by
      simpa [CombineBranch.chunkValue, Layout.residueScaleRegisters,
        NeighborhoodProgram.ResidueScaleRegisters.bank,
        NeighborhoodProgram.ResidueScaleRegisters.bankSlot,
        NeighborhoodProgram.ResidueBankRegisters.operand,
        Layout.residueScaleMap] using
        combineScratch_slot regs (11 : Fin 19))
  simp only [command, Cmd.seqList, Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono hscratch _
        (initializeAssignmentCount_writesWithin regs),
      hfold,
      by
        simpa [CombineTerm.copy, Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] using
          And.intro hresult hresult⟩

theorem command_specAt_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (hencoding :
      instanceData.encoding =
        NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    SpecAt order controller regs instanceData frame tape slot interval
      logicalBank code outputChunk := by
  intro store hcontext hone
  let range := rangeRegisters regs
  let payloadWidth :=
    NeighborhoodExecutableEvaluation.payloadWidth
      tm instanceData.blockLength
  let fanIn :=
    NeighborhoodExecutableEvaluation.graphFanIn workTapeCount
  let modulus := NeighborhoodScheduler.fieldModulus instanceData
  let assignmentCount := CombineValue.assignmentCount payloadWidth fanIn
  let term :=
    CombineValue.assignmentTerm payloadWidth fanIn
      (GuessedLocalEvaluation.booleanCombineAtGuess
        tm instanceData.blockLength instanceData.encoding
        instanceData.positive instanceData.guess interval tape slot)
      (CombineTerm.computationArguments frame logicalBank)
      outputChunk
  have hparameters :=
    hcontext.computation.computation.parameters
  obtain ⟨initialized, hinitializeRun, hinitializeCount,
      hinitializeOne⟩ :=
    initializeAssignmentCount_runs regs instanceData store hparameters
  have hinitializePrecise :=
    initializeAssignmentCount_preciseWrites regs
  have hinitializeOutside :
      ∀ address,
        address ∉
          ({range.remaining, range.count, range.one} : Finset ℕ) →
        initialized address = store address := by
    intro address haddress
    exact Footprint.runs_eq_outside hinitializePrecise
      hinitializeRun haddress
  have hinitializeABI :
      ControlDecode.PreservesABI regs store initialized :=
    CombineValue.preservesABI_of_combineScratch regs
      (initializeAssignmentCount_writesWithin regs)
      hinitializeRun
  have hinitializeBank :
      initialized regs.layout.bank = store regs.layout.bank := by
    apply hinitializeOutside
    simp [range, CombineValue.rangeRegisters,
      NeighborhoodTrial.Registers.layout, regs.injective.eq_iff]
  have hinitializeGuess :
      initialized controller.guess = store controller.guess := by
    apply hinitializeOutside
    simp [range, CombineValue.rangeRegisters]
    constructor
    · exact
        (regs.index_ne_controller
          (21 : Fin 34) (2 : Fin 17)).symm
    constructor
    · exact
        (regs.index_ne_controller
          (10 : Fin 34) (2 : Fin 17)).symm
    · exact
        (regs.index_ne_controller
          (17 : Fin 34) (2 : Fin 17)).symm
  have hinitializePacked :
      PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk initialized :=
    packedContext_transport regs instanceData frame tape slot interval
      logicalBank code outputChunk hcontext hinitializeABI
      hinitializeBank hinitializeGuess
  have hinitializeControllerOne :
      initialized controller.one = 1 := by
    rw [hinitializeOutside controller.one]
    · exact hone
    · simp [range, CombineValue.rangeRegisters]
      constructor
      · exact
          (regs.index_ne_controller
            (21 : Fin 34) (14 : Fin 17)).symm
      constructor
      · exact
          (regs.index_ne_controller
            (10 : Fin 34) (14 : Fin 17)).symm
      · exact
          (regs.index_ne_controller
            (17 : Fin 34) (14 : Fin 17)).symm
  have hinitializeStack :
      initialized (Layout.frameStackRegisters regs).word =
        store (Layout.frameStackRegisters regs).word := by
    apply hinitializeOutside
    simp [range, CombineValue.rangeRegisters,
      Layout.frameStackRegisters, Layout.frameStackMap,
      regs.injective.eq_iff]
  have hinitializeContext :
      TermContext controller regs instanceData frame tape slot interval
        logicalBank code outputChunk
        (store (Layout.frameStackRegisters regs).word)
        (store regs.layout.bank) initialized :=
    { context :=
        { packed := hinitializePacked
          count_eq := by
            simpa [assignmentCount, payloadWidth, fanIn] using
              hinitializeCount }
      controllerOne_eq := hinitializeControllerOne
      stack_eq := hinitializeStack
      bank_eq := hinitializeBank }
  have hinitializeModulus :
      initialized range.modulus = modulus := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters,
      modulus] using
      hinitializeABI.modulus_eq.trans hparameters.modulus_eq
  have hinitializeModulusPred :
      initialized range.modulusPred = modulus - 1 := by
    simpa [range, rangeRegisters, CombineValue.rangeRegisters,
      modulus] using
      hinitializeABI.modulusPred_eq.trans
        hparameters.modulusPred_eq
  have hmodulusPos : 0 < modulus := by
    simpa [modulus, NeighborhoodScheduler.fieldModulus,
      payloadWidth, fanIn] using
      CombineValue.fieldModulus_pos payloadWidth fanIn
  have htermSpec :=
    assignmentTerm_specAt_internal order controller regs instanceData
      frame tape slot interval logicalBank code outputChunk
      (store (Layout.frameStackRegisters regs).word)
      (store regs.layout.bank) hencoding hguess
  have hstable :
      CombineValue.StableUnderDriverWrites range
        (TermContext controller regs instanceData frame tape slot interval
          logicalBank code outputChunk
          (store (Layout.frameStackRegisters regs).word)
          (store regs.layout.bank)) := by
    intro initial final hcurrent houtside
    exact
      termContext_stableUnderDriverWrites controller regs instanceData
        frame tape slot interval logicalBank code outputChunk
        (store (Layout.frameStackRegisters regs).word)
        (store regs.layout.bank) hcurrent houtside
  obtain ⟨folded, hfoldRun, hfoldPost, hfoldContext⟩ :=
    CombineValue.rangeFold_runsAtContext .add range
      (assignmentTerm tm order controller regs) term initialized modulus
      assignmentCount
      (TermContext controller regs instanceData frame tape slot interval
        logicalBank code outputChunk
        (store (Layout.frameStackRegisters regs).word)
        (store regs.layout.bank))
      hstable htermSpec hmodulusPos hinitializeModulus
      hinitializeModulusPred
      (by
        simpa [assignmentCount, payloadWidth, fanIn] using
          hinitializeCount)
      hinitializeContext
  obtain ⟨final, hcopyRun, hcopyValue, hcopyOutside⟩ :=
    CombineTerm.copy_runs_internal
      (CombineBranch.chunkValue regs) range.accumulator folded
      (by
        change regs.index 19 ≠ regs.index 18
        exact regs.injective.ne (by decide))
  have hrun :
      Runs (command tm order controller regs) store final := by
    simpa [command, Cmd.seqList, range] using
      Runs.seq hinitializeRun (Runs.seq hfoldRun hcopyRun)
  have hvalue :
      final (CombineBranch.chunkValue regs) =
        NeighborhoodExecutableEvaluation.Residue.evaluateNode
          payloadWidth fanIn
          (GuessedLocalEvaluation.booleanCombineAtGuess
            tm instanceData.blockLength instanceData.encoding
            instanceData.positive instanceData.guess interval tape slot)
          (CombineTerm.computationArguments frame logicalBank)
          outputChunk := by
    calc
      final (CombineBranch.chunkValue regs) =
          folded range.accumulator :=
        hcopyValue
      _ = CombineValue.FoldOp.range .add modulus term
          assignmentCount :=
        hfoldPost.accumulator_eq
      _ =
          NeighborhoodExecutableEvaluation.Residue.evaluateNode
            payloadWidth fanIn
            (GuessedLocalEvaluation.booleanCombineAtGuess
              tm instanceData.blockLength instanceData.encoding
              instanceData.positive instanceData.guess interval tape slot)
            (CombineTerm.computationArguments frame logicalBank)
            outputChunk := by
        symm
        simpa [payloadWidth, fanIn, modulus, term, assignmentCount,
          NeighborhoodScheduler.fieldModulus] using
          CombineValue.evaluateNode_eq_assignmentRange payloadWidth fanIn
            (GuessedLocalEvaluation.booleanCombineAtGuess
              tm instanceData.blockLength instanceData.encoding
              instanceData.positive instanceData.guess interval tape slot)
            (CombineTerm.computationArguments frame logicalBank)
            outputChunk
  have habi :
      ControlDecode.PreservesABI regs store final :=
    preservesABI_of_footprint controller regs
      (command tm order controller regs)
      (command_writesWithin_internal tm order controller regs) hrun
  have hstack :
      final (Layout.frameStackRegisters regs).word =
        store (Layout.frameStackRegisters regs).word := by
    rw [hcopyOutside (Layout.frameStackRegisters regs).word]
    · exact hfoldContext.stack_eq
    · change regs.index 32 ≠ regs.index 19
      exact regs.injective.ne (by decide)
  have hbank :
      final regs.layout.bank = store regs.layout.bank := by
    rw [hcopyOutside regs.layout.bank]
    · exact hfoldContext.bank_eq
    · change regs.index 33 ≠ regs.index 19
      exact regs.injective.ne (by decide)
  have hcursor :
      final (Layout.active regs) = outputChunk.val := by
    rw [hcopyOutside (Layout.active regs)]
    · exact hfoldContext.context.packed.cursor_eq
    · change regs.index 28 ≠ regs.index 19
      exact regs.injective.ne (by decide)
  have hcontrollerOne :
      final controller.one = store controller.one := by
    calc
      final controller.one = folded controller.one := by
        apply hcopyOutside
        change controller.index 14 ≠ regs.index 19
        exact
          (regs.index_ne_controller
            (19 : Fin 34) (14 : Fin 17)).symm
      _ = 1 := hfoldContext.controllerOne_eq
      _ = store controller.one := hone.symm
  refine ⟨final, hrun, ?_⟩
  exact
    { value_eq := by
        simpa [payloadWidth, fanIn] using hvalue
      abi := habi
      stack_eq := hstack
      bank_eq := hbank
      cursor_eq := hcursor
      one_eq := hcontrollerOne }

end Internal
end ComputationChunkKernel
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
