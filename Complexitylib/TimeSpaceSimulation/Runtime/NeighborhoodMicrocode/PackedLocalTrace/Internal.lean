/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalTrace.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalStep
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation

/-!
# Runtime-length packed local traces -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalTrace
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem toNTM_trace_one
    (tm : TM workTapeCount)
    (cfg : Cfg workTapeCount tm.Q) :
    tm.toNTM.trace 1 (fun _ => false) cfg =
      (tm.step cfg).getD cfg := by
  by_cases hhalt : cfg.state = tm.qhalt
  · simp [NTM.trace, TM.step, TM.toNTM, hhalt]
  · simp [NTM.trace, TM.step, TM.toNTM, hhalt]

private theorem trace_headsInWindow
    (tm : TM workTapeCount)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (hcenters :
      ∀ tape,
        blockIndex blockLength (tapeAt seed tape).head =
          centers tape)
    (steps : ℕ) (hsteps : steps ≤ blockLength) :
    PackedLocalStep.HeadsInWindow blockLength centers
      (tm.toNTM.trace steps (fun _ => false) seed) := by
  intro tape
  have htrace :=
    TimeSpaceSimulation.NTM.trace_head_in_threeBlockNeighborhood
      tm.toNTM blockLength steps (fun _ => false)
        seed tape hpositive hsteps
  have htrace' :
      InThreeBlockNeighborhood blockLength (centers tape)
        (tapeAt
          (tm.toNTM.trace steps (fun _ => false) seed) tape).head := by
    let finalHead :=
      (tapeAt
        (tm.toNTM.trace steps (fun _ => false) seed) tape).head
    exact Eq.mp
      (congrArg
        (fun center =>
          InThreeBlockNeighborhood blockLength center finalHead)
        (hcenters tape))
      htrace
  constructor
  · simpa [PackedLocalConfiguration.windowStart,
      threeBlockLower] using htrace'.1
  · apply lt_of_lt_of_le htrace'.2
    cases hcenter : centers tape with
    | zero =>
        simp [threeBlockUpper,
          PackedLocalConfiguration.windowStart,
          PackedLocalConfiguration.tapeSpan]
        omega
    | succ center =>
        simp [threeBlockUpper,
          PackedLocalConfiguration.windowStart,
          PackedLocalConfiguration.tapeSpan, Nat.add_mul]
        omega

private theorem preservesABI_trans
    (regs : NeighborhoodTrial.Registers controller)
    {first second third : Store}
    (hfirst : ControlDecode.PreservesABI regs first second)
    (hsecond : ControlDecode.PreservesABI regs second third) :
    ControlDecode.PreservesABI regs first third :=
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
    bankRadix_eq :=
      hsecond.bankRadix_eq.trans hfirst.bankRadix_eq
    bankDigitCount_eq :=
      hsecond.bankDigitCount_eq.trans hfirst.bankDigitCount_eq
    modulusPred_eq :=
      hsecond.modulusPred_eq.trans hfirst.modulusPred_eq
    modulus_eq := hsecond.modulus_eq.trans hfirst.modulus_eq }

private theorem preservesContext_trans
    (regs : NeighborhoodTrial.Registers controller)
    {first second third : Store}
    (hfirst : PreservesContext regs first second)
    (hsecond : PreservesContext regs second third) :
    PreservesContext regs first third :=
  { assignment_eq :=
      hsecond.assignment_eq.trans hfirst.assignment_eq
    accumulator_eq :=
      hsecond.accumulator_eq.trans hfirst.accumulator_eq
    one_eq := hsecond.one_eq.trans hfirst.one_eq
    catalyticWord_eq :=
      hsecond.catalyticWord_eq.trans hfirst.catalyticWord_eq
    abi := preservesABI_trans regs hfirst.abi hsecond.abi }

private def decrementStore
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) : Store :=
  (Basic.sub
    (CombineValue.rangeRegisters regs).count
    (CombineValue.rangeRegisters regs).count
    (CombineValue.rangeRegisters regs).one).exec store

private theorem decrement_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    Runs
      (.basic
        (.sub (CombineValue.rangeRegisters regs).count
          (CombineValue.rangeRegisters regs).count
          (CombineValue.rangeRegisters regs).one))
      store (decrementStore regs store) :=
  Runs.basic _ _

private theorem decrement_eq_of_ne
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (address : ℕ)
    (hne :
      address ≠ (CombineValue.rangeRegisters regs).count) :
    decrementStore regs store address = store address := by
  simp [decrementStore, Basic.exec, Function.update_of_ne, hne]

private theorem decrement_preservesABI
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    ControlDecode.PreservesABI regs store
      (decrementStore regs store) := by
  let fixed (slot : Fin 34) (hne : slot ≠ 10) :
      decrementStore regs store (regs.index slot) =
        store (regs.index slot) :=
    decrement_eq_of_ne regs store _ (regs.injective.ne hne)
  exact
    { fuel_eq := fixed 22 (by decide)
      nodeCode_eq := fixed 23 (by decide)
      scalar_eq := fixed 25 (by decide)
      out_eq := fixed 26 (by decide)
      phaseCode_eq := fixed 27 (by decide)
      active_eq := fixed 28 (by decide)
      blockLength_eq := fixed 2 (by decide)
      horizon_eq := fixed 3 (by decide)
      chunkCount_eq := fixed 7 (by decide)
      chunkRadix_eq := fixed 8 (by decide)
      frameRadix_eq := fixed 13 (by decide)
      bankRadix_eq := fixed 14 (by decide)
      bankDigitCount_eq := fixed 15 (by decide)
      modulusPred_eq := fixed 16 (by decide)
      modulus_eq := fixed 24 (by decide) }

private theorem decrement_preservesContext
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    PreservesContext regs store (decrementStore regs store) := by
  let fixed (slot : Fin 34) (hne : slot ≠ 10) :
      decrementStore regs store (regs.index slot) =
        store (regs.index slot) :=
    decrement_eq_of_ne regs store _ (regs.injective.ne hne)
  exact
    { assignment_eq := fixed 21 (by decide)
      accumulator_eq := fixed 18 (by decide)
      one_eq := fixed 17 (by decide)
      catalyticWord_eq := fixed 33 (by decide)
      abi := decrement_preservesABI regs store }

private theorem controller_guess_not_mem
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ PackedLocalStep.footprint regs := by
  intro hmember
  simp only [PackedLocalStep.footprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨slot, hslot⟩ := hmember
  exact regs.index_ne_controller
    (PackedLocalStep.writeMap slot) (2 : Fin 17) hslot

private theorem decrement_controller_guess
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) :
    decrementStore regs store controller.guess =
      store controller.guess := by
  apply decrement_eq_of_ne
  exact regs.index_ne_controller (10 : Fin 34) (2 : Fin 17) |>.symm

private theorem trace_loop_runs
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (suffix assignment processed remaining : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph
                (.computation nodeTape slot interval.val)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval.val logicalBank store)
    (hstoreGuess : store controller.guess = guessCode.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (hcentersGuess :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval.val)
    (hseedCenters :
      ∀ tape,
        blockIndex instanceData.blockLength
            (tapeAt seed tape).head =
          centers tape)
    (hbound :
      processed + remaining ≤ instanceData.blockLength)
    (hrep :
      PackedLocalRepresentation.Represents tm order
        instanceData.blockLength centers
        (tm.toNTM.trace processed (fun _ => false) seed)
        suffix
        (store (PackedLocalStep.bankRegisters regs).word))
    (hassignment :
      store (CombineValue.rangeRegisters regs).remaining =
        assignment)
    (hcount :
      store (CombineValue.rangeRegisters regs).count = remaining)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (trace tm order controller regs) store final ∧
      Post tm order instanceData.blockLength centers
        (tm.toNTM.trace (processed + remaining)
          (fun _ => false) seed)
        suffix regs store final := by
  induction remaining generalizing processed store with
  | zero =>
      refine ⟨store, Runs.whileZero hcount, ?_⟩
      exact
        { represents := by simpa using hrep
          count_eq := hcount
          context :=
            { assignment_eq := rfl
              accumulator_eq := rfl
              one_eq := rfl
              catalyticWord_eq := rfl
              abi :=
                { fuel_eq := rfl
                  nodeCode_eq := rfl
                  scalar_eq := rfl
                  out_eq := rfl
                  phaseCode_eq := rfl
                  active_eq := rfl
                  blockLength_eq := rfl
                  horizon_eq := rfl
                  chunkCount_eq := rfl
                  chunkRadix_eq := rfl
                  frameRadix_eq := rfl
                  bankRadix_eq := rfl
                  bankDigitCount_eq := rfl
                  modulusPred_eq := rfl
                  modulus_eq := rfl } }
          eq_outside := by
            intro address _
            rfl }
  | succ remaining ih =>
      let cfg :=
        tm.toNTM.trace processed (fun _ => false) seed
      have hprocessed : processed ≤ instanceData.blockLength := by
        omega
      have hnextBound :
          processed + 1 ≤ instanceData.blockLength := by
        omega
      have hheads :
          PackedLocalStep.HeadsInWindow instanceData.blockLength
            centers cfg := by
        exact trace_headsInWindow tm instanceData.blockLength
          instanceData.positive centers seed hseedCenters
          processed hprocessed
      have hnextHeadsTrace :
          PackedLocalStep.HeadsInWindow instanceData.blockLength
            centers
            (tm.toNTM.trace (processed + 1)
              (fun _ => false) seed) := by
        exact trace_headsInWindow tm instanceData.blockLength
          instanceData.positive centers seed hseedCenters
          (processed + 1) hnextBound
      have htraceNext :
          tm.toNTM.trace (processed + 1)
              (fun _ => false) seed =
            tm.toNTM.trace 1 (fun _ => false) cfg := by
        simpa [cfg] using
          tm.toNTM.trace_add_fun processed 1
            (fun _ => false) seed
      have hnext :
          (tm.step cfg).getD cfg =
            tm.toNTM.trace (processed + 1)
              (fun _ => false) seed :=
        (toNTM_trace_one tm cfg).symm.trans htraceNext.symm
      have hnextHeads :
          PackedLocalStep.HeadsInWindow instanceData.blockLength
            centers ((tm.step cfg).getD cfg) := by
        rw [hnext]
        exact hnextHeadsTrace
      obtain ⟨stepped, hstepRun, hstepPost⟩ :=
        PackedLocalStep.step_runs order regs instanceData nodeTape slot
          interval.val logicalBank guessCode centers cfg suffix
          (store (PackedLocalStep.bankRegisters regs).word)
          store hfits hcontext hstoreGuess hguess
          (Nat.le_of_lt interval.isLt) hcentersGuess hrep
          hheads hnextHeads rfl hone
      let decremented := decrementStore regs stepped
      have hdecrementRun :
          Runs
            (.basic
              (.sub (CombineValue.rangeRegisters regs).count
                (CombineValue.rangeRegisters regs).count
                (CombineValue.rangeRegisters regs).one))
            stepped decremented := by
        exact decrement_runs regs stepped
      have hdecrementContext :
          PreservesContext regs stepped decremented :=
        decrement_preservesContext regs stepped
      have hstepContext :
          PreservesContext regs store stepped :=
        { assignment_eq := hstepPost.context.assignment_eq
          accumulator_eq := hstepPost.context.accumulator_eq
          one_eq := hstepPost.context.one_eq
          catalyticWord_eq := hstepPost.context.catalyticWord_eq
          abi := hstepPost.context.abi }
      have hfirstContext :
          PreservesContext regs store decremented :=
        preservesContext_trans regs hstepContext hdecrementContext
      have hdecrementedContext :
          CombineTerm.ComputationContext regs instanceData nodeTape slot
            interval.val logicalBank decremented := by
        have hsteppedContext :
            CombineTerm.ComputationContext regs instanceData nodeTape slot
              interval.val logicalBank stepped := by
          exact
            CombineTerm.Internal.computationContext_transport_internal
              regs instanceData nodeTape slot interval.val logicalBank
              hcontext hstepPost.context.abi
              hstepPost.context.catalyticWord_eq
        exact
          CombineTerm.Internal.computationContext_transport_internal
            regs instanceData nodeTape slot interval.val logicalBank
            hsteppedContext (decrement_preservesABI regs stepped)
            hdecrementContext.catalyticWord_eq
      have hdecrementedGuess :
          decremented controller.guess = guessCode.val := by
        calc
          decremented controller.guess =
              stepped controller.guess :=
            decrement_controller_guess regs stepped
          _ = store controller.guess :=
            hstepPost.eq_outside controller.guess
              (controller_guess_not_mem regs)
          _ = guessCode.val := hstoreGuess
      have hdecrementedRep :
          PackedLocalRepresentation.Represents tm order
            instanceData.blockLength centers
            (tm.toNTM.trace (processed + 1)
              (fun _ => false) seed)
            suffix
            (decremented
              (PackedLocalStep.bankRegisters regs).word) := by
        change
          PackedLocalRepresentation.Represents tm order
            instanceData.blockLength centers
            (tm.toNTM.trace (processed + 1)
              (fun _ => false) seed)
            suffix
            (decrementStore regs stepped
              (PackedLocalStep.bankRegisters regs).word)
        rw [decrement_eq_of_ne regs stepped]
        · rw [← hnext]
          exact hstepPost.represents
        · exact regs.injective.ne (by decide)
      have hdecrementedAssignment :
          decremented (CombineValue.rangeRegisters regs).remaining =
            assignment := by
        exact hfirstContext.assignment_eq.trans hassignment
      have hdecrementedCount :
          decremented (CombineValue.rangeRegisters regs).count =
            remaining := by
        simp [decremented, decrementStore, Basic.exec,
          hstepPost.context.count_eq, hcount,
          hstepPost.context.one_eq, hone]
      have hdecrementedOne :
          decremented (CombineValue.rangeRegisters regs).one = 1 := by
        exact hfirstContext.one_eq.trans hone
      obtain ⟨final, hloopRun, hloopPost⟩ :=
        ih (processed := processed + 1) (store := decremented)
          hdecrementedContext hdecrementedGuess
          (by omega) hdecrementedRep hdecrementedAssignment
          hdecrementedCount hdecrementedOne
      have hbodyRun :
          Runs (body tm order controller regs) store decremented := by
        exact Runs.seq hstepRun hdecrementRun
      have hrun :
          Runs (trace tm order controller regs) store final := by
        exact Runs.whileNonzero (by omega) hbodyRun hloopRun
      refine ⟨final, hrun, ?_⟩
      exact
        { represents := by
            have htime :
                processed + 1 + remaining =
                  processed + (remaining + 1) := by
              omega
            rw [← htime]
            exact hloopPost.represents
          count_eq := hloopPost.count_eq
          context :=
            preservesContext_trans regs hfirstContext hloopPost.context
          eq_outside := by
            intro address haddress
            have haddressCount :
                address ≠
                  (CombineValue.rangeRegisters regs).count := by
              intro heq
              apply haddress
              rw [heq]
              apply Finset.mem_image.mpr
              exact ⟨(6 : Fin 17), Finset.mem_univ _, rfl⟩
            calc
              final address = decremented address :=
                hloopPost.eq_outside address haddress
              _ = stepped address :=
                decrement_eq_of_ne regs stepped address haddressCount
              _ = store address :=
                hstepPost.eq_outside address haddress }

theorem trace_runs_internal
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (assignment suffix : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph
                (.computation nodeTape slot interval.val)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval.val logicalBank store)
    (hstoreGuess : store controller.guess = guessCode.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (hword :
      store (PackedLocalStep.bankRegisters regs).word =
        PackedLocalConfiguration.assignmentStartWord
          tm order instanceData.blockLength instanceData.positive
          instanceData.guess interval assignment suffix)
    (hassignment :
      store (CombineValue.rangeRegisters regs).remaining =
        assignment)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        instanceData.blockLength)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (trace tm order controller regs) store final ∧
      Post tm order instanceData.blockLength
        (NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval.val)
        (GuessedLocalEvaluation.localTraceAtCenters
          tm instanceData.blockLength
          (NeighborhoodGraph.Guess.Consistency.guessedCenters
            instanceData.guess interval.val)
          (LocalAssignmentSemantics.assignmentInputs
            tm order instanceData.blockLength instanceData.positive
            assignment))
        suffix regs store final := by
  let centers :=
    NeighborhoodGraph.Guess.Consistency.guessedCenters
      instanceData.guess interval.val
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order instanceData.blockLength instanceData.positive assignment
  let seed :=
    NeighborhoodGraph.Guess.Consistency.localStartCfg
      tm instanceData.blockLength centers inputs
  have hrep :
      PackedLocalRepresentation.Represents tm order
        instanceData.blockLength centers
        (tm.toNTM.trace 0 (fun _ => false) seed)
        suffix
        (store (PackedLocalStep.bankRegisters regs).word) := by
    rw [hword]
    simpa [PackedLocalConfiguration.assignmentStartWord, centers,
      inputs, seed, NTM.trace] using
      PackedLocalRepresentation.encodeAbove_represents
        tm order instanceData.blockLength centers seed suffix
  have hseedCenters :
      ∀ tape,
        blockIndex instanceData.blockLength
            (tapeAt seed tape).head =
          centers tape := by
    intro tape
    exact
      PackedLocalConfiguration.localStartCfg_headBlock
        tm instanceData.blockLength instanceData.positive
        centers inputs tape
  obtain ⟨final, hrun, hpost⟩ :=
    trace_loop_runs order regs instanceData nodeTape slot interval
      logicalBank guessCode centers seed suffix assignment 0
      instanceData.blockLength store hfits hcontext hstoreGuess
      hguess rfl hseedCenters (by omega) hrep hassignment hcount hone
  refine ⟨final, hrun, ?_⟩
  change
    Post tm order instanceData.blockLength centers
      (tm.toNTM.trace instanceData.blockLength
        (fun _ => false) seed)
      suffix regs store final
  rw [Nat.zero_add] at hpost
  exact hpost

theorem trace_writesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (PackedLocalStep.footprint regs)
      (trace tm order controller regs) := by
  unfold trace body
  exact
    ⟨PackedLocalStep.step_writesWithin tm order controller regs,
      by
        apply Finset.mem_image.mpr
        refine ⟨(6 : Fin 17), Finset.mem_univ _, ?_⟩
        rfl⟩

theorem trace_compiledWritesWithin_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (trace tm order controller regs).compile
      (PackedLocalStep.footprint regs) :=
  Footprint.programWritesWithin_compile
    (trace_writesWithin_internal tm order controller regs)

-- The semantic refinement proof is developed below.

end Internal
end PackedLocalTrace
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
