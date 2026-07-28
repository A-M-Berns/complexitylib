/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderResultDecoding.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderQueryEvaluation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrialInstance

/-!
# Decoding completed provider-query results -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderResultDecoding
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

theorem storedResultResidues_eq_resultResidues_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run
          (NeighborhoodScheduler.Decision.queryInitial
            (ProviderRootInitialization.providerRoot
              instanceData interval child)))
        store) :
    storedResultResidues tm regs instanceData store =
      resultResidues tm instanceData interval child := by
  funext chunk
  exact hquery.bank (Fin.last (graphFanIn workTapeCount)) chunk

theorem decodedStoredResult_eq_decodedResult_internal
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run
          (NeighborhoodScheduler.Decision.queryInitial
            (ProviderRootInitialization.providerRoot
              instanceData interval child)))
        store) :
    decodedStoredResult tm regs instanceData store =
      decodedResult tm instanceData interval child := by
  rw [decodedStoredResult, decodedResult,
    storedResultResidues_eq_resultResidues_internal
      regs instanceData interval child store hquery]

theorem providerRoot_eq_graph_predecessorAt_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter tape boundary.val =
              some (NeighborhoodGraph.Guess.actualCenterTrajectory
                tm instanceData.x instanceData.blockLength
                  tape boundary.val)) :
    ProviderRootInitialization.providerRoot
        instanceData interval child =
      .graph
        (NeighborhoodGraph.predecessorAt
          tm instanceData.x instanceData.blockLength
            interval.val child) := by
  simp only [ProviderRootInitialization.providerRoot,
    NeighborhoodEvaluator.childAt]
  rw [dif_pos interval.isLt]
  rw [instanceData.guess.predecessorAt?_eq_of_prefix
    tm instanceData.x instanceData.blockLength interval child hprefix]

theorem some_decodedResult_eq_schedulerNodeContent_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (node : NeighborhoodGraph.Node workTapeCount)
    (hroot :
      ProviderRootInitialization.providerRoot
        instanceData interval child = .graph node) :
    some (decodedResult tm instanceData interval child) =
      NeighborhoodTrialInstance.schedulerNodeContent
        tm instanceData node := by
  simp only [decodedResult, resultResidues,
    NeighborhoodTrialInstance.schedulerNodeContent, hroot]

theorem decodedResult_eq_expectedContent_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter tape boundary.val =
              some (NeighborhoodGraph.Guess.actualCenterTrajectory
                tm instanceData.x instanceData.blockLength
                  tape boundary.val)) :
    decodedResult tm instanceData interval child =
      expectedContent tm instanceData interval child := by
  have hroot :=
    providerRoot_eq_graph_predecessorAt_internal
      instanceData interval child hprefix
  have hscheduler :=
    some_decodedResult_eq_schedulerNodeContent_internal
      instanceData interval child
        (NeighborhoodGraph.predecessorAt
          tm instanceData.x instanceData.blockLength
            interval.val child)
        hroot
  rw [NeighborhoodTrialInstance.schedulerNodeContent_eq_nodeCallback]
      at hscheduler
  have hexact :=
    Residue.nodeCallback_isPrefixExact
      tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess interval hprefix
        ((NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount).symm child)
  have hpredecessor :=
    instanceData.guess.predecessor?_eq_of_prefix
      tm instanceData.x instanceData.blockLength interval
        ((NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount).symm child) hprefix
  simp only [NeighborhoodGraph.Guess.EvaluatedProvider.inputAt?,
    hpredecessor, Option.bind_some] at hexact
  apply Option.some.inj
  exact hscheduler.trans (by
    simpa [NeighborhoodGraph.predecessorAt, expectedContent]
      using hexact)

theorem evaluate_runs_with_decoded_result_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : SchedulerStep.CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1)
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter tape boundary.val =
              some (NeighborhoodGraph.Guess.actualCenterTrajectory
                tm instanceData.x instanceData.blockLength
                  tape boundary.val)) :
    ∃ final,
      Runs
        (ProviderQueryEvaluation.evaluate
          tm order controller regs combine)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run
          (NeighborhoodScheduler.Decision.queryInitial
            (ProviderRootInitialization.providerRoot
              instanceData interval child)))
        final ∧
      decodedStoredResult tm regs instanceData final =
        expectedContent tm instanceData interval child ∧
      Representation.Parameters regs instanceData final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.verdict = child.val := by
  obtain ⟨final, hruns, hquery, hframeFinal,
      hinputLengthFinal, honeFinal, hguessFinal,
      hintervalFinal, hchildFinal⟩ :=
    ProviderQueryEvaluation.evaluate_runs
      order controller regs combine instanceData code interval child store
      hcombineWrites hcombine hencoding hguess hstoreGuess
      hstoreInterval hstoreChild hparameters hframe hinputLength hone
  exact
    ⟨final, hruns, hquery,
      (decodedStoredResult_eq_decodedResult_internal
        regs instanceData interval child final hquery).trans
          (decodedResult_eq_expectedContent_internal
            instanceData interval child hprefix),
      hquery.parameters, hframeFinal, hinputLengthFinal, honeFinal,
      hguessFinal, hintervalFinal, hchildFinal⟩

end Internal
end ProviderResultDecoding
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
