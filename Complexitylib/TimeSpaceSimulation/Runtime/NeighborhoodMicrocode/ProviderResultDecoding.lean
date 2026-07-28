/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderResultDecoding.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderResultDecoding.Internal

/-!
# Decoding completed provider-query results
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderResultDecoding

open RAM Structured
open NeighborhoodExecutableEvaluation

/-- A completed query-state representation identifies the packed
`Fin.last` row with the exact logical scheduler result, chunk by chunk. -/
theorem storedResultResidues_eq_resultResidues
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
      resultResidues tm instanceData interval child :=
  Internal.storedResultResidues_eq_resultResidues_internal
    regs instanceData interval child store hquery

/-- Applying the canonical residue decoder to the packed result row gives
the same compact content as decoding the pure scheduler result. -/
theorem decodedStoredResult_eq_decodedResult
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
      decodedResult tm instanceData interval child :=
  Internal.decodedStoredResult_eq_decodedResult_internal
    regs instanceData interval child store hquery

/-- On a correct center prefix, the runtime interval and role-major child
cursors select the corresponding semantic predecessor node. -/
theorem providerRoot_eq_graph_predecessorAt
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
            interval.val child) :=
  Internal.providerRoot_eq_graph_predecessorAt_internal
    instanceData interval child hprefix

/-- Whenever cursor selection produces a graph node, the decoded
distinguished row is exactly that node's scheduler-backed compact content. -/
theorem some_decodedResult_eq_schedulerNodeContent
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
        tm instanceData node :=
  Internal.some_decodedResult_eq_schedulerNodeContent_internal
    instanceData interval child node hroot

/-- On a correct center prefix, decoding the queried `Fin.last` scheduler
row gives the exact compact predecessor content for the selected cursor. -/
theorem decodedResult_eq_expectedContent
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
      expectedContent tm instanceData interval child :=
  Internal.decodedResult_eq_expectedContent_internal
    instanceData interval child hprefix

/-- Complete provider evaluation leaves a packed result whose canonical
decoding is the exact selected predecessor content, while preserving the
parameter representation, input frame, shared constants, guess, and both
outer cursors. -/
theorem evaluate_runs_with_decoded_result
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
      final controller.verdict = child.val :=
  Internal.evaluate_runs_with_decoded_result_internal
    order controller regs combine instanceData code interval child store
    hcombineWrites hcombine hencoding hguess hstoreGuess
    hstoreInterval hstoreChild hparameters hframe hinputLength hone hprefix

end ProviderResultDecoding
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
