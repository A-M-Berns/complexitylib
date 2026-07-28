/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryLoop
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.StateQueryEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.StateRootInitialization

/-!
# Complete uniform evaluation of the state-consistency root -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace StateQueryEvaluation
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

theorem evaluate_writesWithin_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (evaluate tm order controller regs combine) :=
  ⟨StateRootInitialization.initializeStateQuery_writesWithin
      workTapeCount controller regs,
    QueryLoop.run_writesWithin
      tm order controller regs combine hcombine⟩

theorem evaluate_runs_internal
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
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (evaluate tm order controller regs combine) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run
          (NeighborhoodScheduler.Decision.queryInitial
            (NeighborhoodEvaluator.stateRoot instanceData.guess)))
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val := by
  obtain ⟨initialized, hinitialize, hquery, hframeInitialized,
      hinputLengthInitialized, honeInitialized, hguessInitialized⟩ :=
    StateRootInitialization.initializeStateQuery_runs_preserving_abi
      controller regs instanceData code.val store hparameters hone
      hframe hinputLength hstoreGuess
  have hcoherent :
      NeighborhoodScheduler.Coherence.StateCoherent
        (NeighborhoodScheduler.Decision.queryInitial
          (NeighborhoodEvaluator.stateRoot instanceData.guess)) :=
    NeighborhoodScheduler.Coherence.stateCoherent_initial
      instanceData.horizon
      (NeighborhoodEvaluator.stateRoot instanceData.guess)
      (TreeEval.CookMertz.PrimeField.Runtime.normalize
        (NeighborhoodScheduler.fieldModulus instanceData) 1)
      (Fin.last (graphFanIn workTapeCount))
      NeighborhoodScheduler.Decision.zeroRegisters
  obtain ⟨final, hloop, hqueryFinal, hframeFinal,
      hinputLengthFinal, honeFinal, hguessFinal⟩ :=
    QueryLoop.run_runs
      order controller regs combine instanceData code
      (NeighborhoodScheduler.Decision.queryInitial
        (NeighborhoodEvaluator.stateRoot instanceData.guess))
      initialized hcombineWrites hcombine hencoding hguess
      hguessInitialized hquery hcoherent hframeInitialized
      hinputLengthInitialized honeInitialized
  exact
    ⟨final, by
      simpa [evaluate] using Runs.seq hinitialize hloop,
      hqueryFinal, hframeFinal, hinputLengthFinal, honeFinal,
      hguessFinal⟩

end Internal
end StateQueryEvaluation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
