/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryLoop.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryLoop.Internal

/-!
# Uniform iteration of neighborhood query microsteps
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryLoop

open RAM Structured
open NeighborhoodExecutableEvaluation

/-- The complete query loop writes only inside the evaluator layout whenever
its fixed combine command does. -/
theorem run_writesWithin
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (run tm order controller regs combine) :=
  Internal.run_writesWithin_internal
    tm order controller regs combine hcombine

/-- Iterating the uniform body reaches the exact pure scheduler run while
preserving the public-input controller ABI and movement-code register. -/
theorem run_runs
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
    (state : NeighborhoodScheduler.State tm instanceData)
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
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hcoherent :
      NeighborhoodScheduler.Coherence.StateCoherent state)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (run tm order controller regs combine) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run state) final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val :=
  Internal.run_runs_internal
    order controller regs combine instanceData code state store
    hcombineWrites hcombine hencoding hguess hstoreGuess hquery
    hcoherent hframe hinputLength hone

end QueryLoop
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
