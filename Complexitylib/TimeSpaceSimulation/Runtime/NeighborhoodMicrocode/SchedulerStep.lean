/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SchedulerStep.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SchedulerStep.Internal

/-!
# One uniform neighborhood-scheduler microstep
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace SchedulerStep

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- The uniform phase dispatcher stays inside the evaluator layout whenever
the supplied fixed combine command does. -/
theorem step_writesWithin
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step tm order controller regs combine) :=
  Internal.step_writesWithin_internal
    tm order controller regs combine hcombine

/-- One uniform dispatch implements exactly one coherent nonterminal query
scheduler transition and preserves the public-input controller ABI. -/
theorem step_runs
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
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hcoherent :
      NeighborhoodScheduler.Coherence.StateCoherent
        { stack := frame :: rest
          registers := logicalBank })
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (step tm order controller regs combine) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 :=
  Internal.step_runs_internal order controller regs combine
    instanceData code frame rest logicalBank store hcombineWrites
    hcombine hencoding hguess hstoreGuess hquery hcoherent hframe
    hinputLength hone

end SchedulerStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
