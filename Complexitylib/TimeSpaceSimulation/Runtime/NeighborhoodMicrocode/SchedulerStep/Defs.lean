/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupScaleStep.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareBranch.Defs

/-!
# One uniform neighborhood-scheduler microstep

This definitions layer composes the four completed control phases with an
explicit combine command. The combine command is a parameter because its
runtime-driven tensor-basis kernel is a separate construction boundary; it
must nevertheless be one fixed command for every runtime instance.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace SchedulerStep

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- A fixed combine command implements every represented computation-frame
combine transition. The decoded residue fields are part of its runtime ABI. -/
def CombineSpec
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd) : Prop :=
  ∀ (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval residue residuesLeft : ℕ),
    instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength →
    frame.phase = .combine residue residuesLeft →
    frame.node = .graph (.computation tape slot interval) →
    interval < instanceData.horizon →
    Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store →
    SearchProgram.InputFrame
        controller regs.footprint instanceData.x store →
    store controller.inputLength = instanceData.x.length →
    store controller.one = 1 →
    store (Dispatcher.decodedResidue regs) = residue →
    store (Dispatcher.decodedResiduesLeft regs) = residuesLeft →
    ∃ final,
      Runs combine store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final

/-- Decode the active phase and execute its fixed uniform branch. -/
def step
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd) : Cmd :=
  Dispatcher.decodeAndDispatch regs
    (EnterBranch.step tm order regs)
    (PrepareBranch.step workTapeCount controller regs)
    combine
    (CleanupBranch.step workTapeCount controller regs)
    (CleanupScaleStep.step regs)

end SchedulerStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
