/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupScaleStep.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupScaleStep.Internal

/-!
# Concrete cleanup-scale scheduler step
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CleanupScaleStep

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The self-initializing cleanup-scale step stays inside the evaluator
layout. -/
theorem step_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint (step regs) :=
  Internal.step_writesWithin_internal regs

/-- A represented cleanup-scale frame is transformed into its exact
cleanup-call successor, with inverse scaling applied to precisely the
selected child coordinate. -/
theorem step_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (residue residuesLeft nextChild : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .cleanupScale residue residuesLeft child nextChild)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hdecodedNext :
      store (Dispatcher.decodedNextChild regs) = nextChild) :
    ∃ final,
      Runs (step regs) store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            resumedParent frame residue residuesLeft nextChild :: rest
          registers :=
            scaledBank frame residue child logicalBank }
        final :=
  Internal.step_runs_internal
    frame rest logicalBank regs store residue residuesLeft nextChild
    child hquery hphase hdecodedResidue hdecodedLeft hdecodedChild
    hdecodedNext

/-- The cleanup-scale command implements exactly one pure scheduler step. -/
theorem step_next_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (residue residuesLeft nextChild : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .cleanupScale residue residuesLeft child nextChild)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hdecodedNext :
      store (Dispatcher.decodedNextChild regs) = nextChild) :
    ∃ final,
      Runs (step regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final :=
  Internal.step_next_runs_internal
    frame rest logicalBank regs store residue residuesLeft nextChild
    child hquery hphase hdecodedResidue hdecodedLeft hdecodedChild
    hdecodedNext

end CleanupScaleStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
