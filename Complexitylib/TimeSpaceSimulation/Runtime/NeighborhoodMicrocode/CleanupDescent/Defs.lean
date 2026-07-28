/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildReady
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Descent
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParentPhase

/-!
# Concrete cleanup-child descent

A cleanup-call descent advances and suspends its parent, regenerates the
selected child from the packed movement guess, and installs the child as a
live cleanup frame.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CleanupDescent

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The semantic parent continuation installed before a cleanup child. -/
def advancedParent
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)) :
    NeighborhoodScheduler.Frame tm instanceData :=
  { frame with
    phase :=
      .cleanupScale residue residuesLeft child (child.val + 1) }

/-- Advance and suspend a cleanup parent, regenerate its selected child,
and install the cleanup child as the new active frame. -/
def descendChild
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ParentPhase.suspendCleanup regs,
      ChildReady.prepare workTapeCount controller regs,
      FrameInstall.installCleanupChild regs]

end CleanupDescent
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
