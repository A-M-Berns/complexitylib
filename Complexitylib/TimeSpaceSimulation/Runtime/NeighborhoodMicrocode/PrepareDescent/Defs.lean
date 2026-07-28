/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildReady.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameInstall.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParentPhase.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareScale.Defs

/-!
# Concrete prepare-child descent

A prepare descent scales the selected catalytic child register, reconstructs
the phase decoder ABI consumed by parent advancement, suspends the advanced
parent, regenerates the selected child from the packed movement guess, and
installs the child as the new active frame.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareDescent

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The semantic parent continuation installed before a prepare child. -/
def advancedParent
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)) :
    NeighborhoodScheduler.Frame tm instanceData :=
  { frame with
    phase := .prepare residue residuesLeft (child.val + 1) }

/-- Core prepare descent under an initialized local constant.

Phase decoding is repeated after scaling because the packed-bank scaler
legitimately reuses the decoder's scratch cells. -/
def descendChildCore
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [PrepareScale.scaleChildTarget regs,
      ControlDecode.decodePhase regs,
      ParentPhase.suspendPrepare regs,
      ChildReady.prepare workTapeCount controller regs,
      FrameInstall.installPrepareChild regs]

/-- Initialize the local constant, scale one prepare target, suspend its
parent, regenerate the selected child, and install the child as the new active
frame. -/
def descendChild
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic
      (.imm (Dispatcher.cleanupInverseRegisters regs).one 1))
    (descendChildCore workTapeCount controller regs)

end PrepareDescent
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
