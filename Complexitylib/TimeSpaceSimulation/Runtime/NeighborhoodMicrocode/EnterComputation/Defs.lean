/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterLeaf.Defs

/-!
# Successful computation-node entry

A positive-fuel computation node whose interval lies below the runtime
horizon starts the residue fold at residue one, with the remaining-residue
counter set to the predecessor of the nonzero residue count.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterComputation

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The active frame installed when a valid computation node starts its first
residue fold. -/
def prepareFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData) :
    NeighborhoodScheduler.Frame tm instanceData :=
  { frame with
    phase :=
      .prepare 1
        (NeighborhoodScheduler.Frame.residueCount instanceData - 1)
        0 }

/-- Seed the first residue fields and reuse the verified nonfinal-residue
advance fragment to install the initial prepare phase. -/
def start
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (Dispatcher.decodedResidue regs) 0),
      Dispatcher.copy
        (Dispatcher.decodedResiduesLeft regs)
        (Layout.modulusPred regs),
      CursorFinish.nextResidueAfterDecode regs]

/-- Select failure-value return or successful residue-fold initialization
from the active fuel and decoded computation interval. -/
def step
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .ifZero (Layout.fuel regs)
    (EnterLeaf.failure regs)
    (.seq
      (.basic
        (.sub (Layout.codecScratch regs)
          (Layout.horizon regs)
          (ControlDecode.nodePayload1 regs)))
      (.ifZero (Layout.codecScratch regs)
        (EnterLeaf.failure regs)
        (start regs)))

end EnterComputation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
