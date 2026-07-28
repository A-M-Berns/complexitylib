/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareDescent.Defs

/-!
# Concrete prepare-phase branch

The decoded child cursor is compared with the compile-time graph fan-in.
An in-range cursor descends to that child; an exhausted cursor changes the
active parent to its combine phase.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareBranch

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Runtime child-bound test followed by the selected prepare transition. -/
def step
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic
      (.imm (Layout.codecScratch regs)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)),
      .basic
        (.sub (Layout.codecScratch regs)
          (Layout.codecScratch regs)
          (Dispatcher.decodedChild regs)),
      .ifZero (Layout.codecScratch regs)
        (CursorFinish.finishPrepare regs)
        (PrepareDescent.descendChild
          workTapeCount controller regs)]

end PrepareBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
