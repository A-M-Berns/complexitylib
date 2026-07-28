/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CleanupDescent.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish.Defs

/-!
# Concrete cleanup-call branch

The decoded child cursor is compared with the compile-time graph fan-in.
An in-range cursor descends to the cleanup child; an exhausted cursor either
returns from the call or starts the next residue.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CleanupBranch

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Runtime child-bound test followed by the selected cleanup-call
transition. -/
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
        (CursorFinish.finishCleanup regs)
        (CleanupDescent.descendChild
          workTapeCount controller regs)]

end CleanupBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
