/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterComputation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterLeaf.Defs

/-!
# Concrete enter-phase branch

The active query node is decoded once and dispatched by its semantic tag:
failure (`0`), source (`1`), or computation (`2`).
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterBranch

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Decode the active node and select its concrete enter transition. -/
def step
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Dispatcher.decodeAndDispatchNode regs
    (EnterLeaf.failure regs)
    (EnterLeaf.source tm order regs)
    (EnterComputation.step regs)

end EnterBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
