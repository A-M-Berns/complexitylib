/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SchedulerStep.Defs

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

/-- Iterate the fixed scheduler body until the represented continuation stack
sets its active flag to zero. -/
def run
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd) : Cmd :=
  .whileNonzero (Layout.active regs)
    (SchedulerStep.step tm order controller regs combine)

end QueryLoop
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
