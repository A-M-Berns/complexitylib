/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryLoop.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.StateRootInitialization.Defs

/-!
# Complete uniform evaluation of the state-consistency root
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace StateQueryEvaluation

open RAM Structured
open NeighborhoodExecutableEvaluation

/-- Build the runtime state root, initialize its zero-bank query, and execute
the complete fixed scheduler loop. -/
def evaluate
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd) : Cmd :=
  Cmd.seq
    (StateRootInitialization.initializeStateQuery
      workTapeCount controller regs)
    (QueryLoop.run tm order controller regs combine)

end StateQueryEvaluation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
