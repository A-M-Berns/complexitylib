/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderRootInit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryLoop.Defs

/-!
# Complete uniform evaluation of one consistency-provider coordinate
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderQueryEvaluation

open RAM Structured
open NeighborhoodExecutableEvaluation

/-- Build the predecessor root selected by the outer interval/child cursors,
initialize its zero-bank query, and execute the complete scheduler loop. -/
def evaluate
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd) : Cmd :=
  Cmd.seq
    (ProviderRootInitialization.initializeProviderQuery
      workTapeCount controller regs)
    (QueryLoop.run tm order controller regs combine)

end ProviderQueryEvaluation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
