/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Defs

/-!
# Operational bounds for runtime neighborhood instances

The first-order evaluator receives only bounded ternary movement guesses.
This module records the corresponding compact-node bounds used by the packed
frame codec.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodProgram
namespace InstanceBounds

open NeighborhoodGraph

/-- A graph node fits the numeric horizon carried by a runtime instance.
Source blocks use an inclusive bound; computation nodes use a strict interval
bound. -/
def NodeWithin (horizon : ℕ) : Node workTapeCount → Prop
  | .source _ block => block ≤ horizon
  | .computation _ _ interval => interval < horizon

/-- The explicit failure query is always bounded. -/
def QueryNodeWithin (horizon : ℕ) :
    NeighborhoodEvaluator.QueryNode workTapeCount horizon → Prop
  | .failure => True
  | .graph node => NodeWithin horizon node

end InstanceBounds
end NeighborhoodProgram
end Runtime
end TimeSpaceSimulation
end Complexity
