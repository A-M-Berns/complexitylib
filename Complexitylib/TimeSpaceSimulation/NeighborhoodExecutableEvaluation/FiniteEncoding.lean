/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.FiniteEncoding.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.FiniteEncoding.Internal

/-!
# Fixed finite coordinate orders for executable neighborhood evaluation

Every fixed source machine admits a state order.  Once chosen, `ofStateOrder`
constructs the block-dependent compact encoding without any further
input-dependent finite-type choice.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodExecutableEvaluation

namespace FiniteEncoding

/-- A fixed finite source state type can be hardwired into a simulator. -/
theorem exists_stateOrder (tm : TM workTapeCount) :
    Nonempty (StateOrder tm) :=
  Internal.exists_stateOrder_internal tm

end FiniteEncoding

end NeighborhoodExecutableEvaluation

end TimeSpaceSimulation

end Complexity
