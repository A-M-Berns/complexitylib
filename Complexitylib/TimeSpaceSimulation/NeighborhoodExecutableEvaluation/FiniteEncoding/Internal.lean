/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.FiniteEncoding.Defs

/-!
# Existence internals for fixed finite coordinate orders
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodExecutableEvaluation

namespace FiniteEncoding

namespace Internal

theorem exists_stateOrder_internal (tm : TM workTapeCount) :
    Nonempty (StateOrder tm) :=
  ⟨{ state := Fintype.equivFin tm.Q }⟩

end Internal

end FiniteEncoding

end NeighborhoodExecutableEvaluation

end TimeSpaceSimulation

end Complexity
