/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram.Defs

/-!
# All-prefix invariants for fixed-register prime search -- definitions

This module names the eight-register mutable footprint used by
`PrimeSearch`.  The accompanying surface module proves that primality and
upward prime search preserve a common mutable-word bound at every structured
source-program point.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace PrimeSearchInvariant

open RAM Structured

/-- The finite set of direct destinations used by a prime-search allocation. -/
def footprint (regs : PrimeSearch.Registers) : Finset ℕ :=
  Finset.univ.image regs.index

/-- Every allocated prime-search register belongs to its footprint. -/
@[simp]
theorem index_mem_footprint
    (regs : PrimeSearch.Registers) (slot : Fin 8) :
    regs.index slot ∈ footprint regs :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

end PrimeSearchInvariant

end Runtime

end TimeSpaceSimulation

end Complexity
