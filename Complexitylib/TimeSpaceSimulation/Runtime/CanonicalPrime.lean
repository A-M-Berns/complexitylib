/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CanonicalPrime.Internal

/-!
# Canonical Cook--Mertz prime search

The natural-residue evaluator uses the first prime beginning at
`degree + 2`. This module identifies that executable modulus with the result
of the fixed-register structured-RAM prime search.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CanonicalPrime

open RAM Structured
open TreeEval CookMertz PrimeField

/-- The executable Cook--Mertz modulus is exactly the first prime scanned
from `degree + 2`. -/
theorem searchModulus_isFirstPrimeAtOrAbove
    (degree : ℕ) :
    PrimeSearch.IsFirstPrimeAtOrAbove
      (degree + 2) (PrimeField.Search.searchModulus degree) :=
  Internal.searchModulus_isFirstPrimeAtOrAbove_internal degree

/-- Any completed fixed-register search from the canonical lower endpoint
contains the evaluator's executable modulus. -/
theorem PrimeSearch.SearchPost.candidate_eq_searchModulus
    (regs : PrimeSearch.Registers) (store : Store)
    (degree : ℕ)
    (hpost : PrimeSearch.SearchPost regs (degree + 2) store) :
    store regs.candidate =
      PrimeField.Search.searchModulus degree :=
  Internal.searchPost_candidate_eq_searchModulus_internal
    regs store degree hpost

/-- Starting at `degree + 2`, fixed-register prime search terminates at the
exact canonical modulus used by the natural-residue evaluator. -/
theorem search_runs
    (regs : PrimeSearch.Registers) (store : Store)
    (degree : ℕ)
    (hlower : store regs.candidate = degree + 2) :
    ∃ final,
      Runs (PrimeSearch.search regs) store final ∧
      PrimeSearch.SearchPost regs (degree + 2) final ∧
      final regs.candidate =
        PrimeField.Search.searchModulus degree :=
  Internal.search_runs_internal regs store degree hlower

end CanonicalPrime

end Runtime

end TimeSpaceSimulation

end Complexity
