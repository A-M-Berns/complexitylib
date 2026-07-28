/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.PrimeField
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Search.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Search.Internal

/-!
# Executable Cook--Mertz prime choice

`PrimeField.searchChoice degree` streams the explicit finite interval

`degree + 2, ..., 2 * (degree + 1)`

with decidable primality and returns its first prime. Bertrand's postulate is
used only to prove the fallback unreachable; evaluating the definition runs
the tail-recursive scan and does not allocate the proof-side candidate list
or invoke a classical witness.

The selected modulus carries direct `NeZero` and primality-fact instances, so
`ZMod` arithmetic and `PrimeField.units` are executable without manually
transporting the `Choice` certificate.

## Main definitions and results

- `PrimeField.Search.searchModulus` -- executable selected modulus
- `PrimeField.searchChoice` -- executable certified choice
- `PrimeField.SearchField` -- selected `ZMod` field
- `PrimeField.searchUnits` -- executable nonzero-residue enumeration
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Search

@[simp] theorem isPrime_eq_true_iff (value : ℕ) :
    isPrime value = true ↔ value.Prime :=
  Internal.isPrime_eq_true_iff_internal value

/-- Membership in the explicit candidate list is exactly membership in the
Bertrand interval. -/
theorem mem_candidates_iff {degree value : ℕ} :
    value ∈ candidates degree ↔
      degree + 1 < value ∧ value ≤ 2 * (degree + 1) :=
  Internal.mem_candidates_iff_internal

/-- Bertrand's postulate puts a prime in the finite candidate list. -/
theorem exists_prime_mem_candidates (degree : ℕ) :
    ∃ modulus ∈ candidates degree, modulus.Prime :=
  Internal.exists_prime_mem_candidates_internal degree

/-- The streamed scan agrees with list search over the corresponding
consecutive range. The list occurs only in this correctness statement. -/
theorem scanPrime_eq_find_range' (fuel current : ℕ) :
    scanPrime fuel current =
      (List.range' current fuel).find? isPrime :=
  Internal.scanPrime_eq_find_range'_internal fuel current

/-- The runtime scan chooses the same first prime as the proof-side Bertrand
candidate list. -/
theorem firstPrime?_eq_find_candidates (degree : ℕ) :
    firstPrime? degree =
      (candidates degree).find? isPrime :=
  Internal.firstPrime?_eq_find_candidates_internal degree

/-- The executable finite search never reaches its fallback. -/
theorem firstPrime?_ne_none (degree : ℕ) :
    firstPrime? degree ≠ none :=
  Internal.firstPrime?_ne_none_internal degree

/-- The option-valued search returns the total executable modulus. -/
theorem firstPrime?_eq_some_searchModulus (degree : ℕ) :
    firstPrime? degree = some (searchModulus degree) :=
  Internal.firstPrime?_eq_some_searchModulus_internal degree

/-- The selected modulus is one of the scanned candidates. -/
theorem searchModulus_mem_candidates (degree : ℕ) :
    searchModulus degree ∈ candidates degree :=
  Internal.searchModulus_mem_candidates_internal degree

/-- The selected modulus is prime. -/
theorem searchModulus_prime (degree : ℕ) :
    (searchModulus degree).Prime :=
  Internal.searchModulus_prime_internal degree

/-- Exact strict lower and Bertrand upper bounds for the selected modulus. -/
theorem searchModulus_bounds (degree : ℕ) :
    degree + 1 < searchModulus degree ∧
      searchModulus degree ≤ 2 * (degree + 1) :=
  Internal.searchModulus_bounds_internal degree

/-- No smaller prime occurs after the lower endpoint of the finite scan. -/
theorem searchModulus_minimal
    (degree : ℕ) {prior : ℕ}
    (hlower : degree + 2 ≤ prior)
    (hprior : prior < searchModulus degree) :
    ¬prior.Prime :=
  Internal.searchModulus_minimal_internal degree hlower hprior

/-- Cook--Mertz's required strict degree cutoff for the selected modulus. -/
theorem degree_lt_searchModulus_sub_one (degree : ℕ) :
    degree < searchModulus degree - 1 :=
  Internal.degree_lt_searchModulus_sub_one_internal degree

end Search

/-- Executable prime-field choice obtained from the finite Bertrand scan. -/
def searchChoice (degree : ℕ) : Choice degree :=
  Search.Internal.searchChoiceInternal degree

@[simp] theorem searchChoice_modulus (degree : ℕ) :
    (searchChoice degree).modulus = Search.searchModulus degree :=
  rfl

/-- The option-valued scan returns the modulus stored in `searchChoice`. -/
theorem firstPrime?_eq_some_searchChoice_modulus (degree : ℕ) :
    Search.firstPrime? degree = some (searchChoice degree).modulus := by
  simpa using Search.firstPrime?_eq_some_searchModulus degree

instance instNeZeroSearchModulus (degree : ℕ) :
    NeZero (Search.searchModulus degree) :=
  ⟨(Search.searchModulus_prime degree).ne_zero⟩

instance instFactPrimeSearchModulus (degree : ℕ) :
    Fact (Search.searchModulus degree).Prime :=
  ⟨Search.searchModulus_prime degree⟩

/-- Prime field produced by the executable search. -/
abbrev SearchField (degree : ℕ) :=
  ZMod (Search.searchModulus degree)

/-- Explicit nonzero residues of the executably selected prime field. -/
def searchUnits (degree : ℕ) : List (SearchField degree)ˣ :=
  units (Search.searchModulus degree)

@[simp] theorem searchUnits_length (degree : ℕ) :
    (searchUnits degree).length =
      Search.searchModulus degree - 1 :=
  units_length (Search.searchModulus degree)

theorem searchUnits_nodup (degree : ℕ) :
    (searchUnits degree).Nodup :=
  units_nodup (Search.searchModulus degree)

/-- Every unit of the selected field occurs in the executable residue list. -/
theorem mem_searchUnits (degree : ℕ)
    (unit : (SearchField degree)ˣ) :
    unit ∈ searchUnits degree :=
  mem_units (Search.searchModulus degree) unit

/-- The executable residue list enumerates every selected field unit exactly
once. -/
theorem enumeratesSearchUnits (degree : ℕ) :
    EnumeratesUnits (searchUnits degree) :=
  enumeratesUnits (Search.searchModulus degree)

end PrimeField

end CookMertz

end TreeEval

end Complexity
