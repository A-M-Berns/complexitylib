/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Search.Defs

/-!
# Correctness of executable prime-modulus search

Bertrand's postulate proves that the finite scan cannot reach its fallback.
The selected list element inherits executable primality and the exact interval
bounds needed by `PrimeField.Choice`.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Search

namespace Internal

theorem isPrime_eq_true_iff_internal (value : ℕ) :
    isPrime value = true ↔ value.Prime := by
  simp [isPrime]

theorem mem_candidates_iff_internal {degree value : ℕ} :
    value ∈ candidates degree ↔
      degree + 1 < value ∧ value ≤ 2 * (degree + 1) := by
  constructor
  · intro hmem
    rw [candidates, List.mem_map] at hmem
    obtain ⟨offset, hoffset, rfl⟩ := hmem
    have hoffsetLt := List.mem_range.mp hoffset
    omega
  · rintro ⟨hlower, hupper⟩
    let offset := value - (degree + 2)
    have hoffsetLt : offset < degree + 1 := by
      dsimp [offset]
      omega
    have hvalue : degree + 2 + offset = value := by
      dsimp [offset]
      omega
    rw [candidates, List.mem_map]
    exact ⟨offset, List.mem_range.mpr hoffsetLt, hvalue⟩

theorem exists_prime_mem_candidates_internal (degree : ℕ) :
    ∃ modulus ∈ candidates degree, modulus.Prime := by
  obtain ⟨modulus, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (degree + 1) (by omega)
  exact ⟨modulus,
    mem_candidates_iff_internal.mpr ⟨hlower, hupper⟩, hprime⟩

theorem scanPrime_eq_find_range'_internal
    (fuel current : ℕ) :
    scanPrime fuel current =
      (List.range' current fuel).find? isPrime := by
  induction fuel generalizing current with
  | zero =>
      simp [scanPrime]
  | succ fuel ih =>
      by_cases hprime : isPrime current = true
      · simp [scanPrime, List.range'_succ, hprime]
      · have hfalse : isPrime current = false :=
          Bool.eq_false_of_not_eq_true hprime
        simp [scanPrime, List.range'_succ, hfalse,
          ih (current + 1)]

theorem firstPrime?_eq_find_candidates_internal (degree : ℕ) :
    firstPrime? degree =
      (candidates degree).find? isPrime := by
  rw [firstPrime?, scanPrime_eq_find_range'_internal,
    List.range'_eq_map_range]
  rfl

theorem firstPrime?_ne_none_internal (degree : ℕ) :
    firstPrime? degree ≠ none := by
  intro hnone
  obtain ⟨modulus, hmem, hprime⟩ :=
    exists_prime_mem_candidates_internal degree
  have hfindNone :
      (candidates degree).find? isPrime = none := by
    rw [← firstPrime?_eq_find_candidates_internal]
    exact hnone
  have hnot := (List.find?_eq_none.mp hfindNone) modulus hmem
  exact hnot
    (isPrime_eq_true_iff_internal modulus |>.2 hprime)

theorem firstPrime?_eq_some_searchModulus_internal (degree : ℕ) :
    firstPrime? degree = some (searchModulus degree) := by
  cases hfind : firstPrime? degree with
  | none =>
      exact (firstPrime?_ne_none_internal degree hfind).elim
  | some modulus =>
      simp [searchModulus, hfind]

theorem scanPrime_prior_not_prime_internal
    {fuel current modulus : ℕ}
    (hscan : scanPrime fuel current = some modulus)
    {prior : ℕ} (hlower : current ≤ prior)
    (hprior : prior < modulus) :
    ¬prior.Prime := by
  induction fuel generalizing current with
  | zero =>
      simp [scanPrime] at hscan
  | succ fuel ih =>
      by_cases hcurrent : isPrime current = true
      · have hmodulus : modulus = current := by
          simpa [scanPrime, hcurrent] using hscan.symm
        omega
      · have hfalse : isPrime current = false :=
          Bool.eq_false_of_not_eq_true hcurrent
        have htail :
            scanPrime fuel (current + 1) = some modulus := by
          simpa [scanPrime, hfalse] using hscan
        by_cases heq : prior = current
        · subst prior
          exact fun hprime =>
            hcurrent
              ((isPrime_eq_true_iff_internal current).mpr hprime)
        · exact ih htail (by omega)

theorem searchModulus_prime_internal (degree : ℕ) :
    (searchModulus degree).Prime := by
  have hfind :=
    firstPrime?_eq_some_searchModulus_internal degree
  have hfindList :
      (candidates degree).find? isPrime =
        some (searchModulus degree) := by
    rw [← firstPrime?_eq_find_candidates_internal]
    exact hfind
  have hprimeBool : isPrime (searchModulus degree) = true := by
    exact List.find?_some hfindList
  exact (isPrime_eq_true_iff_internal _).mp hprimeBool

theorem searchModulus_mem_candidates_internal (degree : ℕ) :
    searchModulus degree ∈ candidates degree := by
  apply List.mem_of_find?_eq_some
  rw [← firstPrime?_eq_find_candidates_internal]
  exact firstPrime?_eq_some_searchModulus_internal degree

theorem searchModulus_bounds_internal (degree : ℕ) :
    degree + 1 < searchModulus degree ∧
      searchModulus degree ≤ 2 * (degree + 1) :=
  mem_candidates_iff_internal.mp
    (searchModulus_mem_candidates_internal degree)

theorem searchModulus_minimal_internal
    (degree : ℕ) {prior : ℕ}
    (hlower : degree + 2 ≤ prior)
    (hprior : prior < searchModulus degree) :
    ¬prior.Prime :=
  scanPrime_prior_not_prime_internal
    (firstPrime?_eq_some_searchModulus_internal degree)
    hlower hprior

theorem degree_lt_searchModulus_sub_one_internal (degree : ℕ) :
    degree < searchModulus degree - 1 := by
  have hlower := (searchModulus_bounds_internal degree).1
  omega

/-- The executable search packaged with its erased correctness proofs. -/
def searchChoiceInternal (degree : ℕ) : PrimeField.Choice degree where
  modulus := searchModulus degree
  prime := searchModulus_prime_internal degree
  degree_lt_sub_one :=
    degree_lt_searchModulus_sub_one_internal degree
  modulus_le_two_mul :=
    (searchModulus_bounds_internal degree).2

end Internal

end Search

end PrimeField

end CookMertz

end TreeEval

end Complexity
