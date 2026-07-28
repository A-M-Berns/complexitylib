/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.PrimeSearch
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Search

/-!
# Canonical Cook--Mertz prime search internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CanonicalPrime

open RAM Structured
open TreeEval CookMertz PrimeField

namespace Internal

theorem searchModulus_isFirstPrimeAtOrAbove_internal
    (degree : ℕ) :
    PrimeSearch.IsFirstPrimeAtOrAbove
      (degree + 2) (PrimeField.Search.searchModulus degree) := by
  refine ⟨?_, PrimeField.Search.searchModulus_prime degree, ?_⟩
  · have hlower :=
      (PrimeField.Search.searchModulus_bounds degree).1
    omega
  · intro prior hlower hprior
    exact PrimeField.Search.searchModulus_minimal
      degree hlower hprior

theorem searchPost_candidate_eq_searchModulus_internal
    (regs : PrimeSearch.Registers) (store : Store)
    (degree : ℕ)
    (hpost : PrimeSearch.SearchPost regs (degree + 2) store) :
    store regs.candidate =
      PrimeField.Search.searchModulus degree := by
  apply Nat.le_antisymm
  · by_contra hnotLe
    have hprior :
        PrimeField.Search.searchModulus degree <
          store regs.candidate :=
      Nat.lt_of_not_ge hnotLe
    exact
      (hpost.firstPrime.2.2
        (PrimeField.Search.searchModulus degree)
        (searchModulus_isFirstPrimeAtOrAbove_internal degree).1
        hprior)
        (PrimeField.Search.searchModulus_prime degree)
  · by_contra hnotLe
    have hprior :
        store regs.candidate <
          PrimeField.Search.searchModulus degree :=
      Nat.lt_of_not_ge hnotLe
    exact
      (PrimeField.Search.searchModulus_minimal
        degree hpost.firstPrime.1 hprior)
        hpost.firstPrime.2.1

theorem search_runs_internal
    (regs : PrimeSearch.Registers) (store : Store)
    (degree : ℕ)
    (hlower : store regs.candidate = degree + 2) :
    ∃ final,
      Runs (PrimeSearch.search regs) store final ∧
      PrimeSearch.SearchPost regs (degree + 2) final ∧
      final regs.candidate =
        PrimeField.Search.searchModulus degree := by
  obtain ⟨final, hrun, hpost⟩ :=
    PrimeSearch.search_runs regs store (degree + 2) hlower
  exact ⟨final, hrun, hpost,
    searchPost_candidate_eq_searchModulus_internal
      regs final degree hpost⟩

end Internal

end CanonicalPrime

end Runtime

end TimeSpaceSimulation

end Complexity
