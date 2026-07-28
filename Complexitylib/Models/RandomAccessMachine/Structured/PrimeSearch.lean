/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.PrimeSearch.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.PrimeSearch.Internal

/-!
# Fixed-register primality and prime search

This module exposes a deterministic first-order structured RAM primality test
and an upward prime search. Both programs use eight fixed registers and stream
their search state without materializing candidate or divisor collections.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace PrimeSearch

/-- The fixed-register trial-division program terminates with the exact
Boolean primality verdict. -/
theorem primality_runs
    (regs : Registers) (store : Store) (candidate : ℕ)
    (hcandidate : store regs.candidate = candidate) :
    ∃ final,
      Runs (primality regs) store final ∧
      PrimalityPost regs candidate final :=
  Internal.primality_runs_internal regs store candidate hcandidate

/-- Upward fixed-register search terminates at exactly the first prime at or
above the entry candidate. -/
theorem search_runs
    (regs : Registers) (store : Store) (lower : ℕ)
    (hlower : store regs.candidate = lower) :
    ∃ final,
      Runs (search regs) store final ∧
      SearchPost regs lower final :=
  Internal.search_runs_internal regs store lower hlower

/-- A common numeric bound gives a constant-factor data-bit bound for all
eight allocated registers. -/
theorem bounded_dataBits
    (regs : Registers) (bound : ℕ) (store : Store)
    (hbounded : regs.Bounded bound store) :
    regs.dataBits store ≤ registerBitBudget bound :=
  Internal.bounded_dataBits_internal regs bound store hbounded

/-- Each allocated register individually fits the common bit width. -/
theorem bounded_bitlen
    (regs : Registers) (bound : ℕ) (store : Store)
    (hbounded : regs.Bounded bound store) (slot : Fin 8) :
    bitlen (store (regs.index slot)) ≤ bitlen bound := by
  simpa [bitlen] using Nat.size_le_size (hbounded slot)

/-- For candidates at least two, the exact primality postcondition bounds
every fixed register by the candidate itself. -/
theorem PrimalityPost.registers_bounded
    (regs : Registers) (candidate : ℕ) (store : Store)
    (hcandidate : 2 ≤ candidate)
    (hpost : PrimalityPost regs candidate store) :
    regs.Bounded candidate store :=
  Internal.primalityPost_bounded_internal
    regs candidate store hcandidate hpost

/-- The full primality state occupies at most eight candidate-width words. -/
theorem PrimalityPost.dataBits_le
    (regs : Registers) (candidate : ℕ) (store : Store)
    (hcandidate : 2 ≤ candidate)
    (hpost : PrimalityPost regs candidate store) :
    regs.dataBits store ≤ registerBitBudget candidate :=
  bounded_dataBits regs candidate store
    (hpost.registers_bounded regs candidate store hcandidate)

/-- Primality execution and its constant-factor terminal width certificate,
packaged together for runtime clients. -/
theorem primality_runs_bounded
    (regs : Registers) (store : Store) (candidate : ℕ)
    (hcandidateValue : store regs.candidate = candidate)
    (hcandidate : 2 ≤ candidate) :
    ∃ final,
      Runs (primality regs) store final ∧
      PrimalityPost regs candidate final ∧
      regs.dataBits final ≤ registerBitBudget candidate := by
  obtain ⟨final, hrun, hpost⟩ :=
    primality_runs regs store candidate hcandidateValue
  exact ⟨final, hrun, hpost,
    hpost.dataBits_le regs candidate final hcandidate⟩

/-- The terminal search state occupies at most eight selected-prime-width
words. -/
theorem SearchPost.dataBits_le
    (regs : Registers) (lower : ℕ) (store : Store)
    (hpost : SearchPost regs lower store) :
    regs.dataBits store ≤
      registerBitBudget (store regs.candidate) :=
  bounded_dataBits regs (store regs.candidate) store
    hpost.registers_bounded

/-- For a positive lower bound, the first selected prime is at most twice the
lower bound. -/
theorem SearchPost.candidate_le_two_mul
    (regs : Registers) (lower : ℕ) (store : Store)
    (hlower : 0 < lower)
    (hpost : SearchPost regs lower store) :
    store regs.candidate ≤ 2 * lower := by
  obtain ⟨prime, hprime, hlowerPrime, hprimeUpper⟩ :=
    Nat.bertrand lower (Nat.ne_of_gt hlower)
  apply le_trans (show store regs.candidate ≤ prime by
    by_contra hnotLe
    have hprimePrior : prime < store regs.candidate :=
      Nat.lt_of_not_ge hnotLe
    exact
      (hpost.firstPrime.2.2 prime hlowerPrime.le hprimePrior)
        hprime) hprimeUpper

/-- The selected prime has at most one more bit than a positive search lower
bound. -/
theorem SearchPost.candidate_bitlen_le
    (regs : Registers) (lower : ℕ) (store : Store)
    (hlower : 0 < lower)
    (hpost : SearchPost regs lower store) :
    bitlen (store regs.candidate) ≤ bitlen lower + 1 := by
  have hsize := Nat.size_le_size
    (hpost.candidate_le_two_mul regs lower store hlower)
  have hdouble :
      bitlen (2 * lower) = bitlen lower + 1 := by
    simpa [bitlen, Nat.shiftLeft_eq_mul_pow, Nat.mul_comm] using
      Nat.size_shiftLeft (Nat.ne_of_gt hlower) 1
  rw [← hdouble]
  simpa [bitlen] using hsize

/-- The complete terminal fixed-register state has a constant-factor bit
budget in the positive lower bound. -/
theorem SearchPost.dataBits_le_input
    (regs : Registers) (lower : ℕ) (store : Store)
    (hlower : 0 < lower)
    (hpost : SearchPost regs lower store) :
    regs.dataBits store ≤ searchBitBudget lower := by
  apply (hpost.dataBits_le regs lower store).trans
  unfold registerBitBudget searchBitBudget
  exact Nat.mul_le_mul_left 8
    (hpost.candidate_bitlen_le regs lower store hlower)

/-- Upward search execution, exact first-prime correctness, and the
constant-factor input-width certificate packaged together. -/
theorem search_runs_bounded
    (regs : Registers) (store : Store) (lower : ℕ)
    (hlowerValue : store regs.candidate = lower)
    (hlower : 0 < lower) :
    ∃ final,
      Runs (search regs) store final ∧
      SearchPost regs lower final ∧
      bitlen (final regs.candidate) ≤ bitlen lower + 1 ∧
      regs.dataBits final ≤ searchBitBudget lower := by
  obtain ⟨final, hrun, hpost⟩ :=
    search_runs regs store lower hlowerValue
  exact ⟨final, hrun, hpost,
    hpost.candidate_bitlen_le regs lower final hlower,
    hpost.dataBits_le_input regs lower final hlower⟩

end PrimeSearch

end Structured

end RAM

end Complexity
