/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.Bertrand
import Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Defs

/-!
# Fixed-register primality and prime search — definitions

This module defines the first-order structured RAM programs used to select a
runtime prime in the Williams simulation. The primality test streams possible
divisors downward through one register and uses the runtime remainder program;
it never materializes a list of divisors. Prime search likewise increments one
candidate register and stops at the first prime at or above its entry value.

The allocation has eight registers, independent of the candidate. Every
arithmetic value used by the primality test is at most the candidate.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace PrimeSearch

/-- Eight distinct registers used by primality testing and prime search. -/
structure Registers where
  /-- Register allocation in the order candidate, result, divisor,
  divisor predecessor, remainder, reduction test, constant one, and loop
  activity. -/
  index : Fin 8 → ℕ
  /-- The fixed allocation is injective. -/
  injective : Function.Injective index

namespace Registers

/-- Distinct logical fields occupy distinct concrete registers. -/
theorem index_ne (regs : Registers) {first second : Fin 8}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

/-- Equality of allocated registers reflects equality of logical slots. -/
@[simp]
theorem index_inj_iff (regs : Registers) {first second : Fin 8} :
    regs.index first = regs.index second ↔ first = second :=
  regs.injective.eq_iff

/-- Current candidate; preserved by primality and incremented by search. -/
abbrev candidate (regs : Registers) : ℕ := regs.index 0

/-- Boolean-valued primality result: one for prime and zero otherwise. -/
abbrev result (regs : Registers) : ℕ := regs.index 1

/-- Current streamed divisor. -/
abbrev divisor (regs : Registers) : ℕ := regs.index 2

/-- Preserved value `divisor - 1` for the runtime remainder loop. -/
abbrev divisorPred (regs : Registers) : ℕ := regs.index 3

/-- Copy of the candidate reduced modulo the current divisor. -/
abbrev remainder (regs : Registers) : ℕ := regs.index 4

/-- Scratch register used by runtime reduction. -/
abbrev reduceTest (regs : Registers) : ℕ := regs.index 5

/-- Preserved constant one. -/
abbrev one (regs : Registers) : ℕ := regs.index 6

/-- Loop activity and branch-test scratch register. -/
abbrev active (regs : Registers) : ℕ := regs.index 7

/-- Runtime-remainder view of the fixed allocation. -/
def reduceRegisters (regs : Registers) :
    RuntimeArithmetic.ReduceRegisters where
  value := regs.remainder
  modulus := regs.divisor
  modulusPred := regs.divisorPred
  test := regs.reduceTest
  value_ne_modulus := regs.index_ne (by decide)
  value_ne_modulusPred := regs.index_ne (by decide)
  value_ne_test := regs.index_ne (by decide)
  modulus_ne_modulusPred := regs.index_ne (by decide)
  modulus_ne_test := regs.index_ne (by decide)
  modulusPred_ne_test := regs.index_ne (by decide)

/-- Every allocated data register is at most `bound`. -/
def Bounded (regs : Registers) (bound : ℕ) (store : Store) : Prop :=
  ∀ slot, store (regs.index slot) ≤ bound

/-- Total data-bit occupancy of the eight allocated registers. -/
def dataBits (regs : Registers) (store : Store) : ℕ :=
  ∑ slot : Fin 8, bitlen (store (regs.index slot))

end Registers

/-- Straight-line initialization shared by all primality tests.

After this block, `active = candidate - 1`. Thus candidates zero and one take
the small-number branch, while every candidate at least two enters trial
division. -/
def primalitySetupOps (regs : Registers) : List Basic :=
  [.imm regs.one 1,
    .imm regs.result 0,
    .imm regs.divisor 0,
    .imm regs.divisorPred 0,
    .imm regs.remainder 0,
    .imm regs.reduceTest 0,
    .sub regs.active regs.candidate regs.one]

/-- Initialize the divisor stream for a candidate known to be at least two. -/
def trialSetupOps (regs : Registers) : List Basic :=
  [.imm regs.result 1,
    .sub regs.divisor regs.candidate regs.one,
    .sub regs.divisorPred regs.divisor regs.one,
    .mul regs.active regs.result regs.divisorPred]

/-- Decrement a divisor that did not divide the candidate. -/
def decrementDivisor (regs : Registers) : Cmd :=
  Cmd.seq
    (.basic (.sub regs.divisor regs.divisor regs.one))
    (.basic (.sub regs.divisorPred regs.divisorPred regs.one))

/-- One streamed trial-division iteration.

At loop entry `result = 1`, so multiplying by `result` copies the candidate
into the remainder register. A zero remainder clears the result; otherwise the
divisor stream moves down by one. The final multiplication clears `active`
exactly when a divisor was found or the stream has passed divisor two. -/
def trialBody (regs : Registers) : Cmd :=
  Cmd.seq
    (.basic (.mul regs.remainder regs.candidate regs.result))
    (Cmd.seq
      (RuntimeArithmetic.reduce regs.reduceRegisters)
      (Cmd.seq
        (.ifZero regs.remainder
          (.basic (.imm regs.result 0))
          (decrementDivisor regs))
        (.basic (.mul regs.active regs.result regs.divisorPred))))

/-- Stream divisors until one divides the candidate or every proper divisor at
least two has been rejected. -/
def trialLoop (regs : Registers) : Cmd :=
  .whileNonzero regs.active (trialBody regs)

/-- Deterministic fixed-register primality test.

The command preserves `candidate` and writes exactly zero or one to `result`. -/
def primality (regs : Registers) : Cmd :=
  Cmd.seq
    (Cmd.basics (primalitySetupOps regs))
    (.ifZero regs.active
      .skip
      (Cmd.seq (Cmd.basics (trialSetupOps regs)) (trialLoop regs)))

/-- Set the search-loop test to one exactly when the last candidate was
composite. The primality result is Boolean-valued. -/
def refreshSearchTest (regs : Registers) : Cmd :=
  .basic (.sub regs.active regs.one regs.result)

/-- Advance to the next candidate, test it, and refresh the search-loop test. -/
def searchBody (regs : Registers) : Cmd :=
  Cmd.seq
    (.basic (.add regs.candidate regs.candidate regs.one))
    (Cmd.seq (primality regs) (refreshSearchTest regs))

/-- Starting from the value in `candidate`, stream upward to the first prime. -/
def search (regs : Registers) : Cmd :=
  Cmd.seq
    (primality regs)
    (Cmd.seq
      (refreshSearchTest regs)
      (.whileNonzero regs.active (searchBody regs)))

/-- A number is the first prime at or above `lower`. -/
def IsFirstPrimeAtOrAbove (lower candidate : ℕ) : Prop :=
  lower ≤ candidate ∧ candidate.Prime ∧
    ∀ prior, lower ≤ prior → prior < candidate → ¬prior.Prime

/-- Exact Boolean encoding produced by `primality`. -/
def primalityValue (candidate : ℕ) : ℕ :=
  if candidate.Prime then 1 else 0

/-- Exact functional and fixed-register width postcondition of primality. -/
structure PrimalityPost (regs : Registers) (candidate : ℕ)
    (store : Store) : Prop where
  /-- The tested candidate is preserved. -/
  candidate_eq : store regs.candidate = candidate
  /-- The result is the exact Boolean primality verdict. -/
  result_eq : store regs.result = primalityValue candidate
  /-- The streamed divisor remains no larger than the candidate. -/
  divisor_le : store regs.divisor ≤ candidate
  /-- The divisor predecessor remains no larger than the candidate. -/
  divisorPred_le : store regs.divisorPred ≤ candidate
  /-- The final remainder remains no larger than the candidate. -/
  remainder_le : store regs.remainder ≤ candidate
  /-- Runtime reduction leaves its test scratch cleared. -/
  reduceTest_eq : store regs.reduceTest = 0
  /-- The constant-one register is preserved. -/
  one_eq : store regs.one = 1
  /-- The trial loop is inactive on exit. -/
  active_eq : store regs.active = 0

/-- Exact functional and fixed-register width postcondition of upward search. -/
structure SearchPost (regs : Registers) (lower : ℕ)
    (store : Store) : Prop where
  /-- The candidate is the first prime at or above the entry value. -/
  firstPrime : IsFirstPrimeAtOrAbove lower (store regs.candidate)
  /-- The final primality verdict is true. -/
  result_eq : store regs.result = 1
  /-- All eight fixed registers are bounded by the selected prime. -/
  registers_bounded :
    regs.Bounded (store regs.candidate) store
  /-- The constant-one register is preserved. -/
  one_eq : store regs.one = 1
  /-- The search loop is inactive on exit. -/
  active_eq : store regs.active = 0

/-- Constant-factor data-bit budget for the eight fixed registers. -/
def registerBitBudget (candidate : ℕ) : ℕ :=
  8 * bitlen candidate

/-- Constant-factor fixed-register budget in terms of a positive search lower
bound. Bertrand's postulate supplies the one-bit cushion. -/
def searchBitBudget (lower : ℕ) : ℕ :=
  8 * (bitlen lower + 1)

end PrimeSearch

end Structured

end RAM

end Complexity
