/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComplexityBridge.Defs
import Complexitylib.TimeSpaceSimulation.ComplexityBridge.Internal

/-!
# Time-to-square-root-space complexity bridge

This module exposes the arithmetic and class-level shell for Williams's
square-root-space simulation. It does not assume the missing machine
construction: instead, `HasSpaceSimulation` and
`HasConcreteSpaceSimulation` state the precise contract that construction
must discharge.

The concrete functions use a positive ceiling square root and `log₂ n + 1`,
so they are total and usable as exact machine bounds. Under the theorem's
standard hypothesis `T(n) ≥ n`, they are asymptotically bounded by the exact
natural target `⌊√(T(n) log₂ T(n))⌋`.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComplexityBridge

/-- The natural square root is at most its ceiling. -/
theorem sqrt_le_ceilSqrt (n : ℕ) :
    Nat.sqrt n ≤ ceilSqrt n :=
  Internal.sqrt_le_ceilSqrt_internal n

/-- The square of the natural ceiling square root covers its argument. -/
theorem ceilSqrt_sq_ge (n : ℕ) :
    n ≤ ceilSqrt n * ceilSqrt n :=
  Internal.ceilSqrt_sq_ge_internal n

/-- The ceiling square root is at most one above the floor square root. -/
theorem ceilSqrt_le_sqrt_add_one (n : ℕ) :
    ceilSqrt n ≤ Nat.sqrt n + 1 :=
  Internal.ceilSqrt_le_sqrt_add_one_internal n

/-- Exact upper-bound characterization of the natural ceiling square root. -/
theorem ceilSqrt_le_iff {n m : ℕ} :
    ceilSqrt n ≤ m ↔ n ≤ m * m :=
  Internal.ceilSqrt_le_iff_internal

/-- The positive ceiling square root is always nonzero. -/
theorem positiveCeilSqrt_pos (n : ℕ) :
    0 < positiveCeilSqrt n :=
  Internal.positiveCeilSqrt_pos_internal n

/-- The positive ceiling square root still covers its argument when squared. -/
theorem positiveCeilSqrt_sq_ge (n : ℕ) :
    n ≤ positiveCeilSqrt n * positiveCeilSqrt n :=
  Internal.positiveCeilSqrt_sq_ge_internal n

/-- Replacing the zero ceiling by one preserves the floor-plus-one bound. -/
theorem positiveCeilSqrt_le_sqrt_add_one (n : ℕ) :
    positiveCeilSqrt n ≤ Nat.sqrt n + 1 :=
  Internal.positiveCeilSqrt_le_sqrt_add_one_internal n

/-- The protected logarithmic factor is positive on every input. -/
theorem protectedBinaryLog_pos (n : ℕ) :
    0 < protectedBinaryLog n :=
  Internal.protectedBinaryLog_pos_internal n

/-- On positive inputs, `log₂ n + 1` is at most `n`. -/
theorem protectedBinaryLog_le_self_of_pos {n : ℕ} (hn : 0 < n) :
    protectedBinaryLog n ≤ n :=
  Internal.protectedBinaryLog_le_self_of_pos_internal hn

/-- The balanced block is large enough to store its protected logarithmic
factor. -/
theorem protectedBinaryLog_le_balancedBlockLength (time : ℕ) :
    protectedBinaryLog time ≤ balancedBlockLength time :=
  Internal.protectedBinaryLog_le_balancedBlockLength_internal time

/-- The quotient contribution is at most one balanced block. -/
theorem quotient_mul_log_le_blockLength (time : ℕ) :
    time / balancedBlockLength time * protectedBinaryLog time ≤
      balancedBlockLength time :=
  Internal.quotient_mul_log_le_blockLength_internal time

/-- The chosen number of time blocks reaches at least the requested time
horizon. -/
theorem time_le_timeBlockCount_mul_blockLength (time : ℕ) :
    time ≤ timeBlockCount time * balancedBlockLength time :=
  Internal.time_le_timeBlockCount_mul_blockLength_internal time

/-- All full blocks plus a possible final partial block cost at most two
balanced blocks after multiplication by the logarithmic path width. -/
theorem timeBlockCount_mul_log_le (time : ℕ) :
    timeBlockCount time * protectedBinaryLog time ≤
      2 * balancedBlockLength time :=
  Internal.timeBlockCount_mul_log_le_internal time

/-- The entire concrete balance is at most three balanced blocks. -/
theorem balancedWorkspace_le (time : ℕ) :
    balancedWorkspace time ≤ 3 * balancedBlockLength time :=
  Internal.balancedWorkspace_le_internal time

/-- Above the small-input boundary, the positive ceiling/protected-log block
length is at most three times the exact floor-square-root target. -/
theorem balancedBlockLength_le_three_mul_sqrtLog {time : ℕ}
    (htime : 2 ≤ time) :
    balancedBlockLength time ≤ 3 * Nat.sqrt (time * Nat.log 2 time) :=
  Internal.balancedBlockLength_le_three_mul_sqrtLog_internal htime

/-- The concrete balance is big-O of the positively rounded block length. -/
theorem concreteBalancedSpace_isBigO_rounded (T : ℕ → ℕ) :
    concreteBalancedSpace T =O roundedSqrtLogSpace T :=
  Internal.concreteBalancedSpace_isBigO_rounded_internal T

/-- If `T(n) ≥ n`, the total positive rounding convention is big-O of
`⌊√(T(n) log₂ T(n))⌋`. -/
theorem roundedSqrtLogSpace_isBigO {T : ℕ → ℕ}
    (hT : ∀ n, n ≤ T n) :
    roundedSqrtLogSpace T =O sqrtLogSpace T :=
  Internal.roundedSqrtLogSpace_isBigO_internal hT

/-- The standard concrete block/evaluator balance has the advertised
square-root-logarithmic asymptotic bound. -/
theorem concreteBalancedSpace_isBigO {T : ℕ → ℕ}
    (hT : ∀ n, n ≤ T n) :
    concreteBalancedSpace T =O sqrtLogSpace T :=
  Internal.concreteBalancedSpace_isBigO_internal hT

/-- A machine-level asymptotic simulation contract yields the corresponding
complexity-class containment, with an optional final weakening of the space
bound. -/
theorem HasSpaceSimulation.classContainment {T S S' : ℕ → ℕ}
    (hsim : HasSpaceSimulation T S) (hS : S =O S') :
    DTIME T ⊆ DSPACE S' :=
  Internal.hasSpaceSimulation_classContainment_internal hsim hS

/-- A concrete-space simulator is also an asymptotic-space simulator. -/
theorem HasConcreteSpaceSimulation.toHasSpaceSimulation
    {T S : ℕ → ℕ} (hsim : HasConcreteSpaceSimulation T S) :
    HasSpaceSimulation T S :=
  Internal.hasConcreteSpaceSimulation_toHasSpaceSimulation_internal hsim

/-- The final class-level theorem shell for Williams's simulation.

Once the machine-level construction establishes a positively rounded
square-root-logarithmic space simulator, no further complexity-class or
rounding work is needed. -/
theorem DTIME_subset_DSPACE_sqrtLogSpace_of_simulation {T : ℕ → ℕ}
    (hT : ∀ n, n ≤ T n)
    (hsim : HasSpaceSimulation T (roundedSqrtLogSpace T)) :
    DTIME T ⊆ DSPACE (sqrtLogSpace T) :=
  hsim.classContainment (roundedSqrtLogSpace_isBigO hT)

/-- A concrete simulator using the standard balanced workspace expression
implies the advertised square-root-logarithmic class containment. -/
theorem DTIME_subset_DSPACE_sqrtLogSpace_of_concreteBalancedSimulation
    {T : ℕ → ℕ} (hT : ∀ n, n ≤ T n)
    (hsim : HasConcreteSpaceSimulation T (concreteBalancedSpace T)) :
    DTIME T ⊆ DSPACE (sqrtLogSpace T) :=
  hsim.toHasSpaceSimulation.classContainment
    (concreteBalancedSpace_isBigO hT)

end ComplexityBridge

end TimeSpaceSimulation

end Complexity
