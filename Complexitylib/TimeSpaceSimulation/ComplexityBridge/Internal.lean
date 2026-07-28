/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComplexityBridge.Defs

/-!
# Proof internals for the time-to-square-root-space class bridge

This file proves the natural-number balancing inequalities and the generic
complexity-class transport theorem. Public statements are re-exposed from
`Complexitylib.TimeSpaceSimulation.ComplexityBridge`.
-/

open Asymptotics Filter

namespace Complexity

namespace TimeSpaceSimulation

namespace ComplexityBridge

namespace Internal

theorem sqrt_le_ceilSqrt_internal (n : ℕ) :
    Nat.sqrt n ≤ ceilSqrt n := by
  unfold ceilSqrt
  split_ifs <;> omega

theorem ceilSqrt_sq_ge_internal (n : ℕ) :
    n ≤ ceilSqrt n * ceilSqrt n := by
  unfold ceilSqrt
  split_ifs with h <;> nlinarith [Nat.sqrt_le n, Nat.lt_succ_sqrt n]

theorem ceilSqrt_le_sqrt_add_one_internal (n : ℕ) :
    ceilSqrt n ≤ Nat.sqrt n + 1 := by
  unfold ceilSqrt
  split_ifs <;> omega

theorem ceilSqrt_le_iff_internal {n m : ℕ} :
    ceilSqrt n ≤ m ↔ n ≤ m * m := by
  constructor
  · intro h
    exact (ceilSqrt_sq_ge_internal n).trans (Nat.mul_self_le_mul_self h)
  · intro h
    unfold ceilSqrt
    split_ifs with hsquare
    · rw [← Nat.mul_self_le_mul_self_iff]
      rwa [hsquare]
    · have hsqrtLt : Nat.sqrt n * Nat.sqrt n < n :=
        lt_of_le_of_ne (Nat.sqrt_le n) hsquare
      have hsqrtLtM : Nat.sqrt n < m :=
        Nat.mul_self_lt_mul_self_iff.mp (hsqrtLt.trans_le h)
      omega

theorem positiveCeilSqrt_pos_internal (n : ℕ) :
    0 < positiveCeilSqrt n := by
  simp [positiveCeilSqrt]

theorem positiveCeilSqrt_sq_ge_internal (n : ℕ) :
    n ≤ positiveCeilSqrt n * positiveCeilSqrt n := by
  exact (ceilSqrt_sq_ge_internal n).trans
    (Nat.mul_self_le_mul_self (Nat.le_max_right _ _))

theorem positiveCeilSqrt_le_sqrt_add_one_internal (n : ℕ) :
    positiveCeilSqrt n ≤ Nat.sqrt n + 1 := by
  simp [positiveCeilSqrt, ceilSqrt_le_sqrt_add_one_internal]

theorem protectedBinaryLog_pos_internal (n : ℕ) :
    0 < protectedBinaryLog n := by
  simp [protectedBinaryLog]

theorem protectedBinaryLog_le_self_of_pos_internal {n : ℕ} (hn : 0 < n) :
    protectedBinaryLog n ≤ n := by
  simpa [protectedBinaryLog] using Nat.log_lt_self 2 hn.ne'

theorem protectedBinaryLog_le_balancedBlockLength_internal (time : ℕ) :
    protectedBinaryLog time ≤ balancedBlockLength time := by
  rcases eq_or_ne time 0 with rfl | htime
  · simp [protectedBinaryLog, balancedBlockLength, positiveCeilSqrt, ceilSqrt]
  · have hlog :=
      protectedBinaryLog_le_self_of_pos_internal (Nat.pos_of_ne_zero htime)
    unfold balancedBlockLength
    rw [← Nat.mul_self_le_mul_self_iff]
    exact (Nat.mul_le_mul_right _ hlog).trans
      (positiveCeilSqrt_sq_ge_internal _)

theorem quotient_mul_log_le_blockLength_internal (time : ℕ) :
    time / balancedBlockLength time * protectedBinaryLog time ≤
      balancedBlockLength time := by
  have hb : 0 < balancedBlockLength time := by
    unfold balancedBlockLength
    exact positiveCeilSqrt_pos_internal _
  apply Nat.le_of_mul_le_mul_right (c := balancedBlockLength time) ?_ hb
  calc
    (time / balancedBlockLength time * protectedBinaryLog time) *
          balancedBlockLength time =
        (time / balancedBlockLength time * balancedBlockLength time) *
          protectedBinaryLog time := by
            ac_rfl
    _ ≤ time * protectedBinaryLog time :=
      Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ ≤ balancedBlockLength time * balancedBlockLength time := by
      unfold balancedBlockLength
      exact positiveCeilSqrt_sq_ge_internal _

theorem time_le_timeBlockCount_mul_blockLength_internal
    (time : ℕ) :
    time ≤ timeBlockCount time *
      balancedBlockLength time := by
  have hpositive :
      0 < balancedBlockLength time := by
    unfold balancedBlockLength
    exact positiveCeilSqrt_pos_internal _
  unfold timeBlockCount
  simpa [Nat.mul_comm] using
    Nat.le_of_lt
      (Nat.lt_mul_div_succ time hpositive)

theorem timeBlockCount_mul_log_le_internal (time : ℕ) :
    timeBlockCount time * protectedBinaryLog time ≤
      2 * balancedBlockLength time := by
  simp only [timeBlockCount, Nat.add_mul, one_mul]
  calc
    _ ≤ balancedBlockLength time + balancedBlockLength time :=
      Nat.add_le_add (quotient_mul_log_le_blockLength_internal time)
        (protectedBinaryLog_le_balancedBlockLength_internal time)
    _ = 2 * balancedBlockLength time := by omega

theorem balancedWorkspace_le_internal (time : ℕ) :
    balancedWorkspace time ≤ 3 * balancedBlockLength time := by
  exact (Nat.add_le_add_left (timeBlockCount_mul_log_le_internal time)
    (balancedBlockLength time)).trans_eq (by ring)

theorem balancedBlockLength_le_three_mul_sqrtLog_internal {time : ℕ}
    (htime : 2 ≤ time) :
    balancedBlockLength time ≤ 3 * Nat.sqrt (time * Nat.log 2 time) := by
  let ell := Nat.log 2 time
  let radicand := time * ell
  let root := Nat.sqrt radicand
  have hellPos : 0 < ell := Nat.log_pos (by omega) htime
  have hrootPos : 0 < root :=
    Nat.sqrt_pos.mpr (Nat.mul_pos (by omega) hellPos)
  have hprotected : protectedBinaryLog time ≤ 2 * ell := by
    simp only [protectedBinaryLog, ell]
    omega
  have hroundedRadicand :
      time * protectedBinaryLog time ≤ 2 * radicand := by
    dsimp [radicand]
    calc
      time * protectedBinaryLog time ≤ time * (2 * ell) :=
        Nat.mul_le_mul_left _ hprotected
      _ = 2 * (time * ell) := by ring
  have hradicandLt : radicand < (root + 1) * (root + 1) := by
    simpa only [root] using Nat.lt_succ_sqrt radicand
  have hscaledLt : 2 * radicand < (3 * root) * (3 * root) := by
    calc
      2 * radicand < 2 * ((root + 1) * (root + 1)) :=
        (Nat.mul_lt_mul_left (by omega)).2 hradicandLt
      _ ≤ (3 * root) * (3 * root) := by nlinarith
  have hsqrtLt :
      Nat.sqrt (time * protectedBinaryLog time) < 3 * root :=
    Nat.sqrt_lt.mpr (hroundedRadicand.trans_lt hscaledLt)
  calc
    balancedBlockLength time ≤
        Nat.sqrt (time * protectedBinaryLog time) + 1 := by
      unfold balancedBlockLength
      exact positiveCeilSqrt_le_sqrt_add_one_internal _
    _ ≤ 3 * root := by omega
    _ = 3 * Nat.sqrt (time * Nat.log 2 time) := by rfl

theorem concreteBalancedSpace_isBigO_rounded_internal (T : ℕ → ℕ) :
    concreteBalancedSpace T =O roundedSqrtLogSpace T := by
  have hpoint :
      ∀ n, concreteBalancedSpace T n ≤ 3 * roundedSqrtLogSpace T n := by
    intro n
    exact balancedWorkspace_le_internal (T n)
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 3 (BigO.refl (roundedSqrtLogSpace T)))

theorem roundedSqrtLogSpace_isBigO_internal {T : ℕ → ℕ}
    (hT : ∀ n, n ≤ T n) :
    roundedSqrtLogSpace T =O sqrtLogSpace T := by
  rw [BigO]
  apply IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop 2] with n hn
  simp only [Real.norm_natCast]
  exact_mod_cast balancedBlockLength_le_three_mul_sqrtLog_internal
    (hn.trans (hT n))

theorem concreteBalancedSpace_isBigO_internal {T : ℕ → ℕ}
    (hT : ∀ n, n ≤ T n) :
    concreteBalancedSpace T =O sqrtLogSpace T := by
  exact (concreteBalancedSpace_isBigO_rounded_internal T).trans
    (roundedSqrtLogSpace_isBigO_internal hT)

theorem hasSpaceSimulation_classContainment_internal {T S S' : ℕ → ℕ}
    (hsim : HasSpaceSimulation T S) (hS : S =O S') :
    DTIME T ⊆ DSPACE S' := by
  intro L hL
  rcases hL with ⟨workTapes, source, actualTime, hdecides, htime⟩
  obtain ⟨simulatorTapes, simulator, actualSpace, hspace, hspaceO⟩ :=
    hsim workTapes source L actualTime hdecides htime
  exact ⟨simulatorTapes, simulator, actualSpace, hspace, hspaceO.trans hS⟩

theorem hasConcreteSpaceSimulation_toHasSpaceSimulation_internal
    {T S : ℕ → ℕ} (hsim : HasConcreteSpaceSimulation T S) :
    HasSpaceSimulation T S := by
  intro workTapes source L actualTime hdecides htime
  obtain ⟨simulatorTapes, simulator, hspace⟩ :=
    hsim workTapes source L actualTime hdecides htime
  exact ⟨simulatorTapes, simulator, S, hspace, BigO.refl S⟩

end Internal

end ComplexityBridge

end TimeSpaceSimulation

end Complexity
