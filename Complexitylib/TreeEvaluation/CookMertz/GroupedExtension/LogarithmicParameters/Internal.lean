/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.LogarithmicParameters.Defs

/-!
# Proof internals for logarithmic grouped Cook--Mertz parameters

This file proves the exact ceiling-division, interpolation-domain, catalytic
bank, and per-frame arithmetic certificates for the logarithmic chunk choice.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace LogarithmicParameters

namespace Internal

theorem chunkBits_eq_internal (payloadWidth fanIn : ℕ) :
    chunkBits payloadWidth fanIn =
      Nat.log 2 (fanIn * payloadWidth) + 1 := by
  rfl

theorem chunkBits_pos_internal (payloadWidth fanIn : ℕ) :
    0 < chunkBits payloadWidth fanIn := by
  simp [chunkBits]

theorem chunkCount_eq_internal (payloadWidth fanIn : ℕ) :
    chunkCount payloadWidth fanIn =
      payloadWidth ⌈/⌉ chunkBits payloadWidth fanIn := by
  rfl

theorem fieldBits_eq_internal (payloadWidth fanIn : ℕ) :
    fieldBits payloadWidth fanIn =
      2 * chunkBits payloadWidth fanIn := by
  rfl

theorem frameBitBudget_eq_internal
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount =
      (2 * scalarCount + counterCount) *
        chunkBits payloadWidth fanIn := by
  unfold frameBitBudget fieldBits
  ring

theorem frameBitBudget_eq_log_internal
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount =
      (2 * scalarCount + counterCount) *
        (Nat.log 2 (fanIn * payloadWidth) + 1) := by
  rw [frameBitBudget_eq_internal, chunkBits_eq_internal]

theorem layout_internal (payloadWidth fanIn : ℕ) :
    Layout payloadWidth
      (chunkBits payloadWidth fanIn)
      (chunkCount payloadWidth fanIn) := by
  exact Layout.canonical payloadWidth
    (chunkBits payloadWidth fanIn)
    (chunkBits_pos_internal payloadWidth fanIn)

theorem chunkCount_pos_internal
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth) :
    0 < chunkCount payloadWidth fanIn := by
  have hcovers := (layout_internal payloadWidth fanIn).covers
  by_contra hnot
  have hzero : chunkCount payloadWidth fanIn = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rw [hzero] at hcovers
  simp at hcovers
  omega

theorem chunkCount_le_payloadWidth_internal
    (payloadWidth fanIn : ℕ) :
    chunkCount payloadWidth fanIn ≤ payloadWidth := by
  unfold chunkCount
  apply (ceilDiv_le_iff_le_mul
    (chunkBits_pos_internal payloadWidth fanIn)).2
  exact Nat.le_mul_of_pos_left payloadWidth
    (chunkBits_pos_internal payloadWidth fanIn)

theorem payloadWidth_le_capacity_internal
    (payloadWidth fanIn : ℕ) :
    payloadWidth ≤
      chunkCount payloadWidth fanIn *
        chunkBits payloadWidth fanIn :=
  (layout_internal payloadWidth fanIn).covers

theorem capacity_le_add_chunkBits_internal
    (payloadWidth fanIn : ℕ) :
    chunkCount payloadWidth fanIn *
        chunkBits payloadWidth fanIn ≤
      payloadWidth + chunkBits payloadWidth fanIn :=
  (layout_internal payloadWidth fanIn).tight

theorem inputCoordinates_le_internal
    (payloadWidth fanIn : ℕ) :
    fanIn * chunkCount payloadWidth fanIn ≤
      2 ^ chunkBits payloadWidth fanIn := by
  calc
    fanIn * chunkCount payloadWidth fanIn ≤
        fanIn * payloadWidth :=
      Nat.mul_le_mul_left fanIn
        (chunkCount_le_payloadWidth_internal payloadWidth fanIn)
    _ ≤ 2 ^ chunkBits payloadWidth fanIn := by
      simpa only [chunkBits, Nat.succ_eq_add_one] using
        (Nat.lt_pow_succ_log_self Nat.one_lt_two
          (fanIn * payloadWidth)).le

theorem inLogarithmicRegime_iff_internal
    (payloadWidth fanIn : ℕ)
    (hpayload : 0 < payloadWidth) (hfanIn : 0 < fanIn) :
    InLogarithmicRegime payloadWidth fanIn ↔
      fanIn * payloadWidth < 2 ^ payloadWidth := by
  unfold InLogarithmicRegime chunkBits
  rw [Nat.add_one_le_iff]
  exact Nat.log_lt_iff_lt_pow Nat.one_lt_two
    (Nat.mul_ne_zero hfanIn.ne' hpayload.ne')

theorem inLogarithmicRegime_or_small_internal
    (payloadWidth fanIn : ℕ) :
    InLogarithmicRegime payloadWidth fanIn ∨
      RequiresSmallCase payloadWidth fanIn := by
  unfold InLogarithmicRegime RequiresSmallCase
  exact le_or_gt (chunkBits payloadWidth fanIn) payloadWidth

theorem not_inLogarithmicRegime_iff_internal
    (payloadWidth fanIn : ℕ)
    (hpayload : 0 < payloadWidth) (hfanIn : 0 < fanIn) :
    ¬InLogarithmicRegime payloadWidth fanIn ↔
      2 ^ payloadWidth ≤ fanIn * payloadWidth := by
  simpa only [not_lt] using
    not_congr
      (inLogarithmicRegime_iff_internal
        payloadWidth fanIn hpayload hfanIn)

theorem requiresSmallCase_iff_internal
    (payloadWidth fanIn : ℕ)
    (hpayload : 0 < payloadWidth) (hfanIn : 0 < fanIn) :
    RequiresSmallCase payloadWidth fanIn ↔
      2 ^ payloadWidth ≤ fanIn * payloadWidth := by
  calc
    RequiresSmallCase payloadWidth fanIn ↔
        ¬InLogarithmicRegime payloadWidth fanIn := by
      unfold RequiresSmallCase InLogarithmicRegime
      omega
    _ ↔ 2 ^ payloadWidth ≤ fanIn * payloadWidth :=
      not_inLogarithmicRegime_iff_internal
        payloadWidth fanIn hpayload hfanIn

theorem chunkBits_le_payloadWidth_internal
    (payloadWidth fanIn : ℕ)
    (hregime : InLogarithmicRegime payloadWidth fanIn) :
    chunkBits payloadWidth fanIn ≤ payloadWidth :=
  hregime

theorem groupedRegisterBitBudget_eq_internal
    (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        (chunkCount payloadWidth fanIn)
        (fieldBits payloadWidth fanIn) =
      2 * (fanIn + 1) *
        (chunkCount payloadWidth fanIn *
          chunkBits payloadWidth fanIn) := by
  simp [groupedRegisterBitBudget, fieldBits]
  ring

theorem groupedRegisterBitBudget_le_padded_internal
    (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        (chunkCount payloadWidth fanIn)
        (fieldBits payloadWidth fanIn) ≤
      (fanIn + 1) * 2 *
        (payloadWidth + chunkBits payloadWidth fanIn) := by
  apply GroupedExtension.groupedRegisterBitBudget_le
    (layout_internal payloadWidth fanIn)
  exact le_rfl

theorem groupedRegisterBitBudget_le_four_mul_internal
    (payloadWidth fanIn : ℕ)
    (hregime : InLogarithmicRegime payloadWidth fanIn) :
    groupedRegisterBitBudget fanIn
        (chunkCount payloadWidth fanIn)
        (fieldBits payloadWidth fanIn) ≤
      4 * (fanIn + 1) * payloadWidth := by
  apply GroupedExtension.groupedRegisterBitBudget_le_four_mul
    (layout_internal payloadWidth fanIn)
  · exact le_rfl
  · exact hregime

end Internal

end LogarithmicParameters

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
