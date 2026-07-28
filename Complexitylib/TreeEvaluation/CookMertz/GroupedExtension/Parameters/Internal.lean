/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Parameters.Defs

/-!
# Proof internals for padded grouped Cook--Mertz parameters

This file proves the arithmetic side conditions and exact catalytic-register
cost of the padded one-chunk parameter choice.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Parameters

namespace Internal

theorem paddedWidth_eq_internal (payloadWidth fanIn : ℕ) :
    paddedWidth payloadWidth fanIn = payloadWidth + fanIn + 1 := by
  rfl

theorem chunkBits_eq_internal (payloadWidth fanIn : ℕ) :
    chunkBits payloadWidth fanIn = paddedWidth payloadWidth fanIn := by
  rfl

theorem chunkCount_eq_internal :
    chunkCount = 1 := by
  rfl

theorem fieldBits_eq_internal (payloadWidth fanIn : ℕ) :
    fieldBits payloadWidth fanIn =
      2 * paddedWidth payloadWidth fanIn := by
  rfl

theorem paddedWidth_pos_internal (payloadWidth fanIn : ℕ) :
    0 < paddedWidth payloadWidth fanIn := by
  simp [paddedWidth]

theorem payloadWidth_le_paddedWidth_internal
    (payloadWidth fanIn : ℕ) :
    payloadWidth ≤ paddedWidth payloadWidth fanIn := by
  unfold paddedWidth
  omega

theorem fanIn_lt_paddedWidth_internal (payloadWidth fanIn : ℕ) :
    fanIn < paddedWidth payloadWidth fanIn := by
  simp [paddedWidth]

theorem chunkBits_le_paddedWidth_internal
    (payloadWidth fanIn : ℕ) :
    chunkBits payloadWidth fanIn ≤
      paddedWidth payloadWidth fanIn := by
  rfl

theorem layout_internal (payloadWidth fanIn : ℕ) :
    Layout (paddedWidth payloadWidth fanIn)
      (paddedWidth payloadWidth fanIn) 1 where
  chunkBits_pos := paddedWidth_pos_internal payloadWidth fanIn
  covers := by simp
  tight := by simp

theorem capacity_eq_paddedWidth_internal (payloadWidth fanIn : ℕ) :
    chunkCount * chunkBits payloadWidth fanIn =
      paddedWidth payloadWidth fanIn := by
  simp [chunkCount, chunkBits]

theorem fanIn_coordinates_le_internal (payloadWidth fanIn : ℕ) :
    fanIn * chunkCount ≤
      2 ^ chunkBits payloadWidth fanIn := by
  rw [chunkCount_eq_internal, Nat.mul_one, chunkBits_eq_internal]
  calc
    fanIn ≤ 2 ^ fanIn :=
      Nat.lt_two_pow_self.le
    _ ≤ 2 ^ paddedWidth payloadWidth fanIn :=
      Nat.pow_le_pow_right (by omega) (by
        unfold paddedWidth
        omega)

theorem fanIn_mul_one_le_two_pow_paddedWidth_internal
    (payloadWidth fanIn : ℕ) :
    fanIn * 1 ≤ 2 ^ paddedWidth payloadWidth fanIn := by
  simpa only [chunkCount_eq_internal, chunkBits_eq_internal] using
    fanIn_coordinates_le_internal payloadWidth fanIn

theorem groupedRegisterBitBudget_eq_internal
    (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        chunkCount
        (fieldBits payloadWidth fanIn) =
      2 * (fanIn + 1) * paddedWidth payloadWidth fanIn := by
  simp [groupedRegisterBitBudget, chunkCount, fieldBits]
  ring

theorem groupedRegisterBitBudget_le_internal
    (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        chunkCount
        (fieldBits payloadWidth fanIn) ≤
      2 * (fanIn + 1) * paddedWidth payloadWidth fanIn :=
  (groupedRegisterBitBudget_eq_internal payloadWidth fanIn).le

theorem groupedRegisterBitBudget_le_four_mul_internal
    (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        chunkCount
        (fieldBits payloadWidth fanIn) ≤
      4 * (fanIn + 1) * paddedWidth payloadWidth fanIn := by
  apply GroupedExtension.groupedRegisterBitBudget_le_four_mul
    (layout_internal payloadWidth fanIn)
  · simp [fieldBits]
  · exact chunkBits_le_paddedWidth_internal payloadWidth fanIn

end Internal

end Parameters

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
