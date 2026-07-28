/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Parameters.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Parameters.Internal

/-!
# Padded one-chunk parameters for grouped Cook--Mertz evaluation

For payload width `b` and fan-in `d`, choose

`p = b + d + 1`, `chunkBits = p`, and `chunkCount = 1`.

The resulting `Layout p p 1` is tight. Its chunk width is positive, its
interpolation cube has room for all `d` input coordinates, and a field width
of `2 * p` gives the exact catalytic-register cost

`2 * (d + 1) * p`.

This module establishes only these arithmetic and layout facts. It does not
construct the characteristic-two field or its executable representation.

## Main theorems

- `paddedWidth_pos` -- the padded width is nonzero
- `fanIn_coordinates_le` -- `d * 1 ≤ 2 ^ p`
- `chunkBits_le_paddedWidth` -- the chosen chunk fits the padded value
- `groupedRegisterBitBudget_eq` -- exact register-bit cost
- `groupedRegisterBitBudget_le_four_mul` -- generic grouped bound instance
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Parameters

/-- Exact value of the padded Boolean width. -/
@[simp] theorem paddedWidth_eq (payloadWidth fanIn : ℕ) :
    paddedWidth payloadWidth fanIn = payloadWidth + fanIn + 1 :=
  Internal.paddedWidth_eq_internal payloadWidth fanIn

/-- The selected chunk width is the padded Boolean width. -/
@[simp] theorem chunkBits_eq (payloadWidth fanIn : ℕ) :
    chunkBits payloadWidth fanIn =
      paddedWidth payloadWidth fanIn :=
  Internal.chunkBits_eq_internal payloadWidth fanIn

/-- The selected layout has one field coordinate per value. -/
@[simp] theorem chunkCount_eq :
    chunkCount = 1 :=
  Internal.chunkCount_eq_internal

/-- The charged field width is twice the padded Boolean width. -/
@[simp] theorem fieldBits_eq (payloadWidth fanIn : ℕ) :
    fieldBits payloadWidth fanIn =
      2 * paddedWidth payloadWidth fanIn :=
  Internal.fieldBits_eq_internal payloadWidth fanIn

/-- Padding by `fanIn + 1` always produces a positive width. -/
theorem paddedWidth_pos (payloadWidth fanIn : ℕ) :
    0 < paddedWidth payloadWidth fanIn :=
  Internal.paddedWidth_pos_internal payloadWidth fanIn

/-- The original payload embeds into the padded value. -/
theorem payloadWidth_le_paddedWidth (payloadWidth fanIn : ℕ) :
    payloadWidth ≤ paddedWidth payloadWidth fanIn :=
  Internal.payloadWidth_le_paddedWidth_internal payloadWidth fanIn

/-- The fan-in is strictly smaller than the padded width. -/
theorem fanIn_lt_paddedWidth (payloadWidth fanIn : ℕ) :
    fanIn < paddedWidth payloadWidth fanIn :=
  Internal.fanIn_lt_paddedWidth_internal payloadWidth fanIn

/-- The selected chunk fits in the padded Boolean value. -/
theorem chunkBits_le_paddedWidth (payloadWidth fanIn : ℕ) :
    chunkBits payloadWidth fanIn ≤
      paddedWidth payloadWidth fanIn :=
  Internal.chunkBits_le_paddedWidth_internal payloadWidth fanIn

/-- The parameter choice constructs a tight `Layout p p 1`. -/
theorem layout (payloadWidth fanIn : ℕ) :
    Layout (paddedWidth payloadWidth fanIn)
      (paddedWidth payloadWidth fanIn) 1 :=
  Internal.layout_internal payloadWidth fanIn

/-- One full-width chunk has exactly the padded-value capacity. -/
theorem capacity_eq_paddedWidth (payloadWidth fanIn : ℕ) :
    chunkCount * chunkBits payloadWidth fanIn =
      paddedWidth payloadWidth fanIn :=
  Internal.capacity_eq_paddedWidth_internal payloadWidth fanIn

/-- The padded chunk domain contains all `fanIn` input coordinates. -/
theorem fanIn_coordinates_le (payloadWidth fanIn : ℕ) :
    fanIn * chunkCount ≤
      2 ^ chunkBits payloadWidth fanIn :=
  Internal.fanIn_coordinates_le_internal payloadWidth fanIn

/-- Alias-free form of the grouped input-coordinate inequality. -/
theorem fanIn_mul_one_le_two_pow_paddedWidth
    (payloadWidth fanIn : ℕ) :
    fanIn * 1 ≤ 2 ^ paddedWidth payloadWidth fanIn :=
  Internal.fanIn_mul_one_le_two_pow_paddedWidth_internal
    payloadWidth fanIn

/-- Exact catalytic-register cost for one coordinate of width `2 * p`. -/
theorem groupedRegisterBitBudget_eq (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        chunkCount
        (fieldBits payloadWidth fanIn) =
      2 * (fanIn + 1) * paddedWidth payloadWidth fanIn :=
  Internal.groupedRegisterBitBudget_eq_internal payloadWidth fanIn

/-- Sharp register-bit bound supplied by the exact one-chunk cost. -/
theorem groupedRegisterBitBudget_le (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        chunkCount
        (fieldBits payloadWidth fanIn) ≤
      2 * (fanIn + 1) * paddedWidth payloadWidth fanIn :=
  Internal.groupedRegisterBitBudget_le_internal payloadWidth fanIn

/-- Instantiation of the generic `4 * (d + 1) * p` grouped-layout bound. -/
theorem groupedRegisterBitBudget_le_four_mul
    (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        chunkCount
        (fieldBits payloadWidth fanIn) ≤
      4 * (fanIn + 1) * paddedWidth payloadWidth fanIn :=
  Internal.groupedRegisterBitBudget_le_four_mul_internal
    payloadWidth fanIn

end Parameters

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
