/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.LogarithmicParameters.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.LogarithmicParameters.Internal

/-!
# Sharp logarithmic-chunk parameters for grouped Cook--Mertz evaluation

For positive payload width `B` and fan-in `d`, this module chooses

`q = log₂(d * B) + 1`, `t = ⌈B / q⌉`, and `fieldBits = 2 * q`.

The protected `+ 1` makes `q` positive. The canonical layout has type
`Layout B q t`, satisfies

`B ≤ t * q ≤ B + q`,

and its input-coordinate count obeys `d * t ≤ 2 ^ q`. Thus the field-width
charge is exactly `2q`, the catalytic bank is at most
`2(d + 1)(B + q)`, and every fixed collection of field scalars and `q`-bit
counters occupies an exact constant multiple of `q`.

The sharper linear catalytic bound requires `q ≤ B`. This condition cannot
hold for every pair `(B, d)`: for positive parameters it is equivalent to
`d * B < 2 ^ B`. The complementary branch is exposed as
`RequiresSmallCase`, rather than silently folded into an asymptotic claim.

## Main theorems

- `layout` -- the canonical `Layout B q t`
- `inputCoordinates_le` -- the degree-domain condition `d * t ≤ 2 ^ q`
- `inLogarithmicRegime_iff` -- exact boundary `q ≤ B ↔ dB < 2 ^ B`
- `groupedRegisterBitBudget_le_four_mul` -- catalytic bank at most
  `4(d + 1)B` in the logarithmic regime
- `frameBitBudget_eq_log` -- exact logarithmic per-frame accounting
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace LogarithmicParameters

/-- Exact protected logarithmic chunk width. -/
@[simp] theorem chunkBits_eq (payloadWidth fanIn : ℕ) :
    chunkBits payloadWidth fanIn =
      Nat.log 2 (fanIn * payloadWidth) + 1 :=
  Internal.chunkBits_eq_internal payloadWidth fanIn

/-- The protected logarithmic chunk width is always positive. -/
theorem chunkBits_pos (payloadWidth fanIn : ℕ) :
    0 < chunkBits payloadWidth fanIn :=
  Internal.chunkBits_pos_internal payloadWidth fanIn

/-- Exact ceiling-divided chunk count. -/
@[simp] theorem chunkCount_eq (payloadWidth fanIn : ℕ) :
    chunkCount payloadWidth fanIn =
      payloadWidth ⌈/⌉ chunkBits payloadWidth fanIn :=
  Internal.chunkCount_eq_internal payloadWidth fanIn

/-- One field element is charged exactly twice the chunk width. -/
@[simp] theorem fieldBits_eq (payloadWidth fanIn : ℕ) :
    fieldBits payloadWidth fanIn =
      2 * chunkBits payloadWidth fanIn :=
  Internal.fieldBits_eq_internal payloadWidth fanIn

/-- The field-width charge meets the `2q + O(1)` requirement with zero
additive overhead. -/
theorem fieldBits_le_two_mul_chunkBits (payloadWidth fanIn : ℕ) :
    fieldBits payloadWidth fanIn ≤
      2 * chunkBits payloadWidth fanIn :=
  (fieldBits_eq payloadWidth fanIn).le

/-- Fixed scalar and counter counts cost an exact constant multiple of `q`. -/
theorem frameBitBudget_eq
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount =
      (2 * scalarCount + counterCount) *
        chunkBits payloadWidth fanIn :=
  Internal.frameBitBudget_eq_internal
    payloadWidth fanIn scalarCount counterCount

/-- Expanded logarithmic form of the fixed-count per-frame budget. -/
theorem frameBitBudget_eq_log
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount =
      (2 * scalarCount + counterCount) *
        (Nat.log 2 (fanIn * payloadWidth) + 1) :=
  Internal.frameBitBudget_eq_log_internal
    payloadWidth fanIn scalarCount counterCount

/-- Canonical tight `Layout B q ⌈B / q⌉`. -/
theorem layout (payloadWidth fanIn : ℕ) :
    Layout payloadWidth
      (chunkBits payloadWidth fanIn)
      (chunkCount payloadWidth fanIn) :=
  Internal.layout_internal payloadWidth fanIn

/-- A positive payload uses at least one chunk. -/
theorem chunkCount_pos
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth) :
    0 < chunkCount payloadWidth fanIn :=
  Internal.chunkCount_pos_internal payloadWidth fanIn hpayload

/-- The positive chunk width makes the number of chunks at most `B`. -/
theorem chunkCount_le_payloadWidth (payloadWidth fanIn : ℕ) :
    chunkCount payloadWidth fanIn ≤ payloadWidth :=
  Internal.chunkCount_le_payloadWidth_internal payloadWidth fanIn

/-- The chunks cover all payload bits. -/
theorem payloadWidth_le_capacity (payloadWidth fanIn : ℕ) :
    payloadWidth ≤
      chunkCount payloadWidth fanIn *
        chunkBits payloadWidth fanIn :=
  Internal.payloadWidth_le_capacity_internal payloadWidth fanIn

/-- Ceiling division wastes at most one chunk width. -/
theorem capacity_le_add_chunkBits (payloadWidth fanIn : ℕ) :
    chunkCount payloadWidth fanIn *
        chunkBits payloadWidth fanIn ≤
      payloadWidth + chunkBits payloadWidth fanIn :=
  Internal.capacity_le_add_chunkBits_internal payloadWidth fanIn

/-- All grouped input coordinates fit in the Boolean chunk domain. -/
theorem inputCoordinates_le (payloadWidth fanIn : ℕ) :
    fanIn * chunkCount payloadWidth fanIn ≤
      2 ^ chunkBits payloadWidth fanIn :=
  Internal.inputCoordinates_le_internal payloadWidth fanIn

/-- For positive parameters, `q ≤ B` has the exact exponential boundary
`dB < 2 ^ B`. -/
theorem inLogarithmicRegime_iff
    (payloadWidth fanIn : ℕ)
    (hpayload : 0 < payloadWidth) (hfanIn : 0 < fanIn) :
    InLogarithmicRegime payloadWidth fanIn ↔
      fanIn * payloadWidth < 2 ^ payloadWidth :=
  Internal.inLogarithmicRegime_iff_internal
    payloadWidth fanIn hpayload hfanIn

/-- Every parameter pair lies either in the logarithmic regime or in the
explicit relative-small-width branch. -/
theorem inLogarithmicRegime_or_small (payloadWidth fanIn : ℕ) :
    InLogarithmicRegime payloadWidth fanIn ∨
      RequiresSmallCase payloadWidth fanIn :=
  Internal.inLogarithmicRegime_or_small_internal payloadWidth fanIn

/-- Positive parameters require the small-case branch exactly when
`2 ^ B ≤ dB`. -/
theorem requiresSmallCase_iff
    (payloadWidth fanIn : ℕ)
    (hpayload : 0 < payloadWidth) (hfanIn : 0 < fanIn) :
    RequiresSmallCase payloadWidth fanIn ↔
      2 ^ payloadWidth ≤ fanIn * payloadWidth :=
  Internal.requiresSmallCase_iff_internal
    payloadWidth fanIn hpayload hfanIn

/-- In the logarithmic regime, the chosen chunk fits inside the payload. -/
theorem chunkBits_le_payloadWidth
    (payloadWidth fanIn : ℕ)
    (hregime : InLogarithmicRegime payloadWidth fanIn) :
    chunkBits payloadWidth fanIn ≤ payloadWidth :=
  Internal.chunkBits_le_payloadWidth_internal
    payloadWidth fanIn hregime

/-- Exact catalytic-register charge before using ceiling-layout bounds. -/
theorem groupedRegisterBitBudget_eq (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        (chunkCount payloadWidth fanIn)
        (fieldBits payloadWidth fanIn) =
      2 * (fanIn + 1) *
        (chunkCount payloadWidth fanIn *
          chunkBits payloadWidth fanIn) :=
  Internal.groupedRegisterBitBudget_eq_internal payloadWidth fanIn

/-- Unconditional catalytic-bank bound with one additive chunk of padding. -/
theorem groupedRegisterBitBudget_le_padded
    (payloadWidth fanIn : ℕ) :
    groupedRegisterBitBudget fanIn
        (chunkCount payloadWidth fanIn)
        (fieldBits payloadWidth fanIn) ≤
      (fanIn + 1) * 2 *
        (payloadWidth + chunkBits payloadWidth fanIn) :=
  Internal.groupedRegisterBitBudget_le_padded_internal
    payloadWidth fanIn

/-- In the logarithmic regime, the catalytic bank uses at most
`4 * (d + 1) * B` bits. -/
theorem groupedRegisterBitBudget_le_four_mul
    (payloadWidth fanIn : ℕ)
    (hregime : InLogarithmicRegime payloadWidth fanIn) :
    groupedRegisterBitBudget fanIn
        (chunkCount payloadWidth fanIn)
        (fieldBits payloadWidth fanIn) ≤
      4 * (fanIn + 1) * payloadWidth :=
  Internal.groupedRegisterBitBudget_le_four_mul_internal
    payloadWidth fanIn hregime

end LogarithmicParameters

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
