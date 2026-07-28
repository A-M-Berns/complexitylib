/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits.Internal

/-!
# Executable packed radix words

This module exposes a reusable little-endian packed-word foundation for the
fixed-register Williams runtime. It is purely arithmetic: no RAM or Turing
machine implementation is assumed.

## Main definitions

- `digit`, `push`, `pop` — constant-description radix operations
- `foldDigits` — list-free least-to-most-significant streaming fold
- `rebuild`, `replace` — indexed packed-vector transformation

## Main results

- `pop_push`, `digit_push_zero`, `digit_push_succ` — exact stack laws
- `rebuild_digit`, `replace_digit_eq`, `replace_digit_ne` — exact digit laws
- `push_lt_pow`, `rebuild_lt_pow`, `replace_lt_pow` — fixed-length bounds
- `size_le_count_mul_width` — `count` digits of width `width` use at most
  `count * width` bits
- `size_isBigO_count_mul_width` — the corresponding asymptotic transport
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace PackedDigits

/-- Every decoded digit is below a positive base. -/
theorem digit_lt {base word index : ℕ} (hbase : 0 < base) :
    digit base word index < base :=
  Internal.digit_lt_internal hbase

/-- Popping a valid newly pushed digit restores the previous word. -/
theorem pop_push {base value word : ℕ}
    (hbase : 0 < base) (hvalue : value < base) :
    pop base (push base value word) = word :=
  Internal.pop_push_internal hbase hvalue

/-- A valid pushed value is exactly the new digit zero. -/
theorem digit_push_zero {base value word : ℕ}
    (hvalue : value < base) :
    digit base (push base value word) 0 = value :=
  Internal.digit_push_zero_internal hvalue

/-- Popping shifts every digit index down by one. -/
theorem digit_pop (base word index : ℕ) :
    digit base (pop base word) index =
      digit base word (index + 1) :=
  Internal.digit_pop_internal base word index

/-- Pushing shifts every old digit index up by one. -/
theorem digit_push_succ {base value word : ℕ}
    (hbase : 0 < base) (hvalue : value < base) (index : ℕ) :
    digit base (push base value word) (index + 1) =
      digit base word index :=
  Internal.digit_push_succ_internal hbase hvalue index

/-- Splitting off digit zero and pushing it back reconstructs the word. -/
theorem push_digit_pop (base word : ℕ) :
    push base (digit base word 0) (pop base word) = word :=
  Internal.push_digit_pop_internal base word

/-- A streaming fold over a pushed word consumes the pushed digit first. -/
theorem foldDigits_push {α : Type*}
    {base value word count : ℕ} (initial : α)
    (step : α → ℕ → α)
    (hbase : 0 < base) (hvalue : value < base) :
    foldDigits base (count + 1) (push base value word) initial step =
      foldDigits base count word (step initial value) step :=
  Internal.foldDigits_push_internal initial step hbase hvalue

/-- Pushing one valid digit onto a `count`-digit word yields a
`count + 1`-digit word. -/
theorem push_lt_pow {base value word count : ℕ}
    (hword : word < base ^ count) (hvalue : value < base) :
    push base value word < base ^ (count + 1) :=
  Internal.push_lt_pow_internal hword hvalue

/-- Popping a bounded nonempty word removes one radix position. -/
theorem pop_lt_pow {base word count : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ (count + 1)) :
    pop base word < base ^ count :=
  Internal.pop_lt_pow_internal hbase hword

/-- Rebuilding applies `transform` exactly at each in-range digit. -/
theorem rebuild_digit
    {base count word digitIndex : ℕ}
    {transform : ℕ → ℕ → ℕ}
    (hbase : 0 < base)
    (htransform : ∀ index value, value < base →
      transform index value < base)
    (hindex : digitIndex < count) :
    digit base (rebuild base count word transform) digitIndex =
      transform digitIndex (digit base word digitIndex) :=
  Internal.rebuild_digit_internal hbase htransform hindex

/-- A bounded digit transformation produces a `count`-digit word. -/
theorem rebuild_lt_pow
    {base count word : ℕ} {transform : ℕ → ℕ → ℕ}
    (hbase : 0 < base)
    (htransform : ∀ index value, value < base →
      transform index value < base) :
    rebuild base count word transform < base ^ count :=
  Internal.rebuild_lt_pow_internal hbase htransform

/-- Replacing an in-range coordinate installs the requested digit exactly. -/
theorem replace_digit_eq
    {base count word index value : ℕ}
    (hbase : 0 < base) (hvalue : value < base)
    (hindex : index < count) :
    digit base (replace base count word index value) index = value :=
  Internal.replace_digit_eq_internal hbase hvalue hindex

/-- Replacing one coordinate preserves every other in-range digit. -/
theorem replace_digit_ne
    {base count word replacedIndex value digitIndex : ℕ}
    (hbase : 0 < base) (hvalue : value < base)
    (hindex : digitIndex < count)
    (hne : digitIndex ≠ replacedIndex) :
    digit base
        (replace base count word replacedIndex value)
        digitIndex =
      digit base word digitIndex :=
  Internal.replace_digit_ne_internal hbase hvalue hindex hne

/-- Replacing a digit always produces a `count`-digit word. -/
theorem replace_lt_pow
    {base count word index value : ℕ}
    (hbase : 0 < base) (hvalue : value < base) :
    replace base count word index value < base ^ count :=
  Internal.replace_lt_pow_internal hbase hvalue

/-- A word below `base ^ count` fits in `count * width` bits whenever one
base digit fits in `width` bits. -/
theorem size_le_count_mul_width
    {base count width word : ℕ}
    (hword : word < base ^ count)
    (hbase : base ≤ 2 ^ width) :
    word.size ≤ count * width :=
  Internal.size_le_count_mul_width_internal hword hbase

/-- Canonical specialization using `base.size` bits per digit. -/
theorem size_le_count_mul_baseSize
    {base count word : ℕ} (hword : word < base ^ count) :
    word.size ≤ count * base.size :=
  Internal.size_le_count_mul_baseSize_internal hword

/-- A valid push increases the concrete packed width by at most one digit. -/
theorem push_size_le
    {base count width word value : ℕ}
    (hword : word < base ^ count)
    (hvalue : value < base) (hbase : base ≤ 2 ^ width) :
    (push base value word).size ≤ (count + 1) * width :=
  Internal.push_size_le_internal hword hvalue hbase

/-- A bounded rebuild fits the common packed-vector width. -/
theorem rebuild_size_le
    {base count width word : ℕ}
    {transform : ℕ → ℕ → ℕ}
    (hbasePos : 0 < base) (hbaseWidth : base ≤ 2 ^ width)
    (htransform : ∀ index value, value < base →
      transform index value < base) :
    (rebuild base count word transform).size ≤ count * width :=
  Internal.rebuild_size_le_internal
    hbasePos hbaseWidth htransform

/-- Replacing a valid digit preserves the common packed-vector width. -/
theorem replace_size_le
    {base count width word index value : ℕ}
    (hbasePos : 0 < base) (hbaseWidth : base ≤ 2 ^ width)
    (hvalue : value < base) :
    (replace base count word index value).size ≤ count * width :=
  Internal.replace_size_le_internal hbasePos hbaseWidth hvalue

/-- Every prepended in-range coordinate is recovered at its exact low-order
index, independently of the high-order suffix. -/
theorem prependFrom_digit
    {base : ℕ} {digits : ℕ → ℕ}
    (hbase : 0 < base)
    (hdigits : ∀ index, digits index < base)
    (start count suffix offset : ℕ)
    (hoffset : offset < count) :
    digit base
        (prependFrom base digits start count suffix) offset =
      digits (start + offset) :=
  Internal.prependFrom_digit_internal
    hbase hdigits start count suffix offset hoffset

/-- Removing the complete prepended interval recovers its high-order suffix
exactly. -/
theorem drop_prependFrom
    {base : ℕ} {digits : ℕ → ℕ}
    (hbase : 0 < base)
    (hdigits : ∀ index, digits index < base)
    (start count suffix : ℕ) :
    drop base count
        (prependFrom base digits start count suffix) =
      suffix :=
  Internal.drop_prependFrom_internal
    hbase hdigits start count suffix

/-- Prepending a fixed digit interval is affine in the preserved high-order
suffix, with multiplier `base ^ count`. -/
theorem prependFrom_eq
    (base : ℕ) (digits : ℕ → ℕ)
    (start count suffix : ℕ) :
    prependFrom base digits start count suffix =
      prependFrom base digits start count 0 +
        base ^ count * suffix :=
  Internal.prependFrom_eq_internal base digits start count suffix

/-- Pointwise radix bounds transport directly to
`O(count * digitWidth)` packed bit width. -/
theorem size_isBigO_count_mul_width
    {base count width word : ℕ → ℕ}
    (hword : ∀ n, word n < base n ^ count n)
    (hbase : ∀ n, base n ≤ 2 ^ width n) :
    (fun n => (word n).size) =O
      (fun n => count n * width n) :=
  Internal.size_isBigO_count_mul_width_internal hword hbase

end PackedDigits

end Runtime

end TimeSpaceSimulation

end Complexity
