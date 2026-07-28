/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Asymptotics
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits.Defs

/-!
# Executable packed radix words — proof internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace PackedDigits

namespace Internal

theorem digit_lt_internal {base word index : ℕ} (hbase : 0 < base) :
    digit base word index < base :=
  Nat.mod_lt _ hbase

theorem pop_push_internal {base value word : ℕ}
    (hbase : 0 < base) (hvalue : value < base) :
    pop base (push base value word) = word := by
  rw [pop, push, Nat.add_mul_div_left value word hbase,
    Nat.div_eq_of_lt hvalue, Nat.zero_add]

theorem digit_push_zero_internal {base value word : ℕ}
    (hvalue : value < base) :
    digit base (push base value word) 0 = value := by
  rw [digit, Nat.pow_zero, Nat.div_one, push,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvalue]

theorem digit_pop_internal (base word index : ℕ) :
    digit base (pop base word) index =
      digit base word (index + 1) := by
  simp [digit, pop, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

theorem digit_push_succ_internal {base value word : ℕ}
    (hbase : 0 < base) (hvalue : value < base) (index : ℕ) :
    digit base (push base value word) (index + 1) =
      digit base word index := by
  rw [← digit_pop_internal base (push base value word) index,
    pop_push_internal hbase hvalue]

theorem prependFrom_digit_internal
    {base : ℕ} {digits : ℕ → ℕ}
    (hbase : 0 < base)
    (hdigits : ∀ index, digits index < base)
    (start count suffix offset : ℕ)
    (hoffset : offset < count) :
    digit base
        (prependFrom base digits start count suffix) offset =
      digits (start + offset) := by
  induction count generalizing start offset with
  | zero => omega
  | succ count ih =>
      rw [prependFrom]
      cases offset with
      | zero =>
          simpa using digit_push_zero_internal (hdigits start)
      | succ offset =>
          rw [digit_push_succ_internal hbase (hdigits start)]
          rw [ih (start := start + 1) (offset := offset) (by omega)]
          congr 1
          omega

theorem drop_prependFrom_internal
    {base : ℕ} {digits : ℕ → ℕ}
    (hbase : 0 < base)
    (hdigits : ∀ index, digits index < base)
    (start count suffix : ℕ) :
    drop base count
        (prependFrom base digits start count suffix) =
      suffix := by
  induction count generalizing start suffix with
  | zero => rfl
  | succ count ih =>
      rw [prependFrom, drop, pop_push_internal hbase (hdigits start)]
      exact ih (start + 1) suffix

theorem prependFrom_eq_internal
    (base : ℕ) (digits : ℕ → ℕ)
    (start count suffix : ℕ) :
    prependFrom base digits start count suffix =
      prependFrom base digits start count 0 +
        base ^ count * suffix := by
  induction count generalizing start suffix with
  | zero => simp [prependFrom]
  | succ count ih =>
      rw [prependFrom, prependFrom, ih, ih]
      simp only [push, pow_succ]
      ring

theorem push_digit_pop_internal (base word : ℕ) :
    push base (digit base word 0) (pop base word) = word := by
  rw [push, digit, Nat.pow_zero, Nat.div_one, pop,
    Nat.mod_add_div]

theorem foldDigits_push_internal {α : Type*}
    {base value word count : ℕ} (initial : α)
    (step : α → ℕ → α)
    (hbase : 0 < base) (hvalue : value < base) :
    foldDigits base (count + 1) (push base value word) initial step =
      foldDigits base count word (step initial value) step := by
  simp only [foldDigits]
  rw [pop_push_internal hbase hvalue,
    digit_push_zero_internal hvalue]

theorem push_lt_pow_internal {base value word count : ℕ}
    (hword : word < base ^ count) (hvalue : value < base) :
    push base value word < base ^ (count + 1) := by
  simp only [push, pow_succ]
  nlinarith

theorem pop_lt_pow_internal {base word count : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ (count + 1)) :
    pop base word < base ^ count := by
  rw [pop, Nat.div_lt_iff_lt_mul hbase]
  simpa [pow_succ] using hword

theorem rebuildFrom_digit_internal
    {base offset count word : ℕ}
    {transform : ℕ → ℕ → ℕ}
    (hbase : 0 < base)
    (htransform : ∀ index value, value < base →
      transform index value < base) :
    ∀ digitIndex, digitIndex < count →
      digit base
          (rebuildFrom base transform offset count word)
          digitIndex =
        transform (offset + digitIndex)
          (digit base word digitIndex) := by
  induction count generalizing offset word with
  | zero =>
      intro digitIndex hindex
      omega
  | succ count ih =>
      intro digitIndex hindex
      cases digitIndex with
      | zero =>
          simp only [rebuildFrom, Nat.add_zero]
          apply digit_push_zero_internal
          exact htransform offset _ (digit_lt_internal hbase)
      | succ digitIndex =>
          simp only [rebuildFrom]
          rw [digit_push_succ_internal hbase
            (htransform offset _ (digit_lt_internal hbase))]
          rw [ih digitIndex (by omega)]
          rw [digit_pop_internal]
          congr 1
          omega

theorem rebuild_digit_internal
    {base count word digitIndex : ℕ}
    {transform : ℕ → ℕ → ℕ}
    (hbase : 0 < base)
    (htransform : ∀ index value, value < base →
      transform index value < base)
    (hindex : digitIndex < count) :
    digit base (rebuild base count word transform) digitIndex =
      transform digitIndex (digit base word digitIndex) := by
  unfold rebuild
  simpa only [Nat.zero_add] using
    (@rebuildFrom_digit_internal base 0 count word transform
      hbase htransform digitIndex hindex)

theorem rebuildFrom_lt_pow_internal
    {base offset count word : ℕ}
    {transform : ℕ → ℕ → ℕ}
    (hbase : 0 < base)
    (htransform : ∀ index value, value < base →
      transform index value < base) :
    rebuildFrom base transform offset count word < base ^ count := by
  induction count generalizing offset word with
  | zero =>
      simp [rebuildFrom]
  | succ count ih =>
      simp only [rebuildFrom]
      apply push_lt_pow_internal
        (ih (offset := offset + 1) (word := pop base word))
      exact htransform offset _ (digit_lt_internal hbase)

theorem rebuild_lt_pow_internal
    {base count word : ℕ} {transform : ℕ → ℕ → ℕ}
    (hbase : 0 < base)
    (htransform : ∀ index value, value < base →
      transform index value < base) :
    rebuild base count word transform < base ^ count :=
  rebuildFrom_lt_pow_internal hbase htransform

theorem replace_digit_eq_internal
    {base count word index value : ℕ}
    (hbase : 0 < base) (hvalue : value < base)
    (hindex : index < count) :
    digit base (replace base count word index value) index = value := by
  unfold replace
  have htransform : ∀ current old, old < base →
      (if current = index then value else old) < base := by
    intro current old hold
    split <;> assumption
  rw [rebuild_digit_internal hbase htransform hindex]
  simp

theorem replace_digit_ne_internal
    {base count word replacedIndex value digitIndex : ℕ}
    (hbase : 0 < base) (hvalue : value < base)
    (hindex : digitIndex < count)
    (hne : digitIndex ≠ replacedIndex) :
    digit base
        (replace base count word replacedIndex value)
        digitIndex =
      digit base word digitIndex := by
  unfold replace
  have htransform : ∀ current old, old < base →
      (if current = replacedIndex then value else old) < base := by
    intro current old hold
    split <;> assumption
  rw [rebuild_digit_internal hbase htransform hindex]
  simp [hne]

theorem replace_lt_pow_internal
    {base count word index value : ℕ}
    (hbase : 0 < base) (hvalue : value < base) :
    replace base count word index value < base ^ count := by
  unfold replace
  apply rebuild_lt_pow_internal hbase
  intro current old hold
  split <;> assumption

theorem size_le_count_mul_width_internal
    {base count width word : ℕ}
    (hword : word < base ^ count)
    (hbase : base ≤ 2 ^ width) :
    word.size ≤ count * width := by
  apply Nat.size_le.mpr
  calc
    word < base ^ count := hword
    _ ≤ (2 ^ width) ^ count :=
      Nat.pow_le_pow_left hbase count
    _ = 2 ^ (count * width) :=
      (pow_mul' 2 count width).symm

theorem size_le_count_mul_baseSize_internal
    {base count word : ℕ} (hword : word < base ^ count) :
    word.size ≤ count * base.size :=
  size_le_count_mul_width_internal
    hword (Nat.lt_size_self base).le

theorem push_size_le_internal
    {base count width word value : ℕ}
    (hword : word < base ^ count)
    (hvalue : value < base) (hbase : base ≤ 2 ^ width) :
    (push base value word).size ≤ (count + 1) * width :=
  size_le_count_mul_width_internal
    (push_lt_pow_internal hword hvalue) hbase

theorem rebuild_size_le_internal
    {base count width word : ℕ}
    {transform : ℕ → ℕ → ℕ}
    (hbasePos : 0 < base) (hbaseWidth : base ≤ 2 ^ width)
    (htransform : ∀ index value, value < base →
      transform index value < base) :
    (rebuild base count word transform).size ≤ count * width :=
  size_le_count_mul_width_internal
    (rebuild_lt_pow_internal hbasePos htransform) hbaseWidth

theorem replace_size_le_internal
    {base count width word index value : ℕ}
    (hbasePos : 0 < base) (hbaseWidth : base ≤ 2 ^ width)
    (hvalue : value < base) :
    (replace base count word index value).size ≤ count * width :=
  size_le_count_mul_width_internal
    (replace_lt_pow_internal hbasePos hvalue) hbaseWidth

theorem size_isBigO_count_mul_width_internal
    {base count width word : ℕ → ℕ}
    (hword : ∀ n, word n < base n ^ count n)
    (hbase : ∀ n, base n ≤ 2 ^ width n) :
    (fun n => (word n).size) =O
      (fun n => count n * width n) := by
  apply BigO.of_le
  intro n
  exact size_le_count_mul_width_internal (hword n) (hbase n)

end Internal

end PackedDigits

end Runtime

end TimeSpaceSimulation

end Complexity
