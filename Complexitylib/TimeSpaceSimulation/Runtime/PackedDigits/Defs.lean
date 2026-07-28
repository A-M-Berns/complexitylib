/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Nat.Size

/-!
# Executable packed radix words

This file defines a little-endian base-`base` word stored in one natural
number. Digit zero is the least-significant digit. `push` adds a new digit at
that end, while `pop` removes it.

The fold consumes digits from least to most significant without constructing
a list. `rebuild` performs an indexed streaming transformation of a fixed
number of digits, and `replace` specializes it to one coordinate.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace PackedDigits

/-- The little-endian digit at `index` of a packed radix word. -/
def digit (base word index : ℕ) : ℕ :=
  word / base ^ index % base

/-- Add `value` as the new least-significant digit of `word`. -/
def push (base value word : ℕ) : ℕ :=
  value + base * word

/-- Remove the least-significant digit of `word`. -/
def pop (base word : ℕ) : ℕ :=
  word / base

/-- Stream the first `count` digits from least to most significant.

The accumulator is updated before the recursive call, so this is an
executable left fold that never materializes the digit vector. -/
def foldDigits {α : Type*} (base : ℕ) :
    ℕ → ℕ → α → (α → ℕ → α) → α
  | 0, _, initial, _ => initial
  | count + 1, word, initial, step =>
      foldDigits base count (pop base word)
        (step initial (digit base word 0)) step

/-- Indexed worker for rebuilding a fixed-length packed word. -/
def rebuildFrom (base : ℕ) (transform : ℕ → ℕ → ℕ) :
    ℕ → ℕ → ℕ → ℕ
  | _, 0, _ => 0
  | index, count + 1, word =>
      push base (transform index (digit base word 0))
        (rebuildFrom base transform (index + 1) count (pop base word))

/-- Transform and repack the first `count` digits of `word`.

`transform index oldDigit` supplies the replacement digit. Digits are
interpreted and produced in little-endian order. -/
def rebuild (base count word : ℕ)
    (transform : ℕ → ℕ → ℕ) : ℕ :=
  rebuildFrom base transform 0 count word

/-- Replace one digit while rebuilding a `count`-digit packed word. -/
def replace (base count word index value : ℕ) : ℕ :=
  rebuild base count word
    (fun current old => if current = index then value else old)

/-- Place a finite digit interval below an existing high-order suffix.

`prependFrom base digits index count suffix` has `digits index` at low-order
coordinate zero, followed by the next `count - 1` digits; `suffix` begins
above the complete interval. This is the pure endpoint of pushing the digits
from high coordinate to low coordinate.
-/
def prependFrom (base : ℕ) (digits : ℕ → ℕ) :
    ℕ → ℕ → ℕ → ℕ
  | _, 0, suffix => suffix
  | index, count + 1, suffix =>
      push base (digits index)
        (prependFrom base digits (index + 1) count suffix)

/-- Place coordinates `0, ..., count - 1` below an existing suffix. -/
def prepend (base count : ℕ) (digits : ℕ → ℕ) (suffix : ℕ) : ℕ :=
  prependFrom base digits 0 count suffix

/-- Remove a fixed number of low-order packed digits. -/
def drop (base : ℕ) : ℕ → ℕ → ℕ
  | 0, word => word
  | count + 1, word => drop base count (pop base word)

end PackedDigits

end Runtime

end TimeSpaceSimulation

end Complexity
