/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.Defs

/-!
# Width padding for Boolean tree evaluation

Grouped Cook--Mertz interpolation needs the chunk domain to dominate the
node fan-in. Padding a `b`-bit value by `d + 1` false bits makes the resulting
width positive and large enough for every `d`-ary node while preserving the
tree's value and height.

## Main definitions

- `paddedWidth` -- `b + d + 1`
- `padBits` / `unpadBits` -- false padding and prefix recovery
- `padTree` -- width-padded Boolean tree
-/

namespace Complexity

namespace TreeEval

namespace BooleanPadding

/-- Boolean value width after adding fan-in-dependent slack. -/
def paddedWidth (d b : ℕ) : ℕ :=
  b + d + 1

/-- Extend a Boolean vector with trailing false coordinates. -/
def padBits (d : ℕ) (bits : Fin b → Bool) :
    Fin (paddedWidth d b) → Bool :=
  fun position =>
    if h : position.val < b then
      bits ⟨position.val, h⟩
    else
      false

/-- Recover the meaningful prefix of a padded Boolean vector. -/
def unpadBits (d : ℕ)
    (bits : Fin (paddedWidth d b) → Bool) :
    Fin b → Bool :=
  fun position =>
    bits ⟨position.val, by
      unfold paddedWidth
      omega⟩

/-- Recursively pad every value and node function in a Boolean tree. -/
def padTree :
    Tree d (Fin b → Bool) →
      Tree d (Fin (paddedWidth d b) → Bool)
  | .leaf value =>
      .leaf (padBits d value)
  | .node children combine =>
      .node
        (fun index => padTree (children index))
        (fun inputs =>
          padBits d
            (combine fun index => unpadBits d (inputs index)))

end BooleanPadding

end TreeEval

end Complexity
