/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BooleanPadding.Defs
import Complexitylib.TreeEvaluation.BooleanPadding.Internal

/-!
# Correct Boolean tree width padding

Padding by `d + 1` false bits makes every value width positive, preserves the
meaningful prefix exactly, commutes with evaluation, and preserves height.
-/

namespace Complexity

namespace TreeEval

namespace BooleanPadding

/-- Fan-in-dependent padded widths are always positive. -/
theorem paddedWidth_pos (d b : ℕ) :
    0 < paddedWidth d b :=
  Internal.paddedWidth_pos_internal d b

/-- Prefix recovery is a left inverse of false padding. -/
theorem unpadBits_padBits
    (d : ℕ) (bits : Fin b → Bool) :
    unpadBits d (padBits d bits) = bits :=
  Internal.unpadBits_padBits_internal d bits

/-- Padding a Boolean tree commutes with bottom-up evaluation. -/
theorem padTree_value
    (tree : Tree d (Fin b → Bool)) :
    (padTree tree).value = padBits d tree.value :=
  Internal.padTree_value_internal tree

/-- Width padding preserves the exact tree height. -/
theorem padTree_height
    (tree : Tree d (Fin b → Bool)) :
    (padTree tree).height = tree.height :=
  Internal.padTree_height_internal tree

end BooleanPadding

end TreeEval

end Complexity
