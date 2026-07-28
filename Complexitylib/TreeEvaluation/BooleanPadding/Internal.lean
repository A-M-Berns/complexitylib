/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BooleanPadding.Defs

/-!
# Correctness of Boolean tree width padding

False padding is injective through prefix recovery, and padding commutes with
tree evaluation while preserving exact height.
-/

namespace Complexity

namespace TreeEval

namespace BooleanPadding

namespace Internal

theorem paddedWidth_pos_internal (d b : ℕ) :
    0 < paddedWidth d b := by
  unfold paddedWidth
  omega

theorem unpadBits_padBits_internal
    (d : ℕ) (bits : Fin b → Bool) :
    unpadBits d (padBits d bits) = bits := by
  funext position
  simp [unpadBits, padBits]

theorem padTree_value_internal
    (tree : Tree d (Fin b → Bool)) :
    (padTree tree).value = padBits d tree.value := by
  induction tree with
  | leaf value =>
      rfl
  | node children combine ih =>
      rw [padTree, Tree.value_node]
      have hchildren :
          (fun index =>
            unpadBits d (padTree (children index)).value) =
            (fun index => (children index).value) := by
        funext index
        rw [ih index]
        exact unpadBits_padBits_internal
          d (children index).value
      rw [hchildren]
      rfl

theorem padTree_height_internal
    (tree : Tree d (Fin b → Bool)) :
    (padTree tree).height = tree.height := by
  induction tree with
  | leaf value =>
      rfl
  | node children combine ih =>
      simp only [padTree, Tree.height_node]
      congr 2
      funext index
      exact ih index

end Internal

end BooleanPadding

end TreeEval

end Complexity
