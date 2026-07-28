/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Internal
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift.Defs
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Internal

/-!
# Correctness internals for grouped Boolean-tree lifts

This file proves value and height preservation and constructs the recursive
low-degree certificate consumed by the Cook--Mertz interpolation layer.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Internal

variable {K : Type*} [Field K] [Fintype K]
  {d b chunkBits chunkCount : ℕ}

theorem value_liftTree_internal
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool)) :
    (liftTree codebook layout tree).value =
      encodeVector codebook tree.value := by
  induction tree with
  | leaf value =>
      rfl
  | node children combine ih =>
      simp only [liftTree, Tree.value_node]
      have hchildren :
          (fun child => (liftTree codebook layout (children child)).value) =
            fun child => encodeVector codebook (children child).value := by
        funext child
        exact ih child
      rw [hchildren]
      exact
        polynomialNode_nodePolynomials_internal
          codebook layout combine fun child => (children child).value

theorem height_liftTree_internal
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool)) :
    (liftTree codebook layout tree).height = tree.height := by
  induction tree with
  | leaf value =>
      rfl
  | node children combine ih =>
      simp only [liftTree, Tree.height_node]
      congr 1
      apply Finset.sup_congr rfl
      intro child _
      exact ih child

theorem liftTree_isLowDegreePolynomial_internal
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (degreeBound : ℕ)
    (hdegree :
      d * chunkCount * (2 ^ chunkBits - 1) < degreeBound) :
    IsLowDegreePolynomial degreeBound
      (liftTree codebook layout tree) := by
  induction tree with
  | leaf value =>
      simp [liftTree, IsLowDegreePolynomial]
  | node children combine ih =>
      refine ⟨ih, nodePolynomials codebook layout combine, rfl, ?_⟩
      intro outputChunk
      exact
        (nodePolynomials_totalDegree_le_internal
          codebook layout combine outputChunk).trans_lt hdegree

theorem liftTree_isLowDegreePolynomial_squareCard_internal
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (hpositive : 0 < chunkBits)
    (hinputs : d * chunkCount ≤ 2 ^ chunkBits)
    (hcard : Fintype.card K = (2 ^ chunkBits) ^ 2) :
    IsLowDegreePolynomial (Fintype.card K - 1)
      (liftTree codebook layout tree) :=
  liftTree_isLowDegreePolynomial_internal
    codebook layout tree (Fintype.card K - 1)
    (groupedDegree_lt_squareCard_internal
      d chunkCount chunkBits (Fintype.card K)
      hpositive hinputs hcard)

theorem liftTree_lineCompatible_internal [DecidableEq K]
    (units : List Kˣ) (henum : EnumeratesUnits units)
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (hdegree :
      d * chunkCount * (2 ^ chunkBits - 1) <
        Fintype.card K - 1) :
    LineCompatible units (liftTree codebook layout tree) :=
  Interpolation.lowDegreePolynomial_lineCompatible_internal
    units henum (liftTree codebook layout tree)
    (liftTree_isLowDegreePolynomial_internal
      codebook layout tree (Fintype.card K - 1) hdegree)

theorem liftTree_lineCompatible_squareCard_internal [DecidableEq K]
    (units : List Kˣ) (henum : EnumeratesUnits units)
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (hpositive : 0 < chunkBits)
    (hinputs : d * chunkCount ≤ 2 ^ chunkBits)
    (hcard : Fintype.card K = (2 ^ chunkBits) ^ 2) :
    LineCompatible units (liftTree codebook layout tree) :=
  Interpolation.lowDegreePolynomial_lineCompatible_internal
    units henum (liftTree codebook layout tree)
    (liftTree_isLowDegreePolynomial_squareCard_internal
      codebook layout tree hpositive hinputs hcard)

end Internal

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
