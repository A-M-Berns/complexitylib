/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift.Internal

/-!
# Grouped polynomial lifts of Boolean trees

This module exposes the generic tree-level bridge from Boolean evaluation to
the grouped low-degree representation. The recursive lift preserves the
Boolean tree's shape and value after packed field encoding. Its node
polynomials satisfy the exact recursive certificate used by the existing
Cook--Mertz interpolation theorem.

The strongest unconditional statement here is parameterized by the strict
degree inequality

`d * chunkCount * (2 ^ chunkBits - 1) < |K| - 1`.

The square-cardinality corollaries discharge that inequality from the
Appendix A hypotheses `d * chunkCount ≤ 2 ^ chunkBits` and
`|K| = (2 ^ chunkBits) ^ 2`.

## Main theorems

* `value_liftTree` -- grouped lifting preserves the root value
* `height_liftTree` -- grouped lifting preserves tree height
* `liftTree_isLowDegreePolynomial` -- exact recursive degree certificate
* `liftTree_lineCompatible` -- the lifted tree satisfies Cook--Mertz's line
  identity
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

variable {K : Type*} [Field K] [Fintype K]
  {d b chunkBits chunkCount : ℕ}

@[simp] theorem liftTree_leaf
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (value : Fin b → Bool) :
    liftTree codebook layout (.leaf value : Tree d (Fin b → Bool)) =
      .leaf (encodeVector codebook value) :=
  rfl

@[simp] theorem liftTree_node
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (children : Fin d → Tree d (Fin b → Bool))
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool) :
    liftTree codebook layout (.node children combine) =
      .node
        (fun child => liftTree codebook layout (children child))
        (polynomialNode (nodePolynomials codebook layout combine)) :=
  rfl

/-- Grouped lifting preserves the Boolean tree's value after row-major packing
and field encoding. -/
@[simp] theorem value_liftTree
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool)) :
    (liftTree codebook layout tree).value =
      encodeVector codebook tree.value :=
  Internal.value_liftTree_internal codebook layout tree

/-- Grouped lifting changes only leaf values and node functions, not the tree
shape. -/
@[simp] theorem height_liftTree
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool)) :
    (liftTree codebook layout tree).height = tree.height :=
  Internal.height_liftTree_internal codebook layout tree

/-- If the uniform grouped-node degree is strictly below `degreeBound`, the
entire lifted tree carries the recursive polynomial certificate. -/
theorem liftTree_isLowDegreePolynomial
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (degreeBound : ℕ)
    (hdegree :
      d * chunkCount * (2 ^ chunkBits - 1) < degreeBound) :
    IsLowDegreePolynomial degreeBound
      (liftTree codebook layout tree) :=
  Internal.liftTree_isLowDegreePolynomial_internal
    codebook layout tree degreeBound hdegree

/-- The Appendix A square-cardinality assumptions give the exact recursive
degree certificate expected by finite-field interpolation. -/
theorem liftTree_isLowDegreePolynomial_squareCard
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (hpositive : 0 < chunkBits)
    (hinputs : d * chunkCount ≤ 2 ^ chunkBits)
    (hcard : Fintype.card K = (2 ^ chunkBits) ^ 2) :
    IsLowDegreePolynomial (Fintype.card K - 1)
      (liftTree codebook layout tree) :=
  Internal.liftTree_isLowDegreePolynomial_squareCard_internal
    codebook layout tree hpositive hinputs hcard

/-- Under the strict grouped-node degree inequality, the lifted tree satisfies
the affine-line identity required by the Cook--Mertz accumulator. -/
theorem liftTree_lineCompatible [DecidableEq K]
    (units : List Kˣ) (henum : EnumeratesUnits units)
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (hdegree :
      d * chunkCount * (2 ^ chunkBits - 1) <
        Fintype.card K - 1) :
    LineCompatible units (liftTree codebook layout tree) :=
  Internal.liftTree_lineCompatible_internal
    units henum codebook layout tree hdegree

/-- The square-cardinality Appendix A hypotheses imply line compatibility for
the complete lifted tree. -/
theorem liftTree_lineCompatible_squareCard [DecidableEq K]
    (units : List Kˣ) (henum : EnumeratesUnits units)
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (tree : Tree d (Fin b → Bool))
    (hpositive : 0 < chunkBits)
    (hinputs : d * chunkCount ≤ 2 ^ chunkBits)
    (hcard : Fintype.card K = (2 ^ chunkBits) ^ 2) :
    LineCompatible units (liftTree codebook layout tree) :=
  Internal.liftTree_lineCompatible_squareCard_internal
    units henum codebook layout tree hpositive hinputs hcard

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
