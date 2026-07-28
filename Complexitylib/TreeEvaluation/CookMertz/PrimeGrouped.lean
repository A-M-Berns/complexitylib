/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BooleanPadding
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift
import Complexitylib.TreeEvaluation.CookMertz.PrimeField
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Internal

/-!
# One-chunk prime-field grouped Cook--Mertz evaluation

For a `d`-ary Boolean tree with `b`-bit values, let

`p = b + d + 1`, `M = 2 ^ p`, and `D = M ^ 2`.

False-padding every value to width `p` preserves the original tree value and
height. The complete padded value then occupies one chunk. An explicit
`PrimeField.Choice D` gives a prime field into which all `M` chunks inject,
and its cardinality makes every grouped node polynomial strictly low-degree.
The existing interpolation theorem therefore proves line compatibility, and
the Cook--Mertz evaluator returns the field encoding of the padded Boolean
root value.

The selected modulus has binary width at most `2 * p + 2`. Consequently all
`d + 1` catalytic registers occupy at most

`2 * (d + 1) * (p + 1) ≤ 4 * (d + 1) * p`

bits. The codebook and polynomial lift remain certificate-side and
noncomputable. The explicit prime choice likewise does not by itself provide
a uniform prime-search or modular-arithmetic Turing machine.

## Main theorems

* `fanIn_le_domainSize` -- `d ≤ M`
* `groupedDegree_lt_card_sub_one` -- the uniform grouped-node degree bound
* `liftPaddedTree_lineCompatible` -- the complete lift satisfies interpolation
* `evaluatePaddedTree_eq_encode` -- evaluator correctness
* `modulus_size_le_two_mul_paddedWidth` -- concrete residue bit width
* `catalyticRegisterBitBudget_le_four_mul` -- explicit `O((d+1)p)` bank bound
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

/-- The Boolean padding width is exactly `b + d + 1`. -/
@[simp] theorem paddedWidth_eq (d b : ℕ) :
    BooleanPadding.paddedWidth d b = b + d + 1 :=
  Internal.paddedWidth_eq_internal d b

/-- The padded chunk domain is nonempty. -/
theorem domainSize_pos (d b : ℕ) :
    0 < domainSize d b :=
  Internal.domainSize_pos_internal d b

/-- The padded Boolean chunk domain contains at least one point per child. -/
theorem fanIn_le_domainSize (d b : ℕ) :
    d ≤ domainSize d b :=
  Internal.fanIn_le_domainSize_internal d b

/-- The one-chunk grouped-node degree is at most the chosen endpoint `M ^ 2`. -/
theorem groupedDegree_le_endpoint (d b : ℕ) :
    d * 1 * (2 ^ BooleanPadding.paddedWidth d b - 1) ≤
      degreeEndpoint d b :=
  Internal.groupedDegree_le_endpoint_internal d b

/-- The selected prime field places the uniform grouped-node degree strictly
below its interpolation cutoff. -/
theorem groupedDegree_lt_card_sub_one
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    d * 1 * (2 ^ BooleanPadding.paddedWidth d b - 1) <
      Fintype.card choice.Field - 1 :=
  Internal.groupedDegree_lt_card_sub_one_internal choice

/-- Every coordinate polynomial of a padded one-chunk Boolean node meets the
strict Cook--Mertz degree requirement. -/
theorem nodePolynomials_totalDegree_lt_card_sub_one
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (combine :
      (Fin d → Fin (BooleanPadding.paddedWidth d b) → Bool) →
        Fin (BooleanPadding.paddedWidth d b) → Bool)
    (outputChunk : Fin 1) :
    (GroupedExtension.nodePolynomials
        (codebook choice) (oneChunkLayout d b)
        combine outputChunk).totalDegree <
      Fintype.card choice.Field - 1 :=
  Internal.nodePolynomials_totalDegree_lt_card_sub_one_internal
    choice combine outputChunk

/-- The recursively lifted padded tree carries the exact low-degree
certificate consumed by finite-field interpolation. -/
theorem liftPaddedTree_isLowDegreePolynomial
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    IsLowDegreePolynomial (Fintype.card choice.Field - 1)
      (liftPaddedTree choice tree) :=
  Internal.liftPaddedTree_isLowDegreePolynomial_internal choice tree

/-- The prime-field grouped lift satisfies the affine-line identity required
by the Cook--Mertz accumulator. -/
theorem liftPaddedTree_lineCompatible
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    LineCompatible (PrimeField.units choice.modulus)
      (liftPaddedTree choice tree) :=
  Internal.liftPaddedTree_lineCompatible_internal choice tree

/-- Padding and grouped lifting preserve the root value after field
encoding. -/
@[simp] theorem value_liftPaddedTree
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    (liftPaddedTree choice tree).value =
      encodePaddedValue choice tree.value :=
  Internal.value_liftPaddedTree_internal choice tree

/-- Padding and grouped lifting preserve exact tree height. -/
@[simp] theorem height_liftPaddedTree
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    (liftPaddedTree choice tree).height = tree.height :=
  Internal.height_liftPaddedTree_internal choice tree

/-- Cook--Mertz evaluation returns the selected field encoding of the padded
Boolean root value. -/
theorem evaluatePaddedTree_eq_encode
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    evaluatePaddedTree choice tree =
      encodePaddedValue choice tree.value :=
  Internal.evaluatePaddedTree_eq_encode_internal choice tree

/-- A residue of the selected prime field fits in at most `2 * p + 2` bits. -/
theorem modulus_size_le_two_mul_paddedWidth
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    choice.modulus.size ≤
      2 * BooleanPadding.paddedWidth d b + 2 :=
  Internal.modulus_size_le_two_mul_paddedWidth_internal choice

/-- Sharp bound obtained directly from `d + 1` one-coordinate registers and
the concrete modulus-width estimate. -/
theorem catalyticRegisterBitBudget_le
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    catalyticRegisterBitBudget choice ≤
      2 * (d + 1) *
        (BooleanPadding.paddedWidth d b + 1) :=
  Internal.catalyticRegisterBitBudget_le_internal choice

/-- Uniform explicit catalytic-bank bound
`4 * (d + 1) * (b + d + 1)`. -/
theorem catalyticRegisterBitBudget_le_four_mul
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    catalyticRegisterBitBudget choice ≤
      4 * (d + 1) * BooleanPadding.paddedWidth d b :=
  Internal.catalyticRegisterBitBudget_le_four_mul_internal choice

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
