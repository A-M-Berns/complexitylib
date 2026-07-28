/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BooleanPadding.Internal
import Complexitylib.TreeEvaluation.CookMertz
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift.Internal
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Internal
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Defs

/-!
# Correctness internals for one-chunk prime-field grouped evaluation

This file discharges the cardinality, degree, interpolation, semantic, and
register-width obligations for the padded one-chunk prime-field choice.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

namespace Internal

theorem paddedWidth_eq_internal (d b : ℕ) :
    BooleanPadding.paddedWidth d b = b + d + 1 := by
  rfl

theorem domainSize_pos_internal (d b : ℕ) :
    0 < domainSize d b := by
  simp [domainSize]

theorem fanIn_le_domainSize_internal (d b : ℕ) :
    d ≤ domainSize d b := by
  calc
    d ≤ 2 ^ d := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ BooleanPadding.paddedWidth d b :=
      Nat.pow_le_pow_right (by omega) (by
        unfold BooleanPadding.paddedWidth
        omega)
    _ = domainSize d b := by
      rfl

theorem groupedDegree_le_endpoint_internal (d b : ℕ) :
    d * 1 * (2 ^ BooleanPadding.paddedWidth d b - 1) ≤
      degreeEndpoint d b := by
  calc
    d * 1 * (2 ^ BooleanPadding.paddedWidth d b - 1) =
        d * (domainSize d b - 1) := by
      simp [domainSize]
    _ ≤ domainSize d b * (domainSize d b - 1) :=
      Nat.mul_le_mul_right _
        (fanIn_le_domainSize_internal d b)
    _ ≤ domainSize d b * domainSize d b :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = degreeEndpoint d b := by
      simp [degreeEndpoint, pow_two]

theorem groupedDegree_lt_card_sub_one_internal
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    d * 1 * (2 ^ BooleanPadding.paddedWidth d b - 1) <
      Fintype.card choice.Field - 1 :=
  (groupedDegree_le_endpoint_internal d b).trans_lt
    (PrimeField.Internal.degree_lt_card_sub_one_internal choice)

theorem nodePolynomials_totalDegree_lt_card_sub_one_internal
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (combine :
      (Fin d → Fin (BooleanPadding.paddedWidth d b) → Bool) →
        Fin (BooleanPadding.paddedWidth d b) → Bool)
    (outputChunk : Fin 1) :
    (GroupedExtension.nodePolynomials
        (codebook choice) (oneChunkLayout d b)
        combine outputChunk).totalDegree <
      Fintype.card choice.Field - 1 :=
  (GroupedExtension.Internal.nodePolynomials_totalDegree_le_internal
      (codebook choice) (oneChunkLayout d b)
      combine outputChunk).trans_lt
    (groupedDegree_lt_card_sub_one_internal choice)

theorem liftPaddedTree_isLowDegreePolynomial_internal
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    IsLowDegreePolynomial (Fintype.card choice.Field - 1)
      (liftPaddedTree choice tree) := by
  unfold liftPaddedTree
  exact
    GroupedExtension.Internal.liftTree_isLowDegreePolynomial_internal
      (codebook choice) (oneChunkLayout d b)
      (BooleanPadding.padTree tree)
      (Fintype.card choice.Field - 1)
      (groupedDegree_lt_card_sub_one_internal choice)

theorem liftPaddedTree_lineCompatible_internal
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    LineCompatible (PrimeField.units choice.modulus)
      (liftPaddedTree choice tree) := by
  unfold liftPaddedTree
  exact
    GroupedExtension.Internal.liftTree_lineCompatible_internal
      (PrimeField.units choice.modulus)
      (PrimeField.Internal.enumeratesUnits_internal choice.modulus)
      (codebook choice) (oneChunkLayout d b)
      (BooleanPadding.padTree tree)
      (groupedDegree_lt_card_sub_one_internal choice)

theorem value_liftPaddedTree_internal
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    (liftPaddedTree choice tree).value =
      encodePaddedValue choice tree.value := by
  unfold liftPaddedTree encodePaddedValue
  rw [GroupedExtension.Internal.value_liftTree_internal]
  rw [BooleanPadding.Internal.padTree_value_internal]

theorem height_liftPaddedTree_internal
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    (liftPaddedTree choice tree).height = tree.height := by
  unfold liftPaddedTree
  rw [GroupedExtension.Internal.height_liftTree_internal]
  exact BooleanPadding.Internal.padTree_height_internal tree

theorem evaluatePaddedTree_eq_encode_internal
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    evaluatePaddedTree choice tree =
      encodePaddedValue choice tree.value := by
  unfold evaluatePaddedTree
  rw [evaluate_eq_value _ _
    (liftPaddedTree_lineCompatible_internal choice tree)]
  exact value_liftPaddedTree_internal choice tree

theorem modulus_size_le_two_mul_paddedWidth_internal
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    choice.modulus.size ≤
      2 * BooleanPadding.paddedWidth d b + 2 := by
  rw [Nat.size_le]
  calc
    choice.modulus ≤ 2 * (degreeEndpoint d b + 1) :=
      choice.modulus_le_two_mul
    _ < 4 * degreeEndpoint d b := by
      have hendpoint : 1 < degreeEndpoint d b := by
        unfold degreeEndpoint domainSize
        apply Nat.one_lt_pow (by omega)
        apply Nat.one_lt_pow
        · unfold BooleanPadding.paddedWidth
          omega
        · omega
      omega
    _ = 2 ^ (2 * BooleanPadding.paddedWidth d b + 2) := by
      rw [degreeEndpoint, domainSize, pow_two, ← pow_add]
      norm_num [pow_add]
      ring

theorem catalyticRegisterBitBudget_le_internal
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    catalyticRegisterBitBudget choice ≤
      2 * (d + 1) *
        (BooleanPadding.paddedWidth d b + 1) := by
  calc
    catalyticRegisterBitBudget choice =
        (d + 1) * choice.modulus.size := by
      simp [catalyticRegisterBitBudget,
        GroupedExtension.groupedRegisterBitBudget]
    _ ≤ (d + 1) *
        (2 * BooleanPadding.paddedWidth d b + 2) :=
      Nat.mul_le_mul_left _
        (modulus_size_le_two_mul_paddedWidth_internal choice)
    _ = 2 * (d + 1) *
        (BooleanPadding.paddedWidth d b + 1) := by
      ring

theorem catalyticRegisterBitBudget_le_four_mul_internal
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    catalyticRegisterBitBudget choice ≤
      4 * (d + 1) * BooleanPadding.paddedWidth d b := by
  apply (catalyticRegisterBitBudget_le_internal choice).trans
  have hwidth : 1 ≤ BooleanPadding.paddedWidth d b := by
    unfold BooleanPadding.paddedWidth
    omega
  nlinarith

end Internal

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
