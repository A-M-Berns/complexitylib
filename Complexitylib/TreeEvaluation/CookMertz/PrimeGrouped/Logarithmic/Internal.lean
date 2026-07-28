/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift.Internal
import Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Defs

/-!
# Correctness internals for executable logarithmic grouping

This file proves the arithmetic cutoff, interpolation compatibility,
semantic equality, and exact branch-sensitive storage bounds for the
executable logarithmic prime-field parameters.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

namespace Logarithmic

namespace Internal

theorem chunkBits_pos_internal (payloadWidth fanIn : ℕ) :
    0 < chunkBits payloadWidth fanIn :=
  GroupedExtension.LogarithmicParameters.chunkBits_pos _ _

theorem domainSize_pos_internal (payloadWidth fanIn : ℕ) :
    0 < domainSize payloadWidth fanIn := by
  simp [domainSize]

theorem one_lt_domainSize_internal (payloadWidth fanIn : ℕ) :
    1 < domainSize payloadWidth fanIn := by
  unfold domainSize
  exact Nat.one_lt_two_pow
    (chunkBits_pos_internal payloadWidth fanIn).ne'

theorem chunkCodeNat_lt_internal {width : ℕ}
    (value : GroupedExtension.Chunk width) :
    chunkCodeNat value < 2 ^ width := by
  simpa [chunkCodeNat] using
    Nat.fromBits_lt_pow_length (List.ofFn value)

theorem chunkCodeNat_injective_internal {width : ℕ} :
    Function.Injective
      (@chunkCodeNat width) := by
  intro first second heq
  apply List.ofFn_injective
  apply Nat.fromBits_inj_of_length_eq (by simp)
  exact heq

theorem groupedDegree_le_endpoint_internal
    (payloadWidth fanIn : ℕ) :
    groupedDegree payloadWidth fanIn ≤
      degreeEndpoint payloadWidth fanIn :=
  Nat.le_max_left _ _

theorem codebookFloor_le_endpoint_internal
    (payloadWidth fanIn : ℕ) :
    domainSize payloadWidth fanIn - 1 ≤
      degreeEndpoint payloadWidth fanIn :=
  Nat.le_max_right _ _

theorem degreeEndpoint_eq_groupedDegree_internal
    (payloadWidth fanIn : ℕ)
    (hpayload : 0 < payloadWidth) (hfanIn : 0 < fanIn) :
    degreeEndpoint payloadWidth fanIn =
      groupedDegree payloadWidth fanIn := by
  apply max_eq_left
  unfold groupedDegree
  apply Nat.le_mul_of_pos_left
  exact Nat.mul_pos hfanIn
    (GroupedExtension.LogarithmicParameters.chunkCount_pos
      payloadWidth fanIn hpayload)

theorem groupedDegree_lt_card_sub_one_internal
    (payloadWidth fanIn : ℕ) :
    groupedDegree payloadWidth fanIn <
      Fintype.card (Field payloadWidth fanIn) - 1 :=
  (groupedDegree_le_endpoint_internal payloadWidth fanIn).trans_lt
    (PrimeField.Choice.degree_lt_card_sub_one
      (fieldChoice payloadWidth fanIn))

theorem degreeEndpoint_le_domain_mul_pred_internal
    (payloadWidth fanIn : ℕ) :
    degreeEndpoint payloadWidth fanIn ≤
      domainSize payloadWidth fanIn *
        (domainSize payloadWidth fanIn - 1) := by
  apply max_le
  · unfold groupedDegree
    exact Nat.mul_le_mul_right _
      (GroupedExtension.LogarithmicParameters.inputCoordinates_le
        payloadWidth fanIn)
  · exact Nat.le_mul_of_pos_left _
      (domainSize_pos_internal payloadWidth fanIn)

theorem nodePolynomials_totalDegree_le_internal
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (outputChunk : Fin (chunkCount payloadWidth fanIn)) :
    (GroupedExtension.nodePolynomials
        (codebook payloadWidth fanIn)
        (layout payloadWidth fanIn)
        combine outputChunk).totalDegree ≤
      groupedDegree payloadWidth fanIn := by
  exact GroupedExtension.Internal.nodePolynomials_totalDegree_le_internal
    (codebook payloadWidth fanIn) (layout payloadWidth fanIn)
    combine outputChunk

theorem nodePolynomials_totalDegree_lt_card_sub_one_internal
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (outputChunk : Fin (chunkCount payloadWidth fanIn)) :
    (GroupedExtension.nodePolynomials
        (codebook payloadWidth fanIn)
        (layout payloadWidth fanIn)
        combine outputChunk).totalDegree <
      Fintype.card (Field payloadWidth fanIn) - 1 :=
  (nodePolynomials_totalDegree_le_internal
      payloadWidth fanIn combine outputChunk).trans_lt
    (groupedDegree_lt_card_sub_one_internal payloadWidth fanIn)

theorem liftTree_isLowDegreePolynomial_internal
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    IsLowDegreePolynomial
      (Fintype.card (Field payloadWidth fanIn) - 1)
      (liftTree payloadWidth fanIn tree) := by
  unfold liftTree
  exact
    GroupedExtension.Internal.liftTree_isLowDegreePolynomial_internal
      (codebook payloadWidth fanIn) (layout payloadWidth fanIn) tree
      (Fintype.card (Field payloadWidth fanIn) - 1)
      (groupedDegree_lt_card_sub_one_internal payloadWidth fanIn)

theorem liftTree_lineCompatible_internal
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    LineCompatible (units payloadWidth fanIn)
      (liftTree payloadWidth fanIn tree) := by
  unfold liftTree units
  exact
    GroupedExtension.Internal.liftTree_lineCompatible_internal
      (PrimeField.searchUnits
        (degreeEndpoint payloadWidth fanIn))
      (PrimeField.enumeratesSearchUnits
        (degreeEndpoint payloadWidth fanIn))
      (codebook payloadWidth fanIn) (layout payloadWidth fanIn) tree
      (groupedDegree_lt_card_sub_one_internal payloadWidth fanIn)

theorem value_liftTree_internal
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    (liftTree payloadWidth fanIn tree).value =
      encodeValue payloadWidth fanIn tree.value := by
  unfold liftTree encodeValue
  exact GroupedExtension.Internal.value_liftTree_internal
    (codebook payloadWidth fanIn) (layout payloadWidth fanIn) tree

theorem height_liftTree_internal
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    (liftTree payloadWidth fanIn tree).height = tree.height := by
  unfold liftTree
  exact GroupedExtension.Internal.height_liftTree_internal
    (codebook payloadWidth fanIn) (layout payloadWidth fanIn) tree

theorem evaluateTree_eq_encode_internal
    (payloadWidth fanIn : ℕ)
    (tree : Tree fanIn (Fin payloadWidth → Bool)) :
    evaluateTree payloadWidth fanIn tree =
      encodeValue payloadWidth fanIn tree.value := by
  unfold evaluateTree
  rw [evaluate_eq_value _ _
    (liftTree_lineCompatible_internal payloadWidth fanIn tree)]
  exact value_liftTree_internal payloadWidth fanIn tree

theorem fieldBitWidth_le_internal (payloadWidth fanIn : ℕ) :
    fieldBitWidth payloadWidth fanIn ≤
      2 * chunkBits payloadWidth fanIn + 1 := by
  rw [fieldBitWidth, Nat.size_le]
  calc
    PrimeField.Search.searchModulus
          (degreeEndpoint payloadWidth fanIn) ≤
        2 * (degreeEndpoint payloadWidth fanIn + 1) :=
      (PrimeField.Search.searchModulus_bounds
        (degreeEndpoint payloadWidth fanIn)).2
    _ ≤ 2 *
        (domainSize payloadWidth fanIn *
            (domainSize payloadWidth fanIn - 1) + 1) :=
      Nat.mul_le_mul_left 2
        (Nat.add_le_add_right
          (degreeEndpoint_le_domain_mul_pred_internal
            payloadWidth fanIn) 1)
    _ < 2 * domainSize payloadWidth fanIn ^ 2 := by
      have hdomain :=
        one_lt_domainSize_internal payloadWidth fanIn
      have hpred :
          domainSize payloadWidth fanIn - 1 + 1 =
            domainSize payloadWidth fanIn :=
        Nat.sub_add_cancel (by omega)
      nlinarith
    _ = 2 ^ (2 * chunkBits payloadWidth fanIn + 1) := by
      rw [domainSize, pow_two, ← pow_add]
      norm_num [pow_add]
      ring

theorem catalyticRegisterBitBudget_eq_internal
    (payloadWidth fanIn : ℕ) :
    catalyticRegisterBitBudget payloadWidth fanIn =
      (fanIn + 1) * chunkCount payloadWidth fanIn *
        fieldBitWidth payloadWidth fanIn := by
  rfl

theorem catalyticRegisterBitBudget_le_raw_internal
    (payloadWidth fanIn : ℕ) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      (fanIn + 1) * chunkCount payloadWidth fanIn *
        (2 * chunkBits payloadWidth fanIn + 1) := by
  rw [catalyticRegisterBitBudget_eq_internal]
  exact Nat.mul_le_mul_left _
    (fieldBitWidth_le_internal payloadWidth fanIn)

theorem catalyticRegisterBitBudget_le_padded_internal
    (payloadWidth fanIn : ℕ) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      3 * (fanIn + 1) *
        (payloadWidth + chunkBits payloadWidth fanIn) := by
  calc
    catalyticRegisterBitBudget payloadWidth fanIn ≤
        (fanIn + 1) * chunkCount payloadWidth fanIn *
          (2 * chunkBits payloadWidth fanIn + 1) :=
      catalyticRegisterBitBudget_le_raw_internal payloadWidth fanIn
    _ ≤ (fanIn + 1) * chunkCount payloadWidth fanIn *
        (3 * chunkBits payloadWidth fanIn) := by
      apply Nat.mul_le_mul_left
      have hpositive :=
        chunkBits_pos_internal payloadWidth fanIn
      omega
    _ = 3 * (fanIn + 1) *
        (chunkCount payloadWidth fanIn *
          chunkBits payloadWidth fanIn) := by
      ring
    _ ≤ 3 * (fanIn + 1) *
        (payloadWidth + chunkBits payloadWidth fanIn) :=
      Nat.mul_le_mul_left _
        (GroupedExtension.LogarithmicParameters.capacity_le_add_chunkBits
          payloadWidth fanIn)

theorem catalyticRegisterBitBudget_le_logarithmic_internal
    (payloadWidth fanIn : ℕ)
    (hregime :
      GroupedExtension.LogarithmicParameters.InLogarithmicRegime
        payloadWidth fanIn) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      6 * (fanIn + 1) * payloadWidth := by
  calc
    catalyticRegisterBitBudget payloadWidth fanIn ≤
        3 * (fanIn + 1) *
          (payloadWidth + chunkBits payloadWidth fanIn) :=
      catalyticRegisterBitBudget_le_padded_internal payloadWidth fanIn
    _ ≤ 3 * (fanIn + 1) * (payloadWidth + payloadWidth) :=
      Nat.mul_le_mul_left _
        (Nat.add_le_add_left hregime payloadWidth)
    _ = 6 * (fanIn + 1) * payloadWidth := by
      ring

theorem chunkCount_eq_one_of_small_internal
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth)
    (hsmall :
      GroupedExtension.LogarithmicParameters.RequiresSmallCase
        payloadWidth fanIn) :
    chunkCount payloadWidth fanIn = 1 := by
  apply Nat.le_antisymm
  · change
      GroupedExtension.LogarithmicParameters.chunkCount
        payloadWidth fanIn ≤ 1
    rw [GroupedExtension.LogarithmicParameters.chunkCount_eq]
    apply (ceilDiv_le_iff_le_mul
      (chunkBits_pos_internal payloadWidth fanIn)).2
    simpa using hsmall.le
  · change
      1 ≤ GroupedExtension.LogarithmicParameters.chunkCount
        payloadWidth fanIn
    exact GroupedExtension.LogarithmicParameters.chunkCount_pos
      payloadWidth fanIn hpayload

theorem catalyticRegisterBitBudget_le_small_internal
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth)
    (hsmall :
      GroupedExtension.LogarithmicParameters.RequiresSmallCase
        payloadWidth fanIn) :
    catalyticRegisterBitBudget payloadWidth fanIn ≤
      3 * (fanIn + 1) * chunkBits payloadWidth fanIn := by
  have hcount :=
    chunkCount_eq_one_of_small_internal
      payloadWidth fanIn hpayload hsmall
  calc
    catalyticRegisterBitBudget payloadWidth fanIn ≤
        (fanIn + 1) * chunkCount payloadWidth fanIn *
          (2 * chunkBits payloadWidth fanIn + 1) :=
      catalyticRegisterBitBudget_le_raw_internal payloadWidth fanIn
    _ = (fanIn + 1) *
        (2 * chunkBits payloadWidth fanIn + 1) := by
      rw [hcount]
      simp
    _ ≤ (fanIn + 1) * (3 * chunkBits payloadWidth fanIn) := by
      apply Nat.mul_le_mul_left
      have hpositive :=
        chunkBits_pos_internal payloadWidth fanIn
      omega
    _ = 3 * (fanIn + 1) * chunkBits payloadWidth fanIn := by
      ring

theorem catalyticRegisterBitBudget_branch_internal
    (payloadWidth fanIn : ℕ) (hpayload : 0 < payloadWidth) :
    (GroupedExtension.LogarithmicParameters.InLogarithmicRegime
        payloadWidth fanIn ∧
      catalyticRegisterBitBudget payloadWidth fanIn ≤
        6 * (fanIn + 1) * payloadWidth) ∨
    (GroupedExtension.LogarithmicParameters.RequiresSmallCase
        payloadWidth fanIn ∧
      chunkCount payloadWidth fanIn = 1 ∧
      catalyticRegisterBitBudget payloadWidth fanIn ≤
        3 * (fanIn + 1) * chunkBits payloadWidth fanIn) := by
  rcases
      GroupedExtension.LogarithmicParameters.inLogarithmicRegime_or_small
        payloadWidth fanIn with hregime | hsmall
  · exact Or.inl
      ⟨hregime,
        catalyticRegisterBitBudget_le_logarithmic_internal
          payloadWidth fanIn hregime⟩
  · exact Or.inr
      ⟨hsmall,
        chunkCount_eq_one_of_small_internal
          payloadWidth fanIn hpayload hsmall,
        catalyticRegisterBitBudget_le_small_internal
          payloadWidth fanIn hpayload hsmall⟩

theorem frameBitBudget_le_internal
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount ≤
      (2 * scalarCount + counterCount) *
          chunkBits payloadWidth fanIn +
        scalarCount := by
  unfold frameBitBudget
  calc
    scalarCount * fieldBitWidth payloadWidth fanIn +
          counterCount * chunkBits payloadWidth fanIn ≤
        scalarCount *
            (2 * chunkBits payloadWidth fanIn + 1) +
          counterCount * chunkBits payloadWidth fanIn :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left scalarCount
          (fieldBitWidth_le_internal payloadWidth fanIn)) _
    _ = (2 * scalarCount + counterCount) *
          chunkBits payloadWidth fanIn +
        scalarCount := by
      ring

theorem frameBitBudget_le_log_internal
    (payloadWidth fanIn scalarCount counterCount : ℕ) :
    frameBitBudget payloadWidth fanIn scalarCount counterCount ≤
      (3 * scalarCount + counterCount) *
        chunkBits payloadWidth fanIn := by
  calc
    frameBitBudget payloadWidth fanIn scalarCount counterCount ≤
        (2 * scalarCount + counterCount) *
            chunkBits payloadWidth fanIn +
          scalarCount :=
      frameBitBudget_le_internal
        payloadWidth fanIn scalarCount counterCount
    _ ≤ (2 * scalarCount + counterCount) *
          chunkBits payloadWidth fanIn +
        scalarCount * chunkBits payloadWidth fanIn := by
      apply Nat.add_le_add_left
      simpa using Nat.mul_le_mul_left scalarCount
        (chunkBits_pos_internal payloadWidth fanIn)
    _ = (3 * scalarCount + counterCount) *
        chunkBits payloadWidth fanIn := by
      ring

end Internal

end Logarithmic

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
