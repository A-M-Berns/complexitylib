/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Defs

/-!
# Proof internals for Boolean multilinear extensions

This file proves Boolean-cube agreement, individual multilinearity, and total
degree bounds for the definitions in `BooleanExtension.Defs`.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace BooleanExtension

namespace Internal

variable {σ K : Type*} {d b : ℕ}

theorem eval_basis_internal [Fintype σ] [CommRing K]
    (assignment point : σ → Bool) :
    MvPolynomial.eval (embed point)
        (basis assignment : MvPolynomial σ K) =
      if assignment = point then 1 else 0 := by
  classical
  by_cases h : assignment = point
  · subst point
    rw [if_pos rfl, basis, MvPolynomial.eval_prod]
    apply Finset.prod_eq_one
    intro i _
    cases hi : assignment i <;>
      simp [basisFactor, embed, bit, hi]
  · rw [if_neg h, basis, MvPolynomial.eval_prod]
    obtain ⟨i, hi⟩ : ∃ i, assignment i ≠ point i := by
      by_contra hnone
      push Not at hnone
      exact h (funext hnone)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hai : assignment i <;> cases hpi : point i <;>
      simp_all [basisFactor, embed, bit]

theorem eval_multilinearExtension_internal [Fintype σ]
    [CommRing K] (f : (σ → Bool) → K)
    (point : σ → Bool) :
    MvPolynomial.eval (embed point) (multilinearExtension f) =
      f point := by
  classical
  rw [multilinearExtension, MvPolynomial.eval_sum]
  simp [eval_basis_internal]

private theorem basisFactor_degreeOf_le [DecidableEq σ]
    [CommRing K] [Nontrivial K] (value : Bool) (i j : σ) :
    (basisFactor (K := K) value j).degreeOf i ≤
      if i = j then 1 else 0 := by
  cases value
  · rw [basisFactor]
    calc
      (1 - MvPolynomial.X j : MvPolynomial σ K).degreeOf i ≤
          max (MvPolynomial.degreeOf i (1 : MvPolynomial σ K))
            (MvPolynomial.degreeOf i (MvPolynomial.X j)) :=
        MvPolynomial.degreeOf_sub_le _ _ _
      _ = if i = j then 1 else 0 := by
        simp [MvPolynomial.degreeOf_X]
  · simp [basisFactor, MvPolynomial.degreeOf_X]

theorem basis_isMultilinear_internal [Fintype σ]
    [CommRing K] [Nontrivial K] (assignment : σ → Bool) :
    IsMultilinear (basis assignment : MvPolynomial σ K) := by
  classical
  intro i
  rw [basis]
  calc
    (∏ j : σ, basisFactor (K := K) (assignment j) j).degreeOf i ≤
        ∑ j ∈ Finset.univ,
          (basisFactor (K := K) (assignment j) j).degreeOf i :=
      MvPolynomial.degreeOf_prod_le i Finset.univ _
    _ ≤ ∑ j ∈ Finset.univ, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      exact basisFactor_degreeOf_le (assignment j) i j
    _ = 1 := by simp

theorem multilinearExtension_isMultilinear_internal [Fintype σ]
    [CommRing K] [Nontrivial K]
    (f : (σ → Bool) → K) :
    IsMultilinear (multilinearExtension f) := by
  classical
  intro i
  rw [multilinearExtension]
  calc
    (∑ assignment : σ → Bool,
        MvPolynomial.C (f assignment) * basis assignment).degreeOf i ≤
        Finset.univ.sup fun assignment : σ → Bool =>
          (MvPolynomial.C (f assignment) * basis assignment :
            MvPolynomial σ K).degreeOf i :=
      MvPolynomial.degreeOf_sum_le i Finset.univ _
    _ ≤ 1 := by
      apply Finset.sup_le
      intro assignment _
      calc
        (MvPolynomial.C (f assignment) * basis assignment :
            MvPolynomial σ K).degreeOf i ≤
            (MvPolynomial.C (f assignment) :
              MvPolynomial σ K).degreeOf i +
              (basis assignment).degreeOf i :=
          MvPolynomial.degreeOf_mul_le _ _ _
        _ ≤ 1 := by
          simpa using
            basis_isMultilinear_internal (K := K) assignment i

private theorem basisFactor_totalDegree_le [CommRing K] [Nontrivial K]
    (value : Bool) (i : σ) :
    (basisFactor (K := K) value i).totalDegree ≤ 1 := by
  cases value
  · rw [basisFactor]
    calc
      (1 - MvPolynomial.X i : MvPolynomial σ K).totalDegree ≤
          max (1 : MvPolynomial σ K).totalDegree
            (MvPolynomial.X i).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
      _ = 1 := by simp
  · simp [basisFactor]

theorem basis_totalDegree_le_internal [Fintype σ]
    [CommRing K] [Nontrivial K] (assignment : σ → Bool) :
    (basis assignment : MvPolynomial σ K).totalDegree ≤
      Fintype.card σ := by
  classical
  rw [basis]
  calc
    (∏ i : σ, basisFactor (K := K) (assignment i) i).totalDegree ≤
        ∑ i ∈ Finset.univ,
          (basisFactor (K := K) (assignment i) i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd Finset.univ _
    _ ≤ ∑ _i ∈ Finset.univ, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact basisFactor_totalDegree_le (assignment i) i
    _ = Fintype.card σ := by simp

theorem multilinearExtension_totalDegree_le_internal [Fintype σ]
    [CommRing K] [Nontrivial K]
    (f : (σ → Bool) → K) :
    (multilinearExtension f).totalDegree ≤ Fintype.card σ := by
  classical
  rw [multilinearExtension]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro assignment _
  calc
    (MvPolynomial.C (f assignment) * basis assignment :
        MvPolynomial σ K).totalDegree ≤
        (MvPolynomial.C (f assignment) :
          MvPolynomial σ K).totalDegree +
          (basis assignment).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ Fintype.card σ := by
      simpa using basis_totalDegree_le_internal (K := K) assignment

theorem polynomialNode_nodePolynomials_internal [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    polynomialNode (nodePolynomials (K := K) combine)
        (fun r j => bit (args r j)) =
      embed (combine args) := by
  funext j
  change MvPolynomial.eval
      (fun i => bit (args i.1 i.2))
      (multilinearExtension fun assignment =>
        bit (combine (unflatten assignment) j)) =
    bit (combine args j)
  simpa [embed, unflatten] using
    eval_multilinearExtension_internal
      (f := fun assignment : Fin d × Fin b → Bool =>
        bit (combine (unflatten assignment) j))
      (point := fun i => args i.1 i.2)

theorem nodePolynomials_isMultilinear_internal [CommRing K]
    [Nontrivial K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (j : Fin b) :
    IsMultilinear (nodePolynomials (K := K) combine j) :=
  multilinearExtension_isMultilinear_internal _

theorem nodePolynomials_totalDegree_le_internal [CommRing K]
    [Nontrivial K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (j : Fin b) :
    (nodePolynomials (K := K) combine j).totalDegree ≤ d * b := by
  simpa [nodePolynomials] using
    multilinearExtension_totalDegree_le_internal
      (f := fun assignment : Fin d × Fin b → Bool =>
        bit (combine (unflatten assignment) j))

end Internal

end BooleanExtension

end CookMertz

end TreeEval

end Complexity
