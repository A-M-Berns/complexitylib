/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Finset.Dedup
import Mathlib.FieldTheory.Finite.Basic

/-!
# Proofs for Cook--Mertz interpolation

This file proves the finite-field interpolation identity, shows that affine
line restriction does not increase total degree, and lifts those facts
coordinatewise to polynomially labelled trees.
-/

open scoped BigOperators Polynomial

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace Interpolation

private theorem list_sum_apply {ι V : Type*} [AddMonoid V]
    (l : List (ι → V)) (j : ι) :
    l.sum j = (l.map fun f => f j).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [ih]

private theorem list_sum_eq_univ_sum {K V : Type*} [Field K] [Fintype K]
    [DecidableEq K] [AddCommMonoid V] (units : List Kˣ)
    (henum : EnumeratesUnits units) (f : Kˣ → V) :
    (units.map f).sum = ∑ a : Kˣ, f a := by
  classical
  have hfinset : units.toFinset = Finset.univ := by
    ext a
    simp [henum.2 a]
  have hperm : Finset.univ.toList.Perm units := by
    rw [← hfinset]
    exact List.toFinset_toList henum.1
  rw [← (hperm.map f).sum_eq]
  simp

/-- Internal proof of the univariate finite-field interpolation identity. -/
theorem sum_units_eval_eq_neg_eval_zero_internal {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] (units : List Kˣ)
    (henum : EnumeratesUnits units) (P : K[X])
    (hdeg : P.natDegree < Fintype.card K - 1) :
    (units.map fun (a : Kˣ) => P.eval (a : K)).sum = -P.eval 0 := by
  rw [list_sum_eq_univ_sum units henum]
  classical
  calc
    (∑ x : Kˣ, P.eval (x : K)) =
        ∑ x : Kˣ, ∑ i ∈ Finset.range (Fintype.card K - 1),
          P.coeff i * (x : K) ^ i := by
            congr 1
            funext x
            exact P.eval_eq_sum_range' hdeg (x : K)
    _ = ∑ i ∈ Finset.range (Fintype.card K - 1),
          P.coeff i * ∑ x : Kˣ, (x : K) ^ i := by
            rw [Finset.sum_comm]
            congr 1
            funext i
            rw [Finset.mul_sum]
    _ = -P.coeff 0 := by
      rw [Finset.sum_eq_single 0]
      · rw [FiniteField.sum_pow_units]
        simp
      · intro i hi hi0
        rw [FiniteField.sum_pow_units, if_neg]
        · simp
        · intro hdiv
          have hpos : 0 < i := Nat.pos_of_ne_zero hi0
          have hle : Fintype.card K - 1 ≤ i := Nat.le_of_dvd hpos hdiv
          exact (not_le_of_gt (Finset.mem_range.mp hi)) hle
      · intro hzero
        exfalso
        have hcard : 1 < Fintype.card K := Fintype.one_lt_card
        exact hzero (Finset.mem_range.mpr (by omega))
    _ = -P.eval 0 := by rw [P.coeff_zero_eq_eval_zero]

@[simp] private theorem eval_lineRestriction {σ K : Type*} [CommRing K]
    (P : MvPolynomial σ K) (base direction : σ → K) (a : K) :
    (lineRestriction P base direction).eval a =
      MvPolynomial.eval (fun i => base i + direction i * a) P := by
  change Polynomial.evalRingHom a
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (base i) + Polynomial.C (direction i) * Polynomial.X) P) = _
  rw [← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext x
    simp
  · funext i
    simp
  · rfl

/-- Internal proof that affine line restriction does not increase total degree. -/
theorem natDegree_lineRestriction_le_totalDegree_internal {σ K : Type*}
    [CommRing K] (P : MvPolynomial σ K) (base direction : σ → K) :
    (lineRestriction P base direction).natDegree ≤ P.totalDegree := by
  classical
  change (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (base i) + Polynomial.C (direction i) * Polynomial.X) P).natDegree ≤
      P.totalDegree
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponents hexponents
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le exponents.support fun i =>
    (Polynomial.C (base i) + Polynomial.C (direction i) * Polynomial.X) ^
      exponents i).trans ?_
  calc
    (∑ i ∈ exponents.support,
        ((Polynomial.C (base i) + Polynomial.C (direction i) * Polynomial.X) ^
          exponents i).natDegree) ≤
        ∑ i ∈ exponents.support, exponents i := by
          apply Finset.sum_le_sum
          intro i _
          have hdegree :
              (Polynomial.C (base i) +
                Polynomial.C (direction i) * Polynomial.X).natDegree ≤ 1 := by
            refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
            · simp
            · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
          simpa using Polynomial.natDegree_pow_le_of_le (exponents i) hdegree
    _ = exponents.sum fun _ e => e := by rw [Finsupp.sum]
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hexponents

/-- Internal proof of the multivariate affine-line identity. -/
theorem sum_units_eval_affine_eq_neg_eval_base_internal {σ K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (units : List Kˣ)
    (henum : EnumeratesUnits units) (P : MvPolynomial σ K)
    (hdeg : P.totalDegree < Fintype.card K - 1) (base direction : σ → K) :
    (units.map fun (a : Kˣ) =>
      MvPolynomial.eval (fun i => base i + direction i * (a : K)) P).sum =
        -MvPolynomial.eval base P := by
  let Q := lineRestriction P base direction
  calc
    (units.map fun (a : Kˣ) =>
        MvPolynomial.eval (fun i => base i + direction i * (a : K)) P).sum =
        (units.map fun (a : Kˣ) => Q.eval (a : K)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro a _
          exact (eval_lineRestriction P base direction (a : K)).symm
    _ = -Q.eval 0 :=
      sum_units_eval_eq_neg_eval_zero_internal units henum Q
        ((natDegree_lineRestriction_le_totalDegree_internal P base direction).trans_lt hdeg)
    _ = -MvPolynomial.eval base P := by
      rw [eval_lineRestriction]
      apply congrArg Neg.neg
      apply congrArg (fun f : σ → K => MvPolynomial.eval f P)
      funext i
      simp

/-- Internal coordinatewise lifting of the affine-line identity. -/
theorem polynomialNode_line_identity_internal {d : ℕ} {ι K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (units : List Kˣ)
    (henum : EnumeratesUnits units)
    (polynomials : ι → MvPolynomial (Fin d × ι) K)
    (hdeg : ∀ j, (polynomials j).totalDegree < Fintype.card K - 1)
    (direction base : Fin d → ι → K) :
    (units.map fun (a : Kˣ) =>
      polynomialNode polynomials (fun r j => (a : K) * direction r j + base r j)).sum =
        -polynomialNode polynomials base := by
  funext j
  rw [list_sum_apply]
  simp only [List.map_map, polynomialNode, Pi.neg_apply]
  simpa [Function.comp_apply, polynomialNode, add_comm, mul_comm] using
    sum_units_eval_affine_eq_neg_eval_base_internal units henum
      (polynomials j) (hdeg j) (fun i => base i.1 i.2)
        (fun i => direction i.1 i.2)

/-- Internal induction from polynomial certificates to `LineCompatible`. -/
theorem lowDegreePolynomial_lineCompatible_internal {d : ℕ} {ι K : Type*}
    [Field K] [Fintype K] [DecidableEq K] (units : List Kˣ)
    (henum : EnumeratesUnits units) (tree : Tree d (ι → K))
    (hpoly : IsLowDegreePolynomial (Fintype.card K - 1) tree) :
    LineCompatible units tree := by
  induction tree with
  | leaf value => simp [LineCompatible]
  | node children combine ih =>
      rcases hpoly with ⟨hchildren, polynomials, rfl, hdeg⟩
      constructor
      · intro r
        exact ih r (hchildren r)
      · intro direction base
        simpa [Pi.smul_apply] using
          polynomialNode_line_identity_internal units henum polynomials hdeg
            direction base

end Interpolation

end CookMertz

end TreeEval

end Complexity
