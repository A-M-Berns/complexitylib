/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Defs
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Internal

/-!
# Finite-field interpolation for the Cook--Mertz evaluator

This file exposes the algebraic bridge used by the Cook--Mertz algorithm.
Summing a polynomial of degree below `|K| - 1` over every nonzero element of a
finite field gives the negative of its value at zero. Restricting a
multivariate polynomial to an affine line does not increase total degree, so
the same identity applies to low-degree polynomial node functions.

Over the characteristic-two fields used by Cook--Mertz and Williams,
negation is the identity. The signed statements here are valid over every
finite field.

## Main theorems

- `sum_units_eval_eq_neg_eval_zero` -- the univariate interpolation identity
- `lineRestriction_natDegree_le` -- affine restriction preserves the degree bound
- `sum_units_eval_affine_eq_neg_eval_base` -- the multivariate line identity
- `lowDegreePolynomial_lineCompatible` -- low-degree trees satisfy the accumulator hypothesis
- `evaluate_lowDegreePolynomial` -- the executable evaluator returns the tree value
-/

open scoped Polynomial

namespace Complexity

namespace TreeEval

namespace CookMertz

variable {d : ℕ} {ι K : Type*}

/-- Summing a low-degree polynomial over an explicit enumeration of all
nonzero field elements gives the negative of its value at zero. -/
theorem sum_units_eval_eq_neg_eval_zero [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : EnumeratesUnits units) (P : K[X])
    (hdeg : P.natDegree < Fintype.card K - 1) :
    (units.map fun (a : Kˣ) => P.eval (a : K)).sum = -P.eval 0 :=
  Interpolation.sum_units_eval_eq_neg_eval_zero_internal units henum P hdeg

/-- Restricting a multivariate polynomial to an affine line does not increase
its total degree. -/
theorem lineRestriction_natDegree_le {σ : Type*} [CommRing K]
    (P : MvPolynomial σ K) (base direction : σ → K) :
    (lineRestriction P base direction).natDegree ≤ P.totalDegree :=
  Interpolation.natDegree_lineRestriction_le_totalDegree_internal P base direction

/-- The finite-field interpolation identity along an affine line. -/
theorem sum_units_eval_affine_eq_neg_eval_base {σ : Type*} [Field K]
    [Fintype K] [DecidableEq K] (units : List Kˣ)
    (henum : EnumeratesUnits units) (P : MvPolynomial σ K)
    (hdeg : P.totalDegree < Fintype.card K - 1) (base direction : σ → K) :
    (units.map fun (a : Kˣ) =>
      MvPolynomial.eval (fun i => base i + direction i * (a : K)) P).sum =
        -MvPolynomial.eval base P :=
  Interpolation.sum_units_eval_affine_eq_neg_eval_base_internal
    units henum P hdeg base direction

/-- Coordinatewise polynomial node functions obey the affine-line identity
required by the Cook--Mertz accumulator. -/
theorem polynomialNode_line_identity [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : EnumeratesUnits units)
    (polynomials : ι → MvPolynomial (Fin d × ι) K)
    (hdeg : ∀ j, (polynomials j).totalDegree < Fintype.card K - 1)
    (direction base : Fin d → ι → K) :
    (units.map fun (a : Kˣ) =>
      polynomialNode polynomials (fun r j => (a : K) * direction r j + base r j)).sum =
        -polynomialNode polynomials base :=
  Interpolation.polynomialNode_line_identity_internal
    units henum polynomials hdeg direction base

/-- A tree whose node functions have sufficiently low-degree polynomial
extensions satisfies `LineCompatible`. -/
theorem lowDegreePolynomial_lineCompatible [Field K] [Fintype K]
    [DecidableEq K] (units : List Kˣ) (henum : EnumeratesUnits units)
    (tree : Tree d (ι → K))
    (hpoly : IsLowDegreePolynomial (Fintype.card K - 1) tree) :
    LineCompatible units tree :=
  Interpolation.lowDegreePolynomial_lineCompatible_internal
    units henum tree hpoly

/-- The executable Cook--Mertz evaluator agrees with ordinary tree evaluation
for every sufficiently low-degree polynomial tree. -/
theorem evaluate_lowDegreePolynomial [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : EnumeratesUnits units)
    (tree : Tree d (ι → K))
    (hpoly : IsLowDegreePolynomial (Fintype.card K - 1) tree) :
    evaluate units tree = tree.value :=
  evaluate_eq_value units tree
    (lowDegreePolynomial_lineCompatible units henum tree hpoly)

end CookMertz

end TreeEval

end Complexity
