/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Defs
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial data for Cook--Mertz interpolation

This file defines the algebraic certificates used to discharge
`CookMertz.LineCompatible`.

The executable accumulator receives an explicit list of nonzero field
elements. `EnumeratesUnits` records that this list contains every unit exactly
once. Node functions are represented semantically by one multivariate
polynomial per output coordinate. The degree bound is stated using total
degree, since restricting such a polynomial to an affine line does not
increase its degree.

`lineRestriction` and `polynomialNode` are certificate-side definitions, not
the eventual implementation used to evaluate an implicitly presented node.
Consequently they may be noncomputable without weakening the executable
accumulator.

## Main definitions

- `EnumeratesUnits` -- an explicit list contains every nonzero field element
- `lineRestriction` -- restriction of a multivariate polynomial to an affine line
- `polynomialNode` -- coordinatewise polynomial extension of a node function
- `IsLowDegreePolynomial` -- recursive low-degree certificate for a tree
-/

open scoped Polynomial

namespace Complexity

namespace TreeEval

namespace CookMertz

variable {d : ℕ} {ι K : Type*}

/-- `units` contains every nonzero field element exactly once. -/
def EnumeratesUnits [GroupWithZero K] (units : List Kˣ) : Prop :=
  units.Nodup ∧ ∀ a : Kˣ, a ∈ units

/-- Restrict a multivariate polynomial to the affine line
`a ↦ base + a • direction`. -/
noncomputable def lineRestriction {σ : Type*} [CommRing K]
    (P : MvPolynomial σ K) (base direction : σ → K) : K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (base i) + Polynomial.C (direction i) * Polynomial.X) P

/-- Evaluate one multivariate polynomial per output coordinate on the
flattened collection of child values. -/
noncomputable def polynomialNode [CommSemiring K]
    (polynomials : ι → MvPolynomial (Fin d × ι) K)
    (args : Fin d → ι → K) : ι → K :=
  fun j => MvPolynomial.eval (fun i => args i.1 i.2) (polynomials j)

/-- Every internal node is represented by coordinate polynomials whose total
degree is below `degreeBound`. -/
def IsLowDegreePolynomial [CommSemiring K] (degreeBound : ℕ) :
    Tree d (ι → K) → Prop
  | .leaf _ => True
  | .node children combine =>
      (∀ r, IsLowDegreePolynomial degreeBound (children r)) ∧
      ∃ polynomials : ι → MvPolynomial (Fin d × ι) K,
        combine = polynomialNode polynomials ∧
        ∀ j, (polynomials j).totalDegree < degreeBound

end CookMertz

end TreeEval

end Complexity
