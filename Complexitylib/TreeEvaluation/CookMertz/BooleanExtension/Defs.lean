/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Defs

/-!
# Boolean multilinear extensions for Cook--Mertz nodes

This file defines the semantic polynomial extension of a Boolean function.
For an assignment `a : σ → Bool`, `basis a` is the product of the coordinate
factors `Xᵢ` or `1 - Xᵢ`. Summing these basis polynomials with the values of a
function gives its unique multilinear extension on the Boolean cube.

The final definition specializes this construction to a Cook--Mertz node with
`d` children of `b` bits each. The resulting coordinate polynomials have
variables indexed by `Fin d × Fin b`.

These are certificate-side definitions. Constructing a full multivariate
polynomial enumerates all Boolean assignments and is not the eventual
space-bounded implementation.

## Main definitions

- `bit` -- embed a Boolean as zero or one
- `embed` -- coordinatewise Boolean embedding
- `basis` -- Boolean-cube Lagrange basis polynomial
- `multilinearExtension` -- full multilinear extension of a Boolean function
- `IsMultilinear` -- individual degree at most one in every variable
- `nodePolynomials` -- coordinate extensions for a `d`-input, `b`-bit node
-/

open scoped BigOperators

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace BooleanExtension

variable {σ ι K : Type*} {d b : ℕ}

/-- Embed a Boolean value as zero or one. -/
def bit [Zero K] [One K] (value : Bool) : K :=
  if value then 1 else 0

/-- Embed a Boolean vector coordinatewise into a type with zero and one. -/
def embed [Zero K] [One K] (value : ι → Bool) : ι → K :=
  fun i => bit (value i)

/-- The coordinate factor selecting one Boolean value. -/
noncomputable def basisFactor [CommRing K]
    (value : Bool) (i : σ) : MvPolynomial σ K :=
  if value then MvPolynomial.X i else 1 - MvPolynomial.X i

/-- The Lagrange basis polynomial selecting one Boolean assignment. -/
noncomputable def basis [Fintype σ] [CommRing K]
    (assignment : σ → Bool) : MvPolynomial σ K :=
  ∏ i : σ, basisFactor (assignment i) i

/-- The multilinear extension of a function on the Boolean cube. -/
noncomputable def multilinearExtension
    [Fintype σ] [CommRing K]
    (f : (σ → Bool) → K) : MvPolynomial σ K := by
  classical
  exact ∑ assignment : σ → Bool,
    MvPolynomial.C (f assignment) * basis assignment

/-- A multivariate polynomial has individual degree at most one. -/
def IsMultilinear [CommSemiring K] (P : MvPolynomial σ K) : Prop :=
  ∀ i, P.degreeOf i ≤ 1

/-- Unflatten `d * b` Boolean coordinates into `d` vectors of `b` bits. -/
def unflatten (assignment : Fin d × Fin b → Bool) :
    Fin d → Fin b → Bool :=
  fun r j => assignment (r, j)

/-- One multilinear-extension polynomial for each output bit of a Boolean
node function. -/
noncomputable def nodePolynomials [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool) :
    Fin b → MvPolynomial (Fin d × Fin b) K :=
  fun j => multilinearExtension fun assignment =>
    bit (combine (unflatten assignment) j)

end BooleanExtension

end CookMertz

end TreeEval

end Complexity
