/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Defs
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Internal

/-!
# Boolean multilinear extensions for Cook--Mertz evaluation

Every function on a finite Boolean cube has a coordinatewise multilinear
extension over a commutative ring. This module exposes cube agreement,
individual-degree bounds, and the total-degree bound needed by the
Cook--Mertz interpolation theorem.

A Boolean node with `d` inputs of `b` bits receives `d * b` Boolean
coordinates. Its output-coordinate extension therefore has total degree at
most `d * b`.

## Main theorems

- `eval_basis` -- basis polynomials are Boolean Kronecker deltas
- `eval_multilinearExtension` -- extension agrees on the Boolean cube
- `multilinearExtension_isMultilinear` -- every individual degree is at most one
- `multilinearExtension_totalDegree_le` -- total degree is at most the cube dimension
- `polynomialNode_nodePolynomials` -- node extensions agree on Boolean inputs
- `nodePolynomials_totalDegree_le` -- each node coordinate has degree at most `d * b`
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace BooleanExtension

variable {σ K : Type*} {d b : ℕ}

@[simp] theorem bit_false [Zero K] [One K] :
    bit (K := K) false = 0 :=
  rfl

@[simp] theorem bit_true [Zero K] [One K] :
    bit (K := K) true = 1 :=
  rfl

/-- A Boolean basis polynomial evaluates to one at its selected assignment
and zero at every other Boolean assignment. -/
theorem eval_basis [Fintype σ] [CommRing K]
    (assignment point : σ → Bool) :
    MvPolynomial.eval (embed point)
        (basis assignment : MvPolynomial σ K) =
      if assignment = point then 1 else 0 :=
  Internal.eval_basis_internal assignment point

/-- The multilinear extension agrees with the original function at every
Boolean point. -/
theorem eval_multilinearExtension [Fintype σ]
    [CommRing K] (f : (σ → Bool) → K) (point : σ → Bool) :
    MvPolynomial.eval (embed point) (multilinearExtension f) =
      f point :=
  Internal.eval_multilinearExtension_internal f point

/-- Every Boolean basis polynomial has individual degree at most one. -/
theorem basis_isMultilinear [Fintype σ]
    [CommRing K] [Nontrivial K] (assignment : σ → Bool) :
    IsMultilinear (basis assignment : MvPolynomial σ K) :=
  Internal.basis_isMultilinear_internal assignment

/-- A Boolean-cube extension is multilinear. -/
theorem multilinearExtension_isMultilinear [Fintype σ]
    [CommRing K] [Nontrivial K]
    (f : (σ → Bool) → K) :
    IsMultilinear (multilinearExtension f) :=
  Internal.multilinearExtension_isMultilinear_internal f

/-- A Boolean basis polynomial has total degree at most the cube dimension. -/
theorem basis_totalDegree_le [Fintype σ]
    [CommRing K] [Nontrivial K] (assignment : σ → Bool) :
    (basis assignment : MvPolynomial σ K).totalDegree ≤
      Fintype.card σ :=
  Internal.basis_totalDegree_le_internal assignment

/-- The total degree of a Boolean-cube extension is at most the number of
input bits. -/
theorem multilinearExtension_totalDegree_le [Fintype σ]
    [CommRing K] [Nontrivial K]
    (f : (σ → Bool) → K) :
    (multilinearExtension f).totalDegree ≤ Fintype.card σ :=
  Internal.multilinearExtension_totalDegree_le_internal f

/-- The coordinate polynomials for a Boolean node agree with that node after
embedding Boolean inputs and outputs into the ring. -/
theorem polynomialNode_nodePolynomials [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    polynomialNode (nodePolynomials (K := K) combine)
        (fun r j => bit (args r j)) =
      embed (combine args) :=
  Internal.polynomialNode_nodePolynomials_internal combine args

/-- Every node-coordinate extension has individual degree at most one. -/
theorem nodePolynomials_isMultilinear [CommRing K] [Nontrivial K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (j : Fin b) :
    IsMultilinear (nodePolynomials (K := K) combine j) :=
  Internal.nodePolynomials_isMultilinear_internal combine j

/-- Every node-coordinate extension has total degree at most the number
`d * b` of Boolean input coordinates. -/
theorem nodePolynomials_totalDegree_le [CommRing K] [Nontrivial K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (j : Fin b) :
    (nodePolynomials (K := K) combine j).totalDegree ≤ d * b :=
  Internal.nodePolynomials_totalDegree_le_internal combine j

end BooleanExtension

end CookMertz

end TreeEval

end Complexity
