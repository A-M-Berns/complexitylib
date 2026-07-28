/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation.Defs
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation.Internal

/-!
# Executable evaluation of Boolean multilinear extensions

This module exposes a binary-code evaluator for Boolean multilinear
extensions. It generates assignments one at a time and agrees with the
semantic polynomial at every ring-valued point.

The node specialization is the operational combining function used by the
Boolean ordered-DAG lift. Its correctness and degree certificate remain
separate: `evaluateNode_eq_polynomialNode` proves extensional equality to the
semantic polynomial node, while the executable definition itself contains no
multivariate-polynomial data.

## Main theorems

- `assignmentOfCode_codeOfAssignment` -- every assignment round-trips
- `assignments_nodup` and `mem_assignments` -- exact Boolean-cube enumeration
- `basisValue_eq_eval_basis` -- executable basis evaluation is semantic evaluation
- `evaluate_eq_eval_multilinearExtension` -- executable and polynomial evaluations agree
- `evaluateNode_eq_polynomialNode` -- executable Boolean-node extension is the certified node
- `evaluateNode_bool` -- executable node evaluation agrees on Boolean inputs
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace BooleanExtension

namespace Evaluation

variable {σ K : Type*} {width d b : ℕ}

@[simp] theorem assignmentOfCode_codeOfAssignment
    (encoding : σ ≃ Fin width) (assignment : σ → Bool) :
    assignmentOfCode encoding (codeOfAssignment encoding assignment) =
      assignment :=
  Internal.assignmentOfCode_codeOfAssignment_internal
    encoding assignment

@[simp] theorem codeOfAssignment_assignmentOfCode
    (encoding : σ ≃ Fin width) {code : ℕ}
    (hcode : code < 2 ^ width) :
    codeOfAssignment encoding (assignmentOfCode encoding code) =
      code :=
  Internal.codeOfAssignment_assignmentOfCode_internal encoding hcode

theorem codeOfAssignment_lt (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) :
    codeOfAssignment encoding assignment < 2 ^ width :=
  Internal.codeOfAssignment_lt_internal encoding assignment

theorem assignments_nodup (encoding : σ ≃ Fin width) :
    (assignments encoding).Nodup :=
  Internal.assignments_nodup_internal encoding

theorem mem_assignments (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) :
    assignment ∈ assignments encoding :=
  Internal.mem_assignments_internal encoding assignment

theorem assignments_toFinset [Fintype σ] [DecidableEq σ]
    (encoding : σ ≃ Fin width) :
    (assignments encoding).toFinset = Finset.univ :=
  Internal.assignments_toFinset_internal encoding

@[simp] theorem assignments_length (encoding : σ ≃ Fin width) :
    (assignments encoding).length = 2 ^ width :=
  Internal.assignments_length_internal encoding

theorem coordinates_nodup (encoding : σ ≃ Fin width) :
    (coordinates encoding).Nodup :=
  Internal.coordinates_nodup_internal encoding

theorem mem_coordinates (encoding : σ ≃ Fin width) (i : σ) :
    i ∈ coordinates encoding :=
  Internal.mem_coordinates_internal encoding i

theorem coordinates_toFinset [Fintype σ] [DecidableEq σ]
    (encoding : σ ≃ Fin width) :
    (coordinates encoding).toFinset = Finset.univ :=
  Internal.coordinates_toFinset_internal encoding

@[simp] theorem coordinates_length (encoding : σ ≃ Fin width) :
    (coordinates encoding).length = width :=
  Internal.coordinates_length_internal encoding

/-- Tail-recursive range summation agrees with the corresponding explicit
list sum. -/
theorem sumRange_eq_map_sum [AddMonoid K]
    (term : ℕ → K) (count : ℕ) :
    sumRange term count = ((List.range count).map term).sum :=
  Internal.sumRange_eq_map_sum_internal term count

/-- Executable evaluation of one basis weight agrees with evaluation of the
semantic basis polynomial. -/
theorem basisValue_eq_eval_basis [Fintype σ] [DecidableEq σ]
    [CommRing K] (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) (point : σ → K) :
    basisValue encoding assignment point =
      MvPolynomial.eval point (basis assignment) :=
  Internal.basisValue_eq_eval_basis_internal
    encoding assignment point

/-- The binary-code evaluator agrees with the full multilinear-extension
polynomial at every ring-valued point. -/
theorem evaluate_eq_eval_multilinearExtension [Fintype σ]
    [DecidableEq σ] [CommRing K] (encoding : σ ≃ Fin width)
    (f : (σ → Bool) → K) (point : σ → K) :
    evaluate encoding f point =
      MvPolynomial.eval point (multilinearExtension f) :=
  Internal.evaluate_eq_eval_multilinearExtension_internal
    encoding f point

/-- The executable extension of a Boolean node is extensionally equal to its
coordinatewise polynomial certificate. -/
theorem evaluateNode_eq_polynomialNode [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool) :
    evaluateNode (K := K) combine =
      polynomialNode (nodePolynomials (K := K) combine) :=
  Internal.evaluateNode_eq_polynomialNode_internal combine

/-- At Boolean inputs, executable node-extension evaluation agrees with the
original Boolean node after zero-one embedding. -/
theorem evaluateNode_bool [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    evaluateNode (K := K) combine (fun r j => bit (args r j)) =
      embed (combine args) :=
  Internal.evaluateNode_bool_internal combine args

end Evaluation

end BooleanExtension

end CookMertz

end TreeEval

end Complexity
