/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation.Defs

/-!
# Correctness internals for executable Boolean extension evaluation

This file proves that the binary-code loop enumerates the Boolean cube
exactly once and that the executable evaluator agrees with the semantic
multivariate polynomial at every ring-valued point.
-/

open scoped BigOperators

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace BooleanExtension

namespace Evaluation

namespace Internal

variable {σ K : Type*} {width d b : ℕ}

private theorem ofFn_assignmentOfCode
    (encoding : σ ≃ Fin width) (code : ℕ) :
    List.ofFn
        (fun i : Fin width =>
          assignmentOfCode encoding code (encoding.symm i)) =
      Nat.toBits width code := by
  calc
    List.ofFn
        (fun i : Fin width =>
          assignmentOfCode encoding code (encoding.symm i)) =
        List.ofFn fun i : Fin width =>
          (Nat.toBits width code).get
            (Fin.cast (Nat.length_toBits width code).symm i) := by
      congr
      funext i
      simp [assignmentOfCode]
    _ = List.ofFn (Nat.toBits width code).get :=
      (List.ofFn_congr (Nat.length_toBits width code)
        (Nat.toBits width code).get).symm
    _ = Nat.toBits width code := List.ofFn_get _

theorem assignmentOfCode_codeOfAssignment_internal
    (encoding : σ ≃ Fin width) (assignment : σ → Bool) :
    assignmentOfCode encoding (codeOfAssignment encoding assignment) =
      assignment := by
  have hflat :
      (fun i : Fin width =>
        assignmentOfCode encoding (codeOfAssignment encoding assignment)
          (encoding.symm i)) =
        fun i : Fin width => assignment (encoding.symm i) := by
    apply List.ofFn_injective
    rw [ofFn_assignmentOfCode]
    simpa [codeOfAssignment] using
      Nat.toBits_fromBits
        (List.ofFn fun i : Fin width => assignment (encoding.symm i))
  funext i
  have hi := congrFun hflat (encoding i)
  simpa using hi

theorem codeOfAssignment_assignmentOfCode_internal
    (encoding : σ ≃ Fin width) {code : ℕ}
    (hcode : code < 2 ^ width) :
    codeOfAssignment encoding (assignmentOfCode encoding code) =
      code := by
  rw [codeOfAssignment, ofFn_assignmentOfCode]
  exact Nat.fromBits_toBits hcode

theorem codeOfAssignment_lt_internal (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) :
    codeOfAssignment encoding assignment < 2 ^ width := by
  simpa [codeOfAssignment] using
    Nat.fromBits_lt_pow_length
      (List.ofFn fun i : Fin width => assignment (encoding.symm i))

theorem assignments_nodup_internal (encoding : σ ≃ Fin width) :
    (assignments encoding).Nodup := by
  rw [assignments, List.nodup_map_iff_inj_on List.nodup_range]
  intro first hfirst second hsecond heq
  calc
    first =
        codeOfAssignment encoding (assignmentOfCode encoding first) :=
      (codeOfAssignment_assignmentOfCode_internal encoding
        (List.mem_range.mp hfirst)).symm
    _ = codeOfAssignment encoding (assignmentOfCode encoding second) :=
      congrArg (codeOfAssignment encoding) heq
    _ = second :=
      codeOfAssignment_assignmentOfCode_internal encoding
        (List.mem_range.mp hsecond)

theorem mem_assignments_internal (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) :
    assignment ∈ assignments encoding := by
  rw [assignments, List.mem_map]
  exact
    ⟨codeOfAssignment encoding assignment,
      List.mem_range.mpr
        (codeOfAssignment_lt_internal encoding assignment),
      assignmentOfCode_codeOfAssignment_internal encoding assignment⟩

theorem assignments_toFinset_internal [Fintype σ] [DecidableEq σ]
    (encoding : σ ≃ Fin width) :
    (assignments encoding).toFinset = Finset.univ := by
  ext assignment
  simp [mem_assignments_internal]

theorem assignments_length_internal (encoding : σ ≃ Fin width) :
    (assignments encoding).length = 2 ^ width := by
  simp [assignments]

theorem coordinates_nodup_internal (encoding : σ ≃ Fin width) :
    (coordinates encoding).Nodup := by
  rw [coordinates]
  exact (List.nodup_finRange width).map encoding.symm.injective

theorem mem_coordinates_internal (encoding : σ ≃ Fin width) (i : σ) :
    i ∈ coordinates encoding := by
  rw [coordinates, List.mem_map]
  exact ⟨encoding i, List.mem_finRange _, by simp⟩

theorem coordinates_toFinset_internal [Fintype σ] [DecidableEq σ]
    (encoding : σ ≃ Fin width) :
    (coordinates encoding).toFinset = Finset.univ := by
  ext i
  simp [mem_coordinates_internal]

theorem coordinates_length_internal (encoding : σ ≃ Fin width) :
    (coordinates encoding).length = width := by
  simp [coordinates]

private theorem foldRange_eq (term : ℕ → K) [AddMonoid K]
    (count : ℕ) (accumulator : K) :
    foldRange term count accumulator =
      ((List.range count).map term).sum + accumulator := by
  induction count generalizing accumulator with
  | zero => simp [foldRange]
  | succ count ih =>
      rw [foldRange, ih, List.range_succ, List.map_append,
        List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      exact (add_assoc _ _ _).symm

theorem sumRange_eq_map_sum_internal [AddMonoid K]
    (term : ℕ → K) (count : ℕ) :
    sumRange term count = ((List.range count).map term).sum := by
  rw [sumRange, foldRange_eq, add_zero]

theorem basisValue_eq_eval_basis_internal [Fintype σ]
    [DecidableEq σ] [CommRing K] (encoding : σ ≃ Fin width)
    (assignment : σ → Bool) (point : σ → K) :
    basisValue encoding assignment point =
      MvPolynomial.eval point (basis assignment) := by
  calc
    basisValue encoding assignment point =
        (coordinates encoding).toFinset.prod fun i =>
          if assignment i then point i else 1 - point i := by
      exact
        (List.prod_toFinset _ (coordinates_nodup_internal encoding)).symm
    _ = ∏ i : σ,
        if assignment i then point i else 1 - point i := by
      rw [coordinates_toFinset_internal]
    _ = MvPolynomial.eval point (basis assignment) := by
      rw [basis, MvPolynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro i _
      cases assignment i <;> simp [basisFactor]

private theorem evaluate_eq_fintype_sum [Fintype σ]
    [DecidableEq σ] [CommRing K] (encoding : σ ≃ Fin width)
    (f : (σ → Bool) → K) (point : σ → K) :
    evaluate encoding f point =
      ∑ assignment : σ → Bool,
        f assignment * basisValue encoding assignment point := by
  rw [evaluate, sumRange_eq_map_sum_internal]
  let term := fun assignment : σ → Bool =>
    f assignment * basisValue encoding assignment point
  change ((List.range (2 ^ width)).map
    (fun code => term (assignmentOfCode encoding code))).sum = _
  rw [show (List.range (2 ^ width)).map
      (fun code => term (assignmentOfCode encoding code)) =
      (assignments encoding).map term by
    simp [assignments, List.map_map, Function.comp_def]]
  rw [← List.sum_toFinset term (assignments_nodup_internal encoding),
    assignments_toFinset_internal]

theorem evaluate_eq_eval_multilinearExtension_internal [Fintype σ]
    [DecidableEq σ] [CommRing K] (encoding : σ ≃ Fin width)
    (f : (σ → Bool) → K) (point : σ → K) :
    evaluate encoding f point =
      MvPolynomial.eval point (multilinearExtension f) := by
  rw [evaluate_eq_fintype_sum, multilinearExtension,
    MvPolynomial.eval_sum]
  apply Finset.sum_congr
  · ext
    simp
  · intro assignment _
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C,
      basisValue_eq_eval_basis_internal]

theorem evaluateNode_eq_polynomialNode_internal [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool) :
    evaluateNode (K := K) combine =
      polynomialNode (nodePolynomials (K := K) combine) := by
  funext args j
  rw [evaluateNode, evaluate_eq_eval_multilinearExtension_internal]
  rfl

theorem evaluateNode_bool_internal [CommRing K]
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    evaluateNode (K := K) combine (fun r j => bit (args r j)) =
      embed (combine args) := by
  rw [evaluateNode_eq_polynomialNode_internal]
  exact polynomialNode_nodePolynomials combine args

end Internal

end Evaluation

end BooleanExtension

end CookMertz

end TreeEval

end Complexity
