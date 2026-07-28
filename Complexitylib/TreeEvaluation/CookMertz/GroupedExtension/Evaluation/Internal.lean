/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Evaluation.Defs

/-!
# Correctness internals for executable grouped evaluation

This file proves exact code enumeration, identifies the explicit range
products with Lagrange basis evaluation, and then identifies the streaming
outer sum with evaluation of the semantic grouped extension.
-/

open scoped BigOperators

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Evaluation

namespace Internal

variable {σ K : Type*}
  {coordinateCount chunkBits d b chunkCount : ℕ}

theorem chunkAssignmentOfCode_codeOfChunkAssignment_internal
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    (assignment : σ → Chunk chunkBits) :
    chunkAssignmentOfCode encoding chunkBits
        (codeOfChunkAssignment encoding chunkBits assignment) =
      assignment := by
  have h :=
    BooleanExtension.Evaluation.assignmentOfCode_codeOfAssignment
      (bitEncoding encoding chunkBits)
      (fun coordinate : σ × Fin chunkBits =>
        assignment coordinate.1 coordinate.2)
  funext coordinate offset
  exact congrFun h (coordinate, offset)

theorem codeOfChunkAssignment_chunkAssignmentOfCode_internal
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    {code : ℕ} (hcode : code < 2 ^ (coordinateCount * chunkBits)) :
    codeOfChunkAssignment encoding chunkBits
        (chunkAssignmentOfCode encoding chunkBits code) =
      code :=
  BooleanExtension.Evaluation.codeOfAssignment_assignmentOfCode
    (bitEncoding encoding chunkBits) hcode

theorem codeOfChunkAssignment_lt_internal
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    (assignment : σ → Chunk chunkBits) :
    codeOfChunkAssignment encoding chunkBits assignment <
      2 ^ (coordinateCount * chunkBits) :=
  BooleanExtension.Evaluation.codeOfAssignment_lt
    (bitEncoding encoding chunkBits)
    (fun coordinate => assignment coordinate.1 coordinate.2)

theorem assignments_nodup_internal
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ) :
    (assignments encoding chunkBits).Nodup := by
  rw [assignments, List.nodup_map_iff_inj_on List.nodup_range]
  intro first hfirst second hsecond heq
  calc
    first =
        codeOfChunkAssignment encoding chunkBits
          (chunkAssignmentOfCode encoding chunkBits first) :=
      (codeOfChunkAssignment_chunkAssignmentOfCode_internal
        encoding chunkBits (List.mem_range.mp hfirst)).symm
    _ = codeOfChunkAssignment encoding chunkBits
          (chunkAssignmentOfCode encoding chunkBits second) :=
      congrArg (codeOfChunkAssignment encoding chunkBits) heq
    _ = second :=
      codeOfChunkAssignment_chunkAssignmentOfCode_internal
        encoding chunkBits (List.mem_range.mp hsecond)

theorem mem_assignments_internal
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    (assignment : σ → Chunk chunkBits) :
    assignment ∈ assignments encoding chunkBits := by
  rw [assignments, List.mem_map]
  exact
    ⟨codeOfChunkAssignment encoding chunkBits assignment,
      List.mem_range.mpr
        (codeOfChunkAssignment_lt_internal
          encoding chunkBits assignment),
      chunkAssignmentOfCode_codeOfChunkAssignment_internal
        encoding chunkBits assignment⟩

theorem assignments_toFinset_internal [Fintype σ] [DecidableEq σ]
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ) :
    (assignments encoding chunkBits).toFinset = Finset.univ := by
  ext assignment
  simp [mem_assignments_internal]

theorem assignments_length_internal
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ) :
    (assignments encoding chunkBits).length =
      2 ^ (coordinateCount * chunkBits) := by
  simp [assignments]

theorem chunkOfCode_codeOfChunk_internal
    (chunk : Chunk chunkBits) :
    chunkOfCode chunkBits (codeOfChunk chunk) = chunk :=
  BooleanExtension.Evaluation.assignmentOfCode_codeOfAssignment
    (Equiv.refl (Fin chunkBits)) chunk

theorem codeOfChunk_chunkOfCode_internal {code : ℕ}
    (hcode : code < 2 ^ chunkBits) :
    codeOfChunk (chunkOfCode chunkBits code) = code :=
  BooleanExtension.Evaluation.codeOfAssignment_assignmentOfCode
    (Equiv.refl (Fin chunkBits)) hcode

theorem codeOfChunk_lt_internal (chunk : Chunk chunkBits) :
    codeOfChunk chunk < 2 ^ chunkBits :=
  BooleanExtension.Evaluation.codeOfAssignment_lt
    (Equiv.refl (Fin chunkBits)) chunk

theorem chunks_nodup_internal (chunkBits : ℕ) :
    (chunks chunkBits).Nodup := by
  simpa [chunks, chunkOfCode,
    BooleanExtension.Evaluation.assignments] using
      BooleanExtension.Evaluation.assignments_nodup
        (Equiv.refl (Fin chunkBits))

theorem mem_chunks_internal (chunk : Chunk chunkBits) :
    chunk ∈ chunks chunkBits := by
  simpa [chunks, chunkOfCode,
    BooleanExtension.Evaluation.assignments] using
      BooleanExtension.Evaluation.mem_assignments
        (Equiv.refl (Fin chunkBits)) chunk

theorem chunks_toFinset_internal (chunkBits : ℕ) :
    (chunks chunkBits).toFinset = Finset.univ := by
  simpa [chunks, chunkOfCode,
    BooleanExtension.Evaluation.assignments] using
      BooleanExtension.Evaluation.assignments_toFinset
        (Equiv.refl (Fin chunkBits))

theorem chunks_length_internal (chunkBits : ℕ) :
    (chunks chunkBits).length = 2 ^ chunkBits := by
  simp [chunks]

private theorem foldProductRange_eq (term : ℕ → K) [Monoid K]
    (count : ℕ) (accumulator : K) :
    foldProductRange term count accumulator =
      ((List.range count).map term).prod * accumulator := by
  induction count generalizing accumulator with
  | zero => simp [foldProductRange]
  | succ count ih =>
      rw [foldProductRange, ih, List.range_succ, List.map_append,
        List.prod_append]
      simp only [List.map_singleton, List.prod_singleton]
      exact (mul_assoc _ _ _).symm

theorem productRange_eq_map_prod_internal [Monoid K]
    (term : ℕ → K) (count : ℕ) :
    productRange term count = ((List.range count).map term).prod := by
  rw [productRange, foldProductRange_eq, mul_one]

theorem lagrangeFactorValue_eq_eval_basisDivisor_internal
    [Field K] [Fintype K] (codebook : Codebook K chunkBits)
    (selected other : Chunk chunkBits) (point : K)
    (hne : selected ≠ other) :
    lagrangeFactorValue codebook selected other point =
      Polynomial.eval point
        (Lagrange.basisDivisor
          (codebook.encode selected) (codebook.encode other)) := by
  simp [lagrangeFactorValue, hne, Lagrange.basisDivisor]

theorem chunkBasisValue_eq_eval_lagrangeBasis_internal
    [Field K] [Fintype K] (codebook : Codebook K chunkBits)
    (selected : Chunk chunkBits) (point : K) :
    chunkBasisValue codebook selected point =
      Polynomial.eval point
        (Lagrange.basis Finset.univ codebook.encode selected) := by
  rw [chunkBasisValue, productRange_eq_map_prod_internal]
  let factor := fun other : Chunk chunkBits =>
    lagrangeFactorValue codebook selected other point
  calc
    ((List.range (2 ^ chunkBits)).map
        (fun code =>
          lagrangeFactorValue codebook selected
            (chunkOfCode chunkBits code) point)).prod =
        ((chunks chunkBits).map factor).prod := by
      simp [chunks, factor, List.map_map, Function.comp_def]
    _ = (chunks chunkBits).toFinset.prod factor := by
      exact
        (List.prod_toFinset factor
          (chunks_nodup_internal chunkBits)).symm
    _ = (Finset.univ : Finset (Chunk chunkBits)).prod factor := by
      rw [chunks_toFinset_internal]
    _ = (Finset.univ.erase selected).prod factor := by
      symm
      exact Finset.prod_erase Finset.univ (by
        simp [lagrangeFactorValue])
    _ = Polynomial.eval point
        (Lagrange.basis Finset.univ codebook.encode selected) := by
      rw [Lagrange.basis, Polynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro other hother
      have hne : selected ≠ other :=
        (Finset.mem_erase.mp hother).1.symm
      exact
        lagrangeFactorValue_eq_eval_basisDivisor_internal
          codebook selected other point hne

theorem basisValue_eq_eval_basis_internal [Fintype σ]
    [DecidableEq σ] [Field K] [Fintype K]
    (encoding : σ ≃ Fin coordinateCount)
    (codebook : Codebook K chunkBits)
    (assignment : σ → Chunk chunkBits) (point : σ → K) :
    basisValue encoding codebook assignment point =
      MvPolynomial.eval point (basis codebook assignment) := by
  calc
    basisValue encoding codebook assignment point =
        (BooleanExtension.Evaluation.coordinates encoding).toFinset.prod
          fun coordinate =>
            chunkBasisValue codebook
              (assignment coordinate) (point coordinate) := by
      exact
        (List.prod_toFinset _
          (BooleanExtension.Evaluation.coordinates_nodup encoding)).symm
    _ = ∏ coordinate : σ,
        chunkBasisValue codebook
          (assignment coordinate) (point coordinate) := by
      rw [BooleanExtension.Evaluation.coordinates_toFinset]
    _ = MvPolynomial.eval point (basis codebook assignment) := by
      rw [basis, MvPolynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro coordinate _
      rw [chunkBasisValue_eq_eval_lagrangeBasis_internal,
        basisFactor, MvPolynomial.eval_toMvPolynomial]

private theorem evaluate_eq_fintype_sum [Fintype σ]
    [DecidableEq σ] [Field K] [Fintype K]
    (encoding : σ ≃ Fin coordinateCount)
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K) (point : σ → K) :
    evaluate encoding codebook f point =
      ∑ assignment : σ → Chunk chunkBits,
        f assignment *
          basisValue encoding codebook assignment point := by
  rw [evaluate, BooleanExtension.Evaluation.sumRange_eq_map_sum]
  let term := fun assignment : σ → Chunk chunkBits =>
    f assignment *
      basisValue encoding codebook assignment point
  change
    ((List.range (2 ^ (coordinateCount * chunkBits))).map
      (fun code =>
        term (chunkAssignmentOfCode encoding chunkBits code))).sum = _
  rw [show
    (List.range (2 ^ (coordinateCount * chunkBits))).map
        (fun code =>
          term (chunkAssignmentOfCode encoding chunkBits code)) =
      (assignments encoding chunkBits).map term by
    simp [assignments, List.map_map, Function.comp_def]]
  rw [← List.sum_toFinset term
      (assignments_nodup_internal encoding chunkBits),
    assignments_toFinset_internal]

theorem evaluate_eq_eval_extension_internal [Fintype σ]
    [DecidableEq σ] [Field K] [Fintype K]
    (encoding : σ ≃ Fin coordinateCount)
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K) (point : σ → K) :
    evaluate encoding codebook f point =
      MvPolynomial.eval point (extension codebook f) := by
  rw [evaluate_eq_fintype_sum, extension,
    MvPolynomial.eval_sum]
  apply Finset.sum_congr
  · ext
    simp
  · intro assignment _
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C,
      basisValue_eq_eval_basis_internal]

theorem evaluateNode_eq_polynomialNode_internal
    [Field K] [Fintype K]
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool) :
    evaluateNode codebook layout combine =
      polynomialNode (nodePolynomials codebook layout combine) := by
  funext args outputChunk
  rw [evaluateNode, evaluate_eq_eval_extension_internal]
  rfl

theorem evaluateNode_encoded_internal [Field K] [Fintype K]
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    evaluateNode codebook layout combine
        (fun child =>
          encodeVector codebook (args child)) =
      encodeVector codebook (combine args) := by
  rw [evaluateNode_eq_polynomialNode_internal]
  exact polynomialNode_nodePolynomials codebook layout combine args

end Internal

end Evaluation

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
