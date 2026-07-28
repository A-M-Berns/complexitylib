/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Evaluation.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Evaluation.Internal

/-!
# Executable evaluation of grouped Lagrange extensions

This module exposes a fixed-width-code evaluator for grouped Lagrange
extensions. It streams over assignments and Lagrange factors without
constructing the semantic `MvPolynomial` or a list of all assignments.

The correctness theorems identify each explicit product with its Lagrange
basis polynomial, then identify the complete evaluator with the grouped
extension at every field-valued point.

## Main theorems

- `assignments_nodup` and `assignments_toFinset` -- exact assignment enumeration
- `chunks_nodup` and `chunks_toFinset` -- exact chunk enumeration
- `productRange_eq_map_prod` -- correctness of the tail-recursive product loop
- `chunkBasisValue_eq_eval_lagrangeBasis` -- explicit Lagrange-weight correctness
- `evaluate_eq_eval_extension` -- streaming and semantic evaluation agree
- `evaluateNode_eq_polynomialNode` -- executable node evaluation is the certified node
- `evaluateNode_encoded` -- executable node correctness on encoded Boolean inputs
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Evaluation

variable {σ K : Type*}
  {coordinateCount chunkBits d b chunkCount : ℕ}

@[simp] theorem chunkAssignmentOfCode_codeOfChunkAssignment
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    (assignment : σ → Chunk chunkBits) :
    chunkAssignmentOfCode encoding chunkBits
        (codeOfChunkAssignment encoding chunkBits assignment) =
      assignment :=
  Internal.chunkAssignmentOfCode_codeOfChunkAssignment_internal
    encoding chunkBits assignment

@[simp] theorem codeOfChunkAssignment_chunkAssignmentOfCode
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    {code : ℕ} (hcode : code < 2 ^ (coordinateCount * chunkBits)) :
    codeOfChunkAssignment encoding chunkBits
        (chunkAssignmentOfCode encoding chunkBits code) =
      code :=
  Internal.codeOfChunkAssignment_chunkAssignmentOfCode_internal
    encoding chunkBits hcode

theorem codeOfChunkAssignment_lt
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    (assignment : σ → Chunk chunkBits) :
    codeOfChunkAssignment encoding chunkBits assignment <
      2 ^ (coordinateCount * chunkBits) :=
  Internal.codeOfChunkAssignment_lt_internal
    encoding chunkBits assignment

theorem assignments_nodup
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ) :
    (assignments encoding chunkBits).Nodup :=
  Internal.assignments_nodup_internal encoding chunkBits

theorem mem_assignments
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ)
    (assignment : σ → Chunk chunkBits) :
    assignment ∈ assignments encoding chunkBits :=
  Internal.mem_assignments_internal encoding chunkBits assignment

theorem assignments_toFinset [Fintype σ] [DecidableEq σ]
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ) :
    (assignments encoding chunkBits).toFinset = Finset.univ :=
  Internal.assignments_toFinset_internal encoding chunkBits

@[simp] theorem assignments_length
    (encoding : σ ≃ Fin coordinateCount) (chunkBits : ℕ) :
    (assignments encoding chunkBits).length =
      2 ^ (coordinateCount * chunkBits) :=
  Internal.assignments_length_internal encoding chunkBits

@[simp] theorem chunkOfCode_codeOfChunk (chunk : Chunk chunkBits) :
    chunkOfCode chunkBits (codeOfChunk chunk) = chunk :=
  Internal.chunkOfCode_codeOfChunk_internal chunk

@[simp] theorem codeOfChunk_chunkOfCode {code : ℕ}
    (hcode : code < 2 ^ chunkBits) :
    codeOfChunk (chunkOfCode chunkBits code) = code :=
  Internal.codeOfChunk_chunkOfCode_internal hcode

theorem codeOfChunk_lt (chunk : Chunk chunkBits) :
    codeOfChunk chunk < 2 ^ chunkBits :=
  Internal.codeOfChunk_lt_internal chunk

theorem chunks_nodup (chunkBits : ℕ) :
    (chunks chunkBits).Nodup :=
  Internal.chunks_nodup_internal chunkBits

theorem mem_chunks (chunk : Chunk chunkBits) :
    chunk ∈ chunks chunkBits :=
  Internal.mem_chunks_internal chunk

theorem chunks_toFinset (chunkBits : ℕ) :
    (chunks chunkBits).toFinset = Finset.univ :=
  Internal.chunks_toFinset_internal chunkBits

@[simp] theorem chunks_length (chunkBits : ℕ) :
    (chunks chunkBits).length = 2 ^ chunkBits :=
  Internal.chunks_length_internal chunkBits

/-- The tail-recursive product loop agrees with the corresponding list
product. -/
theorem productRange_eq_map_prod [Monoid K]
    (term : ℕ → K) (count : ℕ) :
    productRange term count = ((List.range count).map term).prod :=
  Internal.productRange_eq_map_prod_internal term count

/-- The explicit normalized Lagrange factor agrees with evaluation of the
corresponding divisor polynomial away from the selected point. -/
theorem lagrangeFactorValue_eq_eval_basisDivisor
    [Field K] [Fintype K] (codebook : Codebook K chunkBits)
    (selected other : Chunk chunkBits) (point : K)
    (hne : selected ≠ other) :
    lagrangeFactorValue codebook selected other point =
      Polynomial.eval point
        (Lagrange.basisDivisor
          (codebook.encode selected) (codebook.encode other)) :=
  Internal.lagrangeFactorValue_eq_eval_basisDivisor_internal
    codebook selected other point hne

/-- Streaming over all fixed-width chunks computes exactly one univariate
Lagrange basis value. -/
theorem chunkBasisValue_eq_eval_lagrangeBasis
    [Field K] [Fintype K] (codebook : Codebook K chunkBits)
    (selected : Chunk chunkBits) (point : K) :
    chunkBasisValue codebook selected point =
      Polynomial.eval point
        (Lagrange.basis Finset.univ codebook.encode selected) :=
  Internal.chunkBasisValue_eq_eval_lagrangeBasis_internal
    codebook selected point

/-- The executable tensor-product basis value agrees with evaluation of the
semantic grouped basis polynomial. -/
theorem basisValue_eq_eval_basis [Fintype σ]
    [DecidableEq σ] [Field K] [Fintype K]
    (encoding : σ ≃ Fin coordinateCount)
    (codebook : Codebook K chunkBits)
    (assignment : σ → Chunk chunkBits) (point : σ → K) :
    basisValue encoding codebook assignment point =
      MvPolynomial.eval point (basis codebook assignment) :=
  Internal.basisValue_eq_eval_basis_internal
    encoding codebook assignment point

/-- The fixed-width-code evaluator agrees with the semantic grouped
extension at every field-valued point. -/
theorem evaluate_eq_eval_extension [Fintype σ]
    [DecidableEq σ] [Field K] [Fintype K]
    (encoding : σ ≃ Fin coordinateCount)
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K) (point : σ → K) :
    evaluate encoding codebook f point =
      MvPolynomial.eval point (extension codebook f) :=
  Internal.evaluate_eq_eval_extension_internal
    encoding codebook f point

/-- Executable grouped-node evaluation is extensionally equal to its
coordinatewise polynomial certificate. -/
theorem evaluateNode_eq_polynomialNode
    [Field K] [Fintype K]
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool) :
    evaluateNode codebook layout combine =
      polynomialNode (nodePolynomials codebook layout combine) :=
  Internal.evaluateNode_eq_polynomialNode_internal
    codebook layout combine

/-- On encoded Boolean children, executable grouped-node evaluation returns
the encoded Boolean output. -/
theorem evaluateNode_encoded [Field K] [Fintype K]
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    evaluateNode codebook layout combine
        (fun child =>
          encodeVector codebook (args child)) =
      encodeVector codebook (combine args) :=
  Internal.evaluateNode_encoded_internal
    codebook layout combine args

end Evaluation

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
