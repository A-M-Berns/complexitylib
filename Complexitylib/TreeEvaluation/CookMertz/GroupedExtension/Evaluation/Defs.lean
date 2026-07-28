/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Executable grouped-extension evaluation

The semantic grouped extension is an `MvPolynomial` certificate rather than
an executable evaluator. This module instead streams over fixed-width binary codes. A code of width
`coordinateCount * chunkBits` is decoded on demand as one assignment of a
Boolean chunk to every coordinate.

For each assignment and coordinate, the evaluator computes the Lagrange
weight explicitly. The product over the `2 ^ chunkBits` possible chunks is a
tail-recursive range loop, and the outer sum reuses
`BooleanExtension.Evaluation.sumRange`. Neither executable loop constructs a
semantic polynomial or a list of all assignments.

The certification lists `chunks` and `assignments` are retained only for
proofs that the code loops enumerate their finite domains exactly once.

## Main definitions

- `bitEncoding` -- flatten coordinate/chunk-bit pairs to one code width
- `chunkAssignmentOfCode` -- decode one grouped assignment
- `productRange` -- tail-recursive product over a natural range
- `chunkBasisValue` -- explicit univariate Lagrange weight
- `basisValue` -- product of chunk weights over all coordinates
- `evaluate` -- streaming grouped-extension evaluation
- `evaluateNode` -- executable grouped Boolean-node specialization
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Evaluation

variable {σ K : Type*}
  {coordinateCount chunkBits d b chunkCount : ℕ}

/-- Flatten one semantic coordinate and one bit offset into a fixed-width
binary-code coordinate. -/
def bitEncoding (encoding : σ ≃ Fin coordinateCount)
    (chunkBits : ℕ) :
    (σ × Fin chunkBits) ≃ Fin (coordinateCount * chunkBits) :=
  (Equiv.prodCongr encoding (Equiv.refl (Fin chunkBits))).trans
    finProdFinEquiv

/-- Decode one fixed-width code as a chunk-valued assignment. Codes outside
the fixed width are truncated by `Nat.toBits`. -/
def chunkAssignmentOfCode (encoding : σ ≃ Fin coordinateCount)
    (chunkBits code : ℕ) : σ → Chunk chunkBits :=
  fun coordinate offset =>
    BooleanExtension.Evaluation.assignmentOfCode
      (bitEncoding encoding chunkBits) code (coordinate, offset)

/-- Encode a chunk-valued assignment in the inverse flattened coordinate
order. -/
def codeOfChunkAssignment (encoding : σ ≃ Fin coordinateCount)
    (chunkBits : ℕ) (assignment : σ → Chunk chunkBits) : ℕ :=
  BooleanExtension.Evaluation.codeOfAssignment
    (bitEncoding encoding chunkBits)
    (fun coordinate => assignment coordinate.1 coordinate.2)

/-- Certification list of every chunk-valued assignment in increasing code
order. The streaming evaluator does not construct this list. -/
def assignments (encoding : σ ≃ Fin coordinateCount)
    (chunkBits : ℕ) : List (σ → Chunk chunkBits) :=
  (List.range (2 ^ (coordinateCount * chunkBits))).map
    (chunkAssignmentOfCode encoding chunkBits)

/-- Decode one fixed-width binary chunk code. -/
def chunkOfCode (chunkBits code : ℕ) : Chunk chunkBits :=
  BooleanExtension.Evaluation.assignmentOfCode
    (Equiv.refl (Fin chunkBits)) code

/-- Encode one chunk as its fixed-width binary code. -/
def codeOfChunk {chunkBits : ℕ} (chunk : Chunk chunkBits) : ℕ :=
  BooleanExtension.Evaluation.codeOfAssignment
    (Equiv.refl (Fin chunkBits)) chunk

/-- Certification list of all chunks in increasing binary-code order. -/
def chunks (chunkBits : ℕ) : List (Chunk chunkBits) :=
  (List.range (2 ^ chunkBits)).map (chunkOfCode chunkBits)

/-- Tail-recursive left-associated multiplication of `term 0` through
`term (count - 1)`. -/
def foldProductRange {R : Type*} [Monoid R] (term : ℕ → R) :
    ℕ → R → R
  | 0, accumulator => accumulator
  | count + 1, accumulator =>
      foldProductRange term count (term count * accumulator)

/-- Product of `term` over the natural numbers below `count`, using one
accumulator. -/
def productRange {R : Type*} [Monoid R]
    (term : ℕ → R) (count : ℕ) : R :=
  foldProductRange term count 1

/-- Explicit value of one normalized Lagrange divisor. The selected point
contributes `1`, matching omission from `Finset.univ.erase selected`. -/
def lagrangeFactorValue [Field K] [Fintype K]
    (codebook : Codebook K chunkBits)
    (selected other : Chunk chunkBits) (point : K) : K :=
  if selected = other then
    1
  else
    (codebook.encode selected - codebook.encode other)⁻¹ *
      (point - codebook.encode other)

/-- Evaluate one chunk's univariate Lagrange basis by streaming over every
fixed-width chunk code. -/
def chunkBasisValue [Field K] [Fintype K]
    (codebook : Codebook K chunkBits)
    (selected : Chunk chunkBits) (point : K) : K :=
  productRange
    (fun code =>
      lagrangeFactorValue codebook selected
        (chunkOfCode chunkBits code) point)
    (2 ^ chunkBits)

/-- Evaluate a grouped tensor-product basis weight over an explicit
coordinate order. -/
def basisValue [Field K] [Fintype K]
    (encoding : σ ≃ Fin coordinateCount)
    (codebook : Codebook K chunkBits)
    (assignment : σ → Chunk chunkBits) (point : σ → K) : K :=
  ((BooleanExtension.Evaluation.coordinates encoding).map fun coordinate =>
    chunkBasisValue codebook
      (assignment coordinate) (point coordinate)).prod

/-- Evaluate a grouped Lagrange extension without constructing its
`MvPolynomial` certificate or the assignment list. -/
def evaluate [Field K] [Fintype K]
    (encoding : σ ≃ Fin coordinateCount)
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K) (point : σ → K) : K :=
  BooleanExtension.Evaluation.sumRange
    (fun code =>
      let assignment :=
        chunkAssignmentOfCode encoding chunkBits code
      f assignment *
        basisValue encoding codebook assignment point)
    (2 ^ (coordinateCount * chunkBits))

/-- Evaluate all output chunks of a grouped Boolean node using the streaming
extension evaluator. -/
def evaluateNode [Field K] [Fintype K]
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin chunkCount → K) :
    Fin chunkCount → K :=
  fun outputChunk =>
    evaluate finProdFinEquiv codebook
      (fun assignment =>
        packedNodeFunction codebook layout combine
          assignment outputChunk)
      (fun input => args input.1 input.2)

end Evaluation

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
