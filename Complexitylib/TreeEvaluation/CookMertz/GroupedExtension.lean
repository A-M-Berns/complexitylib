/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Internal

/-!
# Grouped low-degree extensions for Cook--Mertz evaluation

This module exposes the certificate-side grouped representation from
Appendix A of Williams's simulation. Boolean chunks inject into an explicit
subset of a finite field. Row-major packing stores a
`b`-bit value in `⌈b / chunkBits⌉` field coordinates. Tensor-product Lagrange
interpolation agrees with every encoded chunk assignment and has total degree
at most

`numberOfInputs * (2 ^ chunkBits - 1)`.

For a `d`-input grouped node this becomes

`d * chunkCount * (2 ^ chunkBits - 1)`.

The register arithmetic is also explicit. If one field element uses at most
twice `chunkBits` bits and `chunkBits ≤ b`, all `d + 1` catalytic registers
use at most `4 * (d + 1) * b` bits. This proves the paper-sharp order for the
catalytic bank under stated representation hypotheses; it is not yet an
all-prefix Turing-machine workspace theorem. A concrete executable
finite field, codebook, node-function evaluator, and encoded
recursion frame remain separate obligations.

## Main theorems

* `Layout.unpack_pack` -- padded grouping recovers every meaningful bit
* `eval_extension` -- exact agreement on the encoded chunk cube
* `extension_totalDegree_le` -- tensor-product Lagrange degree bound
* `polynomialNode_nodePolynomials` -- grouped Boolean-node correctness
* `nodePolynomials_totalDegree_le` -- grouped node degree bound
* `nodePolynomials_totalDegree_lt_card_sub_one` -- square-field Cook--Mertz bound
* `groupedRegisterBitBudget_le_four_mul` -- conditional `4(d+1)b` bank bound
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

/-- There are exactly `2 ^ chunkBits` Boolean chunks. -/
theorem chunk_card (chunkBits : ℕ) :
    Fintype.card (Chunk chunkBits) = 2 ^ chunkBits :=
  Internal.chunk_card_internal chunkBits

namespace Codebook

variable {K : Type*} [Field K] [Fintype K] {chunkBits : ℕ}

/-- Every encoded chunk belongs to the explicit interpolation domain. -/
theorem mem_domain (codebook : Codebook K chunkBits)
    (value : Chunk chunkBits) :
    codebook.encode value ∈ codebook.domain :=
  Internal.codebook_mem_domain_internal codebook value

/-- The explicit interpolation domain has one point per Boolean chunk. -/
@[simp] theorem domain_card (codebook : Codebook K chunkBits) :
    codebook.domain.card = 2 ^ chunkBits :=
  Internal.codebook_domain_card_internal codebook

/-- A chunk codebook certifies that the field has at least `2 ^ chunkBits`
elements. -/
theorem card_le (codebook : Codebook K chunkBits) :
    2 ^ chunkBits ≤ Fintype.card K :=
  Internal.codebook_card_le_internal codebook

end Codebook

namespace Layout

/-- Row-major packing followed by unpacking recovers every meaningful bit;
only trailing padding is discarded. -/
theorem unpack_pack {b chunkBits chunkCount : ℕ}
    (layout : Layout b chunkBits chunkCount)
    (bits : Fin b → Bool) :
    layout.unpack (Layout.pack bits) = bits :=
  Internal.layout_unpack_pack_internal layout bits

end Layout

variable {K : Type*} [Field K] [Fintype K]
  {chunkBits b chunkCount d : ℕ}

/-- One lifted coordinate factor evaluates to its Kronecker delta on encoded
chunks. -/
theorem eval_basisFactor
    (codebook : Codebook K chunkBits)
    (value : Chunk chunkBits) (coordinate : σ)
    (point : σ → Chunk chunkBits) :
    MvPolynomial.eval (fun i => codebook.encode (point i))
        (basisFactor codebook value coordinate) =
      if value = point coordinate then 1 else 0 :=
  Internal.eval_basisFactor_internal
    codebook value coordinate point

/-- The tensor-product Lagrange basis selects exactly one encoded chunk
assignment. -/
theorem eval_basis [Fintype σ]
    (codebook : Codebook K chunkBits)
    (assignment point : σ → Chunk chunkBits) :
    MvPolynomial.eval (fun i => codebook.encode (point i))
        (basis codebook assignment) =
      if assignment = point then 1 else 0 :=
  Internal.eval_basis_internal codebook assignment point

/-- The grouped Lagrange extension agrees with the original function at every
encoded chunk assignment. -/
theorem eval_extension [Fintype σ]
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K)
    (point : σ → Chunk chunkBits) :
    MvPolynomial.eval (fun i => codebook.encode (point i))
        (extension codebook f) =
      f point :=
  Internal.eval_extension_internal codebook f point

/-- A grouped basis polynomial has total degree at most the number of input
coordinates times `2 ^ chunkBits - 1`. -/
theorem basis_totalDegree_le [Fintype σ]
    (codebook : Codebook K chunkBits)
    (assignment : σ → Chunk chunkBits) :
    (basis codebook assignment).totalDegree ≤
      Fintype.card σ * (2 ^ chunkBits - 1) :=
  Internal.basis_totalDegree_le_internal codebook assignment

/-- Every grouped extension has total degree at most the number of input
coordinates times `2 ^ chunkBits - 1`. -/
theorem extension_totalDegree_le [Fintype σ]
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K) :
    (extension codebook f).totalDegree ≤
      Fintype.card σ * (2 ^ chunkBits - 1) :=
  Internal.extension_totalDegree_le_internal codebook f

/-- The grouped coordinate polynomials compute the packed field encoding of
the original Boolean node on every Boolean input. -/
theorem polynomialNode_nodePolynomials
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    polynomialNode (nodePolynomials codebook layout combine)
        (fun child chunk =>
          encodeVector codebook (args child) chunk) =
      encodeVector codebook (combine args) :=
  Internal.polynomialNode_nodePolynomials_internal
    codebook layout combine args

/-- Each grouped node-coordinate polynomial has the Appendix A total-degree
bound `d * chunkCount * (2 ^ chunkBits - 1)`. -/
theorem nodePolynomials_totalDegree_le
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (outputChunk : Fin chunkCount) :
    (nodePolynomials codebook layout combine outputChunk).totalDegree ≤
      d * chunkCount * (2 ^ chunkBits - 1) :=
  Internal.nodePolynomials_totalDegree_le_internal
    codebook layout combine outputChunk

/-- If the field has square chunk-domain cardinality and the number of input
coordinates is at most the chunk-domain size, every grouped node polynomial
meets Cook--Mertz's strict interpolation degree requirement. -/
theorem nodePolynomials_totalDegree_lt_card_sub_one
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (outputChunk : Fin chunkCount)
    (hpositive : 0 < chunkBits)
    (hinputs : d * chunkCount ≤ 2 ^ chunkBits)
    (hcard : Fintype.card K = (2 ^ chunkBits) ^ 2) :
    (nodePolynomials codebook layout combine outputChunk).totalDegree <
      Fintype.card K - 1 :=
  Internal.nodePolynomials_totalDegree_lt_card_sub_one_internal
    codebook layout combine outputChunk hpositive hinputs hcard

/-- Exact register-bit reduction for a tight layout when field width is at
most `factor` times the Boolean chunk width. -/
theorem groupedRegisterBitBudget_le
    (layout : Layout b chunkBits chunkCount)
    (d fieldBits factor : ℕ)
    (hfield : fieldBits ≤ factor * chunkBits) :
    groupedRegisterBitBudget d chunkCount fieldBits ≤
      (d + 1) * factor * (b + chunkBits) :=
  Internal.groupedRegisterBitBudget_le_internal
    layout d fieldBits factor hfield

/-- If field elements use at most twice the chunk width and one chunk is no
longer than the value, the complete catalytic bank occupies at most
`4 * (d + 1) * b` bits. -/
theorem groupedRegisterBitBudget_le_four_mul
    (layout : Layout b chunkBits chunkCount)
    (d fieldBits : ℕ)
    (hfield : fieldBits ≤ 2 * chunkBits)
    (hchunk : chunkBits ≤ b) :
    groupedRegisterBitBudget d chunkCount fieldBits ≤
      4 * (d + 1) * b := by
  calc
    groupedRegisterBitBudget d chunkCount fieldBits ≤
        (d + 1) * 2 * (b + chunkBits) :=
      groupedRegisterBitBudget_le layout d fieldBits 2 hfield
    _ ≤ (d + 1) * 2 * (b + b) :=
      Nat.mul_le_mul_left ((d + 1) * 2)
        (Nat.add_le_add_left hchunk b)
    _ = 4 * (d + 1) * b := by ring

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
