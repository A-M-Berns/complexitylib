/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Defs
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.LinearAlgebra.Lagrange

/-!
# Grouped low-degree extensions

The paper-sharp Cook--Mertz representation groups several Boolean bits into
one element of a finite field. A value of `b` bits is then stored
in `t = ⌈b / chunkBits⌉` field coordinates instead of `b` field coordinates.

This file separates the two assumptions needed by that construction:

* `Codebook K chunkBits` injects one Boolean chunk into a finite field `K`;
* `Layout b chunkBits chunkCount` gives a row-major packing whose capacity
  covers `b` bits and has less than one chunk of slack.

Lagrange interpolation is indexed by chunks themselves, so the finite domain
is explicit and no arbitrary enumeration of a field subset is hidden.

## Main definitions

* `Chunk` -- one fixed-width Boolean chunk
* `Codebook` -- a finite-field chunk injection
* `Layout.pack` / `Layout.unpack` -- padded grouping and recovery
* `basis` / `extension` -- Lagrange extension on a chunk-valued cube
* `nodePolynomials` -- grouped coordinate polynomials for a Boolean node
* `groupedRegisterBitBudget` -- exact bit budget of the catalytic bank
-/

open scoped BigOperators

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

/-- One chunk of `chunkBits` Boolean bits. -/
abbrev Chunk (chunkBits : ℕ) :=
  Fin chunkBits → Bool

/-- Injection of Boolean chunks into a finite field. -/
structure Codebook (K : Type*) [Field K] [Fintype K]
    (chunkBits : ℕ) where
  /-- Distinct Boolean chunks have distinct field encodings. -/
  encode : Chunk chunkBits ↪ K

namespace Codebook

variable {K : Type*} [Field K] [Fintype K] {chunkBits : ℕ}

/-- The explicitly represented interpolation domain inside `K`. -/
noncomputable def domain (codebook : Codebook K chunkBits) : Finset K := by
  classical
  exact Finset.univ.image codebook.encode

/-- Choose a chunk codebook from a field-cardinality lower bound.

This is certificate-side and noncomputable. A later machine implementation
must supply an executable finite-field representation and encoding. -/
noncomputable def ofCardLE
    (hcard : 2 ^ chunkBits ≤ Fintype.card K) :
    Codebook K chunkBits where
  encode :=
    let source :
        Chunk chunkBits ≃ Fin (Fintype.card (Chunk chunkBits)) :=
      Fintype.equivFin _
    let target : K ≃ Fin (Fintype.card K) :=
      Fintype.equivFin _
    ⟨fun value =>
        target.symm
          (Fin.castLE (by simpa using hcard) (source value)),
      by
        intro first second heq
        apply source.injective
        apply Fin.castLE_injective
        exact target.symm.injective heq⟩

end Codebook

/-- A row-major grouping of `b` bits into `chunkCount` chunks.

`covers` makes unpacking total. `tight` records that fewer than one full
chunk of capacity is unused; it is the arithmetic fact needed for the
register-bit reduction. -/
structure Layout (b chunkBits chunkCount : ℕ) where
  /-- Chunks are nonempty. -/
  chunkBits_pos : 0 < chunkBits
  /-- The chunk array has enough slots for all `b` bits. -/
  covers : b ≤ chunkCount * chunkBits
  /-- Padding consumes at most one extra chunk. -/
  tight : chunkCount * chunkBits ≤ b + chunkBits

namespace Layout

variable {b chunkBits chunkCount : ℕ}

/-- Pack a bit vector into row-major chunks, padding unused trailing slots
with `false`. -/
def pack (bits : Fin b → Bool) :
    Fin chunkCount → Chunk chunkBits :=
  fun chunk offset =>
    if h : chunk.val * chunkBits + offset.val < b then
      bits ⟨chunk.val * chunkBits + offset.val, h⟩
    else
      false

/-- Recover the `b` meaningful bits from a chunk array. -/
def unpack (layout : Layout b chunkBits chunkCount)
    (chunks : Fin chunkCount → Chunk chunkBits) : Fin b → Bool :=
  fun position =>
    chunks
      ⟨position.val / chunkBits, by
        apply Nat.div_lt_of_lt_mul
        calc
          position.val < b := position.isLt
          _ ≤ chunkCount * chunkBits := layout.covers
          _ = chunkBits * chunkCount := Nat.mul_comm _ _⟩
      ⟨position.val % chunkBits,
        Nat.mod_lt _ layout.chunkBits_pos⟩

/-- Canonical tight row-major grouping by ceiling division. -/
theorem canonical (b chunkBits : ℕ) (hpositive : 0 < chunkBits) :
    Layout b chunkBits (b ⌈/⌉ chunkBits) where
  chunkBits_pos := hpositive
  covers := by
    have h :=
      (ceilDiv_le_iff_le_mul hpositive).mp
        (le_refl (b ⌈/⌉ chunkBits))
    simpa [Nat.mul_comm] using h
  tight := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact
      (Nat.div_mul_le_self (b + chunkBits - 1) chunkBits).trans
        (Nat.sub_le _ _)

end Layout

variable {K : Type*} [Field K] [Fintype K]
  {chunkBits b chunkCount d : ℕ}

/-- Encode a packed Boolean vector coordinatewise in the field. -/
def encodeVector (codebook : Codebook K chunkBits)
    (bits : Fin b → Bool) : Fin chunkCount → K :=
  fun chunk => codebook.encode (Layout.pack bits chunk)

/-- Lift the univariate Lagrange polynomial for one chunk to one multivariate
coordinate. -/
noncomputable def basisFactor
    (codebook : Codebook K chunkBits) (value : Chunk chunkBits)
    (coordinate : σ) : MvPolynomial σ K :=
  Polynomial.toMvPolynomial coordinate
    (Lagrange.basis Finset.univ codebook.encode value)

/-- Product Lagrange basis selecting one chunk-valued assignment. -/
noncomputable def basis [Fintype σ]
    (codebook : Codebook K chunkBits)
    (assignment : σ → Chunk chunkBits) : MvPolynomial σ K :=
  ∏ coordinate : σ,
    basisFactor codebook (assignment coordinate) coordinate

/-- Lagrange extension of a field-valued function on a chunk cube. -/
noncomputable def extension [Fintype σ]
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K) : MvPolynomial σ K := by
  classical
  exact ∑ assignment : σ → Chunk chunkBits,
    MvPolynomial.C (f assignment) * basis codebook assignment

/-- Interpret grouped inputs as `d` Boolean vectors of length `b`. -/
def unpackChildren
    (layout : Layout b chunkBits chunkCount)
    (assignment : Fin d × Fin chunkCount → Chunk chunkBits) :
    Fin d → Fin b → Bool :=
  fun child =>
    layout.unpack fun chunk => assignment (child, chunk)

/-- Field encoding of one grouped output chunk of a Boolean node. -/
def packedNodeFunction
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (assignment : Fin d × Fin chunkCount → Chunk chunkBits)
    (outputChunk : Fin chunkCount) : K :=
  codebook.encode
    (Layout.pack (combine (unpackChildren layout assignment)) outputChunk)

/-- One grouped Lagrange-extension polynomial per output chunk of a Boolean
node function. -/
noncomputable def nodePolynomials
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool) :
    Fin chunkCount →
      MvPolynomial (Fin d × Fin chunkCount) K :=
  fun outputChunk =>
    extension codebook fun assignment =>
      packedNodeFunction codebook layout combine assignment outputChunk

/-- Exact catalytic-register bit budget with `chunkCount` field coordinates
per value and `fieldBits` bits per encoded field element. -/
def groupedRegisterBitBudget
    (d chunkCount fieldBits : ℕ) : ℕ :=
  (d + 1) * chunkCount * fieldBits

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
