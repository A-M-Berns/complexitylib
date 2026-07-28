/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Defs
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Proof internals for grouped low-degree extensions

This file proves row-major packing correctness, exact interpolation on the
encoded chunk cube, the grouped total-degree bound, and the finite arithmetic
behind the catalytic register-bit reduction.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace GroupedExtension

namespace Internal

open scoped BigOperators

theorem chunk_card_internal (chunkBits : ℕ) :
    Fintype.card (Chunk chunkBits) = 2 ^ chunkBits := by
  simp [Chunk]

theorem codebook_mem_domain_internal
    {K : Type*} [Field K] [Fintype K] {chunkBits : ℕ}
    (codebook : Codebook K chunkBits) (value : Chunk chunkBits) :
    codebook.encode value ∈ codebook.domain := by
  classical
  simp [Codebook.domain]

theorem codebook_domain_card_internal
    {K : Type*} [Field K] [Fintype K] {chunkBits : ℕ}
    (codebook : Codebook K chunkBits) :
    codebook.domain.card = 2 ^ chunkBits := by
  classical
  rw [Codebook.domain,
    Finset.card_image_of_injective _ codebook.encode.injective]
  simp

theorem codebook_card_le_internal
    {K : Type*} [Field K] [Fintype K] {chunkBits : ℕ}
    (codebook : Codebook K chunkBits) :
    2 ^ chunkBits ≤ Fintype.card K := by
  rw [← chunk_card_internal]
  exact Fintype.card_le_of_injective
    codebook.encode codebook.encode.injective

theorem layout_unpack_pack_internal
    {b chunkBits chunkCount : ℕ}
    (layout : Layout b chunkBits chunkCount)
    (bits : Fin b → Bool) :
    layout.unpack (Layout.pack bits) = bits := by
  funext position
  simp only [Layout.unpack, Layout.pack]
  have hindex :
      position.val / chunkBits * chunkBits +
          position.val % chunkBits =
        position.val := by
    rw [Nat.mul_comm (position.val / chunkBits) chunkBits,
      Nat.div_add_mod]
  simp [hindex, position.isLt]

variable {K : Type*} [Field K] [Fintype K]
  {chunkBits b chunkCount d : ℕ}

private theorem codebook_injectiveOn
    (codebook : Codebook K chunkBits) :
    Set.InjOn codebook.encode (Finset.univ : Finset (Chunk chunkBits)) := by
  intro first _ second _ heq
  exact codebook.encode.injective heq

theorem eval_basisFactor_internal
    (codebook : Codebook K chunkBits)
    (value : Chunk chunkBits) (coordinate : σ)
    (point : σ → Chunk chunkBits) :
    MvPolynomial.eval (fun i => codebook.encode (point i))
        (basisFactor codebook value coordinate) =
      if value = point coordinate then 1 else 0 := by
  rw [basisFactor, MvPolynomial.eval_toMvPolynomial]
  by_cases hvalue : value = point coordinate
  · subst value
    rw [if_pos rfl]
    exact Lagrange.eval_basis_self
      (codebook_injectiveOn codebook) (Finset.mem_univ _)
  · rw [if_neg hvalue]
    exact Lagrange.eval_basis_of_ne hvalue (Finset.mem_univ _)

theorem eval_basis_internal [Fintype σ]
    (codebook : Codebook K chunkBits)
    (assignment point : σ → Chunk chunkBits) :
    MvPolynomial.eval (fun i => codebook.encode (point i))
        (basis codebook assignment) =
      if assignment = point then 1 else 0 := by
  classical
  by_cases h : assignment = point
  · subst point
    rw [if_pos rfl, basis, MvPolynomial.eval_prod]
    apply Finset.prod_eq_one
    intro coordinate _
    simpa using
      eval_basisFactor_internal
        codebook (assignment coordinate) coordinate assignment
  · rw [if_neg h, basis, MvPolynomial.eval_prod]
    obtain ⟨coordinate, hcoordinate⟩ :
        ∃ coordinate, assignment coordinate ≠ point coordinate := by
      by_contra hnone
      push Not at hnone
      exact h (funext hnone)
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    rw [eval_basisFactor_internal, if_neg hcoordinate]

theorem eval_extension_internal [Fintype σ]
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K)
    (point : σ → Chunk chunkBits) :
    MvPolynomial.eval (fun i => codebook.encode (point i))
        (extension codebook f) =
      f point := by
  classical
  rw [extension, MvPolynomial.eval_sum]
  simp [eval_basis_internal]

omit [Fintype K] in
private theorem toMvPolynomial_basisDivisor_totalDegree_le
    (x y : K) (coordinate : σ) :
    ((Polynomial.toMvPolynomial coordinate)
      (Lagrange.basisDivisor x y)).totalDegree ≤ 1 := by
  rw [Lagrange.basisDivisor]
  simp only [map_mul, map_sub, Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X]
  calc
    (MvPolynomial.C (x - y)⁻¹ *
        (MvPolynomial.X coordinate - MvPolynomial.C y) :
        MvPolynomial σ K).totalDegree ≤
        (MvPolynomial.C (x - y)⁻¹ :
          MvPolynomial σ K).totalDegree +
          (MvPolynomial.X coordinate - MvPolynomial.C y :
            MvPolynomial σ K).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 1 := Nat.add_le_add (by simp) (by
      calc
        (MvPolynomial.X coordinate - MvPolynomial.C y :
            MvPolynomial σ K).totalDegree ≤
            max
              (MvPolynomial.X coordinate :
                MvPolynomial σ K).totalDegree
              (MvPolynomial.C y :
                MvPolynomial σ K).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
        _ ≤ 1 := by simp)
    _ = 1 := rfl

private theorem basisFactor_totalDegree_le
    (codebook : Codebook K chunkBits)
    (value : Chunk chunkBits) (coordinate : σ) :
    (basisFactor codebook value coordinate).totalDegree ≤
      2 ^ chunkBits - 1 := by
  classical
  rw [basisFactor, Lagrange.basis, map_prod]
  calc
    (∏ other ∈ Finset.univ.erase value,
        (Polynomial.toMvPolynomial coordinate)
          (Lagrange.basisDivisor
            (codebook.encode value)
            (codebook.encode other))).totalDegree ≤
        ∑ other ∈ Finset.univ.erase value,
          ((Polynomial.toMvPolynomial coordinate)
            (Lagrange.basisDivisor
              (codebook.encode value)
              (codebook.encode other))).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _other ∈ Finset.univ.erase value, 1 := by
      apply Finset.sum_le_sum
      intro other _
      exact toMvPolynomial_basisDivisor_totalDegree_le _ _ _
    _ = 2 ^ chunkBits - 1 := by simp [Chunk]

theorem basis_totalDegree_le_internal [Fintype σ]
    (codebook : Codebook K chunkBits)
    (assignment : σ → Chunk chunkBits) :
    (basis codebook assignment).totalDegree ≤
      Fintype.card σ * (2 ^ chunkBits - 1) := by
  classical
  rw [basis]
  calc
    (∏ coordinate : σ,
        basisFactor codebook
          (assignment coordinate) coordinate).totalDegree ≤
        ∑ coordinate ∈ Finset.univ,
          (basisFactor codebook
            (assignment coordinate) coordinate).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _coordinate ∈ Finset.univ,
          (2 ^ chunkBits - 1) := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact basisFactor_totalDegree_le
        codebook (assignment coordinate) coordinate
    _ = Fintype.card σ * (2 ^ chunkBits - 1) := by simp

theorem extension_totalDegree_le_internal [Fintype σ]
    (codebook : Codebook K chunkBits)
    (f : (σ → Chunk chunkBits) → K) :
    (extension codebook f).totalDegree ≤
      Fintype.card σ * (2 ^ chunkBits - 1) := by
  classical
  rw [extension]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro assignment _
  calc
    (MvPolynomial.C (f assignment) *
        basis codebook assignment).totalDegree ≤
        (MvPolynomial.C (f assignment) :
          MvPolynomial σ K).totalDegree +
          (basis codebook assignment).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ Fintype.card σ * (2 ^ chunkBits - 1) := by
      simpa using
        basis_totalDegree_le_internal codebook assignment

theorem polynomialNode_nodePolynomials_internal
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (args : Fin d → Fin b → Bool) :
    polynomialNode (nodePolynomials codebook layout combine)
        (fun child chunk => encodeVector codebook (args child) chunk) =
      encodeVector codebook (combine args) := by
  funext outputChunk
  change
    MvPolynomial.eval
        (fun input =>
          codebook.encode
            (Layout.pack (args input.1) input.2))
        (extension codebook fun assignment =>
          packedNodeFunction
            codebook layout combine assignment outputChunk) =
      codebook.encode
        (Layout.pack (combine args) outputChunk)
  rw [eval_extension_internal]
  unfold packedNodeFunction
  apply congrArg codebook.encode
  apply congrArg (fun bits => Layout.pack bits outputChunk)
  apply congrArg combine
  funext child
  exact layout_unpack_pack_internal layout (args child)

theorem nodePolynomials_totalDegree_le_internal
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (outputChunk : Fin chunkCount) :
    (nodePolynomials codebook layout combine outputChunk).totalDegree ≤
      d * chunkCount * (2 ^ chunkBits - 1) := by
  simpa [nodePolynomials] using
    extension_totalDegree_le_internal
      (σ := Fin d × Fin chunkCount) codebook
      (fun assignment =>
        packedNodeFunction
          codebook layout combine assignment outputChunk)

theorem groupedDegree_lt_squareCard_internal
    (d chunkCount chunkBits fieldCard : ℕ)
    (hpositive : 0 < chunkBits)
    (hinputs : d * chunkCount ≤ 2 ^ chunkBits)
    (hcard : fieldCard = (2 ^ chunkBits) ^ 2) :
    d * chunkCount * (2 ^ chunkBits - 1) <
      fieldCard - 1 := by
  let domainCard := 2 ^ chunkBits
  have hdomain : 2 ≤ domainCard := by
    have : 1 < domainCard := by
      exact Nat.one_lt_pow
        (Nat.ne_of_gt hpositive) (by omega)
    omega
  have hbound :
      d * chunkCount * (domainCard - 1) ≤
        domainCard * (domainCard - 1) :=
    Nat.mul_le_mul_right (domainCard - 1)
      (by simpa [domainCard] using hinputs)
  have hstrict :
      domainCard * (domainCard - 1) <
        domainCard * domainCard - 1 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    exact Nat.sub_lt_sub_left
      (one_lt_mul (by omega) (by omega)) (by omega)
  have hcard' : fieldCard = domainCard * domainCard := by
    simpa [domainCard, pow_two] using hcard
  simpa [domainCard, hcard'] using hbound.trans_lt hstrict

theorem nodePolynomials_totalDegree_lt_card_sub_one_internal
    (codebook : Codebook K chunkBits)
    (layout : Layout b chunkBits chunkCount)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (outputChunk : Fin chunkCount)
    (hpositive : 0 < chunkBits)
    (hinputs : d * chunkCount ≤ 2 ^ chunkBits)
    (hcard : Fintype.card K = (2 ^ chunkBits) ^ 2) :
    (nodePolynomials codebook layout combine outputChunk).totalDegree <
      Fintype.card K - 1 :=
  (nodePolynomials_totalDegree_le_internal
      codebook layout combine outputChunk).trans_lt
    (groupedDegree_lt_squareCard_internal
      d chunkCount chunkBits (Fintype.card K)
      hpositive hinputs hcard)

theorem groupedRegisterBitBudget_le_internal
    (layout : Layout b chunkBits chunkCount)
    (d fieldBits factor : ℕ)
    (hfield : fieldBits ≤ factor * chunkBits) :
    groupedRegisterBitBudget d chunkCount fieldBits ≤
      (d + 1) * factor * (b + chunkBits) := by
  calc
    groupedRegisterBitBudget d chunkCount fieldBits =
        (d + 1) * chunkCount * fieldBits := rfl
    _ ≤ (d + 1) * chunkCount * (factor * chunkBits) :=
      Nat.mul_le_mul_left ((d + 1) * chunkCount) hfield
    _ = (d + 1) * factor * (chunkCount * chunkBits) := by
      ac_rfl
    _ ≤ (d + 1) * factor * (b + chunkBits) :=
      Nat.mul_le_mul_left ((d + 1) * factor) layout.tight

end Internal

end GroupedExtension

end CookMertz

end TreeEval

end Complexity
