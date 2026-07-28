/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.PrimeField
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# Correctness internals for runtime prime-field arithmetic

The proofs connect natural-residue execution with the certificate-side
`ZMod p` field and establish range, bit-width, and streamed-traversal
invariants.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Runtime

namespace Internal

theorem normalize_lt_internal {p value : ℕ} (hp : 0 < p) :
    normalize p value < p := by
  exact Nat.mod_lt value hp

theorem addInput_lt_two_mul_internal
    {p first second : ℕ} (hp : 0 < p) :
    addInput p first second < 2 * p := by
  have hfirst := normalize_lt_internal (value := first) hp
  have hsecond := normalize_lt_internal (value := second) hp
  unfold addInput
  omega

theorem add_lt_internal {p first second : ℕ} (hp : 0 < p) :
    add p first second < p := by
  unfold add normalize
  exact Nat.mod_lt _ hp

theorem subtraction_no_underflow_internal
    {p first second : ℕ} (hp : 0 < p) :
    normalize p second ≤ normalize p first + p := by
  have hsecond := Nat.mod_lt second hp
  simp only [normalize]
  omega

theorem subInput_lt_two_mul_internal
    {p first second : ℕ} (hp : 0 < p) :
    subInput p first second < 2 * p := by
  have hfirst := normalize_lt_internal (value := first) hp
  unfold subInput
  omega

theorem sub_lt_internal {p first second : ℕ} (hp : 0 < p) :
    sub p first second < p := by
  unfold sub normalize
  exact Nat.mod_lt _ hp

theorem mulInput_lt_sq_internal
    {p first second : ℕ} (hp : 0 < p) :
    mulInput p first second < p * p := by
  have hfirst := normalize_lt_internal (value := first) hp
  have hsecond := normalize_lt_internal (value := second) hp
  unfold mulInput
  calc
    normalize p first * normalize p second ≤
        p * normalize p second :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hfirst)
    _ < p * p :=
      (Nat.mul_lt_mul_left hp).2 hsecond

theorem mul_lt_internal {p first second : ℕ} (hp : 0 < p) :
    mul p first second < p := by
  unfold mul normalize
  exact Nat.mod_lt _ hp

theorem powLoop_lt_internal {p base fuel accumulator : ℕ}
    (hp : 0 < p) (haccumulator : accumulator < p) :
    powLoop p base fuel accumulator < p := by
  induction fuel generalizing accumulator with
  | zero =>
      simpa [powLoop] using haccumulator
  | succ fuel ih =>
      rw [powLoop]
      exact ih (mul_lt_internal hp)

theorem pow_lt_internal {p base exponent : ℕ} (hp : 0 < p) :
    pow p base exponent < p := by
  unfold pow
  exact powLoop_lt_internal hp (normalize_lt_internal hp)

theorem inverse_lt_internal {p value : ℕ} (hp : 0 < p) :
    inverse p value < p := by
  unfold inverse
  split
  · exact hp
  · exact pow_lt_internal hp

theorem normalize_size_le_internal {p value : ℕ} (hp : 0 < p) :
    (normalize p value).size ≤ bitWidth p := by
  unfold bitWidth
  exact Nat.size_le_size (Nat.le_of_lt (normalize_lt_internal hp))

theorem two_mul_lt_pow_size_add_one_internal {p : ℕ} :
    2 * p < 2 ^ (p.size + 1) := by
  calc
    2 * p < 2 * 2 ^ p.size :=
      (Nat.mul_lt_mul_left (by omega)).2 (Nat.lt_size_self p)
    _ = 2 ^ (p.size + 1) := by
      rw [Nat.pow_succ]
      ring

theorem sq_lt_pow_two_mul_size_internal {p : ℕ} (hp : 0 < p) :
    p * p < 2 ^ (2 * p.size) := by
  have hsize := Nat.lt_size_self p
  calc
    p * p < 2 ^ p.size * p :=
      (Nat.mul_lt_mul_right hp).2 hsize
    _ < 2 ^ p.size * 2 ^ p.size :=
      (Nat.mul_lt_mul_left (by positivity)).2 hsize
    _ = 2 ^ (2 * p.size) := by
      rw [← Nat.pow_add]
      congr 1
      omega

theorem addInput_size_le_internal
    {p first second : ℕ} (hp : 0 < p) :
    (addInput p first second).size ≤ linearScratchBitWidth p := by
  unfold linearScratchBitWidth bitWidth
  apply Nat.size_le.mpr
  exact (addInput_lt_two_mul_internal hp).trans
    two_mul_lt_pow_size_add_one_internal

theorem subInput_size_le_internal
    {p first second : ℕ} (hp : 0 < p) :
    (subInput p first second).size ≤ linearScratchBitWidth p := by
  unfold linearScratchBitWidth bitWidth
  apply Nat.size_le.mpr
  exact (subInput_lt_two_mul_internal hp).trans
    two_mul_lt_pow_size_add_one_internal

theorem mulInput_size_le_internal
    {p first second : ℕ} (hp : 0 < p) :
    (mulInput p first second).size ≤
      multiplicationScratchBitWidth p := by
  unfold multiplicationScratchBitWidth bitWidth
  apply Nat.size_le.mpr
  exact (mulInput_lt_sq_internal hp).trans
    (sq_lt_pow_two_mul_size_internal hp)

theorem add_size_le_internal {p first second : ℕ} (hp : 0 < p) :
    (add p first second).size ≤ bitWidth p := by
  unfold bitWidth
  exact Nat.size_le_size (Nat.le_of_lt (add_lt_internal hp))

theorem sub_size_le_internal {p first second : ℕ} (hp : 0 < p) :
    (sub p first second).size ≤ bitWidth p := by
  unfold bitWidth
  exact Nat.size_le_size (Nat.le_of_lt (sub_lt_internal hp))

theorem mul_size_le_internal {p first second : ℕ} (hp : 0 < p) :
    (mul p first second).size ≤ bitWidth p := by
  unfold bitWidth
  exact Nat.size_le_size (Nat.le_of_lt (mul_lt_internal hp))

theorem pow_size_le_internal {p base exponent : ℕ} (hp : 0 < p) :
    (pow p base exponent).size ≤ bitWidth p := by
  unfold bitWidth
  exact Nat.size_le_size (Nat.le_of_lt (pow_lt_internal hp))

theorem inverse_size_le_internal {p value : ℕ} (hp : 0 < p) :
    (inverse p value).size ≤ bitWidth p := by
  unfold bitWidth
  exact Nat.size_le_size (Nat.le_of_lt (inverse_lt_internal hp))

theorem coe_normalize_internal (p value : ℕ) :
    ((normalize p value : ℕ) : ZMod p) = (value : ZMod p) := by
  exact (CharP.natCast_eq_natCast_mod (ZMod p) p value).symm

theorem coe_add_internal (p first second : ℕ) :
    ((add p first second : ℕ) : ZMod p) =
      (first : ZMod p) + (second : ZMod p) := by
  unfold add addInput
  rw [coe_normalize_internal, Nat.cast_add,
    coe_normalize_internal, coe_normalize_internal]

theorem coe_sub_internal (p first second : ℕ) [Fact p.Prime] :
    ((sub p first second : ℕ) : ZMod p) =
      (first : ZMod p) - (second : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hle :
      normalize p second ≤ normalize p first + p :=
    subtraction_no_underflow_internal hp
  unfold sub subInput
  rw [coe_normalize_internal, Nat.cast_sub hle, Nat.cast_add,
    coe_normalize_internal, coe_normalize_internal]
  simp

theorem coe_mul_internal (p first second : ℕ) :
    ((mul p first second : ℕ) : ZMod p) =
      (first : ZMod p) * (second : ZMod p) := by
  unfold mul mulInput
  rw [coe_normalize_internal, Nat.cast_mul,
    coe_normalize_internal, coe_normalize_internal]

theorem coe_powLoop_internal
    (p base fuel accumulator : ℕ) :
    ((powLoop p base fuel accumulator : ℕ) : ZMod p) =
      (accumulator : ZMod p) * (base : ZMod p) ^ fuel := by
  induction fuel generalizing accumulator with
  | zero =>
      simp [powLoop]
  | succ fuel ih =>
      rw [powLoop, ih, coe_mul_internal]
      simp only [pow_succ]
      ring

theorem coe_pow_internal (p base exponent : ℕ) :
    ((pow p base exponent : ℕ) : ZMod p) =
      (base : ZMod p) ^ exponent := by
  unfold pow
  rw [coe_powLoop_internal, coe_normalize_internal]
  simp

theorem coe_inverse_internal (p value : ℕ) [Fact p.Prime] :
    ((inverse p value : ℕ) : ZMod p) =
      (value : ZMod p)⁻¹ := by
  by_cases hzero : normalize p value = 0
  · have hvalue : (value : ZMod p) = 0 := by
      rw [← coe_normalize_internal, hzero]
      simp
    simp [inverse, hzero, hvalue]
  · have hvalue : (value : ZMod p) ≠ 0 := by
      intro hcast
      have hdvd : p ∣ value :=
        (ZMod.natCast_eq_zero_iff value p).mp hcast
      exact hzero (Nat.mod_eq_zero_of_dvd hdvd)
    rw [inverse, if_neg hzero, coe_pow_internal]
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    calc
      (value : ZMod p) * (value : ZMod p) ^ (p - 2) =
          (value : ZMod p) ^ (p - 2 + 1) := by
        rw [pow_succ, mul_comm]
      _ = (value : ZMod p) ^ (p - 1) := by
        have hp := (Fact.out : p.Prime).two_le
        congr 1
        omega
      _ = 1 :=
        ZMod.pow_card_sub_one_eq_one hvalue

theorem foldNonzeroLoop_eq_foldl_range_internal
    {State : Type*} (step : State → ℕ → State)
    (fuel candidate : ℕ) (state : State) :
    foldNonzeroLoop step fuel candidate state =
      (List.range' candidate fuel).foldl step state := by
  induction fuel generalizing candidate state with
  | zero =>
      simp [foldNonzeroLoop]
  | succ fuel ih =>
      rw [foldNonzeroLoop, List.range'_succ]
      simp only [List.foldl_cons]
      exact ih (candidate + 1) (step state candidate)

theorem foldNonzero_eq_foldl_range_internal
    {State : Type*} (p : ℕ) (step : State → ℕ → State)
    (initial : State) :
    foldNonzero p step initial =
      (List.range' 1 (p - 1)).foldl step initial := by
  unfold foldNonzero
  exact foldNonzeroLoop_eq_foldl_range_internal
    step (p - 1) 1 initial

theorem mem_nonzero_range_iff_internal {p residue : ℕ} :
    residue ∈ List.range' 1 (p - 1) ↔
      0 < residue ∧ residue < p := by
  rw [List.mem_range']
  constructor
  · rintro ⟨index, hindex, rfl⟩
    simp only [one_mul]
    omega
  · rintro ⟨hpositive, hlt⟩
    refine ⟨residue - 1, by omega, by omega⟩

theorem nonzero_range_nodup_internal (p : ℕ) :
    (List.range' 1 (p - 1)).Nodup := by
  exact List.nodup_range'

theorem nonzero_range_length_internal (p : ℕ) :
    (List.range' 1 (p - 1)).length = p - 1 := by
  exact List.length_range'

theorem coe_ne_zero_of_mem_nonzero_range_internal
    {p residue : ℕ} [Fact p.Prime]
    (hresidue : residue ∈ List.range' 1 (p - 1)) :
    (residue : ZMod p) ≠ 0 := by
  have hrange :=
    mem_nonzero_range_iff_internal.mp hresidue
  intro hzero
  have hdvd : p ∣ residue :=
    (ZMod.natCast_eq_zero_iff residue p).mp hzero
  exact Nat.not_dvd_of_pos_of_lt hrange.1 hrange.2 hdvd

theorem exists_mem_nonzero_range_coe_eq_internal
    (p : ℕ) [Fact p.Prime] (unit : (ZMod p)ˣ) :
    ∃ residue ∈ List.range' 1 (p - 1),
      (residue : ZMod p) = (unit : ZMod p) := by
  let residue := (unit : ZMod p).val
  have hlt : residue < p :=
    ZMod.val_lt (unit : ZMod p)
  have hcoe : (residue : ZMod p) = (unit : ZMod p) :=
    ZMod.natCast_zmod_val (unit : ZMod p)
  have hpositive : 0 < residue := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply unit.ne_zero
    rw [← hcoe, hzero]
    simp
  exact
    ⟨residue,
      mem_nonzero_range_iff_internal.mpr ⟨hpositive, hlt⟩,
      hcoe⟩

end Internal

end Runtime

end PrimeField

end CookMertz

end TreeEval

end Complexity
