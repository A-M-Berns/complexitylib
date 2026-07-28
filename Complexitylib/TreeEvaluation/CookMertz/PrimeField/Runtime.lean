/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.Internal

/-!
# Verified runtime prime-field representation

Natural residues provide an executable representation for a prime modulus
available only at runtime. Addition, subtraction, multiplication,
exponentiation, and inversion agree with `ZMod p`; every result is canonical
and fits in `p.size` bits.

Nonzero residues are traversed by a tail-recursive loop that constructs no
list. The finite list `List.range' 1 (p - 1)` appears only in the public
correctness certificate, proving that the stream visits each residue
`1, ..., p - 1` exactly once.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Runtime

/-- Canonicalization returns a residue below a positive modulus. -/
theorem normalize_lt {p value : ℕ} (hp : 0 < p) :
    normalize p value < p :=
  Internal.normalize_lt_internal hp

/-- The pre-reduction sum is below twice the modulus. -/
theorem addInput_lt_two_mul
    {p first second : ℕ} (hp : 0 < p) :
    addInput p first second < 2 * p :=
  Internal.addInput_lt_two_mul_internal hp

/-- Modular addition returns a canonical residue. -/
theorem add_lt {p first second : ℕ} (hp : 0 < p) :
    add p first second < p :=
  Internal.add_lt_internal hp

/-- Normalized subtraction cannot underflow before its final reduction. -/
theorem subtraction_no_underflow
    {p first second : ℕ} (hp : 0 < p) :
    normalize p second ≤ normalize p first + p :=
  Internal.subtraction_no_underflow_internal hp

/-- The pre-reduction natural difference is below twice the modulus. -/
theorem subInput_lt_two_mul
    {p first second : ℕ} (hp : 0 < p) :
    subInput p first second < 2 * p :=
  Internal.subInput_lt_two_mul_internal hp

/-- Modular subtraction returns a canonical residue. -/
theorem sub_lt {p first second : ℕ} (hp : 0 < p) :
    sub p first second < p :=
  Internal.sub_lt_internal hp

/-- The pre-reduction product is below the square of the modulus. -/
theorem mulInput_lt_sq
    {p first second : ℕ} (hp : 0 < p) :
    mulInput p first second < p * p :=
  Internal.mulInput_lt_sq_internal hp

/-- Modular multiplication returns a canonical residue. -/
theorem mul_lt {p first second : ℕ} (hp : 0 < p) :
    mul p first second < p :=
  Internal.mul_lt_internal hp

/-- Tail-recursive exponentiation preserves the canonical-residue invariant. -/
theorem powLoop_lt {p base fuel accumulator : ℕ}
    (hp : 0 < p) (haccumulator : accumulator < p) :
    powLoop p base fuel accumulator < p :=
  Internal.powLoop_lt_internal hp haccumulator

/-- Modular exponentiation returns a canonical residue. -/
theorem pow_lt {p base exponent : ℕ} (hp : 0 < p) :
    pow p base exponent < p :=
  Internal.pow_lt_internal hp

/-- Prime-field inversion returns a canonical residue. -/
theorem inverse_lt {p value : ℕ} (hp : 0 < p) :
    inverse p value < p :=
  Internal.inverse_lt_internal hp

/-- Canonicalization fits in the modulus bit width. -/
theorem normalize_size_le {p value : ℕ} (hp : 0 < p) :
    (normalize p value).size ≤ bitWidth p :=
  Internal.normalize_size_le_internal hp

/-- A pre-reduction sum fits in one bit beyond the residue width. -/
theorem addInput_size_le
    {p first second : ℕ} (hp : 0 < p) :
    (addInput p first second).size ≤ linearScratchBitWidth p :=
  Internal.addInput_size_le_internal hp

/-- A pre-reduction difference fits in one bit beyond the residue width. -/
theorem subInput_size_le
    {p first second : ℕ} (hp : 0 < p) :
    (subInput p first second).size ≤ linearScratchBitWidth p :=
  Internal.subInput_size_le_internal hp

/-- A pre-reduction product fits in twice the residue width. -/
theorem mulInput_size_le
    {p first second : ℕ} (hp : 0 < p) :
    (mulInput p first second).size ≤
      multiplicationScratchBitWidth p :=
  Internal.mulInput_size_le_internal hp

/-- Modular addition fits in the modulus bit width. -/
theorem add_size_le {p first second : ℕ} (hp : 0 < p) :
    (add p first second).size ≤ bitWidth p :=
  Internal.add_size_le_internal hp

/-- Modular subtraction fits in the modulus bit width. -/
theorem sub_size_le {p first second : ℕ} (hp : 0 < p) :
    (sub p first second).size ≤ bitWidth p :=
  Internal.sub_size_le_internal hp

/-- Modular multiplication fits in the modulus bit width. -/
theorem mul_size_le {p first second : ℕ} (hp : 0 < p) :
    (mul p first second).size ≤ bitWidth p :=
  Internal.mul_size_le_internal hp

/-- Modular exponentiation fits in the modulus bit width. -/
theorem pow_size_le {p base exponent : ℕ} (hp : 0 < p) :
    (pow p base exponent).size ≤ bitWidth p :=
  Internal.pow_size_le_internal hp

/-- Prime-field inversion fits in the modulus bit width. -/
theorem inverse_size_le {p value : ℕ} (hp : 0 < p) :
    (inverse p value).size ≤ bitWidth p :=
  Internal.inverse_size_le_internal hp

/-- Canonicalization preserves the represented `ZMod` value. -/
@[simp] theorem coe_normalize (p value : ℕ) :
    ((normalize p value : ℕ) : ZMod p) = (value : ZMod p) :=
  Internal.coe_normalize_internal p value

/-- Runtime addition agrees with addition in `ZMod p`. -/
@[simp] theorem coe_add (p first second : ℕ) :
    ((add p first second : ℕ) : ZMod p) =
      (first : ZMod p) + (second : ZMod p) :=
  Internal.coe_add_internal p first second

/-- Runtime subtraction agrees with subtraction in the prime field. -/
@[simp] theorem coe_sub (p first second : ℕ) [Fact p.Prime] :
    ((sub p first second : ℕ) : ZMod p) =
      (first : ZMod p) - (second : ZMod p) :=
  Internal.coe_sub_internal p first second

/-- Runtime multiplication agrees with multiplication in `ZMod p`. -/
@[simp] theorem coe_mul (p first second : ℕ) :
    ((mul p first second : ℕ) : ZMod p) =
      (first : ZMod p) * (second : ZMod p) :=
  Internal.coe_mul_internal p first second

/-- The tail-recursive power loop has its standard accumulator semantics. -/
theorem coe_powLoop (p base fuel accumulator : ℕ) :
    ((powLoop p base fuel accumulator : ℕ) : ZMod p) =
      (accumulator : ZMod p) * (base : ZMod p) ^ fuel :=
  Internal.coe_powLoop_internal p base fuel accumulator

/-- Runtime exponentiation agrees with exponentiation in `ZMod p`. -/
@[simp] theorem coe_pow (p base exponent : ℕ) :
    ((pow p base exponent : ℕ) : ZMod p) =
      (base : ZMod p) ^ exponent :=
  Internal.coe_pow_internal p base exponent

/-- Fermat exponentiation implements inversion in the prime field, including
the zero-to-zero convention. -/
@[simp] theorem coe_inverse (p value : ℕ) [Fact p.Prime] :
    ((inverse p value : ℕ) : ZMod p) =
      (value : ZMod p)⁻¹ :=
  Internal.coe_inverse_internal p value

/-- Proof certificate for the allocation-free consecutive-candidate loop. -/
theorem foldNonzeroLoop_eq_foldl_range
    {State : Type*} (step : State → ℕ → State)
    (fuel candidate : ℕ) (state : State) :
    foldNonzeroLoop step fuel candidate state =
      (List.range' candidate fuel).foldl step state :=
  Internal.foldNonzeroLoop_eq_foldl_range_internal
    step fuel candidate state

/-- The streamed traversal is extensionally the fold over
`1, ..., p - 1`; the runtime definition itself does not construct this list. -/
theorem foldNonzero_eq_foldl_range
    {State : Type*} (p : ℕ) (step : State → ℕ → State)
    (initial : State) :
    foldNonzero p step initial =
      (List.range' 1 (p - 1)).foldl step initial :=
  Internal.foldNonzero_eq_foldl_range_internal p step initial

/-- Exact membership characterization of the traversal certificate. -/
theorem mem_nonzero_range_iff {p residue : ℕ} :
    residue ∈ List.range' 1 (p - 1) ↔
      0 < residue ∧ residue < p :=
  Internal.mem_nonzero_range_iff_internal

/-- Every streamed residue appears at most once. -/
theorem nonzero_range_nodup (p : ℕ) :
    (List.range' 1 (p - 1)).Nodup :=
  Internal.nonzero_range_nodup_internal p

/-- The stream performs exactly `p - 1` callbacks. -/
theorem nonzero_range_length (p : ℕ) :
    (List.range' 1 (p - 1)).length = p - 1 :=
  Internal.nonzero_range_length_internal p

/-- Every streamed natural residue represents a nonzero prime-field element. -/
theorem coe_ne_zero_of_mem_nonzero_range
    {p residue : ℕ} [Fact p.Prime]
    (hresidue : residue ∈ List.range' 1 (p - 1)) :
    (residue : ZMod p) ≠ 0 :=
  Internal.coe_ne_zero_of_mem_nonzero_range_internal hresidue

/-- Every unit of `ZMod p` is represented by a residue in the streamed
certificate, so the traversal is complete as well as duplicate-free. -/
theorem exists_mem_nonzero_range_coe_eq
    (p : ℕ) [Fact p.Prime] (unit : (ZMod p)ˣ) :
    ∃ residue ∈ List.range' 1 (p - 1),
      (residue : ZMod p) = (unit : ZMod p) :=
  Internal.exists_mem_nonzero_range_coe_eq_internal p unit

end Runtime

end PrimeField

end CookMertz

end TreeEval

end Complexity
