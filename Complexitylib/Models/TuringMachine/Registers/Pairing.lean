/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Registers.Pair

/-!
# `Nat.pair` and `Nat.unpair` over unary registers

Exact machine implementations of Mathlib's pairing bijection, and one polynomial
dominating the cost of every arithmetic operation in this directory.

## `pairTM`

`Nat.pair a b = if a < b then b*b + a else a*a + a + b` needs no branch at all. Writing
`m = max a b`, both arms are `m*m + a + (if a < b then 0 else b)`, and over truncated
arithmetic `max a b = a + (b - a)` — where `b - a` is exactly what `ltFlagTM` already
leaves in its scratch register. The trailing conditional term is applied by *multiplying*
by the `0/1` flag, so `pairTM` is ten straight-line stages with no control flow.

## `unpairTM`

`Nat.unpair` is computed by iterating the pairing successor `n` times from `(0, 0)`, using
`forRegTM` with the input as the loop counter. Correctness factors through
`unpair_eq_pairStepIter`, an *extensional* identity: the machine never evaluates
`Nat.unpair`'s square-root definition, it computes a function equal to it. **Integer square
root is absent from this development by construction, not by omission.**

`forRegTM` never writes its fuel register's cells — only its head moves — so the input
survives `unpairTM` unchanged and is still available to a later `Code.left` / `Code.right`.

## Cost

`evalnArithmeticCost B = 500 * (B + 1) ^ 4` dominates every operation here on values
bounded by `B`. The degree comes from `mulAddIntoTM`: unary multiplication is a loop of
unary additions, so squaring costs `O(B⁴)`. Only the polynomial shape is load-bearing.

Nothing in this file touches the output tape: `OutAcc ys` is carried through every machine
unchanged, and no `ifTM` appears (see `Registers.Compare` for why it cannot).
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-! ## `Nat.pair`, straight-line -/

/-- `Nat.pair` has a branch-free form over truncated arithmetic.

    Writing `m = max a b`, both branches of `if a < b then b*b + a else a*a + a + b` are
    `m*m + a + (if a < b then 0 else b)`: when `a < b` we have `m = b` and the last term
    vanishes, and otherwise `m = a`, so `m*m + a + b` is `a*a + a + b`. -/
lemma pair_eq_max (a b : ℕ) :
    Nat.pair a b = (a + (b - a)) * (a + (b - a)) + a + (1 - (if a < b then 1 else 0)) * b := by
  unfold Nat.pair
  rcases lt_or_ge a b with h | h
  · rw [if_pos h, if_pos h]
    have : a + (b - a) = b := by omega
    rw [this]; omega
  · rw [if_neg (by omega), if_neg (by omega)]
    have : a + (b - a) = a := by omega
    rw [this]; omega

/-- The eight registers `pairTM` uses.

    | index | role |
    | ---: | --- |
    | `0` | `a` — first input, preserved |
    | `1` | `b` — second input, preserved |
    | `2` | scratch: `b - a`, left by `ltFlagTM` and reused as the `max` correction |
    | `3` | `gLT = [a < b]` |
    | `4` | `m = max a b` |
    | `5` | a copy of `m`, because `mulAddIntoTM` needs distinct factors |
    | `6` | `out` — the result |
    | `7` | `gGE = 1 - gLT` | -/
abbrev PairingRegs (n : ℕ) := Regs 8 n

/-- `out := Nat.pair a b`, straight-line: no branch, no guarded arm, no `ifTM`.

    `max a b` is `a + (b - a)` in truncated arithmetic, and `b - a` is exactly what
    `ltFlagTM` leaves in its scratch register — so the maximum costs one `addIntoTM` on a
    value already computed. The conditional `+ b` is applied by multiplying by the `0/1`
    flag rather than by guarding an arm. -/
def pairTM (r : PairingRegs n) : TM n :=
  seqTM (ltFlagTM (r 0) (r 1) (r 2) (r 3)) <|
  seqTM (copyIntoTM (r 0) (r 4)) <|
  seqTM (addIntoTM (r 2) (r 4)) <|
  seqTM (copyIntoTM (r 4) (r 5)) <|
  seqTM (clearRegTM (r 6)) <|
  seqTM (mulAddIntoTM (r 4) (r 5) (r 6)) <|
  seqTM (addIntoTM (r 0) (r 6)) <|
  seqTM (setOneTM (r 7)) <|
  seqTM (subIntoTM (r 3) (r 7))
        (mulAddIntoTM (r 7) (r 1) (r 6))

/-- Register values after `pairTM`. Inputs `0` and `1` are preserved. -/
def pairVals (v : Fin 8 → ℕ) : Fin 8 → ℕ := fun k =>
  if k = 2 then v 1 - v 0
  else if k = 3 then (if v 0 < v 1 then 1 else 0)
  else if k = 4 then v 0 + (v 1 - v 0)
  else if k = 5 then v 0 + (v 1 - v 0)
  else if k = 6 then Nat.pair (v 0) (v 1)
  else if k = 7 then 1 - (if v 0 < v 1 then 1 else 0)
  else v k

theorem pairTM_hoareTime (r : PairingRegs n) (v : Fin 8 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB : ∀ k, v k ≤ B) :
    (pairTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (pairVals v)) ys)
      (500 * (B + 1) ^ 4) := by
  have hpv := parked_regsWork r hpark
  have hb0 := hB 0
  have hb1 := hB 1
  -- S1: r3 := [a < b], r2 := b - a
  have h1 := ltFlagTM_hoareTime (r 0) (r 1) (r 2) (r 3)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (v 0) (v 1) (v 2) (v 3) inp₀ (regsWork r w₀ v) ys hinp₀ (hpv v)
      (regsWork_apply r w₀ v 0) (regsWork_apply r w₀ v 1)
      (regsWork_apply r w₀ v 2) (regsWork_apply r w₀ v 3)
  rw [regsWork_update, regsWork_update] at h1
  replace h1 := h1.mono_bound
    (ltFlagTime_le (v 0) (v 1) (v 2) (v 3) B (hB 0) (hB 1) (hB 2) (hB 3))
  set V1 := Function.update (Function.update v 2 (v 1 - v 0)) 3
      (if v 0 < v 1 then 1 else 0) with hV1
  have g1_0 : V1 0 = v 0 := by rw [hV1]; simp
  have g1_2 : V1 2 = v 1 - v 0 := by rw [hV1]; simp
  have g1_4 : V1 4 = v 4 := by rw [hV1]; simp
  -- S2: r4 := a
  have h2 := copyIntoTM_hoareTime (r 0) (r 4) (r.ne (by decide)) (v 0) (v 4) inp₀
      (regsWork r w₀ V1) ys hinp₀ (fun i _ => hpv V1 i)
      (by rw [regsWork_apply, g1_0]) (by rw [regsWork_apply, g1_4])
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (show (2 * v 4 + 4) + 1 + (v 0 * ((2 * (0 + v 0) + 4) + 2) + (v 0 + 2))
        ≤ 2 * B + 5 + (B * (2 * B + 6) + (B + 2)) by
      have := hB 4
      exact Nat.add_le_add (by omega)
        (Nat.add_le_add (Nat.mul_le_mul hb0 (by omega)) (by omega)))
  set V2 := Function.update V1 4 (v 0) with hV2
  have g2_2 : V2 2 = v 1 - v 0 := by rw [hV2]; simp [g1_2]
  have g2_4 : V2 4 = v 0 := by rw [hV2]; simp
  -- S3: r4 := a + (b - a) = max a b
  have h3 := addIntoTM_hoareTime (r 2) (r 4) (r.ne (by decide)) (v 1 - v 0) (v 0) inp₀
      (regsWork r w₀ V2) ys hinp₀ (fun i _ => hpv V2 i)
      (by rw [regsWork_apply, g2_2]) (by rw [regsWork_apply, g2_4])
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound
    (show (v 1 - v 0) * ((2 * (v 0 + (v 1 - v 0)) + 4) + 2) + ((v 1 - v 0) + 2)
        ≤ B * (2 * B + 6) + (B + 2) by
      exact Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega))
  set V3 := Function.update V2 4 (v 0 + (v 1 - v 0)) with hV3
  have g3_4 : V3 4 = v 0 + (v 1 - v 0) := by rw [hV3]; simp
  have g3_5 : V3 5 = v 5 := by
    rw [hV3, hV2, hV1]; simp
  -- S4: r5 := m
  have h4 := copyIntoTM_hoareTime (r 4) (r 5) (r.ne (by decide))
      (v 0 + (v 1 - v 0)) (v 5) inp₀ (regsWork r w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (by rw [regsWork_apply, g3_4]) (by rw [regsWork_apply, g3_5])
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (show (2 * v 5 + 4) + 1 + ((v 0 + (v 1 - v 0)) *
        ((2 * (0 + (v 0 + (v 1 - v 0))) + 4) + 2) + ((v 0 + (v 1 - v 0)) + 2))
        ≤ 2 * B + 5 + (B * (2 * B + 6) + (B + 2)) by
      have := hB 5
      exact Nat.add_le_add (by omega)
        (Nat.add_le_add (Nat.mul_le_mul (by omega) (by omega)) (by omega)))
  set V4 := Function.update V3 5 (v 0 + (v 1 - v 0)) with hV4
  have g4_6 : V4 6 = v 6 := by
    rw [hV4, hV3, hV2, hV1]; simp
  -- S5: r6 := 0
  have h5 := clearRegTM_hoareTime (r 6) (v 6) inp₀ (regsWork r w₀ V4) ys hinp₀
      (fun i _ => hpv V4 i) (by rw [regsWork_apply, g4_6])
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound (show 2 * v 6 + 4 ≤ 2 * B + 4 by have := hB 6; omega)
  set V5 := Function.update V4 6 0 with hV5
  have g5_4 : V5 4 = v 0 + (v 1 - v 0) := by
    rw [hV5, hV4, hV3]; simp
  have g5_5 : V5 5 = v 0 + (v 1 - v 0) := by
    rw [hV5, hV4]; simp
  have g5_6 : V5 6 = 0 := by rw [hV5]; simp
  -- S6: r6 := m * m
  have h6 := mulAddIntoTM_hoareTime (r 4) (r 5) (r 6)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (v 0 + (v 1 - v 0)) (v 0 + (v 1 - v 0)) 0 inp₀ (regsWork r w₀ V5) ys hinp₀
      (fun i _ => hpv V5 i) (by rw [regsWork_apply, g5_4]) (by rw [regsWork_apply, g5_5])
      (by rw [regsWork_apply, g5_6])
  rw [regsWork_update] at h6
  replace h6 := h6.mono_bound
    (show (v 0 + (v 1 - v 0)) *
        (mulAddBound (v 0 + (v 1 - v 0)) (v 0 + (v 1 - v 0)) 0 + 2)
        + ((v 0 + (v 1 - v 0)) + 2) ≤ B * (B * (2 * (B * B + B) + 6) + (B + 2) + 2) + (B + 2) by
      have hm : v 0 + (v 1 - v 0) ≤ B := by omega
      have hmb : mulAddBound (v 0 + (v 1 - v 0)) (v 0 + (v 1 - v 0)) 0
          ≤ B * (2 * (B * B + B) + 6) + (B + 2) := by
        unfold mulAddBound
        refine Nat.add_le_add (Nat.mul_le_mul hm ?_) (by omega)
        have : (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) ≤ B * B := Nat.mul_le_mul hm hm
        omega
      exact Nat.add_le_add (Nat.mul_le_mul hm (by omega)) (by omega))
  set V6 := Function.update V5 6 (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0))) with hV6
  have g6_0 : V6 0 = v 0 := by
    rw [hV6, hV5, hV4, hV3, hV2, hV1]; simp
  have g6_6 : V6 6 = 0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) := by
    rw [hV6]; simp
  -- S7: r6 += a
  have h7 := addIntoTM_hoareTime (r 0) (r 6) (r.ne (by decide))
      (v 0) (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0))) inp₀
      (regsWork r w₀ V6) ys hinp₀ (fun i _ => hpv V6 i)
      (by rw [regsWork_apply, g6_0]) (by rw [regsWork_apply, g6_6])
  rw [regsWork_update] at h7
  replace h7 := h7.mono_bound
    (show v 0 * ((2 * (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0) + 4) + 2)
          + (v 0 + 2)
        ≤ B * (2 * (B * B + B) + 6) + (B + 2) by
      have hm : v 0 + (v 1 - v 0) ≤ B := by omega
      have : (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) ≤ B * B := Nat.mul_le_mul hm hm
      exact Nat.add_le_add (Nat.mul_le_mul hb0 (by omega)) (by omega))
  set V7 := Function.update V6 6
      (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0) with hV7
  have g7_7 : V7 7 = v 7 := by
    rw [hV7, hV6, hV5, hV4, hV3, hV2, hV1]; simp
  -- S8: r7 := 1
  have h8 := setOneTM_hoareTime (r 7) (v 7) inp₀ (regsWork r w₀ V7) ys hinp₀
      (fun i _ => hpv V7 i) (by rw [regsWork_apply, g7_7])
  rw [regsWork_update] at h8
  replace h8 := h8.mono_bound
    (show 2 * v 7 + 4 + 1 + (2 * 0 + 4) ≤ 2 * B + 9 by have := hB 7; omega)
  set V8 := Function.update V7 7 1 with hV8
  have g8_3 : V8 3 = (if v 0 < v 1 then 1 else 0) := by
    rw [hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1]; simp
  have g8_7 : V8 7 = 1 := by rw [hV8]; simp
  -- S9: r7 := 1 - gLT
  have h9 := subIntoTM_hoareTime (r 3) (r 7) (r.ne (by decide))
      (if v 0 < v 1 then 1 else 0) 1 inp₀ (regsWork r w₀ V8) ys hinp₀
      (fun i _ => hpv V8 i) (by rw [regsWork_apply, g8_3]) (by rw [regsWork_apply, g8_7])
  rw [regsWork_update] at h9
  replace h9 := h9.mono_bound
    (show (if v 0 < v 1 then 1 else 0) * ((2 * 1 + 4) + 2) +
        ((if v 0 < v 1 then 1 else 0) + 2) ≤ 11 by split_ifs <;> omega)
  set V9 := Function.update V8 7 (1 - if v 0 < v 1 then 1 else 0) with hV9
  have g9_1 : V9 1 = v 1 := by
    rw [hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1]; simp
  have g9_6 : V9 6 = 0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0 := by
    rw [hV9, hV8, hV7]; simp
  have g9_7 : V9 7 = 1 - (if v 0 < v 1 then 1 else 0) := by
    rw [hV9]; simp
  -- S10: r6 += gGE * b
  have h10 := mulAddIntoTM_hoareTime (r 7) (r 1) (r 6)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (1 - if v 0 < v 1 then 1 else 0) (v 1)
      (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0) inp₀
      (regsWork r w₀ V9) ys hinp₀ (fun i _ => hpv V9 i)
      (by rw [regsWork_apply, g9_7]) (by rw [regsWork_apply, g9_1])
      (by rw [regsWork_apply, g9_6])
  rw [regsWork_update] at h10
  replace h10 := h10.mono_bound
    (show (1 - if v 0 < v 1 then 1 else 0) *
        (mulAddBound (1 - if v 0 < v 1 then 1 else 0) (v 1)
          (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0) + 2)
        + ((1 - if v 0 < v 1 then 1 else 0) + 2)
        ≤ (B * (2 * (B * B + B + B + B) + 6) + (B + 2)) + 2 + 3 by
      have hm : v 0 + (v 1 - v 0) ≤ B := by omega
      have hsq : (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) ≤ B * B := Nat.mul_le_mul hm hm
      have hg : (1 - if v 0 < v 1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
      have hk : (1 - if v 0 < v 1 then 1 else 0) * v 1 ≤ B := by
        calc (1 - if v 0 < v 1 then 1 else 0) * v 1 ≤ 1 * v 1 := Nat.mul_le_mul hg le_rfl
          _ ≤ B := by omega
      have hmb : mulAddBound (1 - if v 0 < v 1 then 1 else 0) (v 1)
          (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0)
          ≤ B * (2 * (B * B + B + B + B) + 6) + (B + 2) := by
        unfold mulAddBound
        refine Nat.add_le_add (Nat.mul_le_mul hb1 ?_) (by omega)
        omega
      calc (1 - if v 0 < v 1 then 1 else 0) *
            (mulAddBound (1 - if v 0 < v 1 then 1 else 0) (v 1)
              (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0) + 2)
            + ((1 - if v 0 < v 1 then 1 else 0) + 2)
          ≤ 1 * ((B * (2 * (B * B + B + B + B) + 6) + (B + 2)) + 2) + (1 + 2) :=
            Nat.add_le_add (Nat.mul_le_mul hg (by omega)) (by omega)
        _ ≤ (B * (2 * (B * B + B + B + B) + 6) + (B + 2)) + 2 + 3 := by omega)
  set V10 := Function.update V9 6
      (0 + (v 0 + (v 1 - v 0)) * (v 0 + (v 1 - v 0)) + v 0
        + (1 - if v 0 < v 1 then 1 else 0) * v 1) with hV10
  -- the final vector
  have hfin : V10 = pairVals v := by
    funext k
    simp only [hV10, hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1, pairVals]
    fin_cases k <;> simp  <;>
      rw [pair_eq_max] <;> omega
  rw [hfin] at h10
  have hres := seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 <|
    seqEmit hinp₀ (hpv V6) h6 <|
    seqEmit hinp₀ (hpv V7) h7 <|
    seqEmit hinp₀ (hpv V8) h8 <|
    seqEmit hinp₀ (hpv V9) h9 h10
  refine hres.mono_bound ?_
  ring_nf
  omega

/-! ## `Nat.unpair`, by iterating the successor -/

/-- The pairing successor as a map on pairs. -/
def pairStep : ℕ × ℕ → ℕ × ℕ := fun p => (pairNextFst p.1 p.2, pairNextSnd p.1 p.2)

/-- Iterating the successor `j` times from `(0, 0)` lands on the pair coded by `j`. -/
lemma pair_pairStepIter (j : ℕ) :
    Nat.pair (pairStep^[j] (0, 0)).1 (pairStep^[j] (0, 0)).2 = j := by
  induction j with
  | zero => simp [Nat.pair]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    show Nat.pair (pairNextFst _ _) (pairNextSnd _ _) = i + 1
    rw [pair_pairNext, ih]

/-- **The extensional inverse.** `Nat.unpair` is the `n`-fold successor from `(0, 0)`.

    This is the whole reason integer square root is absent from this development: the
    machine never evaluates `Nat.unpair`'s square-root definition, it computes a function
    that is *equal* to it. -/
lemma unpair_eq_pairStepIter (j : ℕ) : Nat.unpair j = pairStep^[j] (0, 0) := by
  conv_lhs => rw [← pair_pairStepIter j]
  rw [Nat.unpair_pair]

/-- Both components of the `j`-th iterate are at most `j`. -/
lemma pairStepIter_le (j : ℕ) :
    (pairStep^[j] (0, 0)).1 ≤ j ∧ (pairStep^[j] (0, 0)).2 ≤ j := by
  rw [← unpair_eq_pairStepIter]
  exact ⟨Nat.unpair_left_le j, Nat.unpair_right_le j⟩

/-- Every register value the guard phase leaves behind is bounded by the larger input. -/
lemma guardVals_le (v : Fin 9 → ℕ) (k : Fin 9) :
    guardVals v k ≤ max (v 0) (v 1) + 1 := by
  fin_cases k <;> simp only [guardVals] <;> simp <;> (try split_ifs) <;> omega

/-- The state `unpairTM` starts its loop from: the inputs zeroed, scratch untouched. -/
def unpairInit (v : Fin 9 → ℕ) : Fin 9 → ℕ :=
  Function.update (Function.update v 0 0) 1 0

/-- The register values `unpairTM` leaves behind after `N` iterations. -/
def unpairVals (v : Fin 9 → ℕ) (N : ℕ) : Fin 9 → ℕ :=
  pairNextVals^[N] (unpairInit v)

lemma unpairInit_zero (v : Fin 9 → ℕ) : unpairInit v 0 = 0 := by
  simp [unpairInit]

lemma unpairInit_one (v : Fin 9 → ℕ) : unpairInit v 1 = 0 := by
  simp [unpairInit]

/-- The two output registers track the pure iteration. -/
lemma unpairVals_pair (v : Fin 9 → ℕ) (i : ℕ) :
    (unpairVals v i 0, unpairVals v i 1) = pairStep^[i] (0, 0) := by
  unfold unpairVals
  induction i with
  | zero => simp [unpairInit_zero, unpairInit_one]
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      pairNextVals_zero, pairNextVals_one, ← ih]
    rfl

/-- **`unpairTM`'s answer.** -/
lemma unpairVals_zero (v : Fin 9 → ℕ) (N : ℕ) : unpairVals v N 0 = (Nat.unpair N).1 := by
  rw [unpair_eq_pairStepIter, ← unpairVals_pair v N]

@[inherit_doc unpairVals_zero]
lemma unpairVals_one (v : Fin 9 → ℕ) (N : ℕ) : unpairVals v N 1 = (Nat.unpair N).2 := by
  rw [unpair_eq_pairStepIter, ← unpairVals_pair v N]

/-- The two output registers after `i` steps are at most `i`. This is the runtime
    invariant: every iteration runs on values bounded by the loop counter. -/
lemma unpairVals_le (v : Fin 9 → ℕ) (i : ℕ) :
    unpairVals v i 0 ≤ i ∧ unpairVals v i 1 ≤ i := by
  have h := unpairVals_pair v i
  have hle := pairStepIter_le i
  constructor
  · rw [show unpairVals v i 0 = (pairStep^[i] (0,0)).1 from congrArg Prod.fst h]; exact hle.1
  · rw [show unpairVals v i 1 = (pairStep^[i] (0,0)).2 from congrArg Prod.snd h]; exact hle.2

/-- Every register stays inside the size bound throughout the loop. -/
lemma unpairVals_bounded (v : Fin 9 → ℕ) (B : ℕ) (hB : ∀ k, v k ≤ B) (i : ℕ) (hi : i ≤ B)
    (k : Fin 9) : unpairVals v i k ≤ B := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · -- nothing has run yet
    have : unpairVals v 0 = unpairInit v := by simp [unpairVals]
    rw [this, unpairInit, Function.update_apply, Function.update_apply]
    split_ifs <;> first | omega | exact hB k
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj := unpairVals_le v j
    by_cases hk0 : k = 0
    · subst hk0; exact le_trans (unpairVals_le v (j + 1)).1 hi
    · by_cases hk1 : k = 1
      · subst hk1; exact le_trans (unpairVals_le v (j + 1)).2 hi
      · have hstep : unpairVals v (j + 1) = pairNextVals (unpairVals v j) := by
          unfold unpairVals; rw [Function.iterate_succ_apply']
        rw [hstep]
        have : pairNextVals (unpairVals v j) k = guardVals (unpairVals v j) k := by
          simp [pairNextVals, hk0, hk1]
        rw [this]
        exact le_trans (guardVals_le _ k) (by omega)

/-- `(a, b) := Nat.unpair n`, where `n` is the counter register's value.

    The loop counter is `forRegTM`'s fuel register, whose *cells are never written* — only
    its head moves — so the input survives the machine unchanged and is still available to
    `Code.left` / `Code.right` afterwards. -/
def unpairTM (r : PairRegs n) (ctr : Fin n) : TM n :=
  seqTM (clearRegTM (r 0)) (seqTM (clearRegTM (r 1)) (forRegTM (pairNextTM r) ctr))

theorem unpairTM_hoareTime (r : PairRegs n) (ctr : Fin n) (hctr : ∀ k, r k ≠ ctr)
    (v : Fin 9 → ℕ) (N B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hctrv : w₀ ctr = regTape N) (hNB : N ≤ B) (hB : ∀ k, v k ≤ B) :
    (unpairTM r ctr).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (unpairVals v N)) ys)
      (500 * (B + 1) ^ 3) := by
  have hpv := parked_regsWork r hpark
  -- clear the two output registers
  have h1 := clearRegTM_hoareTime (r 0) (v 0) inp₀ (regsWork r w₀ v) ys hinp₀
      (fun i _ => hpv v i) (regsWork_apply r w₀ v 0)
  rw [regsWork_update] at h1
  replace h1 := h1.mono_bound (show 2 * v 0 + 4 ≤ 2 * B + 4 by have := hB 0; omega)
  have h2 := clearRegTM_hoareTime (r 1) (Function.update v 0 0 1) inp₀
      (regsWork r w₀ (Function.update v 0 0)) ys hinp₀
      (fun i _ => hpv (Function.update v 0 0) i)
      (regsWork_apply r w₀ (Function.update v 0 0) 1)
  rw [regsWork_update] at h2
  replace h2 := h2.mono_bound
    (show 2 * Function.update v 0 0 1 + 4 ≤ 2 * B + 4 by
      have := hB 1
      simp only [Function.update_apply]
      split_ifs <;> omega)
  have hinit : Function.update (Function.update v 0 0) 1 0 = unpairInit v := rfl
  rw [hinit] at h2
  -- the loop
  have hbody : ∀ i, i < N → (pairNextTM r).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (regsWork r w₀ (unpairVals v i)) ctr
          ⟨i + 2, regCells N⟩ ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (regsWork r w₀ (unpairVals v (i + 1))) ctr
          ⟨i + 2, regCells N⟩ ∧ OutAcc ys out)
      (400 * (B + 1) ^ 2) := by
    intro i hi
    have hparkU : ∀ j, Parked (Function.update w₀ ctr (⟨i + 2, regCells N⟩ : Tape) j) := by
      intro j
      by_cases hj : j = ctr
      · subst hj; rw [Function.update_self]; exact parked_regCells (by omega)
      · rw [Function.update_of_ne hj]; exact hpark j
    have hspec := pairNextTM_hoareTime_poly r (unpairVals v i) B inp₀
      (Function.update w₀ ctr ⟨i + 2, regCells N⟩) ys hinp₀ hparkU
      (unpairVals_bounded v B hB i (by omega))
    rw [regsWork_update_of_ne r w₀ (unpairVals v i) hctr,
      regsWork_update_of_ne r w₀ (pairNextVals (unpairVals v i)) hctr] at hspec
    have hnext : pairNextVals (unpairVals v i) = unpairVals v (i + 1) := by
      unfold unpairVals; rw [Function.iterate_succ_apply']
    rw [hnext] at hspec
    exact hspec
  have hloop := forRegTM_hoareTime (pairNextTM r) ctr N inp₀
    (fun i => regsWork r w₀ (unpairVals v i)) (fun _ => ys) (400 * (B + 1) ^ 2) hinp₀
    (fun i => by rw [regsWork_of_ne r w₀ (unpairVals v i) hctr]; exact hctrv)
    (fun i j _ => hpv (unpairVals v i) j)
    hbody
  have hzero : unpairVals v 0 = unpairInit v := by simp [unpairVals]
  rw [hzero] at hloop
  -- chain
  have hres := seqEmit hinp₀ (hpv (Function.update v 0 0)) h1 <|
    seqEmit hinp₀ (hpv (unpairInit v)) h2 hloop
  refine hres.mono_bound ?_
  have hmul : N * (400 * (B + 1) ^ 2 + 2) ≤ B * (400 * (B + 1) ^ 2 + 2) :=
    Nat.mul_le_mul hNB le_rfl
  have hexp : B * (400 * (B + 1) ^ 2 + 2) = 400 * (B * ((B + 1) ^ 2)) + 2 * B := by ring
  have hBle : B * ((B + 1) ^ 2) ≤ (B + 1) ^ 3 := by
    have : (B + 1) ^ 3 = (B + 1) * ((B + 1) ^ 2) := by ring
    rw [this]
    exact Nat.mul_le_mul (by omega) le_rfl
  have hone : 1 ≤ (B + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hBcube : B ≤ (B + 1) ^ 3 := by
    have : (B + 1) ^ 3 = B * B * B + 3 * (B * B) + 3 * B + 1 := by ring
    omega
  omega

/-! ## One polynomial for the whole arithmetic layer

The `evaln` compiler will meter a run as *(number of abstract steps) × (cost of one
concrete arithmetic operation)*. For that it needs a single polynomial dominating every
operation in this directory when all live values are bounded by `B` — not an exact formula
per primitive.

`evalnArithmeticCost` is that polynomial. The degree is set by `mulAddIntoTM`: unary
multiplication is a loop of unary additions, so squaring an `O(B)`-length register costs
`O(B⁴)`. Nothing here tries to improve that; only the polynomial *shape* is load-bearing. -/

/-- A single polynomial dominating every arithmetic operation in this directory on values
    bounded by `B`. -/
def evalnArithmeticCost (B : ℕ) : ℕ := 500 * (B + 1) ^ 4

/-- The expansion `omega` needs to see. -/
private lemma cost_expand (B : ℕ) :
    evalnArithmeticCost B
      = 500 * (B * B * B * B) + 2000 * (B * B * B) + 3000 * (B * B) + 2000 * B + 500 := by
  unfold evalnArithmeticCost; ring

/-- `incRegTM`, `decRegTM`, `clearRegTM`. -/
lemma regOpTime_le_arith (d B : ℕ) (hd : d ≤ B) : 2 * d + 4 ≤ evalnArithmeticCost B := by
  have := cost_expand B; omega

/-- `setOneTM`. -/
lemma setOneTime_le_arith (d B : ℕ) (hd : d ≤ B) :
    2 * d + 4 + 1 + (2 * 0 + 4) ≤ evalnArithmeticCost B := by
  have := cost_expand B; omega

/-- `flagNonzeroTM`. -/
lemma flagNonzeroTime_le_arith (v d B : ℕ) (hv : v ≤ B) (hd : d ≤ B) :
    2 * d + 4 + 1 + (v * ((2 * 1 + 4 + 1 + (2 * 0 + 4)) + 2) + (v + 2))
      ≤ evalnArithmeticCost B := by
  have := cost_expand B; omega

/-- `addIntoTM`. -/
lemma addIntoTime_le_arith (a b B : ℕ) (ha : a ≤ B) (hb : b ≤ B) :
    a * ((2 * (b + a) + 4) + 2) + (a + 2) ≤ evalnArithmeticCost B := by
  have h1 : a * ((2 * (b + a) + 4) + 2) ≤ B * (4 * B + 6) :=
    Nat.mul_le_mul ha (by omega)
  have h2 : B * (4 * B + 6) = 4 * (B * B) + 6 * B := by ring
  have := cost_expand B
  omega

/-- `subIntoTM`. -/
lemma subIntoTime_le_arith (a b B : ℕ) (ha : a ≤ B) (hb : b ≤ B) :
    a * ((2 * b + 4) + 2) + (a + 2) ≤ evalnArithmeticCost B := by
  have h1 : a * ((2 * b + 4) + 2) ≤ B * (2 * B + 6) := Nat.mul_le_mul ha (by omega)
  have h2 : B * (2 * B + 6) = 2 * (B * B) + 6 * B := by ring
  have := cost_expand B
  omega

/-- `copyIntoTM`. -/
lemma copyIntoTime_le_arith (a b B : ℕ) (ha : a ≤ B) (hb : b ≤ B) :
    (2 * b + 4) + 1 + (a * ((2 * (0 + a) + 4) + 2) + (a + 2)) ≤ evalnArithmeticCost B := by
  have h1 : a * ((2 * (0 + a) + 4) + 2) ≤ B * (2 * B + 6) := Nat.mul_le_mul ha (by omega)
  have h2 : B * (2 * B + 6) = 2 * (B * B) + 6 * B := by ring
  have := cost_expand B
  omega

/-- `mulAddIntoTM`. This is the operation that sets the degree. -/
lemma mulAddTime_le_arith (a b d B : ℕ) (ha : a ≤ B) (hb : b ≤ B) (hd : d ≤ B) :
    a * (mulAddBound a b d + 2) + (a + 2) ≤ evalnArithmeticCost B := by
  have hab : a * b ≤ B * B := Nat.mul_le_mul ha hb
  have hmb : mulAddBound a b d ≤ 2 * (B * B * B) + 4 * (B * B) + 6 * B + (B + 2) := by
    unfold mulAddBound
    have h1 : b * ((2 * (d + a * b + b) + 4) + 2) ≤ B * (2 * (B + B * B + B) + 6) :=
      Nat.mul_le_mul hb (by omega)
    have h2 : B * (2 * (B + B * B + B) + 6) = 2 * (B * B * B) + 4 * (B * B) + 6 * B := by
      ring
    omega
  have h3 : a * (mulAddBound a b d + 2)
      ≤ B * (2 * (B * B * B) + 4 * (B * B) + 6 * B + (B + 2) + 2) :=
    Nat.mul_le_mul ha (by omega)
  have h4 : B * (2 * (B * B * B) + 4 * (B * B) + 6 * B + (B + 2) + 2)
      = 2 * (B * B * B * B) + 4 * (B * B * B) + 7 * (B * B) + 4 * B := by ring
  have := cost_expand B
  omega

/-- `ltFlagTM`. -/
lemma ltFlagTime_le_arith (a b s f B : ℕ) (ha : a ≤ B) (hb : b ≤ B) (hs : s ≤ B)
    (hf : f ≤ B) : ltFlagTime a b s f ≤ evalnArithmeticCost B := by
  have h := ltFlagTime_le a b s f B ha hb hs hf
  have h2 : (B + 1) ^ 2 = B * B + 2 * B + 1 := by ring
  have := cost_expand B
  omega

/-! ### The capstones, metered by the common cost -/

/-- `pairNextTM` under the common arithmetic cost. -/
theorem pairNextTM_hoareTime_arith (r : PairRegs n) (v : Fin 9 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, v k ≤ B) :
    (pairNextTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (pairNextVals v)) ys)
      (evalnArithmeticCost B) :=
  (pairNextTM_hoareTime_poly r v B inp₀ w₀ ys hinp₀ hpark hB).mono_bound
    (by have h2 : (B + 1) ^ 2 = B * B + 2 * B + 1 := by ring
        have := cost_expand B
        omega)

/-- `pairTM` under the common arithmetic cost. -/
theorem pairTM_hoareTime_arith (r : PairingRegs n) (v : Fin 8 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i)) (hB : ∀ k, v k ≤ B) :
    (pairTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (pairVals v)) ys)
      (evalnArithmeticCost B) :=
  (pairTM_hoareTime r v B inp₀ w₀ ys hinp₀ hpark hB).mono_bound
    (by unfold evalnArithmeticCost; omega)

/-- `unpairTM` under the common arithmetic cost. -/
theorem unpairTM_hoareTime_arith (r : PairRegs n) (ctr : Fin n) (hctr : ∀ k, r k ≠ ctr)
    (v : Fin 9 → ℕ) (N B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hctrv : w₀ ctr = regTape N) (hNB : N ≤ B) (hB : ∀ k, v k ≤ B) :
    (unpairTM r ctr).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (unpairVals v N)) ys)
      (evalnArithmeticCost B) :=
  (unpairTM_hoareTime r ctr hctr v N B inp₀ w₀ ys hinp₀ hpark hctrv hNB hB).mono_bound
    (by have h3 : (B + 1) ^ 3 = B * B * B + 3 * (B * B) + 3 * B + 1 := by ring
        have := cost_expand B
        omega)

end TM

end Complexity
