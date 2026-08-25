/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Registers.Compare
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Nat.Pairing

/-!
# The pairing successor over unary registers

`Nat.pair` enumerates `ℕ × ℕ` in shells: the pairs with code in `[s^2, (s+1)^2)` are
`(0,s), (1,s), …, (s-1,s)` followed by `(s,0), (s,1), …, (s,s)`. `pairNextFst` and
`pairNextSnd` are the successor of that enumeration — the map sending the pair coded by
`k` to the pair coded by `k + 1`.

## Why this shape

Written case-by-case the successor has four arms:

```
a < b,  a+1 < b   ↦  (a+1, b)
a < b,  a+1 = b   ↦  (b, 0)
b < a             ↦  (a, b+1)
a = b             ↦  (0, a+1)
```

and implementing *those* on registers needs four composite arms, two of which copy one
live register over another and so carry copy-before-clear ordering hazards.

Splitting on `a < b` alone collapses all of it. In the first half of a shell the first
component always advances, and in the second half the second component always advances:

```
a < b   ↦  a := a + 1,  and b := 0 when a + 1 = b
b ≤ a   ↦  b := b + 1,  and a := 0 when a = b
```

That is the same function — when `a + 1 = b` the pair `(a+1, 0)` *is* `(b, 0)`, and when
`a = b` the pair `(0, b+1)` *is* `(0, a+1)` — but now every arm is a single `incRegTM` or
`clearRegTM`. No arm copies anything, so no ordering hazard exists to reason about, and
each guarded arm is one application of `guardTM_hoareTime`.

`pairNextFst_eq` and `pairNextSnd_eq` below are exactly that reformulation, stated as the
sum of the guarded increments the machine performs.

## The guards

Four indicators drive the machine, all computed from the original `(a, b)` *before* any
register is mutated:

```
gLT = [a < b]        gGT = [b < a]        gEQ = [a = b]        gB1 = [a + 1 = b]
```

`gLT` and `gGT` are two calls to `ltFlagTM`. The other two are arithmetic on those, with
no extra comparison and no Boolean-algebra machinery:

* `gEQ = 1 - gLT - gGT`, by trichotomy (`pairNext_trichotomy`);
* `gB1 = gLT - min ((b - a) - 1) 1`, reusing the `b - a` that `ltFlagTM` already leaves in
  its scratch register (`gB1_eq`).
-/


@[expose] public section

namespace Complexity

namespace TM

variable {m n : ℕ}

/-! ### Register tuples -/

/-- A tuple of `m` pairwise-distinct registers inside `Fin n`. Bundling them as an
    embedding makes distinctness one hypothesis rather than `m * (m-1) / 2`. -/
abbrev Regs (m n : ℕ) := Fin m ↪ Fin n

/-- Distinct indices name distinct registers. Discharges every side condition of the
    form `r i ≠ r j` by `r.ne (by decide)`. -/
lemma Regs.ne (r : Regs m n) {i j : Fin m} (h : i ≠ j) : r i ≠ r j :=
  fun e => h (r.injective e)

/-! ### The pure successor -/

/-- First component of the successor of `(a, b)` in `Nat.pair`'s enumeration. -/
def pairNextFst (a b : ℕ) : ℕ := if a < b then a + 1 else if a = b then 0 else a

/-- Second component of the successor of `(a, b)` in `Nat.pair`'s enumeration. -/
def pairNextSnd (a b : ℕ) : ℕ := if a < b then (if a + 1 = b then 0 else b) else b + 1

/-! ### Guard arithmetic

The facts that make the four guards mutually exclusive and let two of them be derived
from the other two. Each is a one-line case split; having them in hand before the machine
is written is what keeps the `HoareTime` composition free of arithmetic side quests. -/

/-- **Exactly one arm runs.** The three order guards partition every `(a, b)`. -/
lemma pairNext_trichotomy (a b : ℕ) :
    (if a < b then 1 else 0) + (if b < a then 1 else 0) + (if a = b then 1 else 0) = 1 := by
  split_ifs <;> omega

/-- **At most one arm runs.** No two of the three order relations hold together, so the
    guarded arms never interfere and their order of execution is immaterial. -/
lemma pairNext_guards_disjoint (a b : ℕ) :
    ¬((a < b ∧ b < a) ∨ (a < b ∧ a = b) ∨ (b < a ∧ a = b)) := by
  omega

/-- Every guard is `0` or `1`, the side condition `guardTM_hoareTime` asks for. -/
lemma ite_one_zero_le_one (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by
  split_ifs <;> omega

/-- `gEQ` is derived from the two comparisons, not computed by a third. -/
lemma gEQ_eq (a b : ℕ) :
    1 - (if a < b then 1 else 0) - (if b < a then 1 else 0) = if a = b then 1 else 0 := by
  split_ifs <;> omega

/-- `gB1` is derived from `gLT` and the `b - a` that `ltFlagTM` already leaves in scratch:
    `a + 1 = b` exactly when `b - a` is nonzero but `b - a - 1` is not. -/
lemma gB1_eq (a b : ℕ) :
    (if a < b then 1 else 0) - min (b - a - 1) 1 = if a + 1 = b then 1 else 0 := by
  split_ifs <;> omega

/-! ### The successor as guarded increments

The bridge between the pure function and the machine's arm structure: each component is
its initial value plus the guarded increments, then zeroed by its guarded clear. -/

/-- `a` is incremented under `gLT` and cleared under `gEQ`. -/
lemma pairNextFst_eq (a b : ℕ) :
    pairNextFst a b = if a = b then 0 else a + (if a < b then 1 else 0) := by
  unfold pairNextFst; split_ifs <;> omega

/-- `b` is incremented under `gGT` and under `gEQ`, and cleared under `gB1`. -/
lemma pairNextSnd_eq (a b : ℕ) :
    pairNextSnd a b =
      if a + 1 = b then 0
      else b + (if b < a then 1 else 0) + (if a = b then 1 else 0) := by
  unfold pairNextSnd; split_ifs <;> omega

/-! ### The machine -/

/-- The nine registers `pairNextTM` uses, bundled as an embedding so that pairwise
    distinctness is one hypothesis rather than thirty-six.

    | index | role |
    | ---: | --- |
    | `0` | `a` — first component, in and out |
    | `1` | `b` — second component, in and out |
    | `2` | scratch: `b - a`, then `b - a - 1` |
    | `3` | scratch: `a - b` |
    | `4` | `gLT = [a < b]` |
    | `5` | `gGT = [b < a]` |
    | `6` | `gEQ = [a = b]` |
    | `7` | `gB1 = [a + 1 = b]` |
    | `8` | `min (b - a - 1) 1`, the helper for `gB1` | -/
abbrev PairRegs (n : ℕ) := Regs 9 n

/-- Distinct indices name distinct registers. Discharges every side condition of the form
    `r i ≠ r j` by `r.ne (by decide)`. -/
lemma PairRegs.ne (r : PairRegs n) {i j : Fin 9} (h : i ≠ j) : r i ≠ r j := Regs.ne r h

/-! ### Register-indexed work states

The composition below updates one register at a time and reads several of the others back
out at every stage. Threading that through nested `Function.update`s costs a
`Function.update_of_ne` chain per read, quadratically in the number of stages.

Naming a work state by its *vector of register values* collapses all of it: an update of
the state becomes an update of `v : Fin 9 → ℕ` (`regsWork_update`), and a read is one
rewrite (`regsWork_apply`). The state is only ever used inside pre- and postconditions, so
being noncomputable costs nothing. -/

/-- The work state whose nine named registers hold the values `v`, agreeing with `w₀`
    on every other register. -/
noncomputable def regsWork (r : Regs m n) (w₀ : Fin n → Tape) (v : Fin m → ℕ) :
    Fin n → Tape :=
  fun i => if h : ∃ k, r k = i then regTape (v h.choose) else w₀ i

/-- Reading a named register. -/
lemma regsWork_apply (r : Regs m n) (w₀ : Fin n → Tape) (v : Fin m → ℕ) (k : Fin m) :
    regsWork r w₀ v (r k) = regTape (v k) := by
  have h : ∃ j, r j = r k := ⟨k, rfl⟩
  rw [regsWork, dif_pos h, r.injective h.choose_spec]

/-- Registers outside the nine are untouched. -/
lemma regsWork_of_ne (r : Regs m n) (w₀ : Fin n → Tape) (v : Fin m → ℕ) {i : Fin n}
    (hi : ∀ k, r k ≠ i) : regsWork r w₀ v i = w₀ i := by
  rw [regsWork, dif_neg]
  rintro ⟨k, rfl⟩
  exact hi k rfl

/-- **The stage step.** Updating one named register of the state is updating one entry of
    the value vector — which is what turns the fourteen-stage bookkeeping into finite
    data. -/
lemma regsWork_update (r : Regs m n) (w₀ : Fin n → Tape) (v : Fin m → ℕ) (k : Fin m)
    (x : ℕ) :
    Function.update (regsWork r w₀ v) (r k) (regTape x)
      = regsWork r w₀ (Function.update v k x) := by
  funext i
  by_cases hi : i = r k
  · subst hi
    rw [Function.update_self, regsWork_apply, Function.update_self]
  · rw [Function.update_of_ne hi]
    by_cases h : ∃ j, r j = i
    · obtain ⟨j, rfl⟩ := h
      have hjk : j ≠ k := fun e => hi (by rw [e])
      rw [regsWork_apply, regsWork_apply, Function.update_of_ne hjk]
    · rw [regsWork_of_ne _ _ _ (fun k' e => h ⟨k', e⟩),
        regsWork_of_ne _ _ _ (fun k' e => h ⟨k', e⟩)]

/-- **Framing.** A register-indexed state commutes with an update to a register outside
    its tuple. This is what lets a machine over `r` run inside a loop whose counter lives
    in a register `r` does not name. -/
lemma regsWork_update_of_ne (r : Regs m n) (w₀ : Fin n → Tape) (v : Fin m → ℕ) {i : Fin n}
    (hi : ∀ k, r k ≠ i) (t : Tape) :
    regsWork r (Function.update w₀ i t) v = Function.update (regsWork r w₀ v) i t := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, regsWork_of_ne _ _ _ hi, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases h : ∃ k, r k = j
    · obtain ⟨k, rfl⟩ := h
      rw [regsWork_apply, regsWork_apply]
    · rw [regsWork_of_ne _ _ _ (fun k e => h ⟨k, e⟩),
        regsWork_of_ne _ _ _ (fun k e => h ⟨k, e⟩), Function.update_of_ne hj]

/-- A register-indexed state over a parked base is everywhere parked. -/
lemma parked_regsWork (r : Regs m n) {w₀ : Fin n → Tape} (h : ∀ i, Parked (w₀ i))
    (v : Fin m → ℕ) : ∀ i, Parked (regsWork r w₀ v i) := by
  intro i
  rw [regsWork]
  split
  · exact parked_regTape _
  · exact h i

/-! ### Guarded arms over a register-indexed state

The five mutating arms are all the same shape: a body rewriting one named register, run
under a `{0,1}` guard held in another. `guardRegArm` is that shape once, so each arm below
is a single application. -/

/-- **A guarded arm.** `body` rewrites register `r j` from `v j` to `y`; run under the
    guard in `r k`, it does so when the guard is `1` and nothing when it is `0`.

    `body` is supplied as a spec valid at *any* parked state holding `v j` in `r j`,
    because `guardTM` hands it the state in which the guard register carries `forRegTM`'s
    loop cursor rather than an ordinary register tape. -/
lemma guardRegArm (r : Regs m n) {inp₀ : Tape} {w₀ : Fin n → Tape} {ys : List Bool}
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (v : Fin m → ℕ) (j k : Fin m) (hjk : j ≠ k) (y b_body : ℕ) (body : TM n)
    (hg : v k ≤ 1)
    (hbody : ∀ W : Fin n → Tape, (∀ i, Parked (W i)) → W (r j) = regTape (v j) →
      body.HoareTime (EmitPred inp₀ W ys)
        (EmitPred inp₀ (Function.update W (r j) (regTape y)) ys) b_body) :
    (guardTM body (r k)).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (if v k = 0 then v else Function.update v j y)) ys)
      (v k * (b_body + 2) + (v k + 2)) := by
  have hrk : r j ≠ r k := r.ne hjk
  have hparkW₀ := parked_regsWork r hpark v
  have hparkWT := parked_regsWork r hpark (Function.update v j y)
  have hcur : ∀ i,
      Parked (Function.update (regsWork r w₀ v) (r k) (⟨0 + 2, regCells (v k)⟩ : Tape) i) := by
    intro i
    by_cases hi : i = r k
    · subst hi; rw [Function.update_self]; exact parked_regCells (by omega)
    · rw [Function.update_of_ne hi]; exact hparkW₀ i
  have hspec := hbody (Function.update (regsWork r w₀ v) (r k) ⟨0 + 2, regCells (v k)⟩) hcur
    (by rw [Function.update_of_ne hrk, regsWork_apply])
  have hcomm : Function.update
        (Function.update (regsWork r w₀ v) (r k) (⟨0 + 2, regCells (v k)⟩ : Tape))
        (r j) (regTape y)
      = Function.update (regsWork r w₀ (Function.update v j y)) (r k)
          ⟨0 + 2, regCells (v k)⟩ := by
    rw [Function.update_comm (Ne.symm hrk), regsWork_update]
  rw [hcomm] at hspec
  have hres := guardTM_hoareTime body (r k) (v k) b_body hg inp₀ (regsWork r w₀ v)
    (regsWork r w₀ (Function.update v j y)) ys hinp₀
    (fun i _ => hparkW₀ i) (fun i _ => hparkWT i)
    (regsWork_apply r w₀ v k)
    (by rw [regsWork_apply, Function.update_of_ne (Ne.symm hjk)])
    hspec
  rwa [apply_ite (regsWork r w₀)]

/-- Stages 1–9: compute the four guards from the pristine inputs. -/
def pairGuardTM (r : PairRegs n) : TM n :=
  seqTM (ltFlagTM (r 1) (r 0) (r 3) (r 5)) <|
  seqTM (ltFlagTM (r 0) (r 1) (r 2) (r 4)) <|
  seqTM (decRegTM (r 2)) <|
  seqTM (flagNonzeroTM (r 2) (r 8)) <|
  seqTM (setOneTM (r 6)) <|
  seqTM (subIntoTM (r 4) (r 6)) <|
  seqTM (subIntoTM (r 5) (r 6)) <|
  seqTM (copyIntoTM (r 4) (r 7))
        (subIntoTM (r 8) (r 7))

/-- Register values after the guard phase. Registers `0` and `1` are untouched. -/
def guardVals (v : Fin 9 → ℕ) : Fin 9 → ℕ := fun k =>
  if k = 2 then v 1 - v 0 - 1
  else if k = 3 then v 0 - v 1
  else if k = 4 then (if v 0 < v 1 then 1 else 0)
  else if k = 5 then (if v 1 < v 0 then 1 else 0)
  else if k = 6 then (if v 0 = v 1 then 1 else 0)
  else if k = 7 then (if v 0 + 1 = v 1 then 1 else 0)
  else if k = 8 then min (v 1 - v 0 - 1) 1
  else v k

theorem pairGuardTM_hoareTime (r : PairRegs n) (v : Fin 9 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB : ∀ k, v k ≤ B) :
    (pairGuardTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (guardVals v)) ys)
      (80 * (B + 1) ^ 2 + 22 * B + 77) := by
  have hpv := parked_regsWork r hpark
  -- S1: r5 := [b < a], r3 := a - b
  have h1 := ltFlagTM_hoareTime (r 1) (r 0) (r 3) (r 5)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (v 1) (v 0) (v 3) (v 5) inp₀ (regsWork r w₀ v) ys hinp₀ (hpv v)
      (regsWork_apply r w₀ v 1) (regsWork_apply r w₀ v 0)
      (regsWork_apply r w₀ v 3) (regsWork_apply r w₀ v 5)
  rw [regsWork_update, regsWork_update] at h1
  replace h1 := h1.mono_bound
    (ltFlagTime_le (v 1) (v 0) (v 3) (v 5) B (hB 1) (hB 0) (hB 3) (hB 5))
  set V1 := Function.update (Function.update v 3 (v 0 - v 1)) 5
      (if v 1 < v 0 then 1 else 0) with hV1
  -- S2: r4 := [a < b], r2 := b - a
  have g1_0 : V1 0 = v 0 := by rw [hV1]; simp
  have g1_1 : V1 1 = v 1 := by rw [hV1]; simp
  have g1_2 : V1 2 = v 2 := by rw [hV1]; simp
  have g1_4 : V1 4 = v 4 := by rw [hV1]; simp
  have h2 := ltFlagTM_hoareTime (r 0) (r 1) (r 2) (r 4)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide))
      (v 0) (v 1) (v 2) (v 4) inp₀ (regsWork r w₀ V1) ys hinp₀ (hpv V1)
      (by rw [regsWork_apply, g1_0]) (by rw [regsWork_apply, g1_1])
      (by rw [regsWork_apply, g1_2]) (by rw [regsWork_apply, g1_4])
  rw [regsWork_update, regsWork_update] at h2
  replace h2 := h2.mono_bound
    (ltFlagTime_le (v 0) (v 1) (v 2) (v 4) B (hB 0) (hB 1) (hB 2) (hB 4))
  set V2 := Function.update (Function.update V1 2 (v 1 - v 0)) 4
      (if v 0 < v 1 then 1 else 0) with hV2
  -- S3: r2 := (b - a) - 1
  have g2_2 : V2 2 = v 1 - v 0 := by rw [hV2]; simp
  have h3 := decRegTM_hoareTime (r 2) (v 1 - v 0) inp₀ (regsWork r w₀ V2) ys hinp₀
      (fun i _ => hpv V2 i) (by rw [regsWork_apply, g2_2])
  rw [regsWork_update] at h3
  replace h3 := h3.mono_bound (show 2 * (v 1 - v 0) + 4 ≤ 2 * B + 4 by have := hB 1; omega)
  set V3 := Function.update V2 2 (v 1 - v 0 - 1) with hV3
  -- S4: r8 := min ((b - a) - 1) 1
  have g3_2 : V3 2 = v 1 - v 0 - 1 := by rw [hV3]; simp
  have g3_8 : V3 8 = v 8 := by
    rw [hV3, hV2, hV1]; simp
  have h4 := flagNonzeroTM_hoareTime (r 2) (r 8) (r.ne (by decide))
      (v 1 - v 0 - 1) (v 8) inp₀ (regsWork r w₀ V3) ys hinp₀ (fun i _ => hpv V3 i)
      (by rw [regsWork_apply, g3_2]) (by rw [regsWork_apply, g3_8])
  rw [regsWork_update] at h4
  replace h4 := h4.mono_bound
    (show 2 * v 8 + 4 + 1 + ((v 1 - v 0 - 1) * ((2 * 1 + 4 + 1 + (2 * 0 + 4)) + 2) +
        ((v 1 - v 0 - 1) + 2)) ≤ 16 * B + 7 by
      have := hB 8; have := hB 1; omega)
  set V4 := Function.update V3 8 (min (v 1 - v 0 - 1) 1) with hV4
  -- S5: r6 := 1
  have g4_6 : V4 6 = v 6 := by
    rw [hV4, hV3, hV2, hV1]; simp
  have h5 := setOneTM_hoareTime (r 6) (v 6) inp₀ (regsWork r w₀ V4) ys hinp₀
      (fun i _ => hpv V4 i) (by rw [regsWork_apply, g4_6])
  rw [regsWork_update] at h5
  replace h5 := h5.mono_bound
    (show 2 * v 6 + 4 + 1 + (2 * 0 + 4) ≤ 2 * B + 9 by have := hB 6; omega)
  set V5 := Function.update V4 6 1 with hV5
  -- S6: r6 := 1 - gLT
  have g5_4 : V5 4 = (if v 0 < v 1 then 1 else 0) := by
    rw [hV5, hV4, hV3, hV2]; simp
  have g5_6 : V5 6 = 1 := by rw [hV5]; simp
  have h6 := subIntoTM_hoareTime (r 4) (r 6) (r.ne (by decide))
      (if v 0 < v 1 then 1 else 0) 1 inp₀ (regsWork r w₀ V5) ys hinp₀
      (fun i _ => hpv V5 i) (by rw [regsWork_apply, g5_4]) (by rw [regsWork_apply, g5_6])
  rw [regsWork_update] at h6
  replace h6 := h6.mono_bound
    (show (if v 0 < v 1 then 1 else 0) * ((2 * 1 + 4) + 2) +
        ((if v 0 < v 1 then 1 else 0) + 2) ≤ 11 by split_ifs <;> omega)
  set V6 := Function.update V5 6 (1 - if v 0 < v 1 then 1 else 0) with hV6
  -- S7: r6 := (1 - gLT) - gGT = [a = b]
  have g6_5 : V6 5 = (if v 1 < v 0 then 1 else 0) := by
    rw [hV6, hV5, hV4, hV3, hV2, hV1]; simp
  have g6_6 : V6 6 = 1 - (if v 0 < v 1 then 1 else 0) := by
    rw [hV6]; simp
  have h7 := subIntoTM_hoareTime (r 5) (r 6) (r.ne (by decide))
      (if v 1 < v 0 then 1 else 0) (1 - if v 0 < v 1 then 1 else 0) inp₀
      (regsWork r w₀ V6) ys hinp₀ (fun i _ => hpv V6 i)
      (by rw [regsWork_apply, g6_5]) (by rw [regsWork_apply, g6_6])
  rw [regsWork_update] at h7
  replace h7 := h7.mono_bound
    (show (if v 1 < v 0 then 1 else 0) * ((2 * (1 - if v 0 < v 1 then 1 else 0) + 4) + 2) +
        ((if v 1 < v 0 then 1 else 0) + 2) ≤ 11 by split_ifs <;> omega)
  set V7 := Function.update V6 6
      (1 - (if v 0 < v 1 then 1 else 0) - (if v 1 < v 0 then 1 else 0)) with hV7
  -- S8: r7 := gLT
  have g7_4 : V7 4 = (if v 0 < v 1 then 1 else 0) := by
    rw [hV7, hV6, hV5, hV4, hV3, hV2]; simp
  have g7_7 : V7 7 = v 7 := by
    rw [hV7, hV6, hV5, hV4, hV3, hV2, hV1]; simp
  have h8 := copyIntoTM_hoareTime (r 4) (r 7) (r.ne (by decide))
      (if v 0 < v 1 then 1 else 0) (v 7) inp₀ (regsWork r w₀ V7) ys hinp₀
      (fun i _ => hpv V7 i) (by rw [regsWork_apply, g7_4]) (by rw [regsWork_apply, g7_7])
  rw [regsWork_update] at h8
  replace h8 := h8.mono_bound
    (show (2 * v 7 + 4) + 1 + ((if v 0 < v 1 then 1 else 0) *
        ((2 * (0 + if v 0 < v 1 then 1 else 0) + 4) + 2) +
        ((if v 0 < v 1 then 1 else 0) + 2)) ≤ 2 * B + 16 by
      have := hB 7; split_ifs <;> omega)
  set V8 := Function.update V7 7 (if v 0 < v 1 then 1 else 0) with hV8
  -- S9: r7 := gLT - min ((b-a)-1) 1 = [a + 1 = b]
  have g8_8 : V8 8 = min (v 1 - v 0 - 1) 1 := by
    rw [hV8, hV7, hV6, hV5, hV4]; simp
  have g8_7 : V8 7 = (if v 0 < v 1 then 1 else 0) := by
    rw [hV8]; simp
  have h9 := subIntoTM_hoareTime (r 8) (r 7) (r.ne (by decide))
      (min (v 1 - v 0 - 1) 1) (if v 0 < v 1 then 1 else 0) inp₀
      (regsWork r w₀ V8) ys hinp₀ (fun i _ => hpv V8 i)
      (by rw [regsWork_apply, g8_8]) (by rw [regsWork_apply, g8_7])
  rw [regsWork_update] at h9
  replace h9 := h9.mono_bound
    (show min (v 1 - v 0 - 1) 1 * ((2 * (if v 0 < v 1 then 1 else 0) + 4) + 2) +
        (min (v 1 - v 0 - 1) 1 + 2) ≤ 11 by split_ifs <;> omega)
  set V9 := Function.update V8 7
      ((if v 0 < v 1 then 1 else 0) - min (v 1 - v 0 - 1) 1) with hV9
  -- the final vector is `guardVals v`
  have hfin : V9 = guardVals v := by
    funext k
    simp only [hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1, guardVals]
    fin_cases k <;> simp  <;> (try split_ifs) <;> omega
  rw [hfin] at h9
  -- chain
  have hres := seqEmit hinp₀ (hpv V1) h1 <|
    seqEmit hinp₀ (hpv V2) h2 <|
    seqEmit hinp₀ (hpv V3) h3 <|
    seqEmit hinp₀ (hpv V4) h4 <|
    seqEmit hinp₀ (hpv V5) h5 <|
    seqEmit hinp₀ (hpv V6) h6 <|
    seqEmit hinp₀ (hpv V7) h7 <|
    seqEmit hinp₀ (hpv V8) h8 h9
  exact hres.mono_bound (by generalize (B + 1) ^ 2 = X; omega)

/-- Stages 10–14: five guarded arms, each a single primitive. -/
def pairArmsTM (r : PairRegs n) : TM n :=
  seqTM (guardTM (incRegTM (r 0)) (r 4)) <|
  seqTM (guardTM (incRegTM (r 1)) (r 5)) <|
  seqTM (guardTM (incRegTM (r 1)) (r 6)) <|
  seqTM (guardTM (clearRegTM (r 1)) (r 7))
        (guardTM (clearRegTM (r 0)) (r 6))

/-- Register values after the whole machine: the successor in `0` and `1`, the guard
    phase's leftovers everywhere else. -/
def pairNextVals (v : Fin 9 → ℕ) : Fin 9 → ℕ := fun k =>
  if k = 0 then pairNextFst (v 0) (v 1)
  else if k = 1 then pairNextSnd (v 0) (v 1)
  else guardVals v k

theorem pairArmsTM_hoareTime (r : PairRegs n) (v : Fin 9 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB : ∀ k, v k ≤ B) :
    (pairArmsTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ (guardVals v)) ys)
      (EmitPred inp₀ (regsWork r w₀ (pairNextVals v)) ys)
      (10 * B + 69) := by
  set u := guardVals v with hu
  have hu0 : u 0 = v 0 := by rw [hu]; simp [guardVals]
  have hu1 : u 1 = v 1 := by rw [hu]; simp [guardVals]
  have hu4 : u 4 = (if v 0 < v 1 then 1 else 0) := by rw [hu]; simp [guardVals]
  have hu5 : u 5 = (if v 1 < v 0 then 1 else 0) := by rw [hu]; simp [guardVals]
  have hu6 : u 6 = (if v 0 = v 1 then 1 else 0) := by rw [hu]; simp [guardVals]
  have hu7 : u 7 = (if v 0 + 1 = v 1 then 1 else 0) := by rw [hu]; simp [guardVals]
  have q4 : u 4 ≤ 1 := by rw [hu4]; split_ifs <;> omega
  -- S10: a += gLT
  have a1 := guardRegArm r hinp₀ hpark u 0 4 (by decide) (u 0 + 1) (2 * u 0 + 4)
      (incRegTM (r 0)) q4
      (fun W hW hWj => incRegTM_hoareTime (r 0) (u 0) inp₀ W ys hinp₀ (fun i _ => hW i) hWj)
  replace a1 := a1.mono_bound (show u 4 * (2 * u 0 + 4 + 2) + (u 4 + 2) ≤ 2 * B + 13 by
    have h2 : u 0 ≤ B := by rw [hu0]; exact hB 0
    calc u 4 * (2 * u 0 + 4 + 2) + (u 4 + 2)
        ≤ 1 * (2 * B + 4 + 2) + (1 + 2) :=
          Nat.add_le_add (Nat.mul_le_mul q4 (by omega)) (by omega)
      _ ≤ 2 * B + 13 := by omega)
  set U1 := (if u 4 = 0 then u else Function.update u 0 (u 0 + 1)) with hU1
  have c1_0 : U1 0 = (if v 0 < v 1 then v 0 + 1 else v 0) := by
    rw [hU1, hu4]; by_cases h : v 0 < v 1 <;> simp [h, hu0]
  have c1_1 : U1 1 = v 1 := by
    rw [hU1, hu4]; by_cases h : v 0 < v 1 <;> simp [h, hu1]
  have p1_5 : U1 5 = (if v 1 < v 0 then 1 else 0) := by
    rw [hU1, hu4]; by_cases h : v 0 < v 1 <;> simp [h, hu5]
  have p1_6 : U1 6 = (if v 0 = v 1 then 1 else 0) := by
    rw [hU1, hu4]; by_cases h : v 0 < v 1 <;> simp [h, hu6]
  have p1_7 : U1 7 = (if v 0 + 1 = v 1 then 1 else 0) := by
    rw [hU1, hu4]; by_cases h : v 0 < v 1 <;> simp [h, hu7]
  have n1_1 : U1 1 ≤ B := by rw [c1_1]; exact hB 1
  have q1_5 : U1 5 ≤ 1 := by rw [p1_5]; split_ifs <;> omega
  -- S11: b += gGT
  have a2 := guardRegArm r hinp₀ hpark U1 1 5 (by decide) (U1 1 + 1) (2 * U1 1 + 4)
      (incRegTM (r 1)) q1_5
      (fun W hW hWj => incRegTM_hoareTime (r 1) (U1 1) inp₀ W ys hinp₀ (fun i _ => hW i) hWj)
  replace a2 := a2.mono_bound (show U1 5 * (2 * U1 1 + 4 + 2) + (U1 5 + 2) ≤ 2 * B + 13 by
    calc U1 5 * (2 * U1 1 + 4 + 2) + (U1 5 + 2)
        ≤ 1 * (2 * B + 4 + 2) + (1 + 2) :=
          Nat.add_le_add (Nat.mul_le_mul q1_5 (by omega)) (by omega)
      _ ≤ 2 * B + 13 := by omega)
  set U2 := (if U1 5 = 0 then U1 else Function.update U1 1 (U1 1 + 1)) with hU2
  have c2_0 : U2 0 = (if v 0 < v 1 then v 0 + 1 else v 0) := by
    rw [hU2, p1_5]; by_cases h : v 1 < v 0 <;> simp [h, c1_0]
  have c2_1 : U2 1 = (if v 1 < v 0 then v 1 + 1 else v 1) := by
    rw [hU2, p1_5]; by_cases h : v 1 < v 0 <;> simp [h, c1_1]
  have p2_6 : U2 6 = (if v 0 = v 1 then 1 else 0) := by
    rw [hU2, p1_5]; by_cases h : v 1 < v 0 <;> simp [h, p1_6]
  have p2_7 : U2 7 = (if v 0 + 1 = v 1 then 1 else 0) := by
    rw [hU2, p1_5]; by_cases h : v 1 < v 0 <;> simp [h, p1_7]
  have n2_1 : U2 1 ≤ B + 1 := by have := hB 1; rw [c2_1]; split_ifs <;> omega
  have q2_6 : U2 6 ≤ 1 := by rw [p2_6]; split_ifs <;> omega
  -- S12: b += gEQ
  have a3 := guardRegArm r hinp₀ hpark U2 1 6 (by decide) (U2 1 + 1) (2 * U2 1 + 4)
      (incRegTM (r 1)) q2_6
      (fun W hW hWj => incRegTM_hoareTime (r 1) (U2 1) inp₀ W ys hinp₀ (fun i _ => hW i) hWj)
  replace a3 := a3.mono_bound (show U2 6 * (2 * U2 1 + 4 + 2) + (U2 6 + 2) ≤ 2 * B + 13 by
    calc U2 6 * (2 * U2 1 + 4 + 2) + (U2 6 + 2)
        ≤ 1 * (2 * (B + 1) + 4 + 2) + (1 + 2) :=
          Nat.add_le_add (Nat.mul_le_mul q2_6 (by omega)) (by omega)
      _ ≤ 2 * B + 13 := by omega)
  set U3 := (if U2 6 = 0 then U2 else Function.update U2 1 (U2 1 + 1)) with hU3
  have c3_0 : U3 0 = (if v 0 < v 1 then v 0 + 1 else v 0) := by
    rw [hU3, p2_6]; by_cases h : v 0 = v 1 <;> simp [h, c2_0]
  have c3_1 : U3 1 = (if v 0 < v 1 then v 1 else v 1 + 1) := by
    rw [hU3, p2_6]; by_cases h : v 0 = v 1 <;>
      simp [h, c2_1] <;> split_ifs <;> omega
  have p3_6 : U3 6 = (if v 0 = v 1 then 1 else 0) := by
    rw [hU3, p2_6]; by_cases h : v 0 = v 1 <;> simp [h, p2_6]
  have p3_7 : U3 7 = (if v 0 + 1 = v 1 then 1 else 0) := by
    rw [hU3, p2_6]; by_cases h : v 0 = v 1 <;> simp [h, p2_7]
  have n3_1 : U3 1 ≤ B + 1 := by have := hB 1; rw [c3_1]; split_ifs <;> omega
  have q3_7 : U3 7 ≤ 1 := by rw [p3_7]; split_ifs <;> omega
  -- S13: b := 0 when a + 1 = b
  have a4 := guardRegArm r hinp₀ hpark U3 1 7 (by decide) 0 (2 * U3 1 + 4)
      (clearRegTM (r 1)) q3_7
      (fun W hW hWj => clearRegTM_hoareTime (r 1) (U3 1) inp₀ W ys hinp₀ (fun i _ => hW i) hWj)
  replace a4 := a4.mono_bound (show U3 7 * (2 * U3 1 + 4 + 2) + (U3 7 + 2) ≤ 2 * B + 13 by
    calc U3 7 * (2 * U3 1 + 4 + 2) + (U3 7 + 2)
        ≤ 1 * (2 * (B + 1) + 4 + 2) + (1 + 2) :=
          Nat.add_le_add (Nat.mul_le_mul q3_7 (by omega)) (by omega)
      _ ≤ 2 * B + 13 := by omega)
  set U4 := (if U3 7 = 0 then U3 else Function.update U3 1 0) with hU4
  have c4_0 : U4 0 = (if v 0 < v 1 then v 0 + 1 else v 0) := by
    rw [hU4, p3_7]; by_cases h : v 0 + 1 = v 1 <;> simp [h, c3_0]
  have c4_1 : U4 1 = (if v 0 + 1 = v 1 then 0 else if v 0 < v 1 then v 1 else v 1 + 1) := by
    rw [hU4, p3_7]; by_cases h : v 0 + 1 = v 1 <;> simp [h, c3_1]
  have p4_6 : U4 6 = (if v 0 = v 1 then 1 else 0) := by
    rw [hU4, p3_7]; by_cases h : v 0 + 1 = v 1 <;> simp [h, p3_6]
  have n4_0 : U4 0 ≤ B + 1 := by have := hB 0; rw [c4_0]; split_ifs <;> omega
  have q4_6 : U4 6 ≤ 1 := by rw [p4_6]; split_ifs <;> omega
  -- S14: a := 0 when a = b
  have a5 := guardRegArm r hinp₀ hpark U4 0 6 (by decide) 0 (2 * U4 0 + 4)
      (clearRegTM (r 0)) q4_6
      (fun W hW hWj => clearRegTM_hoareTime (r 0) (U4 0) inp₀ W ys hinp₀ (fun i _ => hW i) hWj)
  replace a5 := a5.mono_bound (show U4 6 * (2 * U4 0 + 4 + 2) + (U4 6 + 2) ≤ 2 * B + 13 by
    calc U4 6 * (2 * U4 0 + 4 + 2) + (U4 6 + 2)
        ≤ 1 * (2 * (B + 1) + 4 + 2) + (1 + 2) :=
          Nat.add_le_add (Nat.mul_le_mul q4_6 (by omega)) (by omega)
      _ ≤ 2 * B + 13 := by omega)
  set U5 := (if U4 6 = 0 then U4 else Function.update U4 0 0) with hU5
  have out0 : U5 0 = pairNextFst (v 0) (v 1) := by
    rw [hU5, p4_6]
    by_cases h : v 0 = v 1 <;>
      simp [h, c4_0, pairNextFst_eq] <;> split_ifs <;> omega
  have out1 : U5 1 = pairNextSnd (v 0) (v 1) := by
    rw [hU5, p4_6]
    by_cases h : v 0 = v 1 <;>
      simp [h, c4_1, pairNextSnd_eq] <;> split_ifs <;> omega
  have hother : ∀ k : Fin 9, k ≠ 0 → k ≠ 1 → U5 k = u k := by
    intro k h0 h1
    rw [hU5, hU4, hU3, hU2, hU1]
    split_ifs <;> simp [h0, h1]
  have hfin : U5 = pairNextVals v := by
    funext k
    by_cases hk0 : k = 0
    · subst hk0; rw [out0]; simp [pairNextVals]
    · by_cases hk1 : k = 1
      · subst hk1; rw [out1]; simp [pairNextVals]
      · rw [hother k hk0 hk1, hu]; simp [pairNextVals, hk0, hk1]
  rw [hfin] at a5
  have hres := seqEmit hinp₀ (parked_regsWork r hpark U1) a1 <|
    seqEmit hinp₀ (parked_regsWork r hpark U2) a2 <|
    seqEmit hinp₀ (parked_regsWork r hpark U3) a3 <|
    seqEmit hinp₀ (parked_regsWork r hpark U4) a4 a5
  exact hres.mono_bound (by omega)

/-! ### The machine, in two phases -/

/-- `(a, b) := (pairNextFst a b, pairNextSnd a b)`: compute the guards from the pristine
    inputs, then run the guarded arms. -/
def pairNextTM (r : PairRegs n) : TM n := seqTM (pairGuardTM r) (pairArmsTM r)


/-! ### The whole machine -/

/-- **`pairNextTM` Hoare specification.** From `(a, b)` in registers `0` and `1` and any
    values in the other seven, reach `(pairNextFst a b, pairNextSnd a b)`, in a number of
    steps quadratic in a bound `B` on every register value.

    The postcondition names the final state of *all nine* registers explicitly
    (`pairNextVals`), and every entry is determined — no choice, no existential — which is
    what lets an iterated caller name the state after each step. Registers outside the nine
    are untouched, and `OutAcc ys` is carried through unchanged. -/
theorem pairNextTM_hoareTime (r : PairRegs n) (v : Fin 9 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB : ∀ k, v k ≤ B) :
    (pairNextTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (pairNextVals v)) ys)
      (80 * (B + 1) ^ 2 + 32 * B + 147) :=
  (seqEmit hinp₀ (parked_regsWork r hpark (guardVals v))
    (pairGuardTM_hoareTime r v B inp₀ w₀ ys hinp₀ hpark hB)
    (pairArmsTM_hoareTime r v B inp₀ w₀ ys hinp₀ hpark hB)).mono_bound (by omega)

/-- **Normalized runtime.** A single quadratic in the size parameter, which is the form an
    iterated caller wants: `k` successor steps on values all `≤ B` cost
    `k * 400 * (B + 1) ^ 2`. -/
theorem pairNextTM_hoareTime_poly (r : PairRegs n) (v : Fin 9 → ℕ) (B : ℕ)
    (inp₀ : Tape) (w₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (w₀ i))
    (hB : ∀ k, v k ≤ B) :
    (pairNextTM r).HoareTime
      (EmitPred inp₀ (regsWork r w₀ v) ys)
      (EmitPred inp₀ (regsWork r w₀ (pairNextVals v)) ys)
      (400 * (B + 1) ^ 2) :=
  (pairNextTM_hoareTime r v B inp₀ w₀ ys hinp₀ hpark hB).mono_bound
    (by have h : (B + 1) ^ 2 = B * B + 2 * B + 1 := by ring
        omega)

/-- **The machine computes the pairing successor.** Combined with
    `pairNextTM_hoareTime`, this is what makes iterating `pairNextTM` compute
    `Nat.unpair`: starting from `(0, 0)` — the pair coded by `0` — `k` steps land on the
    pair coded by `k`. -/
theorem pair_pairNext (a b : ℕ) :
    Nat.pair (pairNextFst a b) (pairNextSnd a b) = Nat.pair a b + 1 := by
  have hsq : ∀ x : ℕ, (x + 1) * (x + 1) = x * x + 2 * x + 1 := fun x => by ring
  unfold pairNextFst pairNextSnd Nat.pair
  rcases lt_trichotomy a b with h | h | h
  · rcases Nat.lt_or_ge (a + 1) b with h2 | h2
    · split_ifs <;> omega
    · have he : a + 1 = b := by omega
      subst he
      have := hsq a
      split_ifs <;> omega
  · subst h
    have := hsq a
    split_ifs <;> omega
  · split_ifs <;> omega

/-- The two output registers, read off the postcondition. -/
theorem pairNextVals_zero (v : Fin 9 → ℕ) :
    pairNextVals v 0 = pairNextFst (v 0) (v 1) := by simp [pairNextVals]

@[inherit_doc pairNextVals_zero]
theorem pairNextVals_one (v : Fin 9 → ℕ) :
    pairNextVals v 1 = pairNextSnd (v 0) (v 1) := by simp [pairNextVals]

/-- One step of the machine advances the pair code by exactly one. -/
theorem pair_pairNextVals (v : Fin 9 → ℕ) :
    Nat.pair (pairNextVals v 0) (pairNextVals v 1) = Nat.pair (v 0) (v 1) + 1 := by
  rw [pairNextVals_zero, pairNextVals_one, pair_pairNext]

end TM

end Complexity
