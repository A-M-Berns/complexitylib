/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Registers.Compare

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

variable {n : ℕ}

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
abbrev PairRegs (n : ℕ) := Fin 9 ↪ Fin n

/-- Distinct indices name distinct registers. Discharges every side condition of the form
    `r i ≠ r j` by `r.ne (by decide)`. -/
lemma PairRegs.ne (r : PairRegs n) {i j : Fin 9} (h : i ≠ j) : r i ≠ r j :=
  fun e => h (r.injective e)

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
noncomputable def regsWork (r : PairRegs n) (w₀ : Fin n → Tape) (v : Fin 9 → ℕ) :
    Fin n → Tape :=
  fun i => if h : ∃ k, r k = i then regTape (v h.choose) else w₀ i

/-- Reading a named register. -/
lemma regsWork_apply (r : PairRegs n) (w₀ : Fin n → Tape) (v : Fin 9 → ℕ) (k : Fin 9) :
    regsWork r w₀ v (r k) = regTape (v k) := by
  have h : ∃ j, r j = r k := ⟨k, rfl⟩
  rw [regsWork, dif_pos h, r.injective h.choose_spec]

/-- Registers outside the nine are untouched. -/
lemma regsWork_of_ne (r : PairRegs n) (w₀ : Fin n → Tape) (v : Fin 9 → ℕ) {i : Fin n}
    (hi : ∀ k, r k ≠ i) : regsWork r w₀ v i = w₀ i := by
  rw [regsWork, dif_neg]
  rintro ⟨k, rfl⟩
  exact hi k rfl

/-- **The stage step.** Updating one named register of the state is updating one entry of
    the value vector — which is what turns the fourteen-stage bookkeeping into finite
    data. -/
lemma regsWork_update (r : PairRegs n) (w₀ : Fin n → Tape) (v : Fin 9 → ℕ) (k : Fin 9)
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

/-- A register-indexed state over a parked base is everywhere parked. -/
lemma parked_regsWork (r : PairRegs n) {w₀ : Fin n → Tape} (h : ∀ i, Parked (w₀ i))
    (v : Fin 9 → ℕ) : ∀ i, Parked (regsWork r w₀ v i) := by
  intro i
  rw [regsWork]
  split
  · exact parked_regTape _
  · exact h i

/-- `(a, b) := (pairNextFst a b, pairNextSnd a b)`.

    Nine stages compute the four guards from the pristine inputs, then five guarded arms
    mutate. Every arm is a single primitive: no arm copies a live register, so the arms
    commute with each other except for the two `(increment, clear)` pairs on `a` and on
    `b`, which are ordered increment-first here. -/
def pairNextTM (r : PairRegs n) : TM n :=
  seqTM (ltFlagTM (r 1) (r 0) (r 3) (r 5)) <|
  seqTM (ltFlagTM (r 0) (r 1) (r 2) (r 4)) <|
  seqTM (decRegTM (r 2)) <|
  seqTM (flagNonzeroTM (r 2) (r 8)) <|
  seqTM (setOneTM (r 6)) <|
  seqTM (subIntoTM (r 4) (r 6)) <|
  seqTM (subIntoTM (r 5) (r 6)) <|
  seqTM (copyIntoTM (r 4) (r 7)) <|
  seqTM (subIntoTM (r 8) (r 7)) <|
  seqTM (guardTM (incRegTM (r 0)) (r 4)) <|
  seqTM (guardTM (incRegTM (r 1)) (r 5)) <|
  seqTM (guardTM (incRegTM (r 1)) (r 6)) <|
  seqTM (guardTM (clearRegTM (r 1)) (r 7))
        (guardTM (clearRegTM (r 0)) (r 6))

end TM

end Complexity
