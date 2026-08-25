/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Registers.Arith
public import Mathlib.Tactic.Ring

/-!
# Guarded commands and comparison over unary registers

Two pieces that together give register arithmetic ordinary structured control flow.

`guardTM` runs a machine at most once, under a register constrained to `{0, 1}`. This is
the register library's conditional. It is *not* built on `ifTM`: `ifTM` branches on the
**output** tape's cell 1, but `EmitPred`'s third conjunct `OutAcc` reserves the output tape
as an append-only emission accumulator whose cells past the emitted prefix must all be
blank, so an `ifTM` test destroys the very invariant every register spec carries.
`forRegTM`, by contrast, branches on a *work* register and never touches the output tape —
so a register holding `0` or `1` already *is* a guarded command, and no new combinator is
needed.

`ltFlagTM` is the comparison that produces such a flag: `flag := if a < b then 1 else 0`,
computed as `min (b - a) 1` from `copyIntoTM`, `subIntoTM` and `flagNonzeroTM`. Truncated
subtraction floors at zero, so no separate underflow test is needed.

Both time bounds are stated exactly, as elsewhere in this directory, and then normalized
against a single size parameter (`ltFlagTime_le`) — the shape iterated callers want.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-! ### Plumbing

Two patterns that every multi-stage register machine repeats once per stage. Extracting
them is worth it purely by line count: `parked_update` replaces a five-line `by_cases`
and `seqEmit` a four-line `emitPred_transition` closure, at every one of a dozen-odd
composition points. -/

/-- Updating a register of an everywhere-parked work state with a register tape leaves it
    everywhere parked. The side condition every register spec asks for. -/
lemma parked_update {w : Fin n → Tape} (h : ∀ i, Parked (w i)) (q : Fin n) (v : ℕ) :
    ∀ i, Parked (Function.update w q (regTape v) i) := by
  intro i
  by_cases hi : i = q
  · subst hi; rw [Function.update_self]; exact parked_regTape _
  · rw [Function.update_of_ne hi]; exact h i

/-- Sequence two `EmitPred`-shaped register machines. Packages the frame step
    (`emitPred_transition`) that `seqTM_hoareTime` demands at every composition point,
    whose only real content is that the intermediate work state is everywhere parked. -/
theorem seqEmit {tm₁ tm₂ : TM n} {inp₀ : Tape} {w₀ w₁ w₂ : Fin n → Tape}
    {ys : List Bool} {b₁ b₂ : ℕ}
    (hinp₀ : Parked inp₀) (hw₁ : ∀ i, Parked (w₁ i))
    (h₁ : tm₁.HoareTime (EmitPred inp₀ w₀ ys) (EmitPred inp₀ w₁ ys) b₁)
    (h₂ : tm₂.HoareTime (EmitPred inp₀ w₁ ys) (EmitPred inp₀ w₂ ys) b₂) :
    (seqTM tm₁ tm₂).HoareTime (EmitPred inp₀ w₀ ys) (EmitPred inp₀ w₂ ys) (b₁ + 1 + b₂) :=
  seqTM_hoareTime _ _ h₁
    (fun inp work out h => emitPred_transition hinp₀ hw₁ ys _ _ _ h) h₂

/-! ### Guarded commands -/

/-- Run `body` at most once, guarded by a register holding `0` or `1`.

    Definitionally `forRegTM`; the separate name records the *intent* (and the `{0,1}`
    side condition, which lives in `guardTM_hoareTime`). -/
def guardTM (body : TM n) (flag : Fin n) : TM n := forRegTM body flag

/-- **`guardTM` Hoare specification.** With `flag` holding `g ≤ 1`, the machine goes from
    `work₀` to `workT` when `g = 1` and stays at `work₀` when `g = 0`.

    The body is specified against the loop's *cursor* state for `flag` — the tape
    `⟨2, regCells g⟩` that `forRegTM` parks there mid-iteration — which is what lets the
    body be any machine that leaves `flag` alone. -/
theorem guardTM_hoareTime (body : TM n) (flag : Fin n) (g b_body : ℕ) (hg : g ≤ 1)
    (inp₀ : Tape) (work₀ workT : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀)
    (hP₀ : ∀ j, j ≠ flag → Parked (work₀ j))
    (hPT : ∀ j, j ≠ flag → Parked (workT j))
    (hf₀ : work₀ flag = regTape g) (hfT : workT flag = regTape g)
    (hbody : body.HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update work₀ flag ⟨0 + 2, regCells g⟩ ∧ OutAcc ys out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update workT flag ⟨0 + 2, regCells g⟩ ∧ OutAcc ys out)
      b_body) :
    (guardTM body flag).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ (if g = 0 then work₀ else workT) ys)
      (g * (b_body + 2) + (g + 2)) := by
  have hloop := forRegTM_hoareTime body flag g inp₀
    (fun i => if i = 0 then work₀ else workT) (fun _ => ys) b_body hinp₀
    (fun i => by split <;> assumption)
    (fun i j hj => by split <;> [exact hP₀ j hj; exact hPT j hj])
    (fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using hbody)
  simpa [guardTM] using hloop

/-- A guard costs its body plus a constant. -/
lemma guardTM_bound_le (g b : ℕ) (hg : g ≤ 1) : g * (b + 2) + (g + 2) ≤ b + 5 := by
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · omega
  · have : g = 1 := by omega
    subst this; omega

/-! ### Comparison -/

/-- `min (b - a) 1` is the indicator of `a < b`: truncated subtraction is nonzero exactly
    when the subtrahend is strictly smaller. -/
lemma min_sub_one_eq_ite (a b : ℕ) : min (b - a) 1 = if a < b then 1 else 0 := by
  by_cases h : a < b <;> simp only [h, if_true, if_false] <;> omega

/-- `flag := if a < b then 1 else 0`, where `a` is in `ra` and `b` is in `rb`.

    `sc` is a scratch register, left holding `b - a`; `ra` and `rb` are untouched. -/
def ltFlagTM (ra rb sc flag : Fin n) : TM n :=
  seqTM (copyIntoTM rb sc) (seqTM (subIntoTM ra sc) (flagNonzeroTM sc flag))

/-- Exact step count of `ltFlagTM` on inputs `a`, `b` with `s` in scratch and `f` in the
    flag register. -/
def ltFlagTime (a b s f : ℕ) : ℕ :=
  ((2 * s + 4) + 1 + (b * ((2 * (0 + b) + 4) + 2) + (b + 2))) + 1 +
    ((a * ((2 * b + 4) + 2) + (a + 2)) + 1 +
      (2 * f + 4 + 1 +
        ((b - a) * ((2 * 1 + 4 + 1 + (2 * 0 + 4)) + 2) + ((b - a) + 2))))

/-- **`ltFlagTM` Hoare specification.** From `regTape a` in `ra` and `regTape b` in `rb`,
    reach `regTape (if a < b then 1 else 0)` in `flag`, with `sc` left holding `b - a`.

    Everything else is untouched: the postcondition's work function updates only `sc` and
    `flag`, so a caller reads `ra`, `rb` and any other register straight back out of
    `work₀` via `Function.update_of_ne`. `OutAcc ys` is carried through unchanged. -/
theorem ltFlagTM_hoareTime (ra rb sc flag : Fin n)
    (hra : ra ≠ sc) (hrb : rb ≠ sc) (hsf : sc ≠ flag)
    (a b s f : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hpark : ∀ i, Parked (work₀ i))
    (hA : work₀ ra = regTape a) (hB : work₀ rb = regTape b)
    (hS : work₀ sc = regTape s) (hF : work₀ flag = regTape f) :
    (ltFlagTM ra rb sc flag).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update (Function.update work₀ sc (regTape (b - a))) flag
          (regTape (if a < b then 1 else 0))) ys)
      (ltFlagTime a b s f) := by
  have hcopy := copyIntoTM_hoareTime rb sc hrb b s inp₀ work₀ ys hinp₀
    (fun i _ => hpark i) hB hS
  have hpark₁ := parked_update hpark sc b
  have hsub := subIntoTM_hoareTime ra sc hra a b inp₀
    (Function.update work₀ sc (regTape b)) ys hinp₀ (fun i _ => hpark₁ i)
    (by rw [Function.update_of_ne hra]; exact hA)
    (by rw [Function.update_self])
  have hupd : Function.update (Function.update work₀ sc (regTape b)) sc
      (regTape (b - a)) = Function.update work₀ sc (regTape (b - a)) := by
    rw [Function.update_idem]
  rw [hupd] at hsub
  have hpark₂ := parked_update hpark sc (b - a)
  have hflg := flagNonzeroTM_hoareTime sc flag hsf (b - a) f inp₀
    (Function.update work₀ sc (regTape (b - a))) ys hinp₀ (fun i _ => hpark₂ i)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne (Ne.symm hsf)]; exact hF)
  rw [min_sub_one_eq_ite] at hflg
  have hres := seqEmit hinp₀ hpark₁ hcopy (seqEmit hinp₀ hpark₂ hsub hflg)
  exact hres.mono_bound (Nat.le_of_eq (by simp only [ltFlagTime]))

/-- **Normalized comparison runtime.** Against a single size parameter `B` bounding every
    register value, `ltFlagTM` runs in `40 * (B + 1) ^ 2` steps.

    This is the shape iterated callers want: a bound depending only on `B`, so that a loop
    running `k` comparisons on values all `≤ B` costs `k * 40 * (B + 1) ^ 2`. -/
lemma ltFlagTime_le (a b s f B : ℕ) (ha : a ≤ B) (hb : b ≤ B) (hs : s ≤ B) (hf : f ≤ B) :
    ltFlagTime a b s f ≤ 40 * (B + 1) ^ 2 := by
  have hba : b - a ≤ B := le_trans (Nat.sub_le b a) hb
  have m1 : b * b ≤ B * B := Nat.mul_le_mul hb hb
  have m2 : a * b ≤ B * B := Nat.mul_le_mul ha hb
  have key : ltFlagTime a b s f ≤ 4 * (B * B) + 32 * B + 18 := by
    have e1 : b * (2 * (0 + b) + 4 + 2) = 2 * (b * b) + 6 * b := by ring
    have e2 : a * (2 * b + 4 + 2) = 2 * (a * b) + 6 * a := by ring
    have e3 : (b - a) * (2 * 1 + 4 + 1 + (2 * 0 + 4) + 2) = 13 * (b - a) := by ring
    simp only [ltFlagTime, e1, e2, e3]
    omega
  have hsq : (B + 1) ^ 2 = B * B + 2 * B + 1 := by ring
  rw [hsq]
  omega

end TM

end Complexity
