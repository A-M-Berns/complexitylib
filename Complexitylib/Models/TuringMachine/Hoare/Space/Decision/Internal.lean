/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space.Defs

/-!
# Decision-space bridges from fresh-start Hoare contracts — proof internals
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Internal bridge from separate fresh-start auxiliary-space, correctness,
and all-prefix output-head obligations to `TM.DecidesInSpace`. -/
theorem decidesInSpace_of_hoareSpace_internal
    {tm : TM n} {L : Language} {S : ℕ → ℕ}
    (hspace : ∀ (x : List Bool), tm.HoareSpace
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      x.length (S x.length))
    (hcorrect : ∀ x, ∃ cfg, tm.reaches (tm.initCfg x) cfg ∧
      tm.halted cfg ∧
      (x ∈ L → cfg.output.cells 1 = Γ.one) ∧
      (x ∉ L → cfg.output.cells 1 = Γ.zero))
    (houtput : ∀ x cfg, tm.reaches (tm.initCfg x) cfg →
      cfg.output.head ≤ S x.length + 1) :
    tm.DecidesInSpace L S := by
  constructor
  · intro x cfg hreach
    constructor
    · exact hspace x _ _ _ ⟨rfl, rfl, rfl⟩ cfg hreach
    · exact houtput x cfg hreach
  · exact hcorrect

/-- Internal specialization in which termination and verdict correctness come
from a time-and-space Hoare contract. -/
theorem decidesInSpace_of_hoareTimeSpace_internal
    {tm : TM n} {L : Language} {T S : ℕ → ℕ}
    {post : List Bool → TapePred n}
    (h : ∀ (x : List Bool), tm.HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (post x)
      (T x.length) x.length (S x.length))
    (hcorrect : ∀ x inp work out, post x inp work out →
      (x ∈ L → out.cells 1 = Γ.one) ∧
      (x ∉ L → out.cells 1 = Γ.zero))
    (houtput : ∀ x cfg, tm.reaches (tm.initCfg x) cfg →
      cfg.output.head ≤ S x.length + 1) :
    tm.DecidesInSpace L S := by
  apply decidesInSpace_of_hoareSpace_internal
    (fun x => (h x).2) ?_ houtput
  intro x
  obtain ⟨cfg, _time, _htime, hreach, hhalt, hpost⟩ :=
    (h x).1 _ _ _ ⟨rfl, rfl, rfl⟩
  exact ⟨cfg, TM.reaches_of_reachesIn hreach, hhalt,
    hcorrect x cfg.input cfg.work cfg.output hpost⟩

end TM

end Complexity
