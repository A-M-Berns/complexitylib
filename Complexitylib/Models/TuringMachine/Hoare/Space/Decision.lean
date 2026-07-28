/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.TuringMachine.Hoare.Space.Decision.Internal

/-!
# Decision-space bridges from fresh-start Hoare contracts

These theorems package the exact obligations required by
`TM.DecidesInSpace`.  `TM.HoareSpace` supplies honest all-reachable input/work
head bounds, while a separate all-reachable output-head hypothesis supplies
the additional decision-space charge.  Endpoint correctness alone is
deliberately insufficient.

## Main results

- `TM.decidesInSpace_of_hoareSpace` — combine separate space, total
  correctness, and output-head obligations.
- `TM.decidesInSpace_of_hoareTimeSpace` — obtain termination and verdict
  correctness from fresh-start time-and-space Hoare contracts.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Fresh-start auxiliary-space, total correctness, and all-prefix output-head
bounds together prove `TM.DecidesInSpace`. -/
theorem decidesInSpace_of_hoareSpace
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
    tm.DecidesInSpace L S :=
  decidesInSpace_of_hoareSpace_internal hspace hcorrect houtput

/-- Fresh-start time-and-space Hoare contracts prove `TM.DecidesInSpace` once
their postcondition implies verdict correctness and the output head is bounded
at every reachable configuration. -/
theorem decidesInSpace_of_hoareTimeSpace
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
    tm.DecidesInSpace L S :=
  decidesInSpace_of_hoareTimeSpace_internal h hcorrect houtput

end TM

end Complexity
