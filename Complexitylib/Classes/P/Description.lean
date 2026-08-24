/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.NormalForm
public import Complexitylib.Models.TuringMachine.Deterministic
public import Complexitylib.Models.TuringMachine.UTM.Internal.Interp

/-!
# Every polynomial-time function has a finite description

`FP` quantifies over machines, and a `Complexity.TM k` is not finite data: its state type is
a bundled `Type` and its tapes are functions `ℕ → Γ`. `TMDesc` *is* finite data — a state
bit-width, two state numbers, and a transition table — so it is what an enumeration, a
Gödel coding, or an executable interpreter can range over.

This file closes the gap, assembling three existing results:

* `mem_FP_iff_computesInTime_polynomial` — an `FP` witness may be taken with a running-time
  bound that is a natural-coefficient polynomial evaluation, valid at *every* input length
  rather than asymptotically;
* `TM.exists_singleTape_computesInTime` — the multi-tape → single-tape reduction, in its
  function-computation form;
* `TM.exists_wf_desc_computesInTime` — extraction of a well-formed description from a
  single-work-tape machine, preserving the function and the time bound exactly.

## Main result

- `exists_desc_computesInTime_polynomial` — every `f ∈ FP` is computed by an interpreted
  well-formed `TMDesc` within a polynomial-evaluation time bound.

The bound stays an explicit polynomial rather than an `=O` class, because the intended
consumers — enumerations indexed by a description together with a clock — need a bound that
holds at every input length, not eventually.
-/


public section

namespace Complexity

/-- **Every polynomial-time function has a finite description.** For `f ∈ FP` there is a
well-formed `TMDesc` whose interpretation computes `f` within the evaluation of a
natural-coefficient polynomial — a bound valid at every input length.

The polynomial is explicit: if `f` is computed by a `k`-work-tape machine within `p.eval`,
the description runs within `16 * (k + 1) * (p + X + 1) ^ 2`, the single-tape simulation's
quadratic overhead. -/
theorem exists_desc_computesInTime_polynomial {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ (d : TMDesc) (q : Polynomial ℕ), d.WF ∧ d.toTM.ComputesInTime f q.eval := by
  obtain ⟨k, tm, p, hp⟩ := mem_FP_iff_computesInTime_polynomial.mp hf
  obtain ⟨M₁, hM₁⟩ := TM.exists_singleTape_computesInTime tm hp
  obtain ⟨d, hwf, hd⟩ := TM.exists_wf_desc_computesInTime M₁ hM₁
  refine ⟨d, Polynomial.C (16 * (k + 1)) * (p + Polynomial.X + 1) ^ 2, hwf, ?_⟩
  have hq : (Polynomial.C (16 * (k + 1)) * (p + Polynomial.X + 1) ^ 2).eval
      = NTM.singleTapeSimTime k p.eval := by
    funext n
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C,
      NTM.singleTapeSimTime]
  rw [hq]
  exact hd

end Complexity
