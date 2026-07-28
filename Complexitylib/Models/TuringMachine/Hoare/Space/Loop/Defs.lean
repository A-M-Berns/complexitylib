/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Hoare.Space.Defs

/-!
# All-prefix space certificates for the generic loop combinator

This file packages the local obligation needed to prove an honest
all-reachable space bound for `TM.loopTM`.  From every invariant loop boundary,
one certified segment either halts or returns to the loop start with a strictly
smaller natural variant.  Every prefix of that segment must fit the common
auxiliary-space budget.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- One-segment all-prefix space certificate for `loopTM`.

The segment begins at the loop start with tapes satisfying `invariant`.  It
either reaches a halted configuration or returns to the loop start with the
invariant preserved and `variant` strictly decreased.  The `prefixWithin`
component is deliberately part of the certificate: a terminal head bound is
not enough to prove `TM.HoareSpace`. -/
structure LoopIterationSpaceSpec (tmBody tmTest : TM n)
    (invariant : TapePred n)
    (variant : Tape → (Fin n → Tape) → Tape → ℕ)
    (inputLength spaceBound : ℕ) where
  /-- Exact iteration segment, its all-prefix bound, and its outcome. -/
  iteration : ∀ inp work out, invariant inp work out →
    ∃ (time : ℕ) (finish : Cfg n (loopTM tmBody tmTest).Q),
      (loopTM tmBody tmTest).reachesIn time
        { state := (loopTM tmBody tmTest).qstart,
          input := inp, work := work, output := out } finish ∧
      (∀ (steps : ℕ) (cfg : Cfg n (loopTM tmBody tmTest).Q),
        steps ≤ time →
        (loopTM tmBody tmTest).reachesIn steps
          { state := (loopTM tmBody tmTest).qstart,
            input := inp, work := work, output := out } cfg →
        cfg.WithinAuxSpace inputLength spaceBound) ∧
      ((loopTM tmBody tmTest).halted finish ∨
        ∃ inp' work' out',
          finish =
            { state := (loopTM tmBody tmTest).qstart,
              input := inp', work := work', output := out' } ∧
          invariant inp' work' out' ∧
          variant inp' work' out' < variant inp work out)

end TM

end Complexity
