/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space.Loop.Defs
import Complexitylib.Models.TuringMachine.Hoare.Space.Loop.Internal

/-!
# All-prefix space certificates for the generic loop combinator

`TM.LoopIterationSpaceSpec` packages an exact loop segment from each invariant
boundary together with bounds for every segment prefix.  A halted outcome ends
the run; a continuing outcome must restore the boundary invariant while
strictly decreasing a natural variant.

## Main result

- `TM.LoopIterationSpaceSpec.toHoareSpace` — every configuration reachable
  from an invariant loop boundary respects the certified auxiliary-space
  budget.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Certified iteration-prefix bounds and a decreasing boundary variant imply
an all-reachable auxiliary-space contract for `loopTM`. -/
theorem LoopIterationSpaceSpec.toHoareSpace
    {tmBody tmTest : TM n} {invariant : TapePred n}
    {variant : Tape → (Fin n → Tape) → Tape → ℕ}
    {inputLength spaceBound : ℕ}
    (spec : LoopIterationSpaceSpec tmBody tmTest invariant variant
      inputLength spaceBound) :
    (loopTM tmBody tmTest).HoareSpace
      invariant inputLength spaceBound :=
  spec.toHoareSpace_internal

end TM

end Complexity
