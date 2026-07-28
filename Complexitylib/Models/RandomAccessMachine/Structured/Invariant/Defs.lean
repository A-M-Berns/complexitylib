/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Defs

/-!
# All-program-point invariants for structured RAM executions

`InvariantRuns invariant cmd initial final steps` mirrors the exact
control-flow and step accounting of `Structured.Exec`, while requiring
`invariant` at every source program point. It deliberately ignores the
ordinary sparse-store space measure, so clients can bound a fixed mutable
overlay without charging the immutable public-input bank.
-/

namespace Complexity

namespace RAM

namespace Structured

/-- A terminating structured execution that satisfies `invariant` at every
source-level program point. -/
inductive InvariantRuns (invariant : Store → Prop) :
    Cmd → Store → Store → ℕ → Prop where
  | skip (store : Store) (hstore : invariant store) :
      InvariantRuns invariant .skip store store 0
  | basic (op : Basic) (store : Store)
      (hstore : invariant store)
      (hnext : invariant (op.exec store)) :
      InvariantRuns invariant (.basic op) store (op.exec store) 1
  | seq {first second : Cmd} {initial middle final : Store}
      {firstSteps secondSteps : ℕ}
      (hfirst :
        InvariantRuns invariant first initial middle firstSteps)
      (hsecond :
        InvariantRuns invariant second middle final secondSteps) :
      InvariantRuns invariant (.seq first second) initial final
        (firstSteps + secondSteps)
  | ifZero {test : ℕ} {onZero onNonzero : Cmd}
      {initial final : Store} {branchSteps : ℕ}
      (htest : initial test = 0)
      (hbranch :
        InvariantRuns invariant onZero initial final branchSteps) :
      InvariantRuns invariant (.ifZero test onZero onNonzero)
        initial final (branchSteps + 1)
  | ifNonzero {test : ℕ} {onZero onNonzero : Cmd}
      {initial final : Store} {branchSteps : ℕ}
      (htest : initial test ≠ 0)
      (hbranch :
        InvariantRuns invariant onNonzero initial final branchSteps) :
      InvariantRuns invariant (.ifZero test onZero onNonzero)
        initial final (branchSteps + 2)
  | whileZero {test : ℕ} {body : Cmd} {store : Store}
      (htest : store test = 0)
      (hstore : invariant store) :
      InvariantRuns invariant (.whileNonzero test body) store store 1
  | whileNonzero {test : ℕ} {body : Cmd}
      {initial middle final : Store}
      {bodySteps loopSteps : ℕ}
      (htest : initial test ≠ 0)
      (hbody :
        InvariantRuns invariant body initial middle bodySteps)
      (hloop :
        InvariantRuns invariant (.whileNonzero test body)
          middle final loopSteps) :
      InvariantRuns invariant (.whileNonzero test body)
        initial final (bodySteps + loopSteps + 2)

end Structured

end RAM

end Complexity
