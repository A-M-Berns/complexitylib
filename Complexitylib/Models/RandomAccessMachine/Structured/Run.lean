/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Run.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Run.Internal

/-!
# Qualitative execution of structured RAM commands

This module exposes resource-erased composition lemmas for the exact
structured semantics. The underlying `Exec` derivation, including all three
resource measurements, remains available through `Runs`.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace Runs

/-- The empty command terminates without changing the store. -/
theorem skip (store : Store) :
    Runs .skip store store :=
  Internal.Runs.skip_internal store

/-- One basic instruction terminates with its specified store effect. -/
theorem basic (op : Basic) (store : Store) :
    Runs (.basic op) store (op.exec store) :=
  Internal.Runs.basic_internal op store

/-- Qualitative executions compose sequentially. -/
theorem seq {first second : Cmd} {initial middle final : Store}
    (hfirst : Runs first initial middle)
    (hsecond : Runs second middle final) :
    Runs (.seq first second) initial final :=
  Internal.Runs.seq_internal hfirst hsecond

/-- Select the zero branch of a structured conditional. -/
theorem ifZero {test : ℕ} {onZero onNonzero : Cmd}
    {initial final : Store} (htest : initial test = 0)
    (hbranch : Runs onZero initial final) :
    Runs (.ifZero test onZero onNonzero) initial final :=
  Internal.Runs.ifZero_internal htest hbranch

/-- Select the nonzero branch of a structured conditional. -/
theorem ifNonzero {test : ℕ} {onZero onNonzero : Cmd}
    {initial final : Store} (htest : initial test ≠ 0)
    (hbranch : Runs onNonzero initial final) :
    Runs (.ifZero test onZero onNonzero) initial final :=
  Internal.Runs.ifNonzero_internal htest hbranch

/-- A zero loop test terminates immediately. -/
theorem whileZero {test : ℕ} {body : Cmd}
    {store : Store} (htest : store test = 0) :
    Runs (.whileNonzero test body) store store :=
  Internal.Runs.whileZero_internal htest

/-- One nonzero loop iteration followed by the remaining loop execution. -/
theorem whileNonzero {test : ℕ} {body : Cmd}
    {initial middle final : Store} (htest : initial test ≠ 0)
    (hbody : Runs body initial middle)
    (hloop : Runs (.whileNonzero test body) middle final) :
    Runs (.whileNonzero test body) initial final :=
  Internal.Runs.whileNonzero_internal htest hbody hloop

end Runs

end Structured

end RAM

end Complexity
