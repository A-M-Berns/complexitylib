/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant.Internal

/-!
# All-program-point invariants for structured RAM executions

This surface exposes a resource-independent invariant relation and its
all-prefix preservation theorem for compiled structured code.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace InvariantRuns

/-- The initial store satisfies an execution invariant. -/
theorem initial
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    invariant initial :=
  Internal.initial_internal hrun

/-- The final store satisfies an execution invariant. -/
theorem final
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    invariant final :=
  Internal.final_internal hrun

/-- Erasing the invariant certificate yields an exact structured execution. -/
theorem toExecExists
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    ∃ cost space, Exec cmd initial final steps cost space :=
  Internal.toExecExists_internal hrun

/-- Erasing the invariant and exact step count yields qualitative execution. -/
theorem toRuns
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    Runs cmd initial final :=
  Internal.toRuns_internal hrun

/-- Every target-instruction prefix of a compiled invariant execution satisfies
the same store predicate. -/
theorem compile_prefix
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps)
    {k : ℕ} (hk : k ≤ steps) :
    invariant
      (RAM.run cmd.compile k { pc := 0, regs := initial }).regs :=
  Internal.compile_prefix_internal hrun hk

end InvariantRuns

end Structured

end RAM

end Complexity
