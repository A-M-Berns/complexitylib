/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Defs

/-!
# Control-flow bounds for structured RAM programs

This definitions layer records when every absolute jump target of a RAM
program stays below one fixed boundary and when that boundary itself is a
halting program counter.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace ControlFlow

/-- Every explicit jump target of an instruction lies at most at `bound`. -/
def InstrTargetsWithin (bound : ℕ) : Instr → Prop
  | .jz _ target => target ≤ bound
  | .jmp target => target ≤ bound
  | _ => True

/-- Every instruction selected by a program has its jump targets within the
fixed control-flow boundary. -/
def ProgramTargetsWithin (program : Program) (bound : ℕ) : Prop :=
  ∀ (pc : ℕ), InstrTargetsWithin bound ((program[pc]?).getD .halt)

/-- The distinguished boundary program counter selects a halt instruction. -/
def BoundaryHalts (program : Program) (bound : ℕ) : Prop :=
  (program[bound]?).getD .halt = .halt

end ControlFlow

end Structured

end RAM

end Complexity
