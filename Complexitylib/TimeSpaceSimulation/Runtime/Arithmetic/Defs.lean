/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.Defs

/-!
# First-order arithmetic used by the time-space simulator

This module connects the structured RAM arithmetic primitives to the natural
residue operations used by the executable Cook--Mertz evaluator.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

open RAM Structured
open TreeEval CookMertz PrimeField

/-- Compute a runtime prime-field inverse in the accumulator register.

The caller supplies a canonical base, a positive prime modulus, its
predecessor, and a constant-one register. The zero branch is explicit; the
nonzero branch computes `base ^ (modulus - 2)` by the first-order modular
power loop. -/
def inverseMod
    (regs : RuntimeArithmetic.PowRegisters) : Cmd :=
  Cmd.seq
    (.basic (.imm regs.accumulator 1))
    (Cmd.seq
      (.basic (.sub regs.exponent regs.modulus regs.one))
      (Cmd.seq
        (.basic (.sub regs.exponent regs.exponent regs.one))
        (.ifZero regs.base
          (Cmd.seq
            (.basic (.imm regs.accumulator 0))
            (Cmd.seq
              (.basic (.imm regs.test 0))
              (.basic (.imm regs.exponent 0))))
          (RuntimeArithmetic.powMod regs))))

end Runtime

end TimeSpaceSimulation

end Complexity
