/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Defs
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Internal

/-!
# Runtime arithmetic programs for structured RAMs

This module exposes a fixed-register remainder program whose modulus is a
runtime value. The proof is against the independent structured semantics and
therefore transfers exactly to the compiled RAM program.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace RuntimeArithmetic

/-- The subtraction loop computes the exact natural remainder and preserves
the modulus registers. -/
theorem reduce_runs
    (regs : ReduceRegisters) (store : Store)
    (modulus value : ℕ) (hmodulus : 0 < modulus)
    (hvalue : store regs.value = value)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (reduce regs) store
      (reduceResultStore regs (value % modulus) store) :=
  Internal.reduce_runs_internal regs store modulus value
    hmodulus hvalue hmodulusValue hmodulusPred

/-- Runtime modular addition computes the exact reduced natural sum. -/
theorem addMod_runs
    (regs : ReduceRegisters) (left right : ℕ)
    (store : Store) (modulus : ℕ) (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (addMod regs left right) store
      (reduceResultStore regs
        ((store left + store right) % modulus) store) :=
  Internal.addMod_runs_internal regs left right store modulus
    hmodulus hmodulusValue hmodulusPred

/-- Runtime modular multiplication computes the exact reduced product. -/
theorem mulMod_runs
    (regs : ReduceRegisters) (left right : ℕ)
    (store : Store) (modulus : ℕ) (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (mulMod regs left right) store
      (reduceResultStore regs
        ((store left * store right) % modulus) store) :=
  Internal.mulMod_runs_internal regs left right store modulus
    hmodulus hmodulusValue hmodulusPred

/-- Runtime modular subtraction computes the exact reduced nonnegative
difference `left + modulus - right`. -/
theorem subMod_runs
    (regs : ReduceRegisters) (left right : ℕ)
    (store : Store) (modulus : ℕ) (hmodulus : 0 < modulus)
    (hright : right ≠ regs.value)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1) :
    Runs (subMod regs left right) store
      (reduceResultStore regs
        ((store left + modulus - store right) % modulus) store) :=
  Internal.subMod_runs_internal regs left right store modulus
    hmodulus hright hmodulusValue hmodulusPred

/-- Runtime modular exponentiation implements the pure tail-recursive power
loop exactly. -/
theorem powMod_runs
    (regs : PowRegisters) (store : Store)
    (modulus base exponent accumulator : ℕ)
    (hmodulus : 0 < modulus)
    (haccumulator :
      store regs.accumulator = accumulator)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hbase : store regs.base = base)
    (hexponent : store regs.exponent = exponent)
    (hone : store regs.one = 1) :
    Runs (powMod regs) store
      (powModResultStore regs
        (powModLoop modulus base exponent accumulator) store) :=
  Internal.powMod_runs_internal regs store modulus base exponent
    accumulator hmodulus haccumulator hmodulusValue
    hmodulusPred hbase hexponent hone

end RuntimeArithmetic

end Structured

end RAM

end Complexity
