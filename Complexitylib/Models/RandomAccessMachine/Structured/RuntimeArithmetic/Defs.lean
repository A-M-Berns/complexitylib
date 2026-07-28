/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Run.Defs

/-!
# Runtime arithmetic programs for structured RAMs

The Williams simulator uses natural representatives of dynamically selected
prime fields. This layer begins the first-order implementation with a
subtraction-based remainder program. Time is intentionally unrestricted;
the program keeps every intermediate value no wider than its input dividend.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace RuntimeArithmetic

/-- Four distinct registers used by the remainder program. -/
structure ReduceRegisters where
  /-- Dividend on entry and remainder on exit. -/
  value : ℕ
  /-- Positive modulus, preserved. -/
  modulus : ℕ
  /-- Preserved value `modulus - 1`. -/
  modulusPred : ℕ
  /-- Loop-test scratch register. -/
  test : ℕ
  /-- The value and modulus registers are distinct. -/
  value_ne_modulus : value ≠ modulus
  /-- The value and predecessor registers are distinct. -/
  value_ne_modulusPred : value ≠ modulusPred
  /-- The value and test registers are distinct. -/
  value_ne_test : value ≠ test
  /-- The modulus and predecessor registers are distinct. -/
  modulus_ne_modulusPred : modulus ≠ modulusPred
  /-- The modulus and test registers are distinct. -/
  modulus_ne_test : modulus ≠ test
  /-- The predecessor and test registers are distinct. -/
  modulusPred_ne_test : modulusPred ≠ test

/-- Recompute whether the current dividend is at least the modulus. -/
def reduceTestOp (regs : ReduceRegisters) : Basic :=
  .sub regs.test regs.value regs.modulusPred

/-- Subtract the modulus once and recompute the loop test. -/
def reduceBody (regs : ReduceRegisters) : Cmd :=
  Cmd.seq
    (.basic (.sub regs.value regs.value regs.modulus))
    (.basic (reduceTestOp regs))

/-- Replace `value` by `value % modulus` using repeated subtraction.

The caller supplies `modulusPred = modulus - 1`; the loop test
`value - modulusPred` is nonzero exactly when `modulus ≤ value`. -/
def reduce (regs : ReduceRegisters) : Cmd :=
  Cmd.seq (.basic (reduceTestOp regs))
    (.whileNonzero regs.test (reduceBody regs))

/-- Pure final store advertised by `reduce`. -/
def reduceResultStore (regs : ReduceRegisters)
    (remainder : ℕ) (store : Store) : Store :=
  Function.update (Function.update store regs.value remainder)
    regs.test 0

/-- Add two source registers into `value` and reduce modulo the runtime
modulus. The basic addition reads both operands before overwriting `value`, so
either operand may alias the result register. -/
def addMod (regs : ReduceRegisters) (left right : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.add regs.value left right))
    (reduce regs)

/-- Multiply two source registers into `value` and reduce modulo the runtime
modulus. The potentially double-width product exists only in `value`. -/
def mulMod (regs : ReduceRegisters) (left right : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.mul regs.value left right))
    (reduce regs)

/-- Compute `left + modulus - right` in `value` and reduce it.

`right` must differ from `value` for the correctness theorem because the
first addition overwrites `value` before the subtraction reads `right`. -/
def subMod (regs : ReduceRegisters) (left right : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.add regs.value left regs.modulus))
    (Cmd.seq
      (.basic (.sub regs.value regs.value right))
      (reduce regs))

/-- Seven distinct fixed registers used by modular exponentiation. -/
structure PowRegisters where
  /-- Register allocation in the order accumulator, modulus,
  modulus-predecessor, reduction test, base, exponent, constant one. -/
  index : Fin 7 → ℕ
  /-- The register allocation is injective. -/
  injective : Function.Injective index

namespace PowRegisters

/-- Distinct logical fields occupy distinct concrete registers. -/
theorem index_ne (regs : PowRegisters) {first second : Fin 7}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

/-- Accumulator and modular-reduction register view. -/
def reduceRegisters (regs : PowRegisters) : ReduceRegisters where
  value := regs.index 0
  modulus := regs.index 1
  modulusPred := regs.index 2
  test := regs.index 3
  value_ne_modulus := regs.index_ne (by decide)
  value_ne_modulusPred := regs.index_ne (by decide)
  value_ne_test := regs.index_ne (by decide)
  modulus_ne_modulusPred := regs.index_ne (by decide)
  modulus_ne_test := regs.index_ne (by decide)
  modulusPred_ne_test := regs.index_ne (by decide)

/-- Modular accumulator register. -/
abbrev accumulator (regs : PowRegisters) : ℕ :=
  regs.index 0

/-- Runtime modulus register. -/
abbrev modulus (regs : PowRegisters) : ℕ :=
  regs.index 1

/-- Runtime `modulus - 1` register. -/
abbrev modulusPred (regs : PowRegisters) : ℕ :=
  regs.index 2

/-- Modular-reduction loop scratch. -/
abbrev test (regs : PowRegisters) : ℕ :=
  regs.index 3

/-- Preserved exponentiation base. -/
abbrev base (regs : PowRegisters) : ℕ :=
  regs.index 4

/-- Countdown exponent. -/
abbrev exponent (regs : PowRegisters) : ℕ :=
  regs.index 5

/-- Preserved constant one. -/
abbrev one (regs : PowRegisters) : ℕ :=
  regs.index 6

end PowRegisters

/-- Pure tail-recursive modular-power loop implemented by `powMod`. -/
def powModLoop (modulus base : ℕ) : ℕ → ℕ → ℕ
  | 0, accumulator => accumulator
  | exponent + 1, accumulator =>
      powModLoop modulus base exponent
        ((accumulator * base) % modulus)

/-- One modular-power loop iteration. -/
def powModBody (regs : PowRegisters) : Cmd :=
  Cmd.seq
    (mulMod regs.reduceRegisters regs.accumulator regs.base)
    (.basic (.sub regs.exponent regs.exponent regs.one))

/-- Runtime modular exponentiation from the accumulator and exponent
registers. The scratch test is cleared before entering the loop. -/
def powMod (regs : PowRegisters) : Cmd :=
  Cmd.seq
    (.basic (.imm regs.test 0))
    (.whileNonzero regs.exponent (powModBody regs))

/-- Pure final store advertised by `powMod`. -/
def powModResultStore (regs : PowRegisters)
    (result : ℕ) (store : Store) : Store :=
  Function.update
    (Function.update
      (Function.update store regs.accumulator result)
      regs.test 0)
    regs.exponent 0

end RuntimeArithmetic

end Structured

end RAM

end Complexity
