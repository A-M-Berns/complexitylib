/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Defs
import Complexitylib.TreeEvaluation.CookMertz.Internal

/-!
# The Cook--Mertz tree evaluator

This file exposes the public correctness theorem for the executable
Cook--Mertz accumulator. The algorithm uses `d + 1` reusable value registers:
a recursive call adds its tree value to one selected register and restores all
other registers.

The algebraic hypothesis `LineCompatible units tree` is discharged for
low-degree polynomial node functions in `CookMertz.Interpolation`.

## Main theorems

- `accumulate_eq_addAt` -- exact accumulator correctness and register framing
- `evaluate_eq_value` -- agreement with ordinary bottom-up tree evaluation
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

variable {d : ℕ} {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The Cook--Mertz accumulator adds the scaled tree value to its selected
output register and restores every other register. -/
theorem accumulate_eq_addAt (units : List Fˣ) (tree : Tree d V)
    (h : LineCompatible units tree) (s : F) (out : Fin (d + 1))
    (regs : Registers d V) :
    accumulate units tree s out regs = addAt regs out (s • tree.value) :=
  Internal.accumulate_eq_addAt_internal units tree h s out regs

/-- Starting from zero registers, the distinguished output of the
Cook--Mertz accumulator is the ordinary bottom-up tree value. -/
theorem evaluate_eq_value (units : List Fˣ) (tree : Tree d V)
    (h : LineCompatible units tree) :
    evaluate units tree = tree.value := by
  rw [evaluate, accumulate_eq_addAt units tree h]
  simp [addAt]

end CookMertz

end TreeEval

end Complexity
