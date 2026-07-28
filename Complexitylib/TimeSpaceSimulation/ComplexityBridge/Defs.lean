/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.Space
import Complexitylib.Classes.Time
import Mathlib.Data.Nat.Sqrt

/-!
# Definitions for the time-to-square-root-space class bridge

This file fixes the natural-number rounding conventions used by the final
time-to-space theorem and states the abstract machine-simulation interfaces.

The concrete balancing functions are total, including at time zero:

* `ceilSqrt` is the exact natural ceiling of the real square root;
* `positiveCeilSqrt` replaces its sole zero value by one;
* `protectedBinaryLog n = log₂ n + 1`;
* `balancedBlockLength` is the positive ceiling square root of
  `n * protectedBinaryLog n`;
* `balancedWorkspace` is the standard block/evaluation expression
  `b + (n / b + 1) * protectedBinaryLog n`.

The asymptotic target `sqrtLogSpace T` deliberately uses Mathlib's floor
square root and unprotected binary logarithm. Public theorems relate the total
concrete convention to this exact `⌊√(T(n) log₂ T(n))⌋` target whenever
`T(n) ≥ n`.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComplexityBridge

/-- The exact natural-number ceiling of the square root. -/
def ceilSqrt (n : ℕ) : ℕ :=
  if Nat.sqrt n * Nat.sqrt n = n then Nat.sqrt n else Nat.sqrt n + 1

/-- A positive square-root ceiling. It differs from `ceilSqrt` only at zero. -/
def positiveCeilSqrt (n : ℕ) : ℕ :=
  max 1 (ceilSqrt n)

/-- A total positive binary logarithmic factor. -/
def protectedBinaryLog (n : ℕ) : ℕ :=
  Nat.log 2 n + 1

/-- The balanced positive block length for a computation of `time` steps. -/
def balancedBlockLength (time : ℕ) : ℕ :=
  positiveCeilSqrt (time * protectedBinaryLog time)

/-- One more than the quotient by the balanced block length.

The extra block safely covers a final partial block and keeps the expression
total at time zero. -/
def timeBlockCount (time : ℕ) : ℕ :=
  time / balancedBlockLength time + 1

/-- The concrete block/evaluator workspace expression.

This is the arithmetic core of the usual balance
`b + (time / b + 1) * log(time)`. -/
def balancedWorkspace (time : ℕ) : ℕ :=
  balancedBlockLength time + timeBlockCount time * protectedBinaryLog time

/-- The exact asymptotic target, using natural floor square root and floor
binary logarithm. -/
def sqrtLogSpace (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.sqrt (T n * Nat.log 2 (T n))

/-- The total, positively rounded square-root-logarithmic bound. -/
def roundedSqrtLogSpace (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  balancedBlockLength (T n)

/-- The concrete balanced workspace associated with a time function. -/
def concreteBalancedSpace (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  balancedWorkspace (T n)

/-- An abstract machine-level simulation from time `T` to space `S`.

The source machine may use any asymptotic running-time witness `actualTime`
for `DTIME(T)`. The output exposes its own concrete space witness, keeping the
machine construction separate from asymptotic packaging. -/
def HasSpaceSimulation (T S : ℕ → ℕ) : Prop :=
  ∀ (workTapes : ℕ) (source : TM workTapes) (L : Language)
      (actualTime : ℕ → ℕ),
    source.DecidesInTime L actualTime →
    actualTime =O T →
    ∃ (simulatorTapes : ℕ) (simulator : TM simulatorTapes)
        (actualSpace : ℕ → ℕ),
      simulator.DecidesInSpace L actualSpace ∧ actualSpace =O S

/-- A stronger simulation contract whose resulting machine satisfies the
advertised concrete space function itself. -/
def HasConcreteSpaceSimulation (T S : ℕ → ℕ) : Prop :=
  ∀ (workTapes : ℕ) (source : TM workTapes) (L : Language)
      (actualTime : ℕ → ℕ),
    source.DecidesInTime L actualTime →
    actualTime =O T →
    ∃ (simulatorTapes : ℕ) (simulator : TM simulatorTapes),
      simulator.DecidesInSpace L S

end ComplexityBridge

end TimeSpaceSimulation

end Complexity
