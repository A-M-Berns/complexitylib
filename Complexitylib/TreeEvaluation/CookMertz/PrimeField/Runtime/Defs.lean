/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Nat.Size

/-!
# Runtime natural-residue arithmetic

This file defines a fully executable representation of arithmetic modulo a
runtime natural modulus. Values are ordinary natural residues; every public
operation returns a canonical residue when the modulus is positive.

No field type, primality proof, finite list, or `List.range` occurs in these
runtime definitions. In particular, exponentiation and traversal use
tail-recursive accumulators:

* `powLoop` performs repeated modular multiplication;
* `foldNonzeroLoop` streams `1, ..., p - 1` through a caller-supplied step.

The proof layer relates these operations to `ZMod p` when `p` is prime.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Runtime

/-- Canonical natural representative modulo `p`. -/
def normalize (p value : ℕ) : ℕ :=
  value % p

/-- Pre-reduction sum of two canonicalized inputs. -/
def addInput (p first second : ℕ) : ℕ :=
  normalize p first + normalize p second

/-- Runtime modular addition on natural representatives. -/
def add (p first second : ℕ) : ℕ :=
  normalize p (addInput p first second)

/-- Pre-reduction difference of two canonicalized inputs. -/
def subInput (p first second : ℕ) : ℕ :=
  normalize p first + p - normalize p second

/-- Runtime modular subtraction on natural representatives.

Both operands are normalized first. For positive `p`, the expression before
the final reduction cannot underflow because `normalize p second < p`. -/
def sub (p first second : ℕ) : ℕ :=
  normalize p (subInput p first second)

/-- Pre-reduction product of two canonicalized inputs. -/
def mulInput (p first second : ℕ) : ℕ :=
  normalize p first * normalize p second

/-- Runtime modular multiplication on natural representatives. -/
def mul (p first second : ℕ) : ℕ :=
  normalize p (mulInput p first second)

/-- Tail-recursive modular exponentiation loop.

`fuel` is the remaining exponent and `accumulator` is the running product.
The base is not required to be normalized because `mul` normalizes both
operands at every step. -/
def powLoop (p base : ℕ) : ℕ → ℕ → ℕ
  | 0, accumulator =>
      accumulator
  | fuel + 1, accumulator =>
      powLoop p base fuel (mul p accumulator base)

/-- Runtime modular exponentiation with canonical multiplicative identity. -/
def pow (p base exponent : ℕ) : ℕ :=
  powLoop p base exponent (normalize p 1)

/-- Runtime prime-field inverse.

Zero maps to zero. A nonzero residue is raised to `p - 2`; Fermat's theorem
proves agreement with inversion in `ZMod p` when `p` is prime. -/
def inverse (p value : ℕ) : ℕ :=
  if normalize p value = 0 then 0 else pow p value (p - 2)

/-- Binary width reserved for one canonical residue modulo `p`. -/
def bitWidth (p : ℕ) : ℕ :=
  p.size

/-- Scratch width sufficient for pre-reduction addition and subtraction. -/
def linearScratchBitWidth (p : ℕ) : ℕ :=
  bitWidth p + 1

/-- Scratch width sufficient for a pre-reduction product. -/
def multiplicationScratchBitWidth (p : ℕ) : ℕ :=
  2 * bitWidth p

/-- Tail-recursive streaming loop over consecutive natural candidates.

Starting at `candidate`, the loop calls `step` exactly `fuel` times. No list
of candidates is constructed. -/
def foldNonzeroLoop {State : Type*}
    (step : State → ℕ → State) : ℕ → ℕ → State → State
  | 0, _, state =>
      state
  | fuel + 1, candidate, state =>
      foldNonzeroLoop step fuel (candidate + 1)
        (step state candidate)

/-- Stream the nonzero canonical residues `1, ..., p - 1`.

The name records the intended prime-field use. The definition remains total
for every natural modulus. -/
def foldNonzero {State : Type*} (p : ℕ)
    (step : State → ℕ → State) (initial : State) : State :=
  foldNonzeroLoop step (p - 1) 1 initial

end Runtime

end PrimeField

end CookMertz

end TreeEval

end Complexity
