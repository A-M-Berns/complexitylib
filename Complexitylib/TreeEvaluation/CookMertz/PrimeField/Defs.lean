/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# Prime-field parameters for Cook--Mertz interpolation

Cook--Mertz requires every node polynomial to have degree strictly below
`|K| - 1`. This file records a concrete prime modulus satisfying that
inequality and defines an explicit increasing enumeration of every nonzero
element of the corresponding `ZMod` field.

The choice certificate also bounds the modulus by twice `degree + 1`. A later
uniform machine must find such a prime and implement modular arithmetic; the
existence proof alone is not an executable prime-search algorithm.

## Main definitions

- `PrimeField.Choice` -- a prime modulus with the required lower and upper bounds
- `PrimeField.Choice.Field` -- the corresponding `ZMod` field
- `PrimeField.unitOfIndex` -- nonzero residue at one bounded index
- `PrimeField.units` -- explicit increasing list of all nonzero residues
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

/-- A prime modulus large enough for polynomials of total degree `degree`,
but at most twice the first admissible lower endpoint. -/
structure Choice (degree : ℕ) where
  /-- Prime-field modulus. -/
  modulus : ℕ
  /-- The modulus is prime. -/
  prime : modulus.Prime
  /-- The Cook--Mertz interpolation degree inequality. -/
  degree_lt_sub_one : degree < modulus - 1
  /-- Bertrand-size upper bound. -/
  modulus_le_two_mul : modulus ≤ 2 * (degree + 1)

namespace Choice

variable {degree : ℕ}

instance (choice : Choice degree) : NeZero choice.modulus :=
  ⟨choice.prime.ne_zero⟩

instance (choice : Choice degree) : Fact choice.modulus.Prime :=
  ⟨choice.prime⟩

/-- The prime field selected by `choice`. -/
abbrev Field (choice : Choice degree) :=
  ZMod choice.modulus

end Choice

variable (p : ℕ) [Fact p.Prime]

/-- The unit represented by the residue `index + 1`. -/
def unitOfIndex (index : Fin (p - 1)) : (ZMod p)ˣ :=
  Units.mk0 ((index.val + 1 : ℕ) : ZMod p) (by
    intro hzero
    have hdvd : p ∣ index.val + 1 :=
      (ZMod.natCast_eq_zero_iff (index.val + 1) p).mp hzero
    exact
      Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) (by omega) hdvd)

/-- Explicit increasing enumeration `1, ..., p - 1` of the nonzero elements
of the prime field. -/
def units : List (ZMod p)ˣ :=
  (List.finRange (p - 1)).map (unitOfIndex p)

end PrimeField

end CookMertz

end TreeEval

end Complexity
