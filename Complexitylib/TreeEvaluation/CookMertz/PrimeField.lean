/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Internal

/-!
# Explicit prime fields for Cook--Mertz evaluation

For every requested degree, Bertrand's postulate gives a prime modulus
strictly larger than `degree + 1` and at most `2 * (degree + 1)`. The
corresponding `ZMod` field therefore satisfies the exact Cook--Mertz
inequality while each residue needs only logarithmically many bits.

The nonzero field elements are exposed as the explicit list
`PrimeField.units`, ordered by their natural residues. This discharges the
enumeration hypothesis of the interpolation theorem without a hidden
`Fintype` sum.

## Main theorems

- `choice_nonempty` -- a suitable prime modulus exists for every degree
- `Choice.degree_lt_card_sub_one` -- the selected field meets the degree bound
- `Choice.modulus_size_le` -- the modulus has logarithmic binary width
- `enumeratesUnits` -- the explicit residue list enumerates all field units
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

/-- A prime-field choice exists for every requested degree. -/
theorem choice_nonempty (degree : ℕ) :
    Nonempty (Choice degree) :=
  Internal.choice_nonempty_internal degree

namespace Choice

variable {degree : ℕ}

/-- The selected prime field satisfies the strict Cook--Mertz degree
inequality. -/
theorem degree_lt_card_sub_one (choice : Choice degree) :
    degree < Fintype.card choice.Field - 1 :=
  Internal.degree_lt_card_sub_one_internal choice

/-- The selected modulus has binary width bounded by the logarithm of twice
the requested degree endpoint. -/
theorem modulus_size_le (choice : Choice degree) :
    choice.modulus.size ≤ Nat.log 2 (2 * (degree + 1)) + 1 :=
  Internal.modulus_size_le_internal choice

end Choice

variable (p : ℕ) [Fact p.Prime]

@[simp] theorem coe_unitOfIndex (index : Fin (p - 1)) :
    (unitOfIndex p index : ZMod p) = (index.val + 1 : ℕ) :=
  Internal.coe_unitOfIndex_internal p index

theorem units_nodup :
    (units p).Nodup :=
  Internal.units_nodup_internal p

theorem mem_units (unit : (ZMod p)ˣ) :
    unit ∈ units p :=
  Internal.mem_units_internal p unit

@[simp] theorem units_length :
    (units p).length = p - 1 :=
  Internal.units_length_internal p

/-- The explicit residue list contains each nonzero prime-field element
exactly once. -/
theorem enumeratesUnits :
    EnumeratesUnits (units p) :=
  Internal.enumeratesUnits_internal p

end PrimeField

end CookMertz

end TreeEval

end Complexity
