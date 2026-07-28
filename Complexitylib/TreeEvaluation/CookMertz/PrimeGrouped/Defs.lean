/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BooleanPadding.Defs
import Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.TreeLift.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Defs
import Mathlib.Data.Nat.Size

/-!
# Prime-field parameters for grouped Boolean tree evaluation

For fan-in `d` and Boolean payload width `b`, set

`p = BooleanPadding.paddedWidth d b = b + d + 1`,
`M = 2 ^ p`, and `D = M ^ 2`.

The padded value occupies one `p`-bit chunk. A `PrimeField.Choice D` supplies
a prime field larger than the degree endpoint and a noncomputable injection
of all `p`-bit chunks into that field.

## Main definitions

* `domainSize` -- the chunk-domain size `M`
* `degreeEndpoint` -- the prime-choice endpoint `M ^ 2`
* `oneChunkLayout` -- the layout `p` bits into one `p`-bit chunk
* `codebook` -- the induced chunk injection into the selected prime field
* `liftPaddedTree` -- pad and then group-lift a Boolean tree
* `evaluatePaddedTree` -- Cook--Mertz evaluation over the selected prime field
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeGrouped

/-- Cardinality of the complete padded Boolean chunk domain. -/
def domainSize (d b : ℕ) : ℕ :=
  2 ^ BooleanPadding.paddedWidth d b

/-- Degree endpoint used to select the prime field. -/
def degreeEndpoint (d b : ℕ) : ℕ :=
  domainSize d b ^ 2

/-- The padded value occupies exactly one full-width chunk. -/
theorem oneChunkLayout (d b : ℕ) :
    GroupedExtension.Layout
      (BooleanPadding.paddedWidth d b)
      (BooleanPadding.paddedWidth d b) 1 where
  chunkBits_pos := by
    simp [BooleanPadding.paddedWidth]
  covers := by
    simp
  tight := by
    simp

/-- Noncomputable injection of all padded chunks into the selected prime
field. Executable encoding remains a separate implementation obligation. -/
noncomputable def codebook
    (choice : PrimeField.Choice (degreeEndpoint d b)) :
    GroupedExtension.Codebook choice.Field
      (BooleanPadding.paddedWidth d b) := by
  apply GroupedExtension.Codebook.ofCardLE
  have hdomainPos : 0 < domainSize d b := by
    simp [domainSize]
  have hdomainLeEndpoint :
      domainSize d b ≤ degreeEndpoint d b := by
    calc
      domainSize d b = domainSize d b * 1 := by simp
      _ ≤ domainSize d b * domainSize d b :=
        Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr hdomainPos.ne')
      _ = degreeEndpoint d b := by
        simp [degreeEndpoint, pow_two]
  have hendpointLt :
      degreeEndpoint d b < choice.modulus - 1 :=
    choice.degree_lt_sub_one
  have hdomainLeModulus : domainSize d b ≤ choice.modulus := by
    exact hdomainLeEndpoint.trans (by omega)
  simpa [domainSize, PrimeField.Choice.Field, ZMod.card] using
    hdomainLeModulus

/-- Pad Boolean values to width `b + d + 1`, then recursively replace leaves
and node functions by the one-chunk grouped field representation. -/
noncomputable def liftPaddedTree
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) :
    Tree d (Fin 1 → choice.Field) :=
  GroupedExtension.liftTree
    (codebook choice) (oneChunkLayout d b)
    (BooleanPadding.padTree tree)

/-- The packed field encoding of a width-padded Boolean value. -/
noncomputable def encodePaddedValue
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (value : Fin b → Bool) : Fin 1 → choice.Field :=
  GroupedExtension.encodeVector (codebook choice)
    (BooleanPadding.padBits d value)

/-- Run Cook--Mertz on the one-chunk prime-field lift. -/
noncomputable def evaluatePaddedTree
    (choice : PrimeField.Choice (degreeEndpoint d b))
    (tree : Tree d (Fin b → Bool)) : Fin 1 → choice.Field :=
  evaluate (PrimeField.units choice.modulus)
    (liftPaddedTree choice tree)

/-- Exact bit count charged to the `d + 1` catalytic field registers. -/
def catalyticRegisterBitBudget
    (choice : PrimeField.Choice (degreeEndpoint d b)) : ℕ :=
  GroupedExtension.groupedRegisterBitBudget
    d 1 choice.modulus.size

end PrimeGrouped

end CookMertz

end TreeEval

end Complexity
