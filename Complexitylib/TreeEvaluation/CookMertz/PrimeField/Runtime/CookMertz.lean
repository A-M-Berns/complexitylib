/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.CookMertz.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.CookMertz.Internal

/-!
# Verified runtime-residue Cook--Mertz evaluation

The runtime accumulator stores only natural residues, uses the natural
operations from `PrimeField.Runtime`, and streams nonzero scalars through
`foldNonzero`. No runtime-sized field type or modulus-sized unit list occurs
in its executable definitions.

`TreeCompatible` is the proof boundary for callers: each natural node
callback must commute with casting its arguments to `ZMod p`. Under that
contract, the residue accumulator casts exactly to the generic Cook--Mertz
accumulator over `PrimeField.units p`. A generic `LineCompatible` certificate
then proves that runtime evaluation returns the canonical residue of the
ordinary natural tree value.

Every stored register remains below `p` and therefore fits in `p.size` bits.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Runtime

namespace CookMertz

variable {d p : ℕ}

/-- Modular register addition preserves canonical residues. -/
theorem addAt_inRange
    {regs : Registers d} (hp : 0 < p)
    (hregs : regs.InRange p)
    (index : Fin (d + 1)) (value : ℕ) :
    (addAt p regs index value).InRange p :=
  Internal.addAt_inRange_internal hp hregs index value

/-- Modular register scaling preserves canonical residues. -/
theorem scaleAt_inRange
    {regs : Registers d} (hp : 0 < p)
    (hregs : regs.InRange p)
    (index : Fin (d + 1)) (scalar : ℕ) :
    (scaleAt p regs index scalar).InRange p :=
  Internal.scaleAt_inRange_internal hp hregs index scalar

/-- Every recursive accumulator call preserves the register range
invariant, independently of the callback's unreduced return value. -/
theorem accumulate_inRange
    (tree : Tree d ℕ) (hp : 0 < p)
    (scalar : ℕ) (out : Fin (d + 1))
    (regs : Registers d) (hregs : regs.InRange p) :
    (accumulate p tree scalar out regs).InRange p :=
  Internal.accumulate_inRange_internal
    tree hp scalar out regs hregs

/-- Canonical residue registers fit in the modulus width. -/
theorem Registers.InRange.fits
    {regs : Registers d} (hregs : regs.InRange p) :
    regs.Fits p :=
  Internal.inRange_fits_internal hregs

/-- Every accumulator result fits pointwise in `p.size` bits when its input
registers are canonical. -/
theorem accumulate_fits
    (tree : Tree d ℕ) (hp : 0 < p)
    (scalar : ℕ) (out : Fin (d + 1))
    (regs : Registers d) (hregs : regs.InRange p) :
    (accumulate p tree scalar out regs).Fits p :=
  Internal.accumulate_fits_internal
    tree hp scalar out regs hregs

/-- Evaluation returns a canonical residue. -/
theorem evaluate_lt
    (tree : Tree d ℕ) (hp : 0 < p) :
    evaluate p tree < p :=
  Internal.evaluate_lt_internal tree hp

/-- The runtime result fits in one modulus-width residue word. -/
theorem evaluate_size_le
    (tree : Tree d ℕ) (hp : 0 < p) :
    (evaluate p tree).size ≤ Runtime.bitWidth p :=
  Internal.evaluate_size_le_internal tree hp

/-- Structurally compatible trees have equal values after casting. -/
theorem TreeCompatible.value_cast
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree) :
    ((runtimeTree.value : ℕ) : ZMod p) =
      fieldTree.value :=
  Internal.treeCompatible_value_internal hcompatible

/-- Runtime register addition casts to generic field-register addition. -/
theorem castRegisters_addAt
    (regs : Registers d) (index : Fin (d + 1))
    (value : ℕ) :
    castRegisters p (addAt p regs index value) =
      Complexity.TreeEval.CookMertz.addAt
        (castRegisters p regs) index (value : ZMod p) :=
  Internal.castRegisters_addAt_internal regs index value

/-- Runtime register scaling casts to generic field-register scaling. -/
theorem castRegisters_scaleAt
    (regs : Registers d) (index : Fin (d + 1))
    (scalar : ℕ) :
    castRegisters p (scaleAt p regs index scalar) =
      Complexity.TreeEval.CookMertz.scaleAt
        (castRegisters p regs) index (scalar : ZMod p) :=
  Internal.castRegisters_scaleAt_internal regs index scalar

/-- The complete natural-residue accumulator casts exactly to the generic
Cook--Mertz accumulator over the explicit nonzero-unit list. The list occurs
only on this certificate side. -/
theorem TreeCompatible.accumulate_cast
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree)
    (scalar : ℕ) (out : Fin (d + 1))
    (regs : Registers d) :
    castRegisters p
        (accumulate p runtimeTree scalar out regs) =
      Complexity.TreeEval.CookMertz.accumulate
        (PrimeField.units p) fieldTree
        (scalar : ZMod p) out (castRegisters p regs) :=
  Internal.accumulate_cast_internal
    hcompatible scalar out regs

/-- Runtime evaluation casts exactly to generic field evaluation. -/
theorem TreeCompatible.evaluate_cast
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree) :
    ((evaluate p runtimeTree : ℕ) : ZMod p) =
      Complexity.TreeEval.CookMertz.evaluate
        (PrimeField.units p) fieldTree :=
  Internal.evaluate_cast_internal hcompatible

/-- Under the generic affine-line identity, runtime evaluation represents
the ordinary runtime-tree value. -/
theorem TreeCompatible.evaluate_cast_eq_value
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree)
    (hline :
      Complexity.TreeEval.CookMertz.LineCompatible
        (PrimeField.units p) fieldTree) :
    ((evaluate p runtimeTree : ℕ) : ZMod p) =
      (runtimeTree.value : ZMod p) :=
  Internal.evaluate_cast_eq_value_internal
    hcompatible hline

/-- Fully natural correctness: the runtime evaluator returns the canonical
residue of the bottom-up natural tree value. -/
theorem TreeCompatible.evaluate_eq_normalize_value
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree)
    (hline :
      Complexity.TreeEval.CookMertz.LineCompatible
        (PrimeField.units p) fieldTree) :
    evaluate p runtimeTree =
      Runtime.normalize p runtimeTree.value :=
  Internal.evaluate_eq_normalize_value_internal
    hcompatible hline

end CookMertz

end Runtime

end PrimeField

end CookMertz

end TreeEval

end Complexity
