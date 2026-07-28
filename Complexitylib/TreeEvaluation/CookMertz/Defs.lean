/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Cook--Mertz catalytic accumulator

This file gives an executable, algebraic version of the recursive `ADD`
procedure from Cook--Mertz tree evaluation. The algorithm owns only `d + 1`
global value registers. Recursive calls add a child value into a selected
register and restore all other registers, allowing the same storage to be
reused at every tree level.

The list `units` fixes an explicit traversal order for the nonzero field
elements. This is intentional: the eventual Turing-machine implementation must
enumerate field elements executablely rather than rely on a noncomputable
ordering of a `Finset`.

## Main definitions

- `LineCompatible` -- the interpolation identity required at every node
- `Registers` -- the `d + 1` reusable global value registers
- `addAt`, `scaleAt` -- elementary register operations
- `accumulate` -- the recursive Cook--Mertz accumulator
- `evaluate` -- evaluate a compatible tree from zeroed registers
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

variable {d : ℕ} {F V : Type*}

/-- The algebraic condition used by the Cook--Mertz accumulator.

At an internal node, summing the combining function along every nonzero
multiple of an affine line yields the negative of its value at the line's
basepoint. Over characteristic two this is exactly Equation (5) in Williams's
Appendix A. The signed form works over arbitrary finite fields. -/
def LineCompatible [Field F] [AddCommGroup V] [Module F V] (units : List Fˣ) :
    Tree d V → Prop
  | .leaf _ => True
  | .node children combine =>
      (∀ r, LineCompatible units (children r)) ∧
      ∀ (direction base : Fin d → V),
        (units.map fun (a : Fˣ) =>
          combine (fun r => (a : F) • direction r + base r)).sum =
            -combine base

/-- The reusable global storage of the accumulator: `d` logical argument
registers and one output register. A recursive call may choose any physical
register as its output; `Fin.succAbove` names the remaining `d` registers. -/
abbrev Registers (d : ℕ) (V : Type*) := Fin (d + 1) → V

/-- Add `v` to register `i`, preserving every other register. -/
def addAt [Add V] (regs : Registers d V) (i : Fin (d + 1)) (v : V) :
    Registers d V :=
  Function.update regs i (regs i + v)

/-- Scale register `i` by `a`, preserving every other register. -/
def scaleAt [SMul F V] (regs : Registers d V) (i : Fin (d + 1)) (a : F) :
    Registers d V :=
  Function.update regs i (a • regs i)

/-- The Cook--Mertz recursive accumulator.

`accumulate units tree s out regs` adds `s • tree.value` to register `out`
while restoring every other register. At an internal node, each nonzero field
element gives one prepare/evaluate/cleanup pass. The node function is
accumulated with coefficient `-s`; `LineCompatible` turns the resulting sum
into `s • tree.value`.

The definition itself is total and executable whenever the supplied field and
node functions are executable. Correctness is proved on the public surface. -/
def accumulate [Field F] [AddCommGroup V] [Module F V] (units : List Fˣ) :
    Tree d V → F → Fin (d + 1) → Registers d V → Registers d V
  | .leaf v => fun s out regs => addAt regs out (s • v)
  | .node children combine => fun s out regs =>
      List.foldl (β := Fˣ) (fun regs a =>
        let regs := (List.finRange d).foldl (fun regs r =>
          let i := out.succAbove r
          accumulate units (children r) 1 i (scaleAt regs i (a : F))) regs
        let args := fun r => regs (out.succAbove r)
        let regs := addAt regs out ((-s) • combine args)
        (List.finRange d).foldl (fun regs r =>
          let i := out.succAbove r
          scaleAt (accumulate units (children r) (-1) i regs) i (↑a⁻¹ : F)) regs) regs
        units

/-- One forward pass over the children of a node.

For child `r`, its physical register is `out.succAbove r`. The existing value
is first scaled by `a`, then the child's value is accumulated into it. -/
def prepare [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (children : Fin d → Tree d V)
    (a : Fˣ) (out : Fin (d + 1)) (regs : Registers d V) :
    Registers d V :=
  (List.finRange d).foldl (fun regs r =>
    let i := out.succAbove r
    accumulate units (children r) 1 i (scaleAt regs i (a : F))) regs

/-- Undo one forward child pass.

Each child value is subtracted from its physical register, after which scaling
by `a⁻¹` restores the register's original value. -/
def cleanup [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (children : Fin d → Tree d V)
    (a : Fˣ) (out : Fin (d + 1)) (regs : Registers d V) :
    Registers d V :=
  (List.finRange d).foldl (fun regs r =>
    let i := out.succAbove r
    scaleAt (accumulate units (children r) (-1) i regs) i (↑a⁻¹ : F)) regs

/-- Run the accumulator with zeroed global storage and return its distinguished
output register. -/
def evaluate [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) : V :=
  accumulate units tree 1 (Fin.last d) 0 (Fin.last d)

end CookMertz

end TreeEval

end Complexity
