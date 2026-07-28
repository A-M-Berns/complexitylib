/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Defs
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.Defs

/-!
# Runtime-residue Cook--Mertz evaluation

This module implements the Cook--Mertz accumulator using only natural
residues and the arithmetic operations from `PrimeField.Runtime`.

The executable definitions never construct a list of field units and never
instantiate a field whose modulus is known only at runtime. Nonzero residues
are streamed by `Runtime.foldNonzero`. The fixed child-index traversals use
`List.finRange`; their length is the already-resident register count, not the
runtime modulus.

`CallbackCompatible` and `TreeCompatible` are proof-only relations connecting
natural callbacks and trees to certificate-side `ZMod` callbacks and trees.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Runtime

namespace CookMertz

variable {d : ℕ}

/-- The `d + 1` global registers, represented by natural residues. -/
abbrev Registers (d : ℕ) :=
  Fin (d + 1) → ℕ

/-- Add a value to one register modulo the runtime modulus. -/
def addAt (p : ℕ) (regs : Registers d)
    (index : Fin (d + 1)) (value : ℕ) : Registers d :=
  Function.update regs index
    (Runtime.add p (regs index) value)

/-- Scale one register modulo the runtime modulus. -/
def scaleAt (p : ℕ) (regs : Registers d)
    (index : Fin (d + 1)) (scalar : ℕ) : Registers d :=
  Function.update regs index
    (Runtime.mul p scalar (regs index))

/-- Runtime-residue Cook--Mertz accumulator.

Every arithmetic update uses canonical modular operations. Nonzero scalars
are generated one at a time by `foldNonzero`; no modulus-sized list is
materialized. -/
def accumulate (p : ℕ) :
    Tree d ℕ → ℕ → Fin (d + 1) → Registers d → Registers d
  | .leaf value => fun scalar out regs =>
      addAt p regs out (Runtime.mul p scalar value)
  | .node children combine => fun scalar out regs =>
      Runtime.foldNonzero p (fun current residue =>
        let current :=
          (List.finRange d).foldl (fun current childIndex =>
            let target := out.succAbove childIndex
            accumulate p (children childIndex)
              (Runtime.normalize p 1) target
              (scaleAt p current target residue))
            current
        let args := fun childIndex =>
          current (out.succAbove childIndex)
        let current :=
          addAt p current out
            (Runtime.mul p (Runtime.sub p 0 scalar)
              (combine args))
        (List.finRange d).foldl (fun current childIndex =>
          let target := out.succAbove childIndex
          scaleAt p
            (accumulate p (children childIndex)
              (Runtime.sub p 0 1) target current)
            target (Runtime.inverse p residue))
          current)
        regs

/-- One forward child pass at a streamed nonzero residue. -/
def prepare (p : ℕ) (children : Fin d → Tree d ℕ)
    (residue : ℕ) (out : Fin (d + 1))
    (regs : Registers d) : Registers d :=
  (List.finRange d).foldl (fun current childIndex =>
    let target := out.succAbove childIndex
    accumulate p (children childIndex)
      (Runtime.normalize p 1) target
      (scaleAt p current target residue))
    regs

/-- Reverse one child pass and restore its scratch registers. -/
def cleanup (p : ℕ) (children : Fin d → Tree d ℕ)
    (residue : ℕ) (out : Fin (d + 1))
    (regs : Registers d) : Registers d :=
  (List.finRange d).foldl (fun current childIndex =>
    let target := out.succAbove childIndex
    scaleAt p
      (accumulate p (children childIndex)
        (Runtime.sub p 0 1) target current)
      target (Runtime.inverse p residue))
    regs

/-- Evaluate from zero residue registers. -/
def evaluate (p : ℕ) (tree : Tree d ℕ) : ℕ :=
  accumulate p tree (Runtime.normalize p 1)
    (Fin.last d) 0 (Fin.last d)

/-- Pointwise canonical-residue invariant for the global register bank. -/
def Registers.InRange (p : ℕ) (regs : Registers d) : Prop :=
  ∀ index, regs index < p

/-- Pointwise binary-width invariant for the global register bank. -/
def Registers.Fits (p : ℕ) (regs : Registers d) : Prop :=
  ∀ index, (regs index).size ≤ Runtime.bitWidth p

/-- Cast natural residue registers into the certificate-side field bank. -/
def castRegisters (p : ℕ) (regs : Registers d) :
    Complexity.TreeEval.CookMertz.Registers d (ZMod p) :=
  fun index => (regs index : ZMod p)

/-- A runtime node callback commutes with casting every natural argument
into the certificate-side `ZMod` field. -/
def CallbackCompatible (p : ℕ)
    (runtimeCombine : (Fin d → ℕ) → ℕ)
    (fieldCombine : (Fin d → ZMod p) → ZMod p) : Prop :=
  ∀ args,
    ((runtimeCombine args : ℕ) : ZMod p) =
      fieldCombine (fun index => (args index : ZMod p))

/-- Structural compatibility between a runtime-residue tree and a
certificate-side field tree. -/
inductive TreeCompatible (p : ℕ) :
    Tree d ℕ → Tree d (ZMod p) → Prop where
  /-- A natural leaf corresponds to its field cast. -/
  | leaf (value : ℕ) :
      TreeCompatible p (.leaf value) (.leaf (value : ZMod p))
  /-- Compatible children and callbacks give compatible internal nodes. -/
  | node
      (runtimeChildren : Fin d → Tree d ℕ)
      (fieldChildren : Fin d → Tree d (ZMod p))
      (runtimeCombine : (Fin d → ℕ) → ℕ)
      (fieldCombine : (Fin d → ZMod p) → ZMod p)
      (hchildren : ∀ index,
        TreeCompatible p
          (runtimeChildren index) (fieldChildren index))
      (hcombine :
        CallbackCompatible p runtimeCombine fieldCombine) :
      TreeCompatible p
        (.node runtimeChildren runtimeCombine)
        (.node fieldChildren fieldCombine)

end CookMertz

end Runtime

end PrimeField

end CookMertz

end TreeEval

end Complexity
