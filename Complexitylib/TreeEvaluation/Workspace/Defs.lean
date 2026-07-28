/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz.Defs

/-!
# Abstract workspace profiles for Cook--Mertz evaluation

This file instruments the executable Cook--Mertz traversals with the peak
number of simultaneously live recursive calls. The instrumentation follows
the evaluator's control flow: sequential child and field-element loops take a
maximum, while entering a recursive child adds one live frame.

The profile deliberately does not assign a bit cost to an oracle call, a field
operation, or one recursive frame. Those costs belong to a later concrete
machine implementation. What is already representation-independent is:

* the catalytic store has exactly `d + 1` value registers;
* for `b`-coordinate values, those registers contain exactly
  `(d + 1) * b` field cells; and
* the direct implicit-DAG traversal's live recursive-frame count is bounded by
  the selected node's dependency depth plus one.

Thus this layer provides the finite register/frame accounting to which a
concrete encoding can attach per-cell and per-frame bit widths.

## Main definitions

* `Profile` -- a result paired with its peak live-frame count
* `profileAccumulate` -- instrumented explicit-tree accumulator
* `profileDAGAccumulate` -- instrumented direct ordered-DAG traversal
* `RegisterCell` -- exact coordinates of the catalytic value store
* `abstractCellBound` -- persistent value cells plus encoded recursive frames
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace Workspace

variable {d size : ℕ} {F V : Type*}

/-- Result of an executable traversal together with the peak number of
simultaneously live recursive calls. -/
structure Profile (α : Type*) where
  /-- The ordinary computational result. -/
  result : α
  /-- Maximum number of live recursive calls, including the current call. -/
  peakFrames : ℕ

namespace Profile

/-- Start one traversal call with its own frame live. -/
def start (value : α) : Profile α :=
  ⟨value, 1⟩

/-- Apply a nonrecursive local operation without changing the frame peak. -/
def map (f : α → β) (profile : Profile α) : Profile β :=
  ⟨f profile.result, profile.peakFrames⟩

/-- Return from a recursive child while recording that the parent's frame was
live throughout the child's execution. Earlier sequential peaks are retained. -/
def recordChild (current child : Profile α) : Profile α :=
  ⟨child.result, max current.peakFrames (child.peakFrames + 1)⟩

end Profile

/-- Cook--Mertz accumulation instrumented with its recursive-frame peak.

This is the same executable prepare/evaluate/cleanup traversal as
`CookMertz.accumulate`. The extra natural number is updated only when a
recursive child call is entered. -/
def profileAccumulate [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) :
    Tree d V → F → Fin (d + 1) → Registers d V → Profile (Registers d V)
  | .leaf value => fun scale out regs =>
      Profile.start (addAt regs out (scale • value))
  | .node children combine => fun scale out regs =>
      units.foldl (fun current (unit : Fˣ) =>
        let current := (List.finRange d).foldl (fun current childIndex =>
          let target := out.succAbove childIndex
          let child :=
            profileAccumulate units (children childIndex) 1 target
              (scaleAt current.result target (unit : F))
          Profile.recordChild current child) current
        let args := fun childIndex =>
          current.result (out.succAbove childIndex)
        let current :=
          Profile.map
            (fun regs => addAt regs out ((-scale) • combine args))
            current
        (List.finRange d).foldl (fun current childIndex =>
          let target := out.succAbove childIndex
          let child :=
            profileAccumulate units (children childIndex) (-1) target
              current.result
          Profile.map (fun regs => scaleAt regs target (↑unit⁻¹ : F))
            (Profile.recordChild current child)) current)
        (Profile.start regs)

/-- Evaluate a tree from zero catalytic registers and retain the traversal's
recursive-frame profile. -/
def profileEvaluate [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) : Profile V :=
  Profile.map (fun regs => regs (Fin.last d))
    (profileAccumulate units tree 1 (Fin.last d) 0)

namespace Ordered

/-- Well-founded, directly instrumented traversal of a compact ordered DAG.

Like `OrderedDAG.Aux.cookMertzAccumulate`, this definition queries `dag.spec`
on demand and never constructs the semantic unrolling. -/
def profileDAGAccumulate [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) :
    (index : ℕ) → index < size → F → Fin (d + 1) →
      Registers d V → Profile (Registers d V)
  | index, hindex, scale, out, regs =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf value =>
          Profile.start (addAt regs out (scale • value))
      | .node children combine =>
          units.foldl (fun current (unit : Fˣ) =>
            let current := (List.finRange d).foldl
              (fun current childIndex =>
                let childNode := children childIndex
                let target := out.succAbove childIndex
                let child :=
                  profileDAGAccumulate units dag childNode.val
                    (Nat.lt_trans childNode.isLt hindex) 1 target
                    (scaleAt current.result target (unit : F))
                Profile.recordChild current child)
              current
            let args := fun childIndex =>
              current.result (out.succAbove childIndex)
            let current :=
              Profile.map
                (fun regs => addAt regs out ((-scale) • combine args))
                current
            (List.finRange d).foldl (fun current childIndex =>
              let childNode := children childIndex
              let target := out.succAbove childIndex
              let child :=
                profileDAGAccumulate units dag childNode.val
                  (Nat.lt_trans childNode.isLt hindex) (-1) target
                  current.result
              Profile.map
                (fun regs => scaleAt regs target (↑unit⁻¹ : F))
                (Profile.recordChild current child)) current)
            (Profile.start regs)
termination_by index _ _ _ _ => index

end Ordered

/-- Public wrapper for the directly instrumented ordered-DAG accumulator. -/
def profileDAGAccumulate [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (scale : F) (out : Fin (d + 1)) (regs : Registers d V) :
    Profile (Registers d V) :=
  Ordered.profileDAGAccumulate units dag index.val index.isLt scale out regs

/-- Directly evaluate one ordered-DAG node from zero catalytic registers while
retaining the recursive-frame profile. -/
def profileDAGEvaluate [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size) :
    Profile V :=
  Profile.map (fun regs => regs (Fin.last d))
    (profileDAGAccumulate units dag index 1 (Fin.last d) 0)

/-- One field-valued cell in the `d + 1` catalytic registers when each value
has `b` coordinates. -/
abbrev RegisterCell (d b : ℕ) :=
  Fin (d + 1) × Fin b

/-- Flatten the catalytic register bank into its exact field-cell indexing. -/
def flattenRegisters {b : ℕ} {K : Type*}
    (regs : Registers d (Fin b → K)) : RegisterCell d b → K :=
  fun cell => regs cell.1 cell.2

/-- Reconstruct the catalytic register bank from its field-cell indexing. -/
def unflattenRegisters {b : ℕ} {K : Type*}
    (cells : RegisterCell d b → K) : Registers d (Fin b → K) :=
  fun register coordinate => cells (register, coordinate)

/-- Exact equivalence between vector-valued registers and their flattened
field-cell store. -/
def registersEquivCells {b : ℕ} {K : Type*} :
    Registers d (Fin b → K) ≃ (RegisterCell d b → K) where
  toFun := flattenRegisters
  invFun := unflattenRegisters
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact number of persistent field cells in the catalytic register bank. -/
def registerFieldCells (d b : ℕ) : ℕ :=
  (d + 1) * b

/-- Bit budget for the catalytic bank when one field element is represented
in `fieldBits` bits. -/
def registerBitBudget (d b fieldBits : ℕ) : ℕ :=
  registerFieldCells d b * fieldBits

/-- Abstract workspace after assigning `frameCells` encoded cells to every
live recursive frame.

This charges the persistent catalytic store once and the peak call stack, not
the total number of recursive calls. Oracle and arithmetic scratch must be
included in `frameCells` by a concrete implementation. -/
def abstractCellUsage (d b frameCells : ℕ) (profile : Profile α) : ℕ :=
  registerFieldCells d b + profile.peakFrames * frameCells

/-- Height-indexed abstract cell bound for the profiled evaluator. -/
def abstractCellBound (d b frameCells height : ℕ) : ℕ :=
  registerFieldCells d b + (height + 1) * frameCells

/-- Abstract bit usage after assigning `fieldBits` bits to every field cell
and `frameBits` bits to every live recursive frame. -/
def abstractBitUsage (d b fieldBits frameBits : ℕ)
    (profile : Profile α) : ℕ :=
  registerBitBudget d b fieldBits + profile.peakFrames * frameBits

/-- Height-indexed abstract bit bound corresponding to `abstractBitUsage`. -/
def abstractBitBound (d b fieldBits frameBits height : ℕ) : ℕ :=
  registerBitBudget d b fieldBits + (height + 1) * frameBits

end Workspace

end CookMertz

end TreeEval

end Complexity
