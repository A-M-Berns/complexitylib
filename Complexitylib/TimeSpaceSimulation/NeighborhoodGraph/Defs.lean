/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.BlockRespecting.Defs
import Complexitylib.TreeEvaluation.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Three-block neighborhood computation-graph topology

This topology applies directly to an arbitrary deterministic Turing machine.
For each named tape and time interval, it represents the three canonical
blocks around the head's block at the start of that interval. Natural
subtraction truncates the lower neighbor at block zero.

A content edge for a requested block searches for the greatest earlier
interval whose three-block neighborhood contains that block, then selects a
slot in that earlier interval carrying exactly the requested block. If no
such interval exists, the edge points to an initial source block. One
additional chronological edge is supplied per named tape.

No block-respecting hypothesis occurs in these definitions.

## Main definitions

* `Slot` -- lower, center, or upper neighborhood slot
* `neighborBlock` -- the canonical block carried by a slot
* `Node` -- a source block or one slot of a computed interval
* `previousInterval` -- greatest earlier neighborhood containing a block
* `predecessorAt` -- fixed `Fin (4 * (workTapeCount + 2))` input oracle
* `nodeValue` / `unroll` -- well-founded generic graph semantics
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

/-- One of the three canonical tape-block slots around an interval's starting
head. -/
inductive Slot where
  /-- The predecessor block, truncated at block zero. -/
  | lower
  /-- The block containing the interval's starting head. -/
  | center
  /-- The successor block. -/
  | upper
  deriving DecidableEq, Fintype

namespace Slot

/-- Explicit lower-center-upper ordering. -/
def toFin : Slot → Fin 3
  | .lower => ⟨0, by omega⟩
  | .center => ⟨1, by omega⟩
  | .upper => ⟨2, by omega⟩

/-- Decode an index in the lower-center-upper ordering. -/
def ofFin (index : Fin 3) : Slot :=
  if index.val = 0 then .lower
  else if index.val = 1 then .center
  else .upper

/-- Explicit equivalence between neighborhood slots and `Fin 3`. -/
def equivFin : Slot ≃ Fin 3 where
  toFun := toFin
  invFun := ofFin
  left_inv slot := by
    cases slot <;> rfl
  right_inv index := by
    apply Fin.ext
    by_cases hzero : index.val = 0
    · simp [ofFin, toFin, hzero]
    · by_cases hone : index.val = 1
      · simp [ofFin, toFin, hone]
      · have htwo : index.val = 2 := by omega
        simp [ofFin, toFin, htwo]

end Slot

/-- Canonical block carried by one slot around `centerBlock`.

At `centerBlock = 0`, both `lower` and `center` carry block zero. -/
def neighborBlock (centerBlock : ℕ) : Slot → ℕ
  | .lower => centerBlock - 1
  | .center => centerBlock
  | .upper => centerBlock + 1

/-- A block belongs to the canonical three-slot neighborhood. -/
def NeighborhoodContains (centerBlock requestedBlock : ℕ) : Prop :=
  requestedBlock = centerBlock - 1 ∨
    requestedBlock = centerBlock ∨
    requestedBlock = centerBlock + 1

instance (centerBlock requestedBlock : ℕ) :
    Decidable (NeighborhoodContains centerBlock requestedBlock) := by
  unfold NeighborhoodContains
  infer_instance

/-- Deterministically select a slot carrying `requestedBlock`.

At the left-boundary duplicate, the lower slot is selected first. Outside
the neighborhood this defaults to the upper slot; correctness uses
`NeighborhoodContains`. -/
def matchingSlot (centerBlock requestedBlock : ℕ) : Slot :=
  if requestedBlock = centerBlock - 1 then .lower
  else if requestedBlock = centerBlock then .center
  else .upper

/-- The center block of one named tape at an interval's start. -/
def centerBlock (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) : ℕ :=
  tm.activeBlock x blockLength timeBlock tape

/-- Block requested by one named tape/slot input of an interval. -/
def requestedBlock (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) (slot : Slot) : ℕ :=
  neighborBlock (centerBlock tm x blockLength timeBlock tape) slot

/-- Earlier intervals whose neighborhood for `tape` contains
`requestedBlock`. The bounded index itself records strict priority over the
target interval. -/
def priorIntervals (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (requestedBlock timeBlock : ℕ) : Finset (Fin timeBlock) :=
  Finset.univ.filter fun previous =>
    NeighborhoodContains
      (centerBlock tm x blockLength previous.val tape)
      requestedBlock

/-- Greatest earlier interval whose neighborhood contains the requested
block, if any. -/
def previousInterval (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (requestedBlock timeBlock : ℕ) : Option (Fin timeBlock) :=
  if h :
      (priorIntervals tm x blockLength tape
        requestedBlock timeBlock).Nonempty then
    some
      ((priorIntervals tm x blockLength tape
        requestedBlock timeBlock).max' h)
  else
    none

/-- An initial source block or one of three computed blocks after a time
interval. -/
inductive Node (workTapeCount : ℕ) where
  /-- Initial contents of one named tape block. -/
  | source (tape : TapeIndex workTapeCount) (block : ℕ)
  /-- One neighborhood slot after `timeBlock`. -/
  | computation
      (tape : TapeIndex workTapeCount) (slot : Slot) (timeBlock : ℕ)
  deriving DecidableEq

namespace Node

/-- Sources have rank zero; all three nodes for interval `i` have rank
`i + 1`. -/
def rank : Node workTapeCount → ℕ
  | .source _ _ => 0
  | .computation _ _ timeBlock => timeBlock + 1

/-- Named tape carried by a node. -/
def tape : Node workTapeCount → TapeIndex workTapeCount
  | .source tape _ => tape
  | .computation tape _ _ => tape

/-- Semantic tape block carried by a node. -/
def block (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) : Node workTapeCount → ℕ
  | .source _ block => block
  | .computation tape slot timeBlock =>
      requestedBlock tm x blockLength timeBlock tape slot

end Node

/-- The four predecessor roles contributed by each named tape. -/
inductive PredecessorKind where
  /-- Contents of one of the tape's three requested neighborhood blocks. -/
  | content (slot : Slot)
  /-- State and head data from the immediately preceding interval. -/
  | chronological
  deriving DecidableEq, Fintype

namespace PredecessorKind

/-- Explicit three-content-then-chronological ordering. -/
def toFin : PredecessorKind → Fin 4
  | .content slot =>
      ⟨slot.toFin.val, by omega⟩
  | .chronological => ⟨3, by omega⟩

/-- Decode one of the four predecessor roles. -/
def ofFin (index : Fin 4) : PredecessorKind :=
  if h : index.val < 3 then
    .content (Slot.ofFin ⟨index.val, h⟩)
  else
    .chronological

/-- Explicit equivalence between predecessor roles and `Fin 4`. -/
def equivFin : PredecessorKind ≃ Fin 4 where
  toFun := toFin
  invFun := ofFin
  left_inv kind := by
    cases kind with
    | content slot =>
        cases slot <;> rfl
    | chronological =>
        rfl
  right_inv index := by
    apply Fin.ext
    by_cases h : index.val < 3
    · have hinverse :
          Slot.toFin (Slot.ofFin ⟨index.val, h⟩) =
            (⟨index.val, h⟩ : Fin 3) :=
        Slot.equivFin.apply_symm_apply ⟨index.val, h⟩
      simpa [ofFin, toFin, h] using congrArg Fin.val hinverse
    · have hthree : index.val = 3 := by omega
      simp [ofFin, toFin, hthree]

end PredecessorKind

/-- Four predecessor roles for every named tape. -/
abbrev PredecessorIndex (workTapeCount : ℕ) :=
  PredecessorKind × TapeIndex workTapeCount

/-- Explicit role-major ordering of all predecessor inputs. -/
def predecessorIndexEquiv (workTapeCount : ℕ) :
    PredecessorIndex workTapeCount ≃
      Fin (4 * (workTapeCount + 2)) :=
  (Equiv.prodCongr PredecessorKind.equivFin (Equiv.refl _)).trans
    finProdFinEquiv

/-- Latest earlier computed copy of the requested block, choosing a matching
slot there, or the block's initial source if no earlier neighborhood contains
it. -/
def contentPredecessor (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) (slot : Slot) :
    Node workTapeCount :=
  let requested :=
    requestedBlock tm x blockLength timeBlock tape slot
  match previousInterval tm x blockLength tape requested timeBlock with
  | none =>
      .source tape requested
  | some previous =>
      .computation tape
        (matchingSlot
          (centerBlock tm x blockLength previous.val tape)
          requested)
        previous.val

/-- Immediately preceding interval for one tape, using its center node, or an
initial center source at interval zero. -/
def chronologicalPredecessor
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) : Node workTapeCount :=
  match timeBlock with
  | 0 =>
      .source tape
        (centerBlock tm x blockLength 0 tape)
  | previous + 1 =>
      .computation tape .center previous

/-- Select one of four predecessor roles for one named tape. -/
def predecessor (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (index : PredecessorIndex workTapeCount) :
    Node workTapeCount :=
  match index.1 with
  | .content slot =>
      contentPredecessor tm x blockLength timeBlock index.2 slot
  | .chronological =>
      chronologicalPredecessor tm x blockLength timeBlock index.2

/-- Fixed-Fin form of the predecessor oracle. -/
def predecessorAt (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (index : Fin (4 * (workTapeCount + 2))) :
    Node workTapeCount :=
  predecessor tm x blockLength timeBlock
    ((predecessorIndexEquiv workTapeCount).symm index)

private theorem contentPredecessor_rank_lt_for_recursion
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape targetTape : TapeIndex workTapeCount)
    (slot targetSlot : Slot) :
    (contentPredecessor tm x blockLength timeBlock tape slot).rank <
      (Node.computation targetTape targetSlot timeBlock).rank := by
  dsimp only [contentPredecessor]
  generalize hprevious :
    previousInterval tm x blockLength tape
      (requestedBlock tm x blockLength timeBlock tape slot)
      timeBlock = result
  cases result with
  | none =>
      simp [Node.rank]
  | some previous =>
      simp only [Node.rank]
      omega

private theorem chronologicalPredecessor_rank_lt_for_recursion
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot) :
    (chronologicalPredecessor tm x blockLength timeBlock tape).rank <
      (Node.computation targetTape targetSlot timeBlock).rank := by
  cases timeBlock <;> simp [chronologicalPredecessor, Node.rank]

private theorem predecessorAt_rank_lt_for_recursion
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (index : Fin (4 * (workTapeCount + 2))) :
    (predecessorAt tm x blockLength timeBlock index).rank <
      (Node.computation targetTape targetSlot timeBlock).rank := by
  unfold predecessorAt
  generalize
    hindex :
      (predecessorIndexEquiv workTapeCount).symm index = decoded
  cases decoded with
  | mk kind tape =>
      cases kind with
      | content slot =>
          exact contentPredecessor_rank_lt_for_recursion
            tm x blockLength timeBlock tape targetTape slot targetSlot
      | chronological =>
          exact chronologicalPredecessor_rank_lt_for_recursion
            tm x blockLength timeBlock tape targetTape targetSlot

variable {V : Type*}

/-- Evaluate arbitrary source labels and local interval functions recursively
through the neighborhood graph. -/
def nodeValue (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (4 * (workTapeCount + 2)) → V) → V) :
    Node workTapeCount → V
  | .source tape block =>
      sourceValue tape block
  | .computation tape slot timeBlock =>
      combine tape slot timeBlock fun index =>
        nodeValue tm x blockLength sourceValue combine
          (predecessorAt tm x blockLength timeBlock index)
termination_by node => node.rank
decreasing_by
  exact predecessorAt_rank_lt_for_recursion
    tm x blockLength timeBlock tape slot index

/-- Unroll the same well-founded recursion into a fixed-arity tree-evaluation
instance. -/
def unroll (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (4 * (workTapeCount + 2)) → V) → V) :
    Node workTapeCount →
      TreeEval.Tree (4 * (workTapeCount + 2)) V
  | .source tape block =>
      .leaf (sourceValue tape block)
  | .computation tape slot timeBlock =>
      .node
        (fun index =>
          unroll tm x blockLength sourceValue combine
            (predecessorAt tm x blockLength timeBlock index))
        (combine tape slot timeBlock)
termination_by node => node.rank
decreasing_by
  exact predecessorAt_rank_lt_for_recursion
    tm x blockLength timeBlock tape slot index

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
