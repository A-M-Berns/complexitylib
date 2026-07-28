/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Internal

/-!
# Three-block neighborhood computation-graph topology

This module exposes a fixed-indegree computation graph for an arbitrary
deterministic Turing machine. During time interval `i`, each named tape is
represented by the lower, center, and upper canonical blocks around its head
at time `blockLength * i`. At the left boundary, natural subtraction
duplicates block zero instead of wrapping.

For each of the three blocks requested from every named tape, the content
oracle selects the greatest earlier interval whose neighborhood contains that
exact block and chooses a matching slot there. If there is no such interval,
it selects the block's initial source. A fourth input per tape supplies the
immediately preceding interval. Thus the fixed fan-in is exactly

`4 * (workTapeCount + 2)`.

Every edge strictly lowers interval rank. Generic recursive node semantics
and fixed-arity tree unrolling are therefore well founded, their values
agree, and unrolled height is at most root rank.

No theorem or definition in this module assumes `BlockRespectingOnInput`.
The finite greatest-prior search is executable as a Lean function, but no
Turing-machine workspace bound for that search is claimed here.

## Main theorems

* `neighborBlock_matchingSlot` -- a selected prior slot carries the exact block
* `previousInterval_some_maximal` -- the returned interval is greatest
* `contentPredecessor_block` -- content edges carry the requested block
* `card_predecessorIndex` -- exact fan-in `4 * (workTapeCount + 2)`
* `predecessorAt_rank_lt` -- every Fin-indexed edge lowers rank
* `value_unroll` / `height_unroll_le_rank` -- generic unrolling correctness
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

/-- There are exactly three named neighborhood slots. -/
@[simp] theorem card_slot :
    Fintype.card Slot = 3 :=
  Internal.card_slot_internal

@[simp] theorem neighborBlock_lower (center : ℕ) :
    neighborBlock center .lower = center - 1 :=
  rfl

@[simp] theorem neighborBlock_center (center : ℕ) :
    neighborBlock center .center = center :=
  rfl

@[simp] theorem neighborBlock_upper (center : ℕ) :
    neighborBlock center .upper = center + 1 :=
  rfl

/-- At the one-sided boundary, the lower slot is truncated to block zero. -/
@[simp] theorem neighborBlock_lower_zero :
    neighborBlock 0 .lower = 0 :=
  rfl

/-- Every canonical slot lies in its three-block neighborhood. -/
theorem neighborBlock_mem (center : ℕ) (slot : Slot) :
    NeighborhoodContains center (neighborBlock center slot) :=
  Internal.neighborBlock_mem_internal center slot

/-- If a requested block belongs to a neighborhood, the deterministic slot
selector carries exactly that block. -/
theorem neighborBlock_matchingSlot
    {center requested : ℕ}
    (hcontains : NeighborhoodContains center requested) :
    neighborBlock center (matchingSlot center requested) =
      requested :=
  Internal.neighborBlock_matchingSlot_internal hcontains

/-- Neighborhood membership is exactly representability by one of the three
named slots. -/
theorem neighborhoodContains_iff_exists_slot
    {center requested : ℕ} :
    NeighborhoodContains center requested ↔
      ∃ slot, neighborBlock center slot = requested :=
  Internal.neighborhoodContains_iff_exists_slot_internal

/-- Membership in the finite earlier-interval search set. -/
theorem mem_priorIntervals
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock} :
    previous ∈
        priorIntervals tm x blockLength tape
          requestedBlock timeBlock ↔
      NeighborhoodContains
        (centerBlock tm x blockLength previous.val tape)
        requestedBlock :=
  Internal.mem_priorIntervals_internal

/-- A successful greatest-prior query returns a member of the search set. -/
theorem previousInterval_some_mem
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock}
    (h :
      previousInterval tm x blockLength tape
        requestedBlock timeBlock = some previous) :
    previous ∈
      priorIntervals tm x blockLength tape
        requestedBlock timeBlock :=
  Internal.previousInterval_some_mem_internal h

/-- The bounded return type records that a successful result is strictly
earlier than the target interval. -/
theorem previousInterval_some_lt
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock}
    (_h :
      previousInterval tm x blockLength tape
        requestedBlock timeBlock = some previous) :
    previous.val < timeBlock :=
  previous.isLt

/-- A returned prior interval's neighborhood contains the requested block. -/
theorem previousInterval_some_contains
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock}
    (h :
      previousInterval tm x blockLength tape
        requestedBlock timeBlock = some previous) :
    NeighborhoodContains
      (centerBlock tm x blockLength previous.val tape)
      requestedBlock :=
  Internal.previousInterval_some_contains_internal h

/-- The slot selected at a returned prior interval carries the exact requested
block. -/
theorem previousInterval_matchingSlot
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock}
    (h :
      previousInterval tm x blockLength tape
        requestedBlock timeBlock = some previous) :
    neighborBlock
        (centerBlock tm x blockLength previous.val tape)
        (matchingSlot
          (centerBlock tm x blockLength previous.val tape)
          requestedBlock) =
      requestedBlock :=
  Internal.previousInterval_matchingSlot_internal h

/-- Every other earlier interval containing the requested block occurs no
later than the returned interval. -/
theorem previousInterval_some_maximal
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock}
    (h :
      previousInterval tm x blockLength tape
        requestedBlock timeBlock = some previous)
    (candidate : Fin timeBlock)
    (hcandidate :
      NeighborhoodContains
        (centerBlock tm x blockLength candidate.val tape)
        requestedBlock) :
    candidate ≤ previous :=
  Internal.previousInterval_some_maximal_internal
    h candidate hcandidate

/-- The prior search fails exactly when no earlier interval neighborhood
contains the requested block. -/
theorem previousInterval_eq_none_iff
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ} :
    previousInterval tm x blockLength tape
        requestedBlock timeBlock = none ↔
      ∀ previous : Fin timeBlock,
        ¬NeighborhoodContains
          (centerBlock tm x blockLength previous.val tape)
          requestedBlock :=
  Internal.previousInterval_eq_none_iff_internal

/-- There are three content roles and one chronological role. -/
@[simp] theorem card_predecessorKind :
    Fintype.card PredecessorKind = 4 :=
  Internal.card_predecessorKind_internal

/-- The fixed input index has exactly four roles per named tape. -/
theorem card_predecessorIndex (workTapeCount : ℕ) :
    Fintype.card (PredecessorIndex workTapeCount) =
      4 * (workTapeCount + 2) :=
  Internal.card_predecessorIndex_internal workTapeCount

/-- A content edge preserves its requested named tape. -/
@[simp] theorem contentPredecessor_tape
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) (slot : Slot) :
    (contentPredecessor tm x blockLength timeBlock tape slot).tape =
      tape :=
  Internal.contentPredecessor_tape_internal
    tm x blockLength timeBlock tape slot

/-- A content edge carries exactly the block requested by its target
interval/slot, whether it selects a source or an earlier computation. -/
@[simp] theorem contentPredecessor_block
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) (slot : Slot) :
    (contentPredecessor tm x blockLength timeBlock tape slot).block
        tm x blockLength =
      requestedBlock tm x blockLength timeBlock tape slot :=
  Internal.contentPredecessor_block_internal
    tm x blockLength timeBlock tape slot

/-- A chronological edge preserves its requested named tape. -/
@[simp] theorem chronologicalPredecessor_tape
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    (chronologicalPredecessor
      tm x blockLength timeBlock tape).tape = tape :=
  Internal.chronologicalPredecessor_tape_internal
    tm x blockLength timeBlock tape

/-- Every ordered predecessor preserves the tape component of its input
index. -/
@[simp] theorem predecessor_tape
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (index : PredecessorIndex workTapeCount) :
    (predecessor tm x blockLength timeBlock index).tape =
      index.2 :=
  Internal.predecessor_tape_internal
    tm x blockLength timeBlock index

/-- Every content edge strictly lowers interval rank. -/
theorem contentPredecessor_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape targetTape : TapeIndex workTapeCount)
    (slot targetSlot : Slot) :
    (contentPredecessor tm x blockLength timeBlock tape slot).rank <
      (Node.computation targetTape targetSlot timeBlock).rank :=
  Internal.contentPredecessor_rank_lt_internal
    tm x blockLength timeBlock tape targetTape slot targetSlot

/-- Every chronological edge strictly lowers interval rank. -/
theorem chronologicalPredecessor_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot) :
    (chronologicalPredecessor
        tm x blockLength timeBlock tape).rank <
      (Node.computation targetTape targetSlot timeBlock).rank :=
  Internal.chronologicalPredecessor_rank_lt_internal
    tm x blockLength timeBlock tape targetTape targetSlot

/-- Every typed predecessor role strictly lowers interval rank. -/
theorem predecessor_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (index : PredecessorIndex workTapeCount) :
    (predecessor tm x blockLength timeBlock index).rank <
      (Node.computation targetTape targetSlot timeBlock).rank :=
  Internal.predecessor_rank_lt_internal
    tm x blockLength timeBlock targetTape targetSlot index

/-- Every fixed-Fin predecessor input strictly lowers interval rank. -/
theorem predecessorAt_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (index : Fin (4 * (workTapeCount + 2))) :
    (predecessorAt tm x blockLength timeBlock index).rank <
      (Node.computation targetTape targetSlot timeBlock).rank :=
  Internal.predecessorAt_rank_lt_internal
    tm x blockLength timeBlock targetTape targetSlot index

variable {V : Type*}

/-- Evaluating the unrolled tree agrees with recursive neighborhood-graph
semantics. -/
theorem value_unroll
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (4 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).value =
      nodeValue tm x blockLength sourceValue combine node :=
  Internal.value_unroll_internal
    tm x blockLength sourceValue combine node

/-- The unrolled tree's height is bounded by its root interval rank. -/
theorem height_unroll_le_rank
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (4 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).height ≤
      node.rank :=
  Internal.height_unroll_le_rank_internal
    tm x blockLength sourceValue combine node

/-- An unrolling rooted at interval `i` has height at most `i + 1`. -/
theorem height_unroll_computation_le
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (4 * (workTapeCount + 2)) → V) → V)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ) :
    (unroll tm x blockLength sourceValue combine
      (.computation tape slot timeBlock)).height ≤
        timeBlock + 1 :=
  height_unroll_le_rank
    tm x blockLength sourceValue combine
      (.computation tape slot timeBlock)

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
