/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Defs

/-!
# Proof internals for the three-block neighborhood graph

This file proves exact slot selection, greatest-prior-interval properties,
fixed fan-in, edge well-foundedness, and correctness of generic tree
unrolling.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Internal

theorem card_slot_internal :
    Fintype.card Slot = 3 := by
  decide

theorem neighborBlock_mem_internal
    (center : ℕ) (slot : Slot) :
    NeighborhoodContains center (neighborBlock center slot) := by
  cases slot <;> simp [NeighborhoodContains, neighborBlock]

theorem neighborBlock_matchingSlot_internal
    {center requested : ℕ}
    (hcontains : NeighborhoodContains center requested) :
    neighborBlock center (matchingSlot center requested) =
      requested := by
  unfold matchingSlot
  split
  · next hlower =>
      simpa [neighborBlock] using hlower.symm
  · next hlower =>
      split
      · next hcenter =>
          simpa [neighborBlock] using hcenter.symm
      · next hcenter =>
          rcases hcontains with hlower' | hcenter' | hupper
          · exact absurd hlower' hlower
          · exact absurd hcenter' hcenter
          · simpa [neighborBlock] using hupper.symm

theorem neighborhoodContains_iff_exists_slot_internal
    {center requested : ℕ} :
    NeighborhoodContains center requested ↔
      ∃ slot, neighborBlock center slot = requested := by
  constructor
  · intro hcontains
    exact
      ⟨matchingSlot center requested,
        neighborBlock_matchingSlot_internal hcontains⟩
  · rintro ⟨slot, rfl⟩
    exact neighborBlock_mem_internal center slot

theorem mem_priorIntervals_internal
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock} :
    previous ∈
        priorIntervals tm x blockLength tape
          requestedBlock timeBlock ↔
      NeighborhoodContains
        (centerBlock tm x blockLength previous.val tape)
        requestedBlock := by
  simp [priorIntervals]

theorem previousInterval_some_mem_internal
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ}
    {previous : Fin timeBlock}
    (h :
      previousInterval tm x blockLength tape
        requestedBlock timeBlock = some previous) :
    previous ∈
      priorIntervals tm x blockLength tape
        requestedBlock timeBlock := by
  unfold previousInterval at h
  split at h
  · next hnonempty =>
      simp only [Option.some.injEq] at h
      subst previous
      exact Finset.max'_mem _ hnonempty
  · contradiction

theorem previousInterval_some_contains_internal
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
  mem_priorIntervals_internal.mp
    (previousInterval_some_mem_internal h)

theorem previousInterval_matchingSlot_internal
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
  neighborBlock_matchingSlot_internal
    (previousInterval_some_contains_internal h)

theorem previousInterval_some_maximal_internal
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
    candidate ≤ previous := by
  unfold previousInterval at h
  split at h
  · next hnonempty =>
      simp only [Option.some.injEq] at h
      rw [← h]
      exact Finset.le_max' _ _
        (mem_priorIntervals_internal.mpr hcandidate)
  · contradiction

theorem previousInterval_eq_none_iff_internal
    {tm : TM workTapeCount} {x : List Bool}
    {blockLength : ℕ} {tape : TapeIndex workTapeCount}
    {requestedBlock timeBlock : ℕ} :
    previousInterval tm x blockLength tape
        requestedBlock timeBlock = none ↔
      ∀ previous : Fin timeBlock,
        ¬NeighborhoodContains
          (centerBlock tm x blockLength previous.val tape)
          requestedBlock := by
  constructor
  · intro h previous hcontains
    have hmem :
        previous ∈
          priorIntervals tm x blockLength tape
            requestedBlock timeBlock :=
      mem_priorIntervals_internal.mpr hcontains
    unfold previousInterval at h
    split at h
    · contradiction
    · next hnone =>
        exact hnone ⟨previous, hmem⟩
  · intro h
    unfold previousInterval
    split
    · next hnonempty =>
        obtain ⟨previous, hmem⟩ := hnonempty
        exact absurd
          (mem_priorIntervals_internal.mp hmem)
          (h previous)
    · rfl

theorem card_predecessorKind_internal :
    Fintype.card PredecessorKind = 4 := by
  decide

theorem card_predecessorIndex_internal (workTapeCount : ℕ) :
    Fintype.card (PredecessorIndex workTapeCount) =
      4 * (workTapeCount + 2) := by
  simp [PredecessorIndex, card_predecessorKind_internal]

theorem contentPredecessor_tape_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) (slot : Slot) :
    (contentPredecessor tm x blockLength timeBlock tape slot).tape =
      tape := by
  dsimp only [contentPredecessor]
  generalize hprevious :
    previousInterval tm x blockLength tape
      (requestedBlock tm x blockLength timeBlock tape slot)
      timeBlock = result
  cases result <;> rfl

theorem contentPredecessor_block_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) (slot : Slot) :
    (contentPredecessor tm x blockLength timeBlock tape slot).block
        tm x blockLength =
      requestedBlock tm x blockLength timeBlock tape slot := by
  dsimp only [contentPredecessor]
  generalize hprevious :
    previousInterval tm x blockLength tape
      (requestedBlock tm x blockLength timeBlock tape slot)
      timeBlock = result
  cases result with
  | none =>
      rfl
  | some previous =>
      simp only [Node.block]
      exact neighborBlock_matchingSlot_internal
        (previousInterval_some_contains_internal hprevious)

theorem chronologicalPredecessor_tape_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    (chronologicalPredecessor
      tm x blockLength timeBlock tape).tape = tape := by
  cases timeBlock <;> rfl

theorem predecessor_tape_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (index : PredecessorIndex workTapeCount) :
    (predecessor tm x blockLength timeBlock index).tape =
      index.2 := by
  cases index with
  | mk kind tape =>
      cases kind with
      | content slot =>
          exact contentPredecessor_tape_internal
            tm x blockLength timeBlock tape slot
      | chronological =>
          exact chronologicalPredecessor_tape_internal
            tm x blockLength timeBlock tape

theorem contentPredecessor_rank_lt_internal
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

theorem chronologicalPredecessor_rank_lt_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot) :
    (chronologicalPredecessor
        tm x blockLength timeBlock tape).rank <
      (Node.computation targetTape targetSlot timeBlock).rank := by
  cases timeBlock <;>
    simp [chronologicalPredecessor, Node.rank]

theorem predecessor_rank_lt_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (index : PredecessorIndex workTapeCount) :
    (predecessor tm x blockLength timeBlock index).rank <
      (Node.computation targetTape targetSlot timeBlock).rank := by
  cases index with
  | mk kind tape =>
      cases kind with
      | content slot =>
          exact contentPredecessor_rank_lt_internal
            tm x blockLength timeBlock tape targetTape
            slot targetSlot
      | chronological =>
          exact chronologicalPredecessor_rank_lt_internal
            tm x blockLength timeBlock tape targetTape targetSlot

theorem predecessorAt_rank_lt_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot)
    (index : Fin (4 * (workTapeCount + 2))) :
    (predecessorAt tm x blockLength timeBlock index).rank <
      (Node.computation targetTape targetSlot timeBlock).rank :=
  predecessor_rank_lt_internal
    tm x blockLength timeBlock targetTape targetSlot
    ((predecessorIndexEquiv workTapeCount).symm index)

variable {V : Type*}

theorem value_unroll_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (4 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).value =
      nodeValue tm x blockLength sourceValue combine node := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [unroll, nodeValue, TreeEval.Tree.value_leaf]
      | computation tape slot timeBlock =>
          rw [unroll, nodeValue, TreeEval.Tree.value_node]
          apply congrArg (combine tape slot timeBlock)
          funext index
          exact ih _
            (predecessorAt_rank_lt_internal
              tm x blockLength timeBlock tape slot index)

theorem height_unroll_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (4 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).height ≤
      node.rank := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [unroll, TreeEval.Tree.height_leaf]
          rfl
      | computation tape slot timeBlock =>
          rw [unroll, TreeEval.Tree.height_node]
          have hsup :
              Finset.univ.sup (fun index =>
                (unroll tm x blockLength sourceValue combine
                  (predecessorAt
                    tm x blockLength timeBlock index)).height) ≤
                timeBlock := by
            rw [Finset.sup_le_iff]
            intro index _
            exact
              (ih _
                (predecessorAt_rank_lt_internal
                  tm x blockLength timeBlock tape slot index)).trans
                (Nat.lt_succ_iff.mp
                  (predecessorAt_rank_lt_internal
                    tm x blockLength timeBlock tape slot index))
          simpa [Node.rank, Nat.add_comm] using
            Nat.add_le_add_left hsup 1

end Internal

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
