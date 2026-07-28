/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Defs

/-!
# Implicit computation-graph topology internals

This file proves correctness of the greatest-prior-visit search, the exact
predecessor count, and strict rank decrease for every generated edge.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Internal

theorem mem_priorVisits_internal {active : ℕ → ℕ}
    {time previous : ℕ} :
    previous ∈ priorVisits active time ↔
      previous < time ∧ active previous = active time := by
  simp [priorVisits]

theorem previousVisit_some_mem_internal {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous) :
    previous ∈ priorVisits active time := by
  unfold previousVisit at h
  split at h
  · next hnonempty =>
      simp only [Option.some.injEq] at h
      rw [← h]
      exact Finset.max'_mem _ hnonempty
  · contradiction

theorem previousVisit_some_lt_internal {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous) :
    previous < time :=
  (mem_priorVisits_internal.mp
    (previousVisit_some_mem_internal h)).1

theorem previousVisit_some_active_internal {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous) :
    active previous = active time :=
  (mem_priorVisits_internal.mp
    (previousVisit_some_mem_internal h)).2

theorem previousVisit_some_maximal_internal {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous)
    {candidate : ℕ} (hcandidate : candidate < time)
    (hactive : active candidate = active time) :
    candidate ≤ previous := by
  unfold previousVisit at h
  split at h
  · next hnonempty =>
      simp only [Option.some.injEq] at h
      rw [← h]
      exact Finset.le_max' _ _
        (mem_priorVisits_internal.mpr ⟨hcandidate, hactive⟩)
  · contradiction

theorem previousVisit_eq_none_iff_internal {active : ℕ → ℕ}
    {time : ℕ} :
    previousVisit active time = none ↔
      ∀ previous, previous < time →
        active previous ≠ active time := by
  constructor
  · intro h previous hlt heq
    have hmem : previous ∈ priorVisits active time :=
      mem_priorVisits_internal.mpr ⟨hlt, heq⟩
    unfold previousVisit at h
    split at h
    · contradiction
    · next hnone => exact hnone ⟨previous, hmem⟩
  · intro h
    unfold previousVisit
    split
    · next hnonempty =>
      obtain ⟨previous, hmem⟩ := hnonempty
      obtain ⟨hlt, heq⟩ := mem_priorVisits_internal.mp hmem
      exact absurd heq (h previous hlt)
    · rfl

theorem card_predecessorKind_internal :
    Fintype.card PredecessorKind = 2 := by
  decide

theorem card_predecessorIndex_internal (workTapeCount : ℕ) :
    Fintype.card (PredecessorIndex workTapeCount) =
      2 * (workTapeCount + 2) := by
  simp [PredecessorIndex, card_predecessorKind_internal]

theorem contentPredecessor_tape_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape : TapeIndex workTapeCount) :
    (contentPredecessor tm x blockLength timeBlock tape).tape = tape := by
  dsimp only [contentPredecessor]
  generalize hprevious :
    previousVisit (activeTrajectory tm x blockLength tape) timeBlock =
      result
  cases result <;> simp [Node.tape]

theorem chronologicalPredecessor_tape_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape : TapeIndex workTapeCount) :
    (chronologicalPredecessor tm x blockLength timeBlock tape).tape =
      tape := by
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
      | content =>
          exact contentPredecessor_tape_internal
            tm x blockLength timeBlock tape
      | chronological =>
          exact chronologicalPredecessor_tape_internal
            tm x blockLength timeBlock tape

theorem contentPredecessor_rank_lt_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape targetTape : TapeIndex workTapeCount) :
    (contentPredecessor tm x blockLength timeBlock tape).rank <
      (Node.computation targetTape timeBlock).rank := by
  dsimp only [contentPredecessor]
  generalize hprevious :
    previousVisit (activeTrajectory tm x blockLength tape) timeBlock =
      result
  cases result with
  | none =>
      simp [Node.rank]
  | some previous =>
      simp only [Node.rank]
      exact Nat.succ_lt_succ (previousVisit_some_lt_internal hprevious)

theorem chronologicalPredecessor_rank_lt_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape targetTape : TapeIndex workTapeCount) :
    (chronologicalPredecessor tm x blockLength timeBlock tape).rank <
      (Node.computation targetTape timeBlock).rank := by
  cases timeBlock <;> simp [chronologicalPredecessor, Node.rank]

theorem predecessor_rank_lt_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (index : PredecessorIndex workTapeCount) :
    (predecessor tm x blockLength timeBlock index).rank <
      (Node.computation targetTape timeBlock).rank := by
  cases index with
  | mk kind tape =>
      cases kind with
      | content =>
          exact contentPredecessor_rank_lt_internal
            tm x blockLength timeBlock tape targetTape
      | chronological =>
          exact chronologicalPredecessor_rank_lt_internal
            tm x blockLength timeBlock tape targetTape

theorem predecessorAt_rank_lt_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (index : Fin (2 * (workTapeCount + 2))) :
    (predecessorAt tm x blockLength timeBlock index).rank <
      (Node.computation targetTape timeBlock).rank := by
  exact predecessor_rank_lt_internal tm x blockLength timeBlock
    targetTape ((predecessorIndexEquiv workTapeCount).symm index)

end Internal

end ComputationGraph

end TimeSpaceSimulation

end Complexity
