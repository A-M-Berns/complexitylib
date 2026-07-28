/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LatestBlock.Defs

/-!
# Correctness of arbitrary latest-block queries
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Internal

theorem mem_blockVisits_internal {active : ℕ → ℕ}
    {block horizon timeBlock : ℕ} :
    timeBlock ∈ blockVisits active block horizon ↔
      timeBlock < horizon ∧ active timeBlock = block := by
  simp [blockVisits]

theorem lastBlockVisit_some_mem_internal {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous) :
    previous ∈ blockVisits active block horizon := by
  unfold lastBlockVisit at h
  split at h
  · next hnonempty =>
      simp only [Option.some.injEq] at h
      rw [← h]
      exact Finset.max'_mem _ hnonempty
  · contradiction

theorem lastBlockVisit_some_lt_internal {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous) :
    previous < horizon :=
  (mem_blockVisits_internal.mp
    (lastBlockVisit_some_mem_internal h)).1

theorem lastBlockVisit_some_active_internal {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous) :
    active previous = block :=
  (mem_blockVisits_internal.mp
    (lastBlockVisit_some_mem_internal h)).2

theorem lastBlockVisit_some_maximal_internal {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous)
    {candidate : ℕ} (hcandidate : candidate < horizon)
    (hactive : active candidate = block) :
    candidate ≤ previous := by
  unfold lastBlockVisit at h
  split at h
  · next hnonempty =>
      simp only [Option.some.injEq] at h
      rw [← h]
      exact Finset.le_max' _ _
        (mem_blockVisits_internal.mpr
          ⟨hcandidate, hactive⟩)
  · contradiction

theorem lastBlockVisit_eq_none_iff_internal {active : ℕ → ℕ}
    {block horizon : ℕ} :
    lastBlockVisit active block horizon = none ↔
      ∀ timeBlock, timeBlock < horizon →
        active timeBlock ≠ block := by
  constructor
  · intro h timeBlock hlt heq
    have hmem :
        timeBlock ∈ blockVisits active block horizon :=
      mem_blockVisits_internal.mpr ⟨hlt, heq⟩
    unfold lastBlockVisit at h
    split at h
    · contradiction
    · next hnone =>
      exact hnone ⟨timeBlock, hmem⟩
  · intro h
    unfold lastBlockVisit
    split
    · next hnonempty =>
      obtain ⟨timeBlock, hmem⟩ := hnonempty
      obtain ⟨hlt, heq⟩ :=
        mem_blockVisits_internal.mp hmem
      exact absurd heq (h timeBlock hlt)
    · rfl

theorem nodeBlockContents_latestBlockNode_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    nodeBlockContents tm x blockLength
        (latestBlockNode tm x blockLength horizon tape block) =
      blockContentsAt tm x blockLength
        (timeBlockStart blockLength horizon) tape block := by
  generalize hprevious :
    lastBlockVisit
      (activeTrajectory tm x blockLength tape)
      block horizon = result
  cases result with
  | none =>
      rw [show
        latestBlockNode tm x blockLength horizon tape block =
          .source tape block by
        simp [latestBlockNode, hprevious]]
      simp only [nodeBlockContents]
      unfold sourceBlockContents
      symm
      have hpersist :=
        inactive_timeBlocks_preserve
          tm x blockLength 0 horizon block tape h
      simpa [timeBlockStart] using hpersist (by
        intro offset hoffset
        simpa [activeTrajectory] using
          lastBlockVisit_eq_none_iff_internal.mp
            hprevious offset hoffset)
  | some previous =>
      rw [show
        latestBlockNode tm x blockLength horizon tape block =
          .computation tape previous by
        simp [latestBlockNode, hprevious]]
      have hprevious_lt :
          previous < horizon :=
        lastBlockVisit_some_lt_internal hprevious
      have hsame :
          activeTrajectory tm x blockLength tape previous =
            block :=
        lastBlockVisit_some_active_internal hprevious
      simp only [nodeBlockContents]
      unfold computedBlockContents
      change tm.activeBlock x blockLength previous tape =
        block at hsame
      rw [hsame]
      symm
      let count := horizon - (previous + 1)
      have hpersist :=
        inactive_timeBlocks_preserve
          tm x blockLength (previous + 1) count
            block tape h
      have hsum : previous + 1 + count = horizon := by
        dsimp only [count]
        omega
      rw [hsum] at hpersist
      exact hpersist (by
        intro offset hoffset hactive
        have hcandidate_lt :
            previous + 1 + offset < horizon := by
          dsimp only [count] at hoffset
          omega
        have hcandidate_le :=
          lastBlockVisit_some_maximal_internal
            hprevious hcandidate_lt (by
              simpa [activeTrajectory] using hactive)
        omega)

theorem verdictBlockNode_cell_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    nodeBlockContents tm x blockLength
        (verdictBlockNode tm x blockLength horizon)
        ⟨1 % blockLength,
          Nat.mod_lt 1 (h.blockLength_pos tm x blockLength)⟩ =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 := by
  rw [verdictBlockNode,
    nodeBlockContents_latestBlockNode_internal
      tm x blockLength horizon
        (TapeIndex.output workTapeCount)
        (blockIndex blockLength 1) h]
  unfold blockContentsAt
  rw [tapeAt_output]
  exact blockContents_ownBlock
    (tm.configurationAt x
      (timeBlockStart blockLength horizon)).output
    blockLength 1
    (h.blockLength_pos tm x blockLength)

end Internal

end ComputationGraph

end TimeSpaceSimulation

end Complexity
