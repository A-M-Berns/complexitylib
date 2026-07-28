/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LatestBlock.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LatestBlock.Internal

/-!
# Correct arbitrary latest-block queries

The greatest visit to a requested block carries exactly that block's contents
at the target horizon. In particular, querying the output block containing
cell `1` recovers the decider's verdict symbol.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Membership in the finite arbitrary-block visit set. -/
theorem mem_blockVisits {active : ℕ → ℕ}
    {block horizon timeBlock : ℕ} :
    timeBlock ∈ blockVisits active block horizon ↔
      timeBlock < horizon ∧ active timeBlock = block :=
  Internal.mem_blockVisits_internal

/-- A successful query returns a member of the requested visit set. -/
theorem lastBlockVisit_some_mem {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous) :
    previous ∈ blockVisits active block horizon :=
  Internal.lastBlockVisit_some_mem_internal h

/-- A returned visit lies strictly before the requested horizon. -/
theorem lastBlockVisit_some_lt {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous) :
    previous < horizon :=
  Internal.lastBlockVisit_some_lt_internal h

/-- A returned visit selects the requested block. -/
theorem lastBlockVisit_some_active {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous) :
    active previous = block :=
  Internal.lastBlockVisit_some_active_internal h

/-- Every other matching visit lies no later than the returned one. -/
theorem lastBlockVisit_some_maximal {active : ℕ → ℕ}
    {block horizon previous : ℕ}
    (h : lastBlockVisit active block horizon = some previous)
    {candidate : ℕ} (hcandidate : candidate < horizon)
    (hactive : active candidate = block) :
    candidate ≤ previous :=
  Internal.lastBlockVisit_some_maximal_internal
    h hcandidate hactive

/-- No result means precisely that the block was never active before the
horizon. -/
theorem lastBlockVisit_eq_none_iff {active : ℕ → ℕ}
    {block horizon : ℕ} :
    lastBlockVisit active block horizon = none ↔
      ∀ timeBlock, timeBlock < horizon →
        active timeBlock ≠ block :=
  Internal.lastBlockVisit_eq_none_iff_internal

/-- The latest-block node carries the requested block exactly as it appears
at the start of the horizon. -/
theorem nodeBlockContents_latestBlockNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    nodeBlockContents tm x blockLength
        (latestBlockNode tm x blockLength horizon tape block) =
      blockContentsAt tm x blockLength
        (timeBlockStart blockLength horizon) tape block :=
  Internal.nodeBlockContents_latestBlockNode_internal
    tm x blockLength horizon tape block h

/-- The queried output-block coordinate equals verdict cell `1` at the target
horizon. -/
theorem verdictBlockNode_cell
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    nodeBlockContents tm x blockLength
        (verdictBlockNode tm x blockLength horizon)
        ⟨1 % blockLength,
          Nat.mod_lt 1 (h.blockLength_pos tm x blockLength)⟩ =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 :=
  Internal.verdictBlockNode_cell_internal
    tm x blockLength horizon h

end ComputationGraph

end TimeSpaceSimulation

end Complexity
