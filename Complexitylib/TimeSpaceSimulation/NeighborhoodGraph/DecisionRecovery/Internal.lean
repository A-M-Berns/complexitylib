/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.BlockRespecting
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodPersistence

/-!
# Correctness internals for neighborhood-graph decision recovery

The proofs use three-block persistence directly. They do not import the
unfinished local-node correctness layer and require no block-respecting
hypothesis.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace DecisionRecovery

namespace Internal

theorem latestBlockNode_tape_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    (latestBlockNode tm x blockLength horizon tape block).tape =
      tape := by
  unfold latestBlockNode
  generalize hprevious :
    previousInterval tm x blockLength tape block horizon = result
  cases result <;> rfl

theorem latestBlockNode_block_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    (latestBlockNode tm x blockLength horizon tape block).block
        tm x blockLength =
      block := by
  unfold latestBlockNode
  generalize hprevious :
    previousInterval tm x blockLength tape block horizon = result
  cases result with
  | none =>
      rfl
  | some previous =>
      simp only [Node.block, requestedBlock]
      exact previousInterval_matchingSlot hprevious

theorem nodeContent_latestBlockNode_cells_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hpositive : 0 < blockLength) :
    (NeighborhoodContent.nodeContent
      tm x blockLength hpositive
      (latestBlockNode
        tm x blockLength horizon tape block)).cells =
      ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength horizon) tape block := by
  generalize hprevious :
    previousInterval tm x blockLength tape block horizon = result
  cases result with
  | none =>
      rw [show
        latestBlockNode tm x blockLength horizon tape block =
          .source tape block by
        simp [latestBlockNode, hprevious]]
      change
        ComputationGraph.blockContentsAt
            tm x blockLength 0 tape block =
          ComputationGraph.blockContentsAt tm x blockLength
            (timeBlockStart blockLength horizon) tape block
      symm
      have hpersist :=
        NeighborhoodPersistence.inactive_intervals_preserve
          tm x blockLength 0 horizon block tape hpositive
      simpa [timeBlockStart] using hpersist (by
        intro offset hoffset
        simpa [NeighborhoodPersistence.centerBlock, centerBlock]
          using previousInterval_eq_none_iff.mp hprevious
            ⟨offset, hoffset⟩)
  | some previous =>
      rw [show
        latestBlockNode tm x blockLength horizon tape block =
          .computation tape
            (matchingSlot
              (centerBlock tm x blockLength previous.val tape)
              block)
            previous.val by
        simp [latestBlockNode, hprevious]]
      change
        ComputationGraph.blockContentsAt tm x blockLength
            (timeBlockStart blockLength (previous.val + 1)) tape
            (neighborBlock
              (centerBlock tm x blockLength previous.val tape)
              (matchingSlot
                (centerBlock tm x blockLength previous.val tape)
                block)) =
          ComputationGraph.blockContentsAt tm x blockLength
            (timeBlockStart blockLength horizon) tape block
      rw [previousInterval_matchingSlot hprevious]
      symm
      let count := horizon - (previous.val + 1)
      have hpersist :=
        NeighborhoodPersistence.inactive_intervals_preserve
          tm x blockLength (previous.val + 1) count
            block tape hpositive
      have hsum : previous.val + 1 + count = horizon := by
        dsimp only [count]
        omega
      rw [hsum] at hpersist
      exact hpersist (by
        intro offset hoffset hcontains
        have hcandidateLt :
            previous.val + 1 + offset < horizon := by
          dsimp only [count] at hoffset
          omega
        let candidate : Fin horizon :=
          ⟨previous.val + 1 + offset, hcandidateLt⟩
        have hgraph :
            NeighborhoodContains
              (centerBlock tm x blockLength candidate.val tape)
              block := by
          simpa [NeighborhoodPersistence.centerBlock, centerBlock]
            using hcontains
        have hmax :=
          previousInterval_some_maximal
            hprevious candidate hgraph
        have himpossible :
            previous.val + 1 + offset ≤ previous.val := by
          exact hmax
        omega)

theorem nodeContent_stateNode_state_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (NeighborhoodContent.nodeContent tm x blockLength hpositive
      (stateNode tm x blockLength horizon)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).state := by
  cases horizon <;>
    simp [stateNode, chronologicalPredecessor,
      NeighborhoodContent.nodeContent,
      NeighborhoodContent.nodeConfigurationTime,
      timeBlockStart]

theorem nodeContent_verdictBlockNode_cell_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (NeighborhoodContent.nodeContent tm x blockLength hpositive
      (verdictBlockNode tm x blockLength horizon)).cells
        (verdictOffset blockLength hpositive) =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 := by
  rw [verdictBlockNode,
    nodeContent_latestBlockNode_cells_internal
      tm x blockLength horizon
        (TapeIndex.output workTapeCount)
        (blockIndex blockLength 1) hpositive]
  unfold ComputationGraph.blockContentsAt
  rw [tapeAt_output]
  exact blockContents_ownBlock
    (tm.configurationAt x
      (timeBlockStart blockLength horizon)).output
    blockLength 1 hpositive

theorem decisionSnapshot_state_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (decisionSnapshot
      tm x blockLength hpositive horizon).state =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).state := by
  unfold decisionSnapshot
  exact nodeContent_stateNode_state_internal
    tm x blockLength horizon hpositive

theorem decisionSnapshot_verdict_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (decisionSnapshot
      tm x blockLength hpositive horizon).verdict =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 := by
  unfold decisionSnapshot
  exact nodeContent_verdictBlockNode_cell_internal
    tm x blockLength horizon hpositive

theorem decisionSnapshot_eq_of_reachesIn_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon haltTime : ℕ)
    (hpositive : 0 < blockLength)
    (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (hle :
      haltTime ≤ timeBlockStart blockLength horizon) :
    decisionSnapshot tm x blockLength hpositive horizon =
      { state := cfg.state
        verdict := cfg.output.cells 1 } := by
  apply Snapshot.ext
  · rw [decisionSnapshot_state_internal
      tm x blockLength horizon hpositive]
    exact congrArg Cfg.state
      (tm.configurationAt_of_reachesIn
        hreach hhalt hle)
  · rw [decisionSnapshot_verdict_internal
      tm x blockLength horizon hpositive]
    exact congrArg (fun current =>
      current.output.cells 1)
      (tm.configurationAt_of_reachesIn
        hreach hhalt hle)

end Internal

end DecisionRecovery

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
