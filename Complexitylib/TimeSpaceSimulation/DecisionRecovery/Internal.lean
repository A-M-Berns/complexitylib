/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LatestBlock
import Complexitylib.TimeSpaceSimulation.ComputationGraph.PaddedTree
import Complexitylib.TimeSpaceSimulation.DecisionRecovery.Defs
import Complexitylib.TreeEvaluation.BooleanPadding

/-!
# Correctness of final decision recovery
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace DecisionRecovery

open ComputationGraph

namespace Internal

theorem recoverContent_pad_encode_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (value : CompactContent.Content blockLength tm.Q) :
    recoverContent tm blockLength hpositive
        (TreeEval.BooleanPadding.padBits
          (PaddedTree.fanIn workTapeCount)
          (CompactEncoding.encode value)) =
      value := by
  unfold recoverContent
  rw [TreeEval.BooleanPadding.unpadBits_padBits]
  exact CompactEncoding.decode_encode
    tm.qstart hpositive value

theorem recoverContent_stateTree_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    recoverContent tm blockLength hpositive
        (stateTree tm x blockLength hpositive horizon).value =
      CompactContent.nodeContent tm x blockLength hpositive
        (chronologicalPredecessor tm x blockLength horizon
          (TapeIndex.input workTapeCount)) := by
  unfold stateTree
  rw [PaddedTree.tree_value tm x blockLength hpositive h]
  exact recoverContent_pad_encode_internal
    tm blockLength hpositive _

theorem recoverContent_verdictTree_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    recoverContent tm blockLength hpositive
        (verdictTree tm x blockLength hpositive horizon).value =
      CompactContent.nodeContent tm x blockLength hpositive
        (verdictBlockNode tm x blockLength horizon) := by
  unfold verdictTree
  rw [PaddedTree.tree_value tm x blockLength hpositive h]
  exact recoverContent_pad_encode_internal
    tm blockLength hpositive _

theorem decisionSnapshot_state_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    (decisionSnapshot tm x blockLength
      (h.blockLength_pos tm x blockLength) horizon).state =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).state := by
  unfold decisionSnapshot
  rw [recoverContent_stateTree_internal
    tm x blockLength
      (h.blockLength_pos tm x blockLength)
      horizon h]
  exact nodeContent_chronologicalPredecessor_state
    tm x blockLength horizon
      (TapeIndex.input workTapeCount)

theorem decisionSnapshot_verdict_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    (decisionSnapshot tm x blockLength
      (h.blockLength_pos tm x blockLength) horizon).verdict =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 := by
  unfold decisionSnapshot
  rw [recoverContent_verdictTree_internal
    tm x blockLength
      (h.blockLength_pos tm x blockLength)
      horizon h]
  change
    (ComputationGraph.nodeContent tm x blockLength
      (verdictBlockNode tm x blockLength horizon)).cells
      ⟨1 % blockLength,
        Nat.mod_lt 1 (h.blockLength_pos tm x blockLength)⟩ = _
  rw [nodeContent_cells]
  exact verdictBlockNode_cell
    tm x blockLength horizon h

theorem decisionSnapshot_eq_of_reachesIn_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon haltTime : ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (hrespecting :
      tm.BlockRespectingOnInput x blockLength)
    (hreach :
      tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (hle :
      haltTime ≤ timeBlockStart blockLength horizon) :
    decisionSnapshot tm x blockLength
        (hrespecting.blockLength_pos tm x blockLength)
        horizon =
      { state := cfg.state
        verdict := cfg.output.cells 1 } := by
  apply Snapshot.ext
  · rw [decisionSnapshot_state_internal
      tm x blockLength horizon hrespecting]
    exact congrArg Cfg.state
      (tm.configurationAt_of_reachesIn
        hreach hhalt hle)
  · rw [decisionSnapshot_verdict_internal
      tm x blockLength horizon hrespecting]
    exact congrArg (fun current =>
      current.output.cells 1)
      (tm.configurationAt_of_reachesIn
        hreach hhalt hle)

end Internal

end DecisionRecovery

end TimeSpaceSimulation

end Complexity
