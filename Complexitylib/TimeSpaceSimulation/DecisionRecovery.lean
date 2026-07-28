/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.DecisionRecovery.Defs
import Complexitylib.TimeSpaceSimulation.DecisionRecovery.Internal

/-!
# Correct final decision recovery

For a block-respecting computation, two padded Boolean tree evaluations
recover exactly the machine state and output verdict cell at the chosen time
horizon.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace DecisionRecovery

open ComputationGraph

/-- Unpadding and decoding a well-formed compact encoding recovers its value. -/
theorem recoverContent_pad_encode
    (tm : TM workTapeCount) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (value : CompactContent.Content blockLength tm.Q) :
    recoverContent tm blockLength hpositive
        (TreeEval.BooleanPadding.padBits
          (PaddedTree.fanIn workTapeCount)
          (CompactEncoding.encode value)) =
      value :=
  Internal.recoverContent_pad_encode_internal
    tm blockLength hpositive value

/-- The state query decodes to its chronological predecessor's compact
semantic value. -/
theorem recoverContent_stateTree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    recoverContent tm blockLength hpositive
        (stateTree tm x blockLength hpositive horizon).value =
      CompactContent.nodeContent tm x blockLength hpositive
        (chronologicalPredecessor tm x blockLength horizon
          (TapeIndex.input workTapeCount)) :=
  Internal.recoverContent_stateTree_internal
    tm x blockLength hpositive horizon h

/-- The verdict query decodes to the latest verdict-block node's compact
semantic value. -/
theorem recoverContent_verdictTree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    recoverContent tm blockLength hpositive
        (verdictTree tm x blockLength hpositive horizon).value =
      CompactContent.nodeContent tm x blockLength hpositive
        (verdictBlockNode tm x blockLength horizon) :=
  Internal.recoverContent_verdictTree_internal
    tm x blockLength hpositive horizon h

/-- The recovered snapshot state is exactly the frozen-run state at the
horizon. -/
theorem decisionSnapshot_state
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    (decisionSnapshot tm x blockLength
      (h.blockLength_pos tm x blockLength) horizon).state =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).state :=
  Internal.decisionSnapshot_state_internal
    tm x blockLength horizon h

/-- The recovered snapshot verdict is exactly output cell `1` at the
horizon. -/
theorem decisionSnapshot_verdict
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    (decisionSnapshot tm x blockLength
      (h.blockLength_pos tm x blockLength) horizon).verdict =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 :=
  Internal.decisionSnapshot_verdict_internal
    tm x blockLength horizon h

/-- Once a halted exact run lies below the queried horizon, the recovered
snapshot is exactly that halted configuration's state and verdict cell. -/
theorem decisionSnapshot_eq_of_reachesIn
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
        verdict := cfg.output.cells 1 } :=
  Internal.decisionSnapshot_eq_of_reachesIn_internal
    tm x blockLength horizon haltTime cfg
      hrespecting hreach hhalt hle

end DecisionRecovery

end TimeSpaceSimulation

end Complexity
