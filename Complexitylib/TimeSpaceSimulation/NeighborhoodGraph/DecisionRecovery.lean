/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery.Internal

/-!
# Correct horizon recovery from the neighborhood graph

For any named tape block, `latestBlockNode` returns the greatest computed
neighborhood copy strictly before the requested horizon, selecting the slot
that carries exactly that block. If no earlier neighborhood contains it, the
query returns its initial source.

Three-block persistence proves that this node's compact cell vector equals
the actual block contents at the start of the horizon. Applying the query to
the output block containing cell `1`, together with one chronological state
node, recovers the exact frozen-run decision snapshot.

These theorems apply to arbitrary deterministic machines. They require only a
positive interval length and never assume `BlockRespectingOnInput`.

## Main theorems

* `nodeContent_latestBlockNode_cells` -- arbitrary block recovery
* `nodeContent_stateNode_state` -- chronological horizon state
* `nodeContent_verdictBlockNode_cell` -- output cell `1`
* `decisionSnapshot_eq_of_reachesIn` -- frozen halted snapshot recovery
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace DecisionRecovery

/-- If no earlier neighborhood contains the block, its latest query is the
initial source. -/
theorem latestBlockNode_eq_source
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hnone :
      previousInterval tm x blockLength tape block horizon = none) :
    latestBlockNode tm x blockLength horizon tape block =
      .source tape block := by
  simp [latestBlockNode, hnone]

/-- A successful prior query selects its exact matching computed slot. -/
theorem latestBlockNode_eq_computation
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (previous : Fin horizon)
    (hsome :
      previousInterval tm x blockLength tape block horizon =
        some previous) :
    latestBlockNode tm x blockLength horizon tape block =
      .computation tape
        (matchingSlot
          (centerBlock tm x blockLength previous.val tape)
          block)
        previous.val := by
  simp [latestBlockNode, hsome]

/-- A latest-block query preserves the requested named tape. -/
@[simp] theorem latestBlockNode_tape
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    (latestBlockNode tm x blockLength horizon tape block).tape =
      tape :=
  Internal.latestBlockNode_tape_internal
    tm x blockLength horizon tape block

/-- A latest-block query carries exactly the requested block, including when
the left-boundary lower and center slots both denote block zero. -/
@[simp] theorem latestBlockNode_block
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    (latestBlockNode tm x blockLength horizon tape block).block
        tm x blockLength =
      block :=
  Internal.latestBlockNode_block_internal
    tm x blockLength horizon tape block

/-- The compact semantic cell vector at the latest queried node equals the
actual requested tape block at the horizon. -/
theorem nodeContent_latestBlockNode_cells
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hpositive : 0 < blockLength) :
    (NeighborhoodContent.nodeContent
      tm x blockLength hpositive
      (latestBlockNode
        tm x blockLength horizon tape block)).cells =
      ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength horizon) tape block :=
  Internal.nodeContent_latestBlockNode_cells_internal
    tm x blockLength horizon tape block hpositive

/-- The canonical chronological state node carries the exact machine state
at the horizon. -/
theorem nodeContent_stateNode_state
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (NeighborhoodContent.nodeContent tm x blockLength hpositive
      (stateNode tm x blockLength horizon)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).state :=
  Internal.nodeContent_stateNode_state_internal
    tm x blockLength horizon hpositive

/-- The latest output-block node recovers output cell `1` at the horizon. -/
theorem nodeContent_verdictBlockNode_cell
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (NeighborhoodContent.nodeContent tm x blockLength hpositive
      (verdictBlockNode tm x blockLength horizon)).cells
        (verdictOffset blockLength hpositive) =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 :=
  Internal.nodeContent_verdictBlockNode_cell_internal
    tm x blockLength horizon hpositive

/-- The recovered snapshot state is the frozen-run horizon state. -/
theorem decisionSnapshot_state
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (decisionSnapshot
      tm x blockLength hpositive horizon).state =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).state :=
  Internal.decisionSnapshot_state_internal
    tm x blockLength horizon hpositive

/-- The recovered snapshot verdict is output cell `1` at the horizon. -/
theorem decisionSnapshot_verdict
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (decisionSnapshot
      tm x blockLength hpositive horizon).verdict =
      (tm.configurationAt x
        (timeBlockStart blockLength horizon)).output.cells 1 :=
  Internal.decisionSnapshot_verdict_internal
    tm x blockLength horizon hpositive

/-- Once a halted exact run lies below the horizon, the two-node snapshot is
exactly that halted configuration's state and verdict cell. -/
theorem decisionSnapshot_eq_of_reachesIn
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
        verdict := cfg.output.cells 1 } :=
  Internal.decisionSnapshot_eq_of_reachesIn_internal
    tm x blockLength horizon haltTime hpositive
      cfg hreach hhalt hle

end DecisionRecovery

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
