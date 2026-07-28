/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.BlockRespecting.Defs
import Complexitylib.TimeSpaceSimulation.BlockRespecting.Internal

/-!
# Block-respecting multitape computations

This file exposes the semantic interface for the block-respecting
normalization used in Williams's time-to-space simulation. The definition
covers the library's read-only input head, every work head, and the output
head. Its half-open time-block convention makes the allowed boundary crossing
explicit.

The results here characterize a machine already known to be block respecting.
They do not yet construct the Hopcroft--Paul--Valiant normalized machine or
prove its linear time overhead.

## Main theorems

- `TM.configurationAt_reaches` -- every frozen-trace configuration is reachable
- `TM.BlockRespectingOnInput.headBlock` -- each head has one active block
- `TM.BlockRespectingOnInput.head_in_activeBlock` -- exact residency theorem
- `TM.BlockRespectingOnInput.head_in_timeBlock` -- arbitrary-time form
-/

namespace Complexity

namespace TimeSpaceSimulation

variable {workTapeCount : ℕ} {Q : Type}

/-- Selecting the named input tape returns the configuration's input tape. -/
@[simp] theorem tapeAt_input (cfg : Cfg workTapeCount Q) :
    tapeAt cfg (TapeIndex.input workTapeCount) = cfg.input :=
  Internal.tapeAt_input_internal cfg

/-- Selecting a named work tape returns that work tape. -/
@[simp] theorem tapeAt_work (cfg : Cfg workTapeCount Q)
    (index : Fin workTapeCount) :
    tapeAt cfg (TapeIndex.work index) = cfg.work index :=
  Internal.tapeAt_work_internal cfg index

/-- Selecting the named output tape returns the configuration's output tape. -/
@[simp] theorem tapeAt_output (cfg : Cfg workTapeCount Q) :
    tapeAt cfg (TapeIndex.output workTapeCount) = cfg.output :=
  Internal.tapeAt_output_internal cfg

/-- Every position lies in the tape block selected by Euclidean division. -/
theorem position_in_ownBlock (blockLength position : ℕ)
    (hpositive : 0 < blockLength) :
    InBlock blockLength (blockIndex blockLength position) position :=
  Internal.position_in_ownBlock_internal
    blockLength position hpositive

/-- Looking up a position at its quotient/remainder coordinates in its tape
block recovers the original tape cell. -/
theorem blockContents_ownBlock (tape : Tape)
    (blockLength position : ℕ) (hpositive : 0 < blockLength) :
    blockContents tape blockLength (blockIndex blockLength position)
        ⟨position % blockLength, Nat.mod_lt _ hpositive⟩ =
      tape.cells position :=
  Internal.blockContents_ownBlock_internal
    tape blockLength position hpositive

/-- The block containing the tape head contains the currently read symbol at
the head's remainder coordinate. -/
theorem blockContents_head (tape : Tape)
    (blockLength : ℕ) (hpositive : 0 < blockLength) :
    blockContents tape blockLength (blockIndex blockLength tape.head)
        ⟨tape.head % blockLength, Nat.mod_lt _ hpositive⟩ =
      tape.read :=
  Internal.blockContents_head_internal tape blockLength hpositive

end TimeSpaceSimulation

namespace TM

open TimeSpaceSimulation

variable {workTapeCount : ℕ}

/-- The deterministic frozen trace starts at the ordinary initial
configuration. -/
@[simp] theorem configurationAt_zero (tm : TM workTapeCount)
    (x : List Bool) :
    tm.configurationAt x 0 = tm.initCfg x :=
  TimeSpaceSimulation.Internal.configurationAt_zero_internal tm x

/-- Every deterministic frozen-trace configuration is reachable. -/
theorem configurationAt_reaches (tm : TM workTapeCount)
    (x : List Bool) (time : ℕ) :
    tm.reaches (tm.initCfg x) (tm.configurationAt x time) :=
  TimeSpaceSimulation.Internal.configurationAt_reaches_internal tm x time

/-- Once an exact run reaches a halted configuration, every later frozen-trace
configuration is that same configuration. -/
theorem configurationAt_of_reachesIn
    (tm : TM workTapeCount) {x : List Bool}
    {cfg : Cfg workTapeCount tm.Q} {haltTime horizon : ℕ}
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg) (hle : haltTime ≤ horizon) :
    tm.configurationAt x horizon = cfg :=
  TimeSpaceSimulation.Internal.configurationAt_of_reachesIn_internal
    tm hreach hhalt hle

namespace BlockRespectingOnInput

/-- A block-respecting run has positive block length. -/
theorem blockLength_pos (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (h : tm.BlockRespectingOnInput x blockLength) :
    0 < blockLength :=
  TimeSpaceSimulation.Internal.blockRespectingOnInput_blockLength_pos_internal
    tm x blockLength h

/-- A named head's block at any offset in a time block is the block active at
the start of that time block. -/
theorem headBlock (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (h : tm.BlockRespectingOnInput x blockLength)
    (timeBlock : ℕ) (offset : Fin blockLength)
    (tape : TapeIndex workTapeCount) :
    TimeSpaceSimulation.headBlock blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock + offset.val))
        tape =
      tm.activeBlock x blockLength timeBlock tape :=
  TimeSpaceSimulation.Internal.blockRespectingOnInput_headBlock_internal
    tm x blockLength h timeBlock offset tape

/-- Every named head lies inside its active tape block throughout a time
block. -/
theorem head_in_activeBlock (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (h : tm.BlockRespectingOnInput x blockLength)
    (timeBlock : ℕ) (offset : Fin blockLength)
    (tape : TapeIndex workTapeCount) :
    InBlock blockLength (tm.activeBlock x blockLength timeBlock tape)
      (tapeAt
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock + offset.val))
        tape).head :=
  TimeSpaceSimulation.Internal.blockRespectingOnInput_head_in_activeBlock_internal
    tm x blockLength h timeBlock offset tape

/-- Quotienting an arbitrary time by the block length identifies the active
tape block containing every named head. -/
theorem headBlock_at_time (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (h : tm.BlockRespectingOnInput x blockLength)
    (time : ℕ) (tape : TapeIndex workTapeCount) :
    TimeSpaceSimulation.headBlock blockLength
        (tm.configurationAt x time) tape =
      tm.activeBlock x blockLength (time / blockLength) tape :=
  TimeSpaceSimulation.Internal.blockRespectingOnInput_headBlock_at_time_internal
    tm x blockLength h time tape

/-- Arbitrary-time residency form of the block-respecting property. -/
theorem head_in_timeBlock (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (h : tm.BlockRespectingOnInput x blockLength)
    (time : ℕ) (tape : TapeIndex workTapeCount) :
    InBlock blockLength
      (tm.activeBlock x blockLength (time / blockLength) tape)
      (tapeAt (tm.configurationAt x time) tape).head :=
  TimeSpaceSimulation.Internal.blockRespectingOnInput_head_in_timeBlock_internal
    tm x blockLength h time tape

end BlockRespectingOnInput

namespace BlockRespecting

/-- Specialize a length-indexed block-respecting machine to one input. -/
theorem onInput (tm : TM workTapeCount) (blockLength : ℕ → ℕ)
    (h : tm.BlockRespecting blockLength) (x : List Bool) :
    tm.BlockRespectingOnInput x (blockLength x.length) :=
  TimeSpaceSimulation.Internal.blockRespecting_onInput_internal
    tm blockLength h x

end BlockRespecting

end TM

end Complexity
