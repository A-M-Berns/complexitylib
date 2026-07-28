/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalSimulation.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalSimulation.Internal

/-!
# Sound local simulation of a block-respecting time block

Two configurations that agree on the state, named heads, and one selected
block of every tape evolve in lockstep for as long as the heads stay in those
blocks. The final theorem specializes this noninterference principle to a
block-respecting time block: any locally agreeing seed configuration can
replay the whole block and recover the actual final state, heads, and active
block contents.

This is the semantic core of a computation-graph node function. The next
layer assembles such a seed from chronological and last-visit predecessor
values.

## Main theorems

- `TapeBlockAgreement.read_eq` -- local agreement gives equal reads
- `trace_one_cfgBlockAgreement` -- one transition preserves agreement
- `configurationAt_trace_cfgBlockAgreement` -- finite lockstep simulation
- `timeBlock_trace_cfgBlockAgreement` -- block-respecting specialization
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace TapeBlockAgreement

/-- Locally agreeing tapes read the same symbol when the left head lies in
the selected block. -/
theorem read_eq
    {blockLength block : ℕ} {left right : Tape}
    (h : TapeBlockAgreement blockLength block left right)
    (hleft : InBlock blockLength block left.head) :
    left.read = right.read :=
  ComputationGraph.LocalSimulation.Internal.tapeBlockAgreement_read_eq_internal
    h hleft

/-- Moving both locally agreeing tapes in the same direction preserves their
agreement. -/
theorem move
    {blockLength block : ℕ} {left right : Tape}
    (h : TapeBlockAgreement blockLength block left right)
    (direction : Dir3) :
    TapeBlockAgreement blockLength block
      (left.move direction) (right.move direction) :=
  ComputationGraph.LocalSimulation.Internal.tapeBlockAgreement_move_internal
    h direction

/-- Applying the same write-and-move action to locally agreeing tapes
preserves their agreement. -/
theorem writeAndMove
    {blockLength block : ℕ} {left right : Tape}
    (h : TapeBlockAgreement blockLength block left right)
    (symbol : Γ) (direction : Dir3) :
    TapeBlockAgreement blockLength block
      (left.writeAndMove symbol direction)
      (right.writeAndMove symbol direction) :=
  ComputationGraph.LocalSimulation.Internal.tapeBlockAgreement_writeAndMove_internal
    h symbol direction

end TapeBlockAgreement

namespace ComputationGraph

namespace LocalSimulation

/-- One deterministic transition preserves selected-block agreement whenever
all current heads lie in their selected blocks. -/
theorem trace_one_cfgBlockAgreement
    (tm : TM workTapeCount) (blockLength : ℕ)
    (blocks : TapeIndex workTapeCount → ℕ)
    (left right : Cfg workTapeCount tm.Q)
    (h : CfgBlockAgreement blockLength blocks left right)
    (hinput :
      InBlock blockLength (blocks (TapeIndex.input workTapeCount))
        left.input.head)
    (hwork : ∀ index,
      InBlock blockLength (blocks (TapeIndex.work index))
        (left.work index).head)
    (houtput :
      InBlock blockLength (blocks (TapeIndex.output workTapeCount))
        left.output.head) :
    CfgBlockAgreement blockLength blocks
      (tm.toNTM.trace 1 (fun _ => false) left)
      (tm.toNTM.trace 1 (fun _ => false) right) :=
  Internal.trace_one_cfgBlockAgreement_internal
    tm blockLength blocks left right h hinput hwork houtput

/-- Lockstep local agreement across an arbitrary finite frozen-trace
interval. -/
theorem configurationAt_trace_cfgBlockAgreement
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (blocks : TapeIndex workTapeCount → ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (hstart : CfgBlockAgreement blockLength blocks
      (tm.configurationAt x start) seed)
    (hinput : ∀ offset, offset < steps →
      InBlock blockLength (blocks (TapeIndex.input workTapeCount))
        (tm.configurationAt x (start + offset)).input.head)
    (hwork : ∀ offset, offset < steps → ∀ index,
      InBlock blockLength (blocks (TapeIndex.work index))
        ((tm.configurationAt x (start + offset)).work index).head)
    (houtput : ∀ offset, offset < steps →
      InBlock blockLength (blocks (TapeIndex.output workTapeCount))
        (tm.configurationAt x (start + offset)).output.head) :
    CfgBlockAgreement blockLength blocks
      (tm.configurationAt x (start + steps))
      (tm.toNTM.trace steps (fun _ => false) seed) :=
  Internal.configurationAt_trace_cfgBlockAgreement_internal
    tm x blockLength start steps blocks seed hstart
      hinput hwork houtput

/-- A block-respecting time block can be replayed from any seed that agrees
with its initial state, heads, and active tape blocks. The replay recovers the
actual final state, heads, and those active block contents. -/
theorem timeBlock_trace_cfgBlockAgreement
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (hrespecting : tm.BlockRespectingOnInput x blockLength)
    (hstart : CfgBlockAgreement blockLength
      (activeBlocks tm x blockLength timeBlock)
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock))
      seed) :
    CfgBlockAgreement blockLength
      (activeBlocks tm x blockLength timeBlock)
      (tm.configurationAt x
        (timeBlockStart blockLength (timeBlock + 1)))
      (tm.toNTM.trace blockLength (fun _ => false) seed) :=
  Internal.timeBlock_trace_cfgBlockAgreement_internal
    tm x blockLength timeBlock seed hrespecting hstart

end LocalSimulation

end ComputationGraph

end TimeSpaceSimulation

end Complexity
