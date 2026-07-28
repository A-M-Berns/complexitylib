/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents.Internal

/-!
# Computation-graph tape-block content soundness

This module exposes the semantic bridge between a block-respecting Turing
machine run and Williams's last-visit computation graph. A transition changes
only the cell under the current head. Consequently an inactive tape block is
unchanged throughout a time block, and repeated inactive time blocks preserve
it. The greatest-prior-visit predecessor therefore carries exactly the active
block contents needed at the start of the target time block.

These results establish content-edge soundness. They do not yet construct the
local `blockLength`-step transition function that combines all predecessor
values into a computation node.

## Main theorems

- `TM.configurationAt_cells_add_eq_of_avoids` -- cell persistence over time
- `blockContentsAt_add_eq_of_headBlock_ne` -- block persistence when avoided
- `inactive_timeBlock_preserves` -- one inactive time block preserves content
- `inactive_timeBlocks_preserve` -- an inactive range preserves content
- `nodeBlockContents_contentPredecessor` -- content-edge semantic soundness
-/

namespace Complexity

namespace Tape

/-- A write-and-move transition changes no cell other than the old head
position. -/
theorem writeAndMove_cells_of_ne
    (tape : Tape) (symbol : Γ) (direction : Dir3)
    {position : ℕ} (hne : position ≠ tape.head) :
    (tape.writeAndMove symbol direction).cells position =
      tape.cells position :=
  TimeSpaceSimulation.ComputationGraph.Internal.writeAndMove_cells_of_ne_internal
    tape symbol direction hne

end Tape

namespace NTM

/-- One traced NTM transition preserves a named tape cell away from that
tape's current head. This includes the halted, frozen-trace case. -/
theorem tapeAt_trace_one_cells_of_ne
    (tm : NTM workTapeCount) (cfg : Cfg workTapeCount tm.Q)
    (choice : Bool)
    (tape : TimeSpaceSimulation.TapeIndex workTapeCount)
    (position : ℕ)
    (hne : position ≠
      (TimeSpaceSimulation.tapeAt cfg tape).head) :
    (TimeSpaceSimulation.tapeAt
        (tm.trace 1 (fun _ => choice) cfg) tape).cells position =
      (TimeSpaceSimulation.tapeAt cfg tape).cells position :=
  TimeSpaceSimulation.ComputationGraph.Internal.tapeAt_trace_one_cells_of_ne_internal
      tm cfg choice tape position hne

end NTM

namespace TM

open TimeSpaceSimulation

/-- Split the final transition from the deterministic frozen trace. -/
theorem configurationAt_succ
    (tm : TM workTapeCount) (x : List Bool) (time : ℕ) :
    tm.configurationAt x (time + 1) =
      tm.toNTM.trace 1 (fun _ => false)
        (tm.configurationAt x time) :=
  TimeSpaceSimulation.ComputationGraph.Internal.configurationAt_succ_internal
    tm x time

/-- One deterministic frozen-trace transition preserves a named tape cell
away from that tape's current head. -/
theorem configurationAt_cell_succ_of_ne
    (tm : TM workTapeCount) (x : List Bool) (time : ℕ)
    (tape : TapeIndex workTapeCount) (position : ℕ)
    (hne : position ≠
      (tapeAt (tm.configurationAt x time) tape).head) :
    (tapeAt (tm.configurationAt x (time + 1)) tape).cells position =
      (tapeAt (tm.configurationAt x time) tape).cells position :=
  TimeSpaceSimulation.ComputationGraph.Internal.configurationAt_cell_succ_of_ne_internal
      tm x time tape position hne

/-- A named tape cell avoided by its head during `steps` successive
transitions has the same final and initial symbol. -/
theorem configurationAt_cells_add_eq_of_avoids
    (tm : TM workTapeCount) (x : List Bool)
    (start steps : ℕ) (tape : TapeIndex workTapeCount) (position : ℕ)
    (havoid : ∀ offset, offset < steps →
      position ≠
        (tapeAt (tm.configurationAt x (start + offset)) tape).head) :
    (tapeAt (tm.configurationAt x (start + steps)) tape).cells position =
      (tapeAt (tm.configurationAt x start) tape).cells position :=
  TimeSpaceSimulation.ComputationGraph.Internal.configurationAt_cells_add_eq_of_avoids_internal
    tm x start steps tape position havoid

end TM

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Every offset of a block points to a position inside that block. -/
theorem blockOffset_in_block
    (blockLength block : ℕ) (offset : Fin blockLength) :
    InBlock blockLength block
      (block * blockLength + offset.val) :=
  Internal.blockOffset_in_block_internal blockLength block offset

/-- Membership in a contiguous block determines the quotient block index. -/
theorem blockIndex_eq_of_inBlock
    {blockLength block position : ℕ}
    (h : InBlock blockLength block position) :
    blockIndex blockLength position = block :=
  Internal.blockIndex_eq_of_inBlock_internal h

/-- A tape block avoided by the named head for `steps` successive
transitions retains all of its contents. -/
theorem blockContentsAt_add_eq_of_headBlock_ne
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength block start steps : ℕ)
    (tape : TapeIndex workTapeCount)
    (havoid : ∀ offset, offset < steps →
      headBlock blockLength
        (tm.configurationAt x (start + offset)) tape ≠ block) :
    blockContentsAt tm x blockLength (start + steps) tape block =
      blockContentsAt tm x blockLength start tape block :=
  Internal.blockContentsAt_add_eq_of_headBlock_ne_internal
    tm x blockLength block start steps tape havoid

/-- One block-respecting time block preserves every inactive tape block. -/
theorem inactive_timeBlock_preserves
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock block : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength)
    (hinactive :
      tm.activeBlock x blockLength timeBlock tape ≠ block) :
    blockContentsAt tm x blockLength
        (timeBlockStart blockLength (timeBlock + 1)) tape block =
      blockContentsAt tm x blockLength
        (timeBlockStart blockLength timeBlock) tape block :=
  Internal.inactive_timeBlock_preserves_internal
    tm x blockLength timeBlock block tape h hinactive

/-- A range of block-respecting time blocks that all avoid a tape block
preserves that block's contents. -/
theorem inactive_timeBlocks_preserve
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength first count block : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength)
    (hinactive : ∀ offset, offset < count →
      tm.activeBlock x blockLength (first + offset) tape ≠ block) :
    blockContentsAt tm x blockLength
        (timeBlockStart blockLength (first + count)) tape block =
      blockContentsAt tm x blockLength
        (timeBlockStart blockLength first) tape block :=
  Internal.inactive_timeBlocks_preserve_internal
    tm x blockLength first count block tape h hinactive

/-- The content predecessor selected by the greatest-prior-visit oracle
carries exactly the active tape-block contents at the start of the target
time block. -/
theorem nodeBlockContents_contentPredecessor
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    nodeBlockContents tm x blockLength
        (contentPredecessor tm x blockLength timeBlock tape) =
      startBlockContents tm x blockLength tape timeBlock :=
  Internal.nodeBlockContents_contentPredecessor_internal
    tm x blockLength timeBlock tape h

end ComputationGraph

end TimeSpaceSimulation

end Complexity
