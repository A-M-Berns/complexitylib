/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Defs

/-!
# Computation-graph tape-block contents

This file defines the semantic tape-block values carried by Williams's
computation graph. A source node contains one block from the initial
configuration. A computation node for time block `i` contains the block that
was active during `i`, sampled after the `blockLength` transitions of that
time block.

The distinction between `startBlockContents` and `computedBlockContents`
records the half-open convention of `TM.BlockRespectingOnInput`: the final
transition of a time block may move the head into a neighboring block, but its
write still occurs in the old active block.

## Main definitions

- `blockContentsAt` -- one tape block at an arbitrary configuration time
- `sourceBlockContents` -- an initial source value
- `startBlockContents` -- the active block at the start of a time block
- `computedBlockContents` -- that active block after the time block
- `nodeBlockContents` -- the semantic value of a computation-graph node
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Contents of one named tape block at an arbitrary configuration time. -/
def blockContentsAt (tm : TM workTapeCount) (x : List Bool)
    (blockLength time : ℕ) (tape : TapeIndex workTapeCount)
    (block : ℕ) : Fin blockLength → Γ :=
  blockContents (tapeAt (tm.configurationAt x time) tape)
    blockLength block

/-- Contents of one named tape block in the initial configuration. -/
def sourceBlockContents (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (block : ℕ) : Fin blockLength → Γ :=
  blockContentsAt tm x blockLength 0 tape block

/-- Contents of the active block at the start of a time block. -/
def startBlockContents (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (timeBlock : ℕ) : Fin blockLength → Γ :=
  blockContentsAt tm x blockLength
    (timeBlockStart blockLength timeBlock) tape
    (tm.activeBlock x blockLength timeBlock tape)

/-- Contents of the block active during `timeBlock`, sampled immediately
after that time block. -/
def computedBlockContents (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (timeBlock : ℕ) : Fin blockLength → Γ :=
  blockContentsAt tm x blockLength
    (timeBlockStart blockLength (timeBlock + 1)) tape
    (tm.activeBlock x blockLength timeBlock tape)

/-- Semantic tape-block contents carried by a computation-graph node. -/
def nodeBlockContents (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) : Node workTapeCount → Fin blockLength → Γ
  | .source tape block =>
      sourceBlockContents tm x blockLength tape block
  | .computation tape timeBlock =>
      computedBlockContents tm x blockLength tape timeBlock

end ComputationGraph

end TimeSpaceSimulation

end Complexity
