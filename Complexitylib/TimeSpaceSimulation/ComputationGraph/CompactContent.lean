/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactContent.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactContent.Internal

/-!
# Correct compact computation-graph node values

The compact node value retains only a machine state, a head position modulo
the positive block length, and one finite tape block. Absolute block numbers
and node identities remain graph metadata. The local function reconstructs
absolute starting heads and executes the original machine for one full time
block.

## Main theorems

- `predecessorCfg_eq_localizedCfg` -- compact inputs reconstruct the start
- `localNodeFunction_semantic` -- the compact local transition is correct
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactContent

/-- Actual compact predecessor values reconstruct the canonical localization
of the target time block's starting configuration. -/
theorem predecessorCfg_eq_localizedCfg
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    predecessorCfg tm x blockLength timeBlock
        (predecessorContents tm x blockLength timeBlock
          (h.blockLength_pos tm x blockLength)) =
      LocalFunction.localizedCfg blockLength
        (activeBlocks tm x blockLength timeBlock)
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)) :=
  Internal.predecessorCfg_eq_localizedCfg_internal
    tm x blockLength timeBlock h

/-- The compact local function computes exactly the compact semantic target
value when supplied actual compact predecessor values. -/
theorem localNodeFunction_semantic
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    localNodeFunction tm x blockLength
        (h.blockLength_pos tm x blockLength)
        timeBlock targetTape
        (predecessorContents tm x blockLength timeBlock
          (h.blockLength_pos tm x blockLength)) =
      nodeContent tm x blockLength
        (h.blockLength_pos tm x blockLength)
        (.computation targetTape timeBlock) :=
  Internal.localNodeFunction_semantic_internal
    tm x blockLength timeBlock targetTape h

end CompactContent

end ComputationGraph

end TimeSpaceSimulation

end Complexity
