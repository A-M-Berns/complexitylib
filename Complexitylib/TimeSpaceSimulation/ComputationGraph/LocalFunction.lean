/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalFunction.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalFunction.Internal

/-!
# Correct local computation-graph node function

The local node function reconstructs only the active block of each named tape,
fills every other cell with blanks, and runs the machine for one time block.
For a block-respecting computation this is sound: chronological predecessors
supply the exact initial state and heads, content predecessors supply the
exact active blocks, and cells outside those blocks cannot be observed.

Unlike a constant semantic function, `localNodeFunction` genuinely executes
the machine from its supplied predecessor values. This module proves exact
agreement on the actual computation graph. Compact graph encoding, invalid
guess detection, and a concrete space-bounded implementation are separate
later layers.

## Main theorems

- `cfg_localized_agreement` -- localization preserves all observable data
- `predecessorCfg_eq_localizedCfg` -- predecessor values reconstruct the start
- `localNodeFunction_semantic` -- the local function computes its target node
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace LocalFunction

/-- Reconstructing a tape from its own selected block preserves its head and
all symbols in that block. -/
theorem tapeFromBlock_agreement
    (blockLength block : ℕ) (hpositive : 0 < blockLength)
    (tape : Tape) :
    TapeBlockAgreement blockLength block tape
      (tapeFromBlock blockLength block tape.head
        (blockContents tape blockLength block)) :=
  Internal.tapeFromBlock_agreement_internal
    blockLength block hpositive tape

/-- Canonically localizing a full configuration preserves the state, every
named head, and all selected block contents. -/
theorem cfg_localized_agreement
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (blocks : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount Q) :
    CfgBlockAgreement blockLength blocks cfg
      (localizedCfg blockLength blocks cfg) :=
  Internal.cfg_localized_agreement_internal
    blockLength hpositive blocks cfg

/-- Configuration block agreement specializes to any named tape. -/
theorem CfgBlockAgreement.tapeAt
    {blockLength : ℕ}
    {blocks : TapeIndex workTapeCount → ℕ}
    {left right : Cfg workTapeCount Q}
    (h : CfgBlockAgreement blockLength blocks left right)
    (tape : TapeIndex workTapeCount) :
    TapeBlockAgreement blockLength (blocks tape)
      (tapeAt left tape) (tapeAt right tape) :=
  Internal.cfgBlockAgreement_tapeAt_internal h tape

/-- On the actual computation graph, chronological and content predecessor
values assemble to the canonical localization of the target time block's
starting configuration. -/
theorem predecessorCfg_eq_localizedCfg
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    predecessorCfg tm x blockLength timeBlock
        (predecessorNodeContents tm x blockLength timeBlock) =
      localizedCfg blockLength
        (activeBlocks tm x blockLength timeBlock)
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)) :=
  Internal.predecessorCfg_eq_localizedCfg_internal
    tm x blockLength timeBlock h

/-- The genuine local time-block function computes exactly the rich semantic
value of its target computation node when supplied the actual predecessor
values. -/
theorem localNodeFunction_semantic
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    localNodeFunction tm x blockLength timeBlock targetTape
        (predecessorNodeContents tm x blockLength timeBlock) =
      nodeContent tm x blockLength
        (.computation targetTape timeBlock) :=
  Internal.localNodeFunction_semantic_internal
    tm x blockLength timeBlock targetTape h

end LocalFunction

end ComputationGraph

end TimeSpaceSimulation

end Complexity
