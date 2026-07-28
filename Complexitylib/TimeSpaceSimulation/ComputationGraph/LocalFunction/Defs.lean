/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalSimulation.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.NodeContent.Defs

/-!
# Local computation-graph node function

This file defines the genuine local function used at a computation-graph
node. It reconstructs one finite active block per named tape, initializes the
state and heads from chronological inputs, initializes the active block cells
from content inputs, and executes exactly `blockLength` transitions.

Cells outside the selected blocks are filled with blanks. The local
noninterference theorem proves that this arbitrary choice cannot affect the
result while the original run is block respecting.

## Main definitions

- `tapeFromBlock` -- reconstruct a total tape from one finite block
- `cfgFromBlocks` -- reconstruct a configuration from per-tape local data
- `localizedCfg` -- canonical localization of a full configuration
- `predecessorNodeContents` -- semantic values at all graph predecessors
- `predecessorCfg` -- assemble a local configuration from predecessor values
- `localNodeFunction` -- execute a time block and return one rich node value
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace LocalFunction

/-- Reconstruct a total tape from one finite block and an absolute head
position. Positions outside the block are filled with blanks. -/
def tapeFromBlock (blockLength block head : ℕ)
    (contents : Fin blockLength → Γ) : Tape where
  head := head
  cells position :=
    if hpositive : 0 < blockLength then
      if blockIndex blockLength position = block then
        contents ⟨position % blockLength, Nat.mod_lt _ hpositive⟩
      else
        Γ.blank
    else
      Γ.blank

/-- Assemble a total configuration from a state and one selected block,
absolute head, and finite cell vector for every named tape. -/
def cfgFromBlocks (blockLength : ℕ)
    (blocks : TapeIndex workTapeCount → ℕ) (state : Q)
    (heads : TapeIndex workTapeCount → ℕ)
    (contents : TapeIndex workTapeCount → Fin blockLength → Γ) :
    Cfg workTapeCount Q where
  state := state
  input :=
    tapeFromBlock blockLength
      (blocks (TapeIndex.input workTapeCount))
      (heads (TapeIndex.input workTapeCount))
      (contents (TapeIndex.input workTapeCount))
  work index :=
    tapeFromBlock blockLength
      (blocks (TapeIndex.work index))
      (heads (TapeIndex.work index))
      (contents (TapeIndex.work index))
  output :=
    tapeFromBlock blockLength
      (blocks (TapeIndex.output workTapeCount))
      (heads (TapeIndex.output workTapeCount))
      (contents (TapeIndex.output workTapeCount))

/-- Canonically localize a full configuration to one selected block per named
tape while retaining its state and absolute head positions. -/
def localizedCfg (blockLength : ℕ)
    (blocks : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount Q) : Cfg workTapeCount Q :=
  cfgFromBlocks blockLength blocks cfg.state
    (fun tape => (tapeAt cfg tape).head)
    (fun tape =>
      blockContents (tapeAt cfg tape) blockLength (blocks tape))

/-- Rich semantic values supplied by every ordered predecessor of a
computation node. -/
def predecessorNodeContents
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) :
    PredecessorIndex workTapeCount →
      NodeContent workTapeCount blockLength tm.Q :=
  fun index =>
    nodeContent tm x blockLength
      (predecessor tm x blockLength timeBlock index)

/-- Assemble the local start configuration from arbitrary ordered predecessor
values. The chronological inputs supply state and heads; the content inputs
supply active-block cells. -/
def predecessorCfg
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (inputs : PredecessorIndex workTapeCount →
      NodeContent workTapeCount blockLength tm.Q) :
    Cfg workTapeCount tm.Q :=
  cfgFromBlocks blockLength
    (activeBlocks tm x blockLength timeBlock)
    (inputs
      (.chronological, TapeIndex.input workTapeCount)).state
    (fun tape => (inputs (.chronological, tape)).head)
    (fun tape => (inputs (.content, tape)).cells)

/-- Simulate one time block from predecessor values and return the requested
per-tape rich node value. This function uses only the supplied predecessor
values, the target node metadata, and `blockLength` executions of `tm`. -/
def localNodeFunction
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (inputs : PredecessorIndex workTapeCount →
      NodeContent workTapeCount blockLength tm.Q) :
    NodeContent workTapeCount blockLength tm.Q :=
  let final :=
    tm.toNTM.trace blockLength (fun _ => false)
      (predecessorCfg tm x blockLength timeBlock inputs)
  { node := .computation targetTape timeBlock
    block := activeBlocks tm x blockLength timeBlock targetTape
    state := final.state
    head := (tapeAt final targetTape).head
    cells :=
      blockContents (tapeAt final targetTape) blockLength
        (activeBlocks tm x blockLength timeBlock targetTape) }

end LocalFunction

end ComputationGraph

end TimeSpaceSimulation

end Complexity
