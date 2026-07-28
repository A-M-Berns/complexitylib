/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactContent.Defs
import Complexitylib.TimeSpaceSimulation.Locality.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Defs

/-!
# Compact semantic values for the three-block neighborhood graph

Every graph value carries one tape block, one machine state, and the named
head position modulo the positive block length. A local node receives three
content blocks and one chronological value for every named tape. It rebuilds
the three-block neighborhoods around the real interval-start heads, executes
one block of transitions, and returns the requested output block.

These definitions apply directly to arbitrary deterministic machines. They
do not assume a block-respecting normalization.

## Main definitions

- `nodeContent` -- the actual compact value carried by a neighborhood node
- `tapeFromNeighborhood` -- rebuild one tape from three finite blocks
- `predecessorCfg` -- rebuild a local interval-start configuration
- `localNodeFunction` -- execute one genuine interval and return one block
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodContent

open NeighborhoodGraph

/-- Compact values are shared with the one-block computation graph: a state,
one head remainder, and one finite tape block. -/
abbrev Content (blockLength : ℕ) (Q : Type*) :=
  ComputationGraph.CompactContent.Content blockLength Q

/-- Configuration time sampled by a neighborhood-graph node. Sources use the
initial configuration; a computation node uses the end of its interval. -/
def nodeConfigurationTime (blockLength : ℕ) :
    Node workTapeCount → ℕ
  | .source _ _ => 0
  | .computation _ _ timeBlock =>
      timeBlockStart blockLength (timeBlock + 1)

/-- Actual compact semantic value carried by one neighborhood-graph node. -/
def nodeContent (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) : Content blockLength tm.Q :=
  let cfg :=
    tm.configurationAt x (nodeConfigurationTime blockLength node)
  let tape := node.tape
  { state := cfg.state
    headRemainder :=
      ⟨(tapeAt cfg tape).head % blockLength,
        Nat.mod_lt _ hpositive⟩
    cells :=
      blockContents (tapeAt cfg tape) blockLength
        (node.block tm x blockLength) }

/-- Actual compact values at all fixed-arity predecessors of one interval. -/
def predecessorContents
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (hpositive : 0 < blockLength) :
    PredecessorIndex workTapeCount → Content blockLength tm.Q :=
  fun index =>
    nodeContent tm x blockLength hpositive
      (predecessor tm x blockLength timeBlock index)

/-- Reconstruct a total tape from the lower, center, and upper blocks around
`centerBlock`. Positions outside that neighborhood are filled with blanks. -/
def tapeFromNeighborhood (blockLength centerBlock head : ℕ)
    (contents : Slot → Fin blockLength → Γ) : Tape where
  head := head
  cells position :=
    if hpositive : 0 < blockLength then
      let block := blockIndex blockLength position
      if NeighborhoodContains centerBlock block then
        contents (matchingSlot centerBlock block)
          ⟨position % blockLength, Nat.mod_lt _ hpositive⟩
      else
        Γ.blank
    else
      Γ.blank

/-- Assemble a configuration from a state, absolute heads, and three
neighborhood blocks for every named tape. -/
def cfgFromNeighborhoods (blockLength : ℕ)
    (centerBlocks : TapeIndex workTapeCount → ℕ) (state : Q)
    (heads : TapeIndex workTapeCount → ℕ)
    (contents :
      TapeIndex workTapeCount → Slot → Fin blockLength → Γ) :
    Cfg workTapeCount Q where
  state := state
  input :=
    tapeFromNeighborhood blockLength
      (centerBlocks (TapeIndex.input workTapeCount))
      (heads (TapeIndex.input workTapeCount))
      (contents (TapeIndex.input workTapeCount))
  work index :=
    tapeFromNeighborhood blockLength
      (centerBlocks (TapeIndex.work index))
      (heads (TapeIndex.work index))
      (contents (TapeIndex.work index))
  output :=
    tapeFromNeighborhood blockLength
      (centerBlocks (TapeIndex.output workTapeCount))
      (heads (TapeIndex.output workTapeCount))
      (contents (TapeIndex.output workTapeCount))

/-- Canonically restrict a full configuration to all three blocks around
each named head while preserving the state and absolute head positions. -/
def localizedCfg (blockLength : ℕ) (cfg : Cfg workTapeCount Q) :
    Cfg workTapeCount Q :=
  cfgFromNeighborhoods blockLength
    (startingBlocks blockLength cfg)
    cfg.state
    (fun tape => (tapeAt cfg tape).head)
    (fun tape slot =>
      blockContents (tapeAt cfg tape) blockLength
        (neighborBlock
          (startingBlocks blockLength cfg tape) slot))

/-- Assemble an interval-start configuration from arbitrary compact
predecessor values. Chronological inputs provide state and head remainders;
the three content inputs provide the selected neighborhood blocks. -/
def predecessorCfg
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (inputs : PredecessorIndex workTapeCount →
      Content blockLength tm.Q) :
    Cfg workTapeCount tm.Q :=
  cfgFromNeighborhoods blockLength
    (centerBlock tm x blockLength timeBlock)
    (inputs
      (.chronological, TapeIndex.input workTapeCount)).state
    (fun tape =>
      centerBlock tm x blockLength timeBlock tape * blockLength +
        (inputs (.chronological, tape)).headRemainder.val)
    (fun tape slot => (inputs (.content slot, tape)).cells)

/-- Execute one genuine length-`blockLength` interval from compact
predecessor values and return the requested target tape/slot value. -/
def localNodeFunction
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (timeBlock : ℕ) (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (inputs : PredecessorIndex workTapeCount →
      Content blockLength tm.Q) :
    Content blockLength tm.Q :=
  let final :=
    tm.toNTM.trace blockLength (fun _ => false)
      (predecessorCfg tm x blockLength timeBlock inputs)
  { state := final.state
    headRemainder :=
      ⟨(tapeAt final targetTape).head % blockLength,
        Nat.mod_lt _ hpositive⟩
    cells :=
      blockContents (tapeAt final targetTape) blockLength
        (requestedBlock tm x blockLength timeBlock
          targetTape targetSlot) }

end NeighborhoodContent

end TimeSpaceSimulation

end Complexity
