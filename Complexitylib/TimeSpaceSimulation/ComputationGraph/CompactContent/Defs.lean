/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalFunction.Defs

/-!
# Compact computation-graph node values

The rich semantic node value stores an absolute head position and graph
metadata. Neither belongs in the value alphabet evaluated by Cook--Mertz.
For a fixed target node, the graph supplies the active block, and the head
position is needed only modulo the block length. This file therefore defines
the compact value used by the final simulation.

The compact local function reconstructs absolute starting heads from the
target active blocks and the chronological predecessors' head remainders,
then executes one genuine time block. A later encoding layer represents this
value using one-hot fields of total width `Fintype.card Q + 5 * blockLength`.

## Main definitions

- `Content` -- state, head remainder, and one finite tape block
- `nodeContent` -- compact projection of a rich semantic node value
- `predecessorCfg` -- reconstruct a local configuration from compact inputs
- `localNodeFunction` -- execute one time block on compact inputs
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactContent

/-- The compact value carried by a computation-graph node. -/
@[ext] structure Content (blockLength : ℕ) (Q : Type*) where
  /-- Machine state at the node's sampled configuration. -/
  state : Q
  /-- Named head position modulo the positive block length. -/
  headRemainder : Fin blockLength
  /-- Symbols in the named tape block carried by this node. -/
  cells : Fin blockLength → Γ

/-- Compact projection of one rich semantic node value. -/
def nodeContent (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) : Content blockLength tm.Q :=
  let value :=
    ComputationGraph.nodeContent tm x blockLength node
  { state := value.state
    headRemainder :=
      ⟨value.head % blockLength, Nat.mod_lt _ hpositive⟩
    cells := value.cells }

/-- Actual compact values at every ordered predecessor of one computation
node. -/
def predecessorContents
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (hpositive : 0 < blockLength) :
    PredecessorIndex workTapeCount → Content blockLength tm.Q :=
  fun index =>
    nodeContent tm x blockLength hpositive
      (predecessor tm x blockLength timeBlock index)

/-- Assemble a local start configuration from arbitrary compact predecessor
values. Chronological values supply the state and head remainders; content
values supply the selected tape blocks. -/
def predecessorCfg
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (inputs : PredecessorIndex workTapeCount →
      Content blockLength tm.Q) :
    Cfg workTapeCount tm.Q :=
  LocalFunction.cfgFromBlocks blockLength
    (activeBlocks tm x blockLength timeBlock)
    (inputs
      (.chronological, TapeIndex.input workTapeCount)).state
    (fun tape =>
      activeBlocks tm x blockLength timeBlock tape * blockLength +
        (inputs (.chronological, tape)).headRemainder.val)
    (fun tape => (inputs (.content, tape)).cells)

/-- Execute one genuine time block from compact predecessor values and return
the compact value for the requested target tape. -/
def localNodeFunction
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (timeBlock : ℕ) (targetTape : TapeIndex workTapeCount)
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
        (activeBlocks tm x blockLength timeBlock targetTape) }

end CompactContent

end ComputationGraph

end TimeSpaceSimulation

end Complexity
