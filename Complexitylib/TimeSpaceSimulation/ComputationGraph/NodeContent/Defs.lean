/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents.Defs

/-!
# Rich semantic values for computation-graph nodes

Williams's local time-block simulation needs more than tape-block cells. It
also receives the machine state and named head positions at the start of the
target time block. This file packages the semantic value associated with one
per-tape computation-graph node.

A source node is sampled from `TM.configurationAt x 0`. A computation node for
time block `i` is sampled from the configuration after that block, at time
`timeBlockStart blockLength (i + 1)`. Its `block` field remains the block that
was active during `i`, even if the final transition moves the head into an
adjacent block.

## Main definitions

* `NodeContent` -- node identity, block, state, named head, and block cells
* `nodeConfigurationTime` -- configuration sampled by one node
* `nodeBlock` -- tape block whose cells the node carries
* `nodeContent` -- the rich semantic value of one node
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Rich semantic value carried by one per-tape computation-graph node. -/
@[ext] structure NodeContent (workTapeCount blockLength : ℕ)
    (Q : Type*) where
  /-- Identity of the source or time-block computation node. -/
  node : Node workTapeCount
  /-- Tape block whose symbols are carried in `cells`. -/
  block : ℕ
  /-- Machine state in the configuration sampled by this node. -/
  state : Q
  /-- Absolute position of this node's named tape head. -/
  head : ℕ
  /-- Symbols of `block`, in increasing offset order. -/
  cells : Fin blockLength → Γ

/-- Configuration time sampled by a computation-graph node.

Sources use the initial configuration. A computation node uses the end of its
time block. -/
def nodeConfigurationTime (blockLength : ℕ) :
    Node workTapeCount → ℕ
  | .source _ _ => 0
  | .computation _ timeBlock =>
      timeBlockStart blockLength (timeBlock + 1)

/-- Tape block whose cells are carried by a computation-graph node. -/
def nodeBlock (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) : Node workTapeCount → ℕ
  | .source _ block => block
  | .computation tape timeBlock =>
      tm.activeBlock x blockLength timeBlock tape

/-- Rich semantic value of one computation-graph node. -/
def nodeContent (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    NodeContent workTapeCount blockLength tm.Q :=
  let time := nodeConfigurationTime blockLength node
  let cfg := tm.configurationAt x time
  let tape := node.tape
  let block := nodeBlock tm x blockLength node
  { node
    block
    state := cfg.state
    head := (tapeAt cfg tape).head
    cells := blockContents (tapeAt cfg tape) blockLength block }

end ComputationGraph

end TimeSpaceSimulation

end Complexity
