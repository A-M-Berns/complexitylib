/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents.Defs

/-!
# Querying an arbitrary tape block at a time horizon

The computation graph normally asks for the block active in a target time
block. Recovering a decider's verdict instead requires output cell `1`, whose
block need not be active at the final time. This file defines the greatest
visit to an arbitrary requested block before a horizon and returns the graph
node carrying its latest contents.

## Main definitions

- `blockVisits` -- visits to a requested block before a horizon
- `lastBlockVisit` -- greatest such visit, if any
- `latestBlockNode` -- latest computation node or initial source node
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Time blocks before `horizon` in which `active` selects `block`. -/
def blockVisits (active : ℕ → ℕ) (block horizon : ℕ) :
    Finset ℕ :=
  (Finset.range horizon).filter fun timeBlock =>
    active timeBlock = block

/-- Greatest visit to `block` strictly before `horizon`, if one exists. -/
def lastBlockVisit (active : ℕ → ℕ)
    (block horizon : ℕ) : Option ℕ :=
  if h : (blockVisits active block horizon).Nonempty then
    some ((blockVisits active block horizon).max' h)
  else
    none

/-- Graph node carrying the latest contents of an arbitrary requested block
at the start of `horizon`. -/
def latestBlockNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    Node workTapeCount :=
  match lastBlockVisit
      (activeTrajectory tm x blockLength tape) block horizon with
  | none => .source tape block
  | some previous => .computation tape previous

/-- Graph node whose block contains the decider verdict cell `1` at the start
of `horizon`. -/
def verdictBlockNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) : Node workTapeCount :=
  latestBlockNode tm x blockLength horizon
    (TapeIndex.output workTapeCount)
    (blockIndex blockLength 1)

end ComputationGraph

end TimeSpaceSimulation

end Complexity
