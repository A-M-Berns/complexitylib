/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Defs

/-!
# Recovering horizon observations from the neighborhood graph

For an arbitrary requested tape block, the latest-block query selects the
greatest interval strictly before a horizon whose three-block neighborhood
contains that block. It chooses the matching slot in that interval, or the
initial source when no such interval exists.

A chronological query supplies the state at the horizon. A latest-block
query on the output block containing cell `1` supplies the verdict symbol.
Together these two compact neighborhood-node values form the final decision
snapshot.

## Main definitions

* `latestBlockNode` -- latest neighborhood copy of an arbitrary block
* `stateNode` -- chronological node carrying the horizon state
* `verdictBlockNode` -- latest node for the output block containing cell `1`
* `decisionSnapshot` -- state and verdict recovered from those two nodes
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace DecisionRecovery

/-- Latest computed neighborhood slot containing `block` before `horizon`,
or the block's initial source if it has not appeared in any earlier
neighborhood. -/
def latestBlockNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    Node workTapeCount :=
  match previousInterval tm x blockLength tape block horizon with
  | none =>
      .source tape block
  | some previous =>
      .computation tape
        (matchingSlot
          (centerBlock tm x blockLength previous.val tape)
          block)
        previous.val

/-- A chronological node carrying the machine state at the start of
`horizon`. The input-tape copy is chosen canonically; every tape's
chronological copy carries the same state. -/
def stateNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) : Node workTapeCount :=
  chronologicalPredecessor tm x blockLength horizon
    (TapeIndex.input workTapeCount)

/-- Latest neighborhood node for the output block containing verdict cell
`1` at the start of `horizon`. -/
def verdictBlockNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) : Node workTapeCount :=
  latestBlockNode tm x blockLength horizon
    (TapeIndex.output workTapeCount)
    (blockIndex blockLength 1)

/-- Offset of verdict cell `1` inside its canonical tape block. -/
def verdictOffset (blockLength : ℕ) (hpositive : 0 < blockLength) :
    Fin blockLength :=
  ⟨1 % blockLength, Nat.mod_lt 1 hpositive⟩

/-- Final state and output verdict recovered from two compact neighborhood
node values. -/
@[ext] structure Snapshot (Q : Type*) where
  /-- Machine state at the requested horizon. -/
  state : Q
  /-- Symbol in output cell `1` at the requested horizon. -/
  verdict : Γ

/-- Read the two compact semantic node values forming the horizon decision
snapshot. -/
def decisionSnapshot
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ) : Snapshot tm.Q :=
  { state :=
      (NeighborhoodContent.nodeContent
        tm x blockLength hpositive
        (stateNode tm x blockLength horizon)).state
    verdict :=
      (NeighborhoodContent.nodeContent
        tm x blockLength hpositive
        (verdictBlockNode tm x blockLength horizon)).cells
        (verdictOffset blockLength hpositive) }

end DecisionRecovery

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
