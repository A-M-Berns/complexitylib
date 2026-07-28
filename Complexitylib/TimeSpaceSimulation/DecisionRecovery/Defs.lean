/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LatestBlock.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.PaddedTree.Defs

/-!
# Recovering a final decision from implicit computation trees

Two implicit tree queries determine the bounded-time outcome:

* a chronological predecessor at the horizon carries the final state;
* the latest node for the output block containing cell `1` carries the
  verdict symbol.

The tree values are fan-in-padded Boolean vectors. This file removes the
padding, decodes their compact values, and packages the two observations.

## Main definitions

- `recoverContent` -- unpad and decode one compact tree value
- `stateTree` / `verdictTree` -- the two final implicit queries
- `decisionSnapshot` -- recovered final state and verdict symbol
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace DecisionRecovery

open ComputationGraph

/-- Final observations required to decide acceptance or rejection. -/
@[ext] structure Snapshot (Q : Type*) where
  /-- Machine state at the requested horizon. -/
  state : Q
  /-- Symbol in output verdict cell `1`. -/
  verdict : Γ

/-- Remove fan-in padding and decode one compact Boolean tree value. -/
noncomputable def recoverContent
    (tm : TM workTapeCount) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (bits : Fin (PaddedTree.width tm blockLength) → Bool) :
    CompactContent.Content blockLength tm.Q :=
  CompactEncoding.decode tm.qstart hpositive
    (TreeEval.BooleanPadding.unpadBits
      (PaddedTree.fanIn workTapeCount) bits)

/-- Implicit tree carrying the machine state at the start of `horizon`. -/
noncomputable def stateTree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ) :=
  PaddedTree.tree tm x blockLength hpositive
    (chronologicalPredecessor tm x blockLength horizon
      (TapeIndex.input workTapeCount))

/-- Implicit tree carrying the latest output block containing verdict cell
`1` at the start of `horizon`. -/
noncomputable def verdictTree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ) :=
  PaddedTree.tree tm x blockLength hpositive
    (verdictBlockNode tm x blockLength horizon)

/-- Decode the two implicit tree roots into the final state and verdict. -/
noncomputable def decisionSnapshot
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ) : Snapshot tm.Q :=
  { state :=
      (recoverContent tm blockLength hpositive
        (stateTree tm x blockLength hpositive horizon).value).state
    verdict :=
      (recoverContent tm blockLength hpositive
        (verdictTree tm x blockLength hpositive horizon).value).cells
        ⟨1 % blockLength, Nat.mod_lt 1 hpositive⟩ }

end DecisionRecovery

end TimeSpaceSimulation

end Complexity
