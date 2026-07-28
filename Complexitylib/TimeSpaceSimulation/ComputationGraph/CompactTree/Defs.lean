/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactContent.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Unroll.Defs

/-!
# Compact tree-evaluation instance

This file unrolls the local compact computation-graph function into the
generic fixed-arity Tree Evaluation problem. Every value stores only a state,
one head remainder, and one finite tape block.

## Main definitions

- `sourceFunction` -- compact semantic source values
- `combineFunction` -- fixed-arity compact local transition
- `nodeValue` -- recursive compact graph evaluation
- `tree` -- compact Tree Evaluation instance
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactTree

/-- Compact semantic value of one source tape block. -/
def sourceFunction
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    CompactContent.Content blockLength tm.Q :=
  CompactContent.nodeContent tm x blockLength hpositive
    (.source tape block)

/-- Fixed-arity wrapper around the compact local transition. -/
def combineFunction
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (timeBlock : ℕ)
    (children : Fin (2 * (workTapeCount + 2)) →
      CompactContent.Content blockLength tm.Q) :
    CompactContent.Content blockLength tm.Q :=
  CompactContent.localNodeFunction
    tm x blockLength hpositive timeBlock tape fun index =>
      children (predecessorIndexEquiv workTapeCount index)

/-- Recursive compact evaluation on the implicit computation graph. -/
def nodeValue
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength) :
    Node workTapeCount →
      CompactContent.Content blockLength tm.Q :=
  ComputationGraph.nodeValue tm x blockLength
    (sourceFunction tm x blockLength hpositive)
    (combineFunction tm x blockLength hpositive)

/-- Fixed-arity compact Tree Evaluation instance. -/
def tree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength) :
    Node workTapeCount →
      TreeEval.Tree (2 * (workTapeCount + 2))
        (CompactContent.Content blockLength tm.Q) :=
  unroll tm x blockLength
    (sourceFunction tm x blockLength hpositive)
    (combineFunction tm x blockLength hpositive)

end CompactTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
