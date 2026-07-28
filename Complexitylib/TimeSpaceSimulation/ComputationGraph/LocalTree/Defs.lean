/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalFunction.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Unroll.Defs

/-!
# Tree-evaluation instance for local time-block simulation

This file instantiates the generic computation-graph unrolling with rich node
contents and the genuine local time-block function. Sources read their initial
tape blocks. Computation nodes reconstruct a local configuration from their
`2 * (workTapeCount + 2)` predecessor values and execute one time block.

## Main definitions

- `localSourceFunction` -- rich semantic source-node values
- `localCombineFunction` -- fixed-arity wrapper around the local simulator
- `localNodeValue` -- recursive computation-graph evaluation
- `localTree` -- the corresponding fixed-arity Tree Evaluation instance
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace LocalTree

/-- Rich semantic value of one initial source block. -/
def localSourceFunction
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    NodeContent workTapeCount blockLength tm.Q :=
  nodeContent tm x blockLength (.source tape block)

/-- Fixed-arity wrapper around the genuine local time-block function.
`predecessorIndexEquiv` converts the tree evaluator's `Fin` ordering back to
the content/chronological predecessor index. -/
def localCombineFunction
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (tape : TapeIndex workTapeCount) (timeBlock : ℕ)
    (children : Fin (2 * (workTapeCount + 2)) →
      NodeContent workTapeCount blockLength tm.Q) :
    NodeContent workTapeCount blockLength tm.Q :=
  LocalFunction.localNodeFunction
    tm x blockLength timeBlock tape fun index =>
      children (predecessorIndexEquiv workTapeCount index)

/-- Recursive local-function evaluation on the implicit computation graph. -/
def localNodeValue
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ) :
    Node workTapeCount →
      NodeContent workTapeCount blockLength tm.Q :=
  nodeValue tm x blockLength
    (localSourceFunction tm x blockLength)
    (localCombineFunction tm x blockLength)

/-- Fixed-arity Tree Evaluation instance obtained by unrolling the implicit
local-function computation graph. -/
def localTree
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ) :
    Node workTapeCount →
      TreeEval.Tree (2 * (workTapeCount + 2))
        (NodeContent workTapeCount blockLength tm.Q) :=
  unroll tm x blockLength
    (localSourceFunction tm x blockLength)
    (localCombineFunction tm x blockLength)

end LocalTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
