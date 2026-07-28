/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph
import Complexitylib.TreeEvaluation.Defs

/-!
# Implicit computation-graph unrolling

This file turns the executable predecessor oracle into two well-founded
semantic objects:

- `nodeValue` recursively evaluates source and local node functions;
- `unroll` expands the same recursion into a fixed-arity tree.

Both recurse on `Node.rank`. The tree is a semantic specification and may be
exponentially large; the eventual simulator must retain the predecessor path
and regenerate nodes rather than construct this term.

## Main definitions

- `ComputationGraph.nodeValue` -- recursive computation-graph semantics
- `ComputationGraph.unroll` -- the corresponding tree-evaluation instance
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

variable {workTapeCount : ℕ} {V : Type*}

/-- Evaluate source labels and local computation-node functions recursively
through the implicit predecessor oracle. -/
def nodeValue (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → ℕ →
      (Fin (2 * (workTapeCount + 2)) → V) → V) :
    Node workTapeCount → V
  | .source tape block => sourceValue tape block
  | .computation tape timeBlock =>
      combine tape timeBlock fun index =>
        nodeValue tm x blockLength sourceValue combine
          (predecessorAt tm x blockLength timeBlock index)
termination_by node => node.rank
decreasing_by
  exact predecessorAt_rank_lt
    tm x blockLength timeBlock tape index

/-- Unroll one computation-graph node into its fixed-arity semantic
tree-evaluation instance. -/
def unroll (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → ℕ →
      (Fin (2 * (workTapeCount + 2)) → V) → V) :
    Node workTapeCount →
      TreeEval.Tree (2 * (workTapeCount + 2)) V
  | .source tape block => .leaf (sourceValue tape block)
  | .computation tape timeBlock =>
      .node
        (fun index =>
          unroll tm x blockLength sourceValue combine
            (predecessorAt tm x blockLength timeBlock index))
        (combine tape timeBlock)
termination_by node => node.rank
decreasing_by
  exact predecessorAt_rank_lt
    tm x blockLength timeBlock tape index

end ComputationGraph

end TimeSpaceSimulation

end Complexity
