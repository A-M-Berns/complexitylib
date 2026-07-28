/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.Defs

/-!
# Ordered bounded-fan-in computation DAGs

Williams's simulation does not materialize its exponentially large evaluation
tree. Instead, it stores a bounded-indegree computation graph and regenerates
the tree below a requested node. This file defines the semantic core of that
interface.

Nodes are indexed by `Fin size`. An internal node at index `i` stores exactly
`d` predecessors in `Fin i`, making acyclicity structural: every edge points
to a strictly smaller index. The graph is therefore suitable for an implicit
implementation in which `spec` is computed on demand.

The definitions here do not assign a resource bound to `spec`. A later
machine layer must implement that oracle and charge every call.

## Main definitions

- `OrderedDAG.Node` -- a leaf or an internal node with earlier children
- `OrderedDAG` -- a topologically ordered `d`-ary computation DAG
- `OrderedDAG.value` -- shared-DAG evaluation
- `OrderedDAG.unroll` -- the corresponding tree, duplicating shared subgraphs
- `OrderedDAG.depth` -- maximum dependency depth below a node
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

/-- The data stored at one topologically ordered computation-DAG node.

An internal node at index `i` may refer only to nodes in `Fin i`, so cycles are
unrepresentable. -/
inductive Node (d : ℕ) (V : Type*) (index : ℕ) where
  | leaf (value : V)
  | node (children : Fin d → Fin index) (combine : (Fin d → V) → V)

end OrderedDAG

/-- A bounded-fan-in computation DAG in a fixed topological ordering. -/
structure OrderedDAG (size d : ℕ) (V : Type*) where
  /-- Generate the leaf value or predecessor list and combining function for
  a requested node. -/
  spec : (index : Fin size) → OrderedDAG.Node d V index.val

namespace OrderedDAG

variable {size d : ℕ} {V : Type*}

/-- Regard a predecessor of `index` as a node of the whole DAG. -/
def liftChild (index : Fin size) (child : Fin index.val) : Fin size :=
  ⟨child.val, Nat.lt_trans child.isLt index.isLt⟩

namespace Aux

/-- Well-founded implementation of shared-DAG evaluation. -/
def value (dag : OrderedDAG size d V) :
    (index : ℕ) → index < size → V
  | index, hindex =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf value => value
      | .node children combine =>
          combine fun r =>
            value dag (children r).val
              (Nat.lt_trans (children r).isLt hindex)
termination_by index _ => index

/-- Well-founded implementation of tree unrolling. -/
def unroll (dag : OrderedDAG size d V) :
    (index : ℕ) → index < size → Tree d V
  | index, hindex =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf value => .leaf value
      | .node children combine =>
          .node
            (fun r =>
              unroll dag (children r).val
                (Nat.lt_trans (children r).isLt hindex))
            combine
termination_by index _ => index

/-- Well-founded implementation of dependency depth. -/
def depth (dag : OrderedDAG size d V) :
    (index : ℕ) → index < size → ℕ
  | index, hindex =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf _ => 0
      | .node children _ =>
          1 + Finset.univ.sup fun r =>
            depth dag (children r).val
              (Nat.lt_trans (children r).isLt hindex)
termination_by index _ => index

end Aux

/-- Evaluate a node while sharing repeated dependencies. -/
def value (dag : OrderedDAG size d V) (index : Fin size) : V :=
  Aux.value dag index.val index.isLt

/-- Unroll all dependencies below `index` into a `d`-ary tree.

This is a semantic object. The Williams simulator traverses this tree
implicitly and must not store the resulting term. -/
def unroll (dag : OrderedDAG size d V) (index : Fin size) : Tree d V :=
  Aux.unroll dag index.val index.isLt

/-- Maximum number of internal dependency nodes on a branch below `index`. -/
def depth (dag : OrderedDAG size d V) (index : Fin size) : ℕ :=
  Aux.depth dag index.val index.isLt

end OrderedDAG

end TreeEval

end Complexity
