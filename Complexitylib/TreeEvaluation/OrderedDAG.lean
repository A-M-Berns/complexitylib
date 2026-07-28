/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG.Defs
import Complexitylib.TreeEvaluation.OrderedDAG.Internal

/-!
# Ordered computation DAGs and implicit tree unrolling

This file exposes the semantic bridge from a topologically ordered,
bounded-fan-in computation DAG to tree evaluation. Unrolling may duplicate
shared subgraphs, but it preserves the value exactly. Its height is the DAG's
dependency depth and is at most the number of DAG nodes.

These results justify representing Williams's tree-evaluation instances by an
implicit computation graph. They do not by themselves prove that the graph
oracle or the tree traversal uses small Turing-machine space.

## Main theorems

- `value_unroll` -- tree evaluation agrees with shared-DAG evaluation
- `height_unroll` -- unrolled height equals dependency depth
- `depth_le_size` -- dependency depth is bounded by the DAG size
- `height_unroll_le_size` -- the corresponding tree-height bound
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

variable {size d : ℕ} {V : Type*}

@[simp] theorem value_of_spec_leaf (dag : OrderedDAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.value index = leafValue :=
  Internal.value_of_spec_leaf_internal dag index leafValue h

theorem value_of_spec_node (dag : OrderedDAG size d V)
    (index : Fin size) (children : Fin d → Fin index.val)
    (combine : (Fin d → V) → V)
    (h : dag.spec index = .node children combine) :
    dag.value index =
      combine (fun r => dag.value (liftChild index (children r))) :=
  Internal.value_of_spec_node_internal dag index children combine h

@[simp] theorem unroll_of_spec_leaf (dag : OrderedDAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.unroll index = .leaf leafValue :=
  Internal.unroll_of_spec_leaf_internal dag index leafValue h

theorem unroll_of_spec_node (dag : OrderedDAG size d V)
    (index : Fin size) (children : Fin d → Fin index.val)
    (combine : (Fin d → V) → V)
    (h : dag.spec index = .node children combine) :
    dag.unroll index =
      .node (fun r => dag.unroll (liftChild index (children r))) combine :=
  Internal.unroll_of_spec_node_internal dag index children combine h

/-- Unrolling a shared computation DAG into a tree preserves its value. -/
theorem value_unroll (dag : OrderedDAG size d V) (index : Fin size) :
    (dag.unroll index).value = dag.value index :=
  Internal.value_unroll_internal dag index

/-- The height of an unrolled dependency tree is exactly the ordered DAG's
dependency depth at its root. -/
theorem height_unroll (dag : OrderedDAG size d V) (index : Fin size) :
    (dag.unroll index).height = dag.depth index :=
  Internal.height_unroll_internal dag index

/-- A node's dependency depth is at most one plus its topological index. -/
theorem depth_le_index_succ (dag : OrderedDAG size d V)
    (index : Fin size) :
    dag.depth index ≤ index.val + 1 :=
  Internal.depth_le_index_succ_internal dag index

/-- Every dependency path contains at most `size` nodes. -/
theorem depth_le_size (dag : OrderedDAG size d V) (index : Fin size) :
    dag.depth index ≤ size :=
  Internal.depth_le_size_internal dag index

/-- Unrolling does not increase dependency height beyond the DAG size. -/
theorem height_unroll_le_size (dag : OrderedDAG size d V)
    (index : Fin size) :
    (dag.unroll index).height ≤ size := by
  rw [height_unroll]
  exact depth_le_size dag index

end OrderedDAG

end TreeEval

end Complexity
