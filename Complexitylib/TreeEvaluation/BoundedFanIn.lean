/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BoundedFanIn.Defs
import Complexitylib.TreeEvaluation.BoundedFanIn.Internal

/-!
# Variable bounded-fan-in trees and ordered DAGs

This file exposes the semantic correspondence between Williams's relaxed
tree-evaluation interface, in which a node may have any fan-in between two and
`d`, and the exactly `d`-ary interface used by the executable Cook--Mertz
accumulator.

Padding repeats the first genuine child in unused positions and makes the node
function ignore those positions. It preserves values, tree heights, and DAG
dependency depths exactly. Thus applying the fixed-arity evaluator does not
silently change either the computed result or the height term in its resource
bound.

## Main theorems

- `Tree.value_pad` -- exact-arity padding preserves tree values
- `Tree.height_pad` -- exact-arity padding preserves tree heights
- `DAG.value_unroll` -- unrolling preserves shared-DAG evaluation
- `DAG.height_unroll` -- unrolled height equals dependency depth
- `DAG.value_pad` -- exact-arity DAG padding preserves values
- `DAG.depth_pad` -- exact-arity DAG padding preserves dependency depth
-/

namespace Complexity

namespace TreeEval

namespace BoundedFanIn

namespace Arity

variable {d : ℕ}

/-- Projecting an embedded genuine child position recovers that position. -/
@[simp] theorem projectIndex_embedIndex
    (arity : Arity d) (index : Fin arity.width) :
    arity.projectIndex (arity.embedIndex index) = index :=
  Internal.projectIndex_embedIndex_internal arity index

/-- Repeating child zero in padding positions does not change a finite
supremum over all genuine child positions. -/
theorem sup_projectIndex (arity : Arity d)
    (f : Fin arity.width → ℕ) :
    Finset.univ.sup (fun index : Fin d => f (arity.projectIndex index)) =
      Finset.univ.sup f :=
  Internal.sup_projectIndex_internal arity f

end Arity

namespace Tree

variable {d : ℕ} {V : Type*}

/-- Exact-arity padding preserves bottom-up tree evaluation. -/
@[simp] theorem value_pad (tree : Tree d V) :
    tree.pad.value = tree.value :=
  Internal.tree_value_pad_internal tree

/-- Exact-arity padding preserves tree height exactly. -/
@[simp] theorem height_pad (tree : Tree d V) :
    tree.pad.height = tree.height :=
  Internal.tree_height_pad_internal tree

end Tree

namespace DAG

variable {size d : ℕ} {V : Type*}

/-- Evaluate a bounded-DAG leaf from its node specification. -/
theorem value_of_spec_leaf (dag : DAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.value index = leafValue :=
  Internal.value_of_spec_leaf_internal dag index leafValue h

/-- Evaluate a bounded-DAG internal node from its node specification. -/
theorem value_of_spec_node (dag : DAG size d V)
    (index : Fin size) (arity : Arity d)
    (children : Fin arity.width → Fin index.val)
    (combine : (Fin arity.width → V) → V)
    (h : dag.spec index = .node arity children combine) :
    dag.value index =
      combine (fun childIndex =>
        dag.value (liftChild index (children childIndex))) :=
  Internal.value_of_spec_node_internal
    dag index arity children combine h

/-- Unroll a bounded-DAG leaf from its node specification. -/
theorem unroll_of_spec_leaf (dag : DAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.unroll index = .leaf leafValue :=
  Internal.unroll_of_spec_leaf_internal dag index leafValue h

/-- Unroll a bounded-DAG internal node from its node specification. -/
theorem unroll_of_spec_node (dag : DAG size d V)
    (index : Fin size) (arity : Arity d)
    (children : Fin arity.width → Fin index.val)
    (combine : (Fin arity.width → V) → V)
    (h : dag.spec index = .node arity children combine) :
    dag.unroll index =
      .node arity
        (fun childIndex =>
          dag.unroll (liftChild index (children childIndex)))
        combine :=
  Internal.unroll_of_spec_node_internal
    dag index arity children combine h

/-- Read the dependency depth of a bounded-DAG leaf. -/
theorem depth_of_spec_leaf (dag : DAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.depth index = 0 :=
  Internal.depth_of_spec_leaf_internal dag index leafValue h

/-- Read the dependency depth of a bounded-DAG internal node. -/
theorem depth_of_spec_node (dag : DAG size d V)
    (index : Fin size) (arity : Arity d)
    (children : Fin arity.width → Fin index.val)
    (combine : (Fin arity.width → V) → V)
    (h : dag.spec index = .node arity children combine) :
    dag.depth index =
      1 + Finset.univ.sup fun childIndex =>
        dag.depth (liftChild index (children childIndex)) :=
  Internal.depth_of_spec_node_internal
    dag index arity children combine h

/-- Unrolling a compact bounded DAG preserves its shared evaluation. -/
theorem value_unroll (dag : DAG size d V) (index : Fin size) :
    (dag.unroll index).value = dag.value index :=
  Internal.value_unroll_internal dag index

/-- The unrolled variable-fan-in tree has exactly the DAG dependency depth. -/
theorem height_unroll (dag : DAG size d V) (index : Fin size) :
    (dag.unroll index).height = dag.depth index :=
  Internal.height_unroll_internal dag index

/-- Dependency depth below a node is bounded by its topological index plus
one. -/
theorem depth_le_index_succ (dag : DAG size d V) (index : Fin size) :
    dag.depth index ≤ index.val + 1 :=
  Internal.depth_le_index_succ_internal dag index

/-- Dependency depth is bounded by the total number of DAG nodes. -/
theorem depth_le_size (dag : DAG size d V) (index : Fin size) :
    dag.depth index ≤ size :=
  Internal.depth_le_size_internal dag index

/-- Padding after variable-fan-in unrolling is the same tree as unrolling the
padded exact-arity DAG. -/
theorem pad_unroll (dag : DAG size d V) (index : Fin size) :
    (dag.unroll index).pad = dag.pad.unroll index :=
  Internal.pad_unroll_internal dag index

/-- Exact-arity DAG padding preserves every node value. -/
@[simp] theorem value_pad (dag : DAG size d V) (index : Fin size) :
    dag.pad.value index = dag.value index :=
  Internal.value_pad_internal dag index

/-- Exact-arity DAG padding preserves dependency depth exactly. -/
@[simp] theorem depth_pad (dag : DAG size d V) (index : Fin size) :
    dag.pad.depth index = dag.depth index :=
  Internal.depth_pad_internal dag index

end DAG

end BoundedFanIn

end TreeEval

end Complexity
