/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG.Defs

/-!
# Variable bounded-fan-in tree evaluation

Williams's tree-evaluation theorem permits every internal node to have its own
fan-in `k`, subject to `2 ≤ k ≤ d`. The original Cook--Mertz implementation in
this library uses exactly `d` inputs and `d + 1` registers. This file defines
the variable-fan-in semantic interface and an exact-arity padding translation.

Padding duplicates the first genuine child in every unused child position.
The padded combining function ignores those positions. Hence padding needs no
distinguished value or dummy leaf, and it preserves both values and dependency
depth exactly.

The DAG interface remains oracle-based: `spec` generates one requested node.
No space bound is assigned to that callback at this layer.

## Main definitions

- `BoundedFanIn.Arity` -- a node fan-in between two and a global bound
- `BoundedFanIn.Tree` -- a tree with node-dependent bounded fan-in
- `BoundedFanIn.Tree.pad` -- translation to an exactly `d`-ary tree
- `BoundedFanIn.DAG` -- a topologically ordered variable-fan-in DAG
- `BoundedFanIn.DAG.pad` -- translation to an exactly `d`-ary ordered DAG
-/

namespace Complexity

namespace TreeEval

namespace BoundedFanIn

/-- A legal internal-node fan-in under the global bound `d`. -/
structure Arity (d : ℕ) where
  /-- The number of genuine children at this node. -/
  width : ℕ
  /-- Williams's relaxed tree-evaluation interface has fan-in at least two. -/
  two_le : 2 ≤ width
  /-- The node fan-in is at most the global register bound. -/
  le_bound : width ≤ d

namespace Arity

variable {d : ℕ}

/-- Embed a genuine child position into the global `d` positions. -/
def embedIndex (arity : Arity d) (index : Fin arity.width) : Fin d :=
  Fin.castLE arity.le_bound index

/-- Project a global child position to a genuine child position.

Positions below the node's fan-in are preserved. Padding positions select
child zero, which exists because the fan-in is at least two. -/
def projectIndex (arity : Arity d) (index : Fin d) : Fin arity.width :=
  if h : index.val < arity.width then
    Fin.castLT index h
  else
    ⟨0, Nat.zero_lt_of_lt arity.two_le⟩

end Arity

/-- A finite tree whose internal nodes have fan-in between two and `d`. -/
inductive Tree (d : ℕ) (V : Type*) where
  | leaf (value : V)
  | node (arity : Arity d)
      (children : Fin arity.width → Tree d V)
      (combine : (Fin arity.width → V) → V)

namespace Tree

variable {d : ℕ} {V : Type*}

/-- Evaluate a bounded-variable-fan-in tree bottom-up. -/
def value : Tree d V → V
  | .leaf leafValue => leafValue
  | .node _ children combine =>
      combine fun index => value (children index)

/-- Maximum number of internal nodes on a root-to-leaf branch. -/
def height : Tree d V → ℕ
  | .leaf _ => 0
  | .node _ children _ =>
      1 + Finset.univ.sup fun index => height (children index)

/-- Pad every internal node to exactly `d` children.

Unused child positions duplicate child zero, while the combining function
reads only the genuine positions. -/
def pad : Tree d V → TreeEval.Tree d V
  | .leaf leafValue => .leaf leafValue
  | .node arity children combine =>
      .node
        (fun index => pad (children (arity.projectIndex index)))
        (fun args => combine fun index => args (arity.embedIndex index))

@[simp] theorem value_leaf (leafValue : V) :
    (Tree.leaf leafValue : Tree d V).value = leafValue := rfl

@[simp] theorem value_node (arity : Arity d)
    (children : Fin arity.width → Tree d V)
    (combine : (Fin arity.width → V) → V) :
    (Tree.node arity children combine).value =
      combine (fun index => (children index).value) := rfl

@[simp] theorem height_leaf (leafValue : V) :
    (Tree.leaf leafValue : Tree d V).height = 0 := rfl

@[simp] theorem height_node (arity : Arity d)
    (children : Fin arity.width → Tree d V)
    (combine : (Fin arity.width → V) → V) :
    (Tree.node arity children combine).height =
      1 + Finset.univ.sup fun index => (children index).height := rfl

@[simp] theorem pad_leaf (leafValue : V) :
    (Tree.leaf leafValue : Tree d V).pad = .leaf leafValue := rfl

@[simp] theorem pad_node (arity : Arity d)
    (children : Fin arity.width → Tree d V)
    (combine : (Fin arity.width → V) → V) :
    (Tree.node arity children combine).pad =
      .node
        (fun index => (children (arity.projectIndex index)).pad)
        (fun args => combine fun index => args (arity.embedIndex index)) := rfl

end Tree

/-- One node of a topologically ordered variable-fan-in computation DAG. -/
inductive Node (d : ℕ) (V : Type*) (index : ℕ) where
  | leaf (value : V)
  | node (arity : Arity d)
      (children : Fin arity.width → Fin index)
      (combine : (Fin arity.width → V) → V)

/-- A topologically ordered computation DAG with node fan-in at most `d`. -/
structure DAG (size d : ℕ) (V : Type*) where
  /-- Generate the leaf or bounded predecessor data for a requested node. -/
  spec : (index : Fin size) → Node d V index.val

namespace DAG

variable {size d : ℕ} {V : Type*}

/-- Regard a predecessor of `index` as a node of the whole DAG. -/
def liftChild (index : Fin size) (child : Fin index.val) : Fin size :=
  ⟨child.val, Nat.lt_trans child.isLt index.isLt⟩

namespace Aux

/-- Well-founded implementation of shared variable-fan-in DAG evaluation. -/
def value (dag : DAG size d V) :
    (index : ℕ) → index < size → V
  | index, hindex =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf leafValue => leafValue
      | .node _ children combine =>
          combine fun childIndex =>
            value dag (children childIndex).val
              (Nat.lt_trans (children childIndex).isLt hindex)
termination_by index _ => index

/-- Well-founded implementation of variable-fan-in tree unrolling. -/
def unroll (dag : DAG size d V) :
    (index : ℕ) → index < size → Tree d V
  | index, hindex =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf leafValue => .leaf leafValue
      | .node arity children combine =>
          .node arity
            (fun childIndex =>
              unroll dag (children childIndex).val
                (Nat.lt_trans (children childIndex).isLt hindex))
            combine
termination_by index _ => index

/-- Well-founded implementation of dependency depth. -/
def depth (dag : DAG size d V) :
    (index : ℕ) → index < size → ℕ
  | index, hindex =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf _ => 0
      | .node _ children _ =>
          1 + Finset.univ.sup fun childIndex =>
            depth dag (children childIndex).val
              (Nat.lt_trans (children childIndex).isLt hindex)
termination_by index _ => index

end Aux

/-- Evaluate one node while sharing repeated dependencies. -/
def value (dag : DAG size d V) (index : Fin size) : V :=
  Aux.value dag index.val index.isLt

/-- Unroll the dependencies below one node into a variable-fan-in tree. -/
def unroll (dag : DAG size d V) (index : Fin size) : Tree d V :=
  Aux.unroll dag index.val index.isLt

/-- Maximum dependency depth below one node. -/
def depth (dag : DAG size d V) (index : Fin size) : ℕ :=
  Aux.depth dag index.val index.isLt

/-- Pad every node to exactly `d` predecessors.

Extra predecessor positions duplicate the first genuine predecessor. The
exact-arity combining function ignores their values. -/
def pad (dag : DAG size d V) : OrderedDAG size d V where
  spec index :=
    match dag.spec index with
    | .leaf leafValue => .leaf leafValue
    | .node arity children combine =>
        .node
          (fun childIndex => children (arity.projectIndex childIndex))
          (fun args => combine fun childIndex =>
            args (arity.embedIndex childIndex))

end DAG

end BoundedFanIn

end TreeEval

end Complexity
