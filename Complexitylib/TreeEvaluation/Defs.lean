/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Tree evaluation

This file defines the semantic core of the tree evaluation problem used by the
Cook--Mertz procedure and Williams's square-root-space simulation.

An internal node has exactly `d` children. The separate
`TreeEvaluation.BoundedFanIn` layer models Williams's relaxed interface with
node-dependent fan-in between two and `d`, and proves an exact-arity padding
translation. Node functions are kept abstract here: later layers attach
algebraic extensions and algorithms for evaluating them.

## Main definitions

- `TreeEval.Tree` -- a finite `d`-ary tree whose nodes compute values in `V`
- `TreeEval.Tree.value` -- the recursively defined value at the root
- `TreeEval.Tree.height` -- the maximum number of internal nodes on a branch
-/

namespace Complexity

namespace TreeEval

/-- A finite `d`-ary tree evaluation instance with values in `V`.

Leaves carry values directly. Every internal node carries its `d` children and
the function that combines their values. -/
inductive Tree (d : ℕ) (V : Type*) where
  | leaf (value : V)
  | node (children : Fin d → Tree d V) (combine : (Fin d → V) → V)

namespace Tree

variable {d : ℕ} {V : Type*}

/-- Evaluate a tree bottom-up. -/
def value : Tree d V → V
  | .leaf v => v
  | .node children combine => combine (fun i => value (children i))

/-- The maximum number of internal nodes on a root-to-leaf branch. -/
def height : Tree d V → ℕ
  | .leaf _ => 0
  | .node children _ => 1 + Finset.univ.sup fun i => height (children i)

@[simp] theorem value_leaf (v : V) : (Tree.leaf v : Tree d V).value = v := rfl

@[simp] theorem value_node (children : Fin d → Tree d V) (combine : (Fin d → V) → V) :
    (Tree.node children combine).value = combine (fun i => (children i).value) := rfl

@[simp] theorem height_leaf (v : V) : (Tree.leaf v : Tree d V).height = 0 := rfl

@[simp] theorem height_node (children : Fin d → Tree d V)
    (combine : (Fin d → V) → V) :
    (Tree.node children combine).height =
      1 + Finset.univ.sup fun i => (children i).height := rfl

end Tree

end TreeEval

end Complexity
