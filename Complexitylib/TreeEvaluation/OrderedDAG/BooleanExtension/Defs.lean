/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation.Defs
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz.Defs

/-!
# Polynomial lifting of Boolean ordered DAGs

This file lifts a Boolean-valued ordered computation DAG to a field-valued
DAG. Boolean leaves are embedded coordinatewise as zero or one. Every Boolean
node function is replaced by its coordinatewise multilinear extension.

The predecessor relation and topological ordering are unchanged. The lift is
executable as a Lean function: its node callback enumerates Boolean
assignments by binary code and never constructs a multivariate polynomial.
The polynomial remains only a certificate. This is still not a claim that
the callback has been compiled to the project's Turing-machine model within
Williams's target space bound.

## Main definition

- `OrderedDAG.liftBoolean` -- replace Boolean values and nodes by their
  zero-one embeddings and multilinear extensions
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

variable {size d b : ℕ} {K : Type*}

/-- Lift a Boolean ordered DAG into a commutative ring by embedding leaves and
replacing every Boolean node with its multilinear extension. -/
def liftBoolean [CommRing K]
    (dag : OrderedDAG size d (Fin b → Bool)) :
    OrderedDAG size d (Fin b → K) where
  spec index :=
    match dag.spec index with
    | .leaf value =>
        .leaf (CookMertz.BooleanExtension.embed value)
    | .node children combine =>
        .node children
          (CookMertz.BooleanExtension.Evaluation.evaluateNode combine)

end OrderedDAG

end TreeEval

end Complexity
