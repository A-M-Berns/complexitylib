/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Interpolation.Defs
import Complexitylib.TreeEvaluation.OrderedDAG.Defs

/-!
# Low-degree certificates for ordered computation DAGs

This file attaches the Cook--Mertz polynomial certificate to each internal
node of an ordered computation DAG. The certificate remains node-local: it
does not expand shared dependencies into a tree.

## Main definitions

- `OrderedDAG.Node.IsLowDegreePolynomial` -- one node has a low-degree extension
- `OrderedDAG.IsLowDegreePolynomial` -- every DAG node has such an extension
- `OrderedDAG.cookMertzAccumulate` -- direct implicit-DAG catalytic traversal
- `OrderedDAG.cookMertzEvaluate` -- evaluate a selected DAG node from zero registers
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

namespace Node

variable {d index : ℕ} {ι K : Type*}

/-- A leaf, or an internal node represented by one sufficiently low-degree
multivariate polynomial per output coordinate. -/
def IsLowDegreePolynomial [CommSemiring K] (degreeBound : ℕ) :
    Node d (ι → K) index → Prop
  | .leaf _ => True
  | .node _ combine =>
      ∃ polynomials : ι → MvPolynomial (Fin d × ι) K,
        combine = CookMertz.polynomialNode polynomials ∧
        ∀ j, (polynomials j).totalDegree < degreeBound

end Node

variable {size d : ℕ} {ι K : Type*}

/-- Every node in the compact computation DAG has a coordinatewise
low-degree polynomial extension. -/
def IsLowDegreePolynomial [CommSemiring K] (degreeBound : ℕ)
    (dag : OrderedDAG size d (ι → K)) : Prop :=
  ∀ index, (dag.spec index).IsLowDegreePolynomial degreeBound

namespace Aux

/-- Well-founded Cook--Mertz traversal of a compact ordered DAG.

Unlike `CookMertz.accumulate units (dag.unroll index)`, this definition never
constructs a `Tree`: it queries `dag.spec` at the current node and recursively
visits its earlier predecessors. A later Turing-machine implementation must
still account for the storage used by those queries and recursive indices. -/
def cookMertzAccumulate {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) :
    (index : ℕ) → index < size → F → Fin (d + 1) →
      CookMertz.Registers d V → CookMertz.Registers d V
  | index, hindex, s, out, regs =>
      match dag.spec ⟨index, hindex⟩ with
      | .leaf value => CookMertz.addAt regs out (s • value)
      | .node children combine =>
          List.foldl (β := Fˣ) (fun regs a =>
            let regs := (List.finRange d).foldl (fun regs r =>
              let child := children r
              let target := out.succAbove r
              cookMertzAccumulate units dag child.val
                (Nat.lt_trans child.isLt hindex) 1 target
                (CookMertz.scaleAt regs target (a : F))) regs
            let args := fun r => regs (out.succAbove r)
            let regs := CookMertz.addAt regs out ((-s) • combine args)
            (List.finRange d).foldl (fun regs r =>
              let child := children r
              let target := out.succAbove r
              CookMertz.scaleAt
                (cookMertzAccumulate units dag child.val
                  (Nat.lt_trans child.isLt hindex) (-1) target regs)
                target (↑a⁻¹ : F)) regs) regs
            units
termination_by index _ _ _ _ => index

end Aux

/-- Direct Cook--Mertz accumulation over a compact ordered DAG. -/
def cookMertzAccumulate {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (s : F) (out : Fin (d + 1)) (regs : CookMertz.Registers d V) :
    CookMertz.Registers d V :=
  Aux.cookMertzAccumulate units dag index.val index.isLt s out regs

/-- Evaluate one compact ordered-DAG node with zeroed catalytic registers. -/
def cookMertzEvaluate {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size) : V :=
  cookMertzAccumulate units dag index 1 (Fin.last d) 0 (Fin.last d)

end OrderedDAG

end TreeEval

end Complexity
