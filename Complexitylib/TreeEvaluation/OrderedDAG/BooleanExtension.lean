/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG.BooleanExtension.Defs
import Complexitylib.TreeEvaluation.OrderedDAG.BooleanExtension.Internal
import Complexitylib.TreeEvaluation.CookMertz.PrimeField
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz

/-!
# Cook--Mertz evaluation of Boolean ordered DAGs

An arbitrary Boolean node with `d` inputs of `b` bits has a multilinear
extension of total degree at most `d * b`. Consequently, whenever the field
satisfies `d * b < |K| - 1`, lifting every node gives exactly the low-degree
certificate consumed by the Cook--Mertz evaluator.

The resulting evaluator returns the zero-one embedding of the original
Boolean DAG value. Each lifted node now uses the executable binary-code
evaluator rather than storing its polynomial certificate. A later machine
layer must still implement this evaluator and the Boolean node oracle in the
concrete Turing-machine model and charge their time and workspace.

## Main theorems

- `liftBoolean_isLowDegreePolynomial` -- the lifted DAG has degree below any
  bound greater than `d * b`
- `value_liftBoolean` -- lifting preserves every node value after embedding
- `cookMertzEvaluate_liftBoolean_eq_embed` -- Cook--Mertz evaluates the
  original Boolean DAG correctly through the lift
- `cookMertzEvaluate_liftBoolean_primeField_eq_embed` -- the explicit prime
  field and unit list discharge all algebraic side conditions
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

variable {size d b : ℕ} {K : Type*}

@[simp] theorem liftBoolean_spec_leaf [CommRing K]
    (dag : OrderedDAG size d (Fin b → Bool)) (index : Fin size)
    (value : Fin b → Bool) (h : dag.spec index = .leaf value) :
    (liftBoolean (K := K) dag).spec index =
      .leaf (CookMertz.BooleanExtension.embed value) := by
  simp [liftBoolean, h]

theorem liftBoolean_spec_node [CommRing K]
    (dag : OrderedDAG size d (Fin b → Bool)) (index : Fin size)
    (children : Fin d → Fin index.val)
    (combine : (Fin d → Fin b → Bool) → Fin b → Bool)
    (h : dag.spec index = .node children combine) :
    (liftBoolean (K := K) dag).spec index =
      .node children
        (CookMertz.BooleanExtension.Evaluation.evaluateNode combine) := by
  simp [liftBoolean, h]

/-- If the requested bound exceeds the number of Boolean input coordinates,
the lifted DAG is a low-degree polynomial DAG. -/
theorem liftBoolean_isLowDegreePolynomial [CommRing K] [Nontrivial K]
    (dag : OrderedDAG size d (Fin b → Bool)) (degreeBound : ℕ)
    (hdegree : d * b < degreeBound) :
    (liftBoolean (K := K) dag).IsLowDegreePolynomial degreeBound :=
  Internal.liftBoolean_isLowDegreePolynomial_internal
    dag degreeBound hdegree

/-- Lifting a Boolean DAG preserves every node value after coordinatewise
zero-one embedding. -/
theorem value_liftBoolean [CommRing K]
    (dag : OrderedDAG size d (Fin b → Bool)) (index : Fin size) :
    (liftBoolean (K := K) dag).value index =
      CookMertz.BooleanExtension.embed (dag.value index) :=
  Internal.value_liftBoolean_internal dag index

/-- Cook--Mertz evaluation of the lifted DAG returns the zero-one embedding
of the original Boolean DAG value. -/
theorem cookMertzEvaluate_liftBoolean_eq_embed
    [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : CookMertz.EnumeratesUnits units)
    (dag : OrderedDAG size d (Fin b → Bool))
    (hdegree : d * b < Fintype.card K - 1) (index : Fin size) :
    (liftBoolean (K := K) dag).cookMertzEvaluate units index =
      CookMertz.BooleanExtension.embed (dag.value index) := by
  rw [cookMertzEvaluate_eq_value units henum
      (liftBoolean (K := K) dag)
      (liftBoolean_isLowDegreePolynomial dag _ hdegree) index]
  exact value_liftBoolean dag index

/-- The explicit prime field selected for degree `d * b`, together with its
increasing nonzero-residue list, discharges the field-size and enumeration
hypotheses of Boolean-DAG Cook--Mertz evaluation. -/
theorem cookMertzEvaluate_liftBoolean_primeField_eq_embed
    (choice : CookMertz.PrimeField.Choice (d * b))
    (dag : OrderedDAG size d (Fin b → Bool)) (index : Fin size) :
    (liftBoolean (K := choice.Field) dag).cookMertzEvaluate
        (CookMertz.PrimeField.units choice.modulus) index =
      CookMertz.BooleanExtension.embed (K := choice.Field)
        (dag.value index) := by
  exact cookMertzEvaluate_liftBoolean_eq_embed
    (CookMertz.PrimeField.units choice.modulus)
    (CookMertz.PrimeField.enumeratesUnits choice.modulus) dag
    choice.degree_lt_card_sub_one index

/-- For every Boolean ordered DAG, some prime field of modulus at most
`2 * (d * b + 1)` makes the direct Cook--Mertz evaluator correct. -/
theorem exists_primeField_cookMertzEvaluate_liftBoolean_eq_embed
    (dag : OrderedDAG size d (Fin b → Bool)) (index : Fin size) :
    ∃ choice : CookMertz.PrimeField.Choice (d * b),
      (liftBoolean (K := choice.Field) dag).cookMertzEvaluate
          (CookMertz.PrimeField.units choice.modulus) index =
        CookMertz.BooleanExtension.embed (K := choice.Field)
          (dag.value index) := by
  obtain ⟨choice⟩ :=
    CookMertz.PrimeField.choice_nonempty (d * b)
  exact
    ⟨choice,
      cookMertzEvaluate_liftBoolean_primeField_eq_embed
        choice dag index⟩

end OrderedDAG

end TreeEval

end Complexity
