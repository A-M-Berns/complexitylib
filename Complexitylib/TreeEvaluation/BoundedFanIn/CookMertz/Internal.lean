/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BoundedFanIn
import Complexitylib.TreeEvaluation.OrderedDAG.BooleanExtension

/-!
# Cook--Mertz correctness for variable bounded fan-in

These internal proofs transfer the fixed-arity Boolean extension and
Cook--Mertz evaluator across exact-arity padding.
-/

namespace Complexity

namespace TreeEval

namespace BoundedFanIn

namespace Internal

variable {size d b : ℕ} {K : Type*}

theorem liftBoolean_pad_isLowDegreePolynomial_internal
    [CommRing K] [Nontrivial K]
    (dag : DAG size d (Fin b → Bool)) (degreeBound : ℕ)
    (hdegree : d * b < degreeBound) :
    (OrderedDAG.liftBoolean (K := K) dag.pad).IsLowDegreePolynomial
      degreeBound :=
  OrderedDAG.liftBoolean_isLowDegreePolynomial
    dag.pad degreeBound hdegree

theorem value_liftBoolean_pad_internal [CommRing K]
    (dag : DAG size d (Fin b → Bool)) (index : Fin size) :
    (OrderedDAG.liftBoolean (K := K) dag.pad).value index =
      CookMertz.BooleanExtension.embed (dag.value index) := by
  rw [OrderedDAG.value_liftBoolean]
  rw [DAG.value_pad]

theorem cookMertzEvaluate_liftBoolean_pad_eq_embed_internal
    [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : CookMertz.EnumeratesUnits units)
    (dag : DAG size d (Fin b → Bool))
    (hdegree : d * b < Fintype.card K - 1) (index : Fin size) :
    (OrderedDAG.liftBoolean (K := K) dag.pad).cookMertzEvaluate
        units index =
      CookMertz.BooleanExtension.embed (dag.value index) := by
  rw [OrderedDAG.cookMertzEvaluate_liftBoolean_eq_embed
      units henum dag.pad hdegree index]
  rw [DAG.value_pad]

theorem cookMertzEvaluate_liftBoolean_pad_primeField_eq_embed_internal
    (choice : CookMertz.PrimeField.Choice (d * b))
    (dag : DAG size d (Fin b → Bool)) (index : Fin size) :
    (OrderedDAG.liftBoolean (K := choice.Field) dag.pad).cookMertzEvaluate
        (CookMertz.PrimeField.units choice.modulus) index =
      CookMertz.BooleanExtension.embed (K := choice.Field)
        (dag.value index) := by
  rw [OrderedDAG.cookMertzEvaluate_liftBoolean_primeField_eq_embed
      choice dag.pad index]
  rw [DAG.value_pad]

theorem exists_primeField_cookMertzEvaluate_liftBoolean_pad_eq_embed_internal
    (dag : DAG size d (Fin b → Bool)) (index : Fin size) :
    ∃ choice : CookMertz.PrimeField.Choice (d * b),
      (OrderedDAG.liftBoolean (K := choice.Field) dag.pad).cookMertzEvaluate
          (CookMertz.PrimeField.units choice.modulus) index =
        CookMertz.BooleanExtension.embed (K := choice.Field)
          (dag.value index) := by
  obtain ⟨choice⟩ := CookMertz.PrimeField.choice_nonempty (d * b)
  exact
    ⟨choice,
      cookMertzEvaluate_liftBoolean_pad_primeField_eq_embed_internal
        choice dag index⟩

end Internal

end BoundedFanIn

end TreeEval

end Complexity
