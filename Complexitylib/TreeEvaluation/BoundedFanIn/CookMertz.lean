/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BoundedFanIn
import Complexitylib.TreeEvaluation.BoundedFanIn.CookMertz.Internal
import Complexitylib.TreeEvaluation.OrderedDAG.BooleanExtension

/-!
# Cook--Mertz evaluation with variable bounded fan-in

Williams's relaxed tree-evaluation theorem allows every node to have its own
fan-in `k`, with `2 ≤ k ≤ d`. Exact-arity padding lets the existing
`d + 1`-register Cook--Mertz evaluator handle that interface without changing
the value or dependency depth.

For `b`-bit Boolean values, padding each node function to `d` inputs and taking
its multilinear extension gives total degree at most `d * b`. The theorems
below combine that certificate with an explicit prime field and enumeration
of its nonzero elements.

This remains an executable Lean-level evaluator, not yet a theorem about the
workspace of a concrete Turing machine. In particular, a later layer must
implement and charge the DAG oracle, Boolean node function, field arithmetic,
assignment counter, and recursive path representation.

## Main theorems

- `DAG.liftBoolean_pad_isLowDegreePolynomial` -- padded node extensions have
  degree at most the global fan-in bound times the bit width
- `DAG.value_liftBoolean_pad` -- lifting and padding preserve Boolean values
- `DAG.cookMertzEvaluate_liftBoolean_pad_primeField_eq_embed` -- explicit-field
  Cook--Mertz evaluation is correct for variable bounded fan-in
-/

namespace Complexity

namespace TreeEval

namespace BoundedFanIn

namespace DAG

variable {size d b : ℕ} {K : Type*}

/-- The padded lift of a bounded-variable-fan-in Boolean DAG has a
coordinatewise low-degree polynomial certificate. -/
theorem liftBoolean_pad_isLowDegreePolynomial
    [CommRing K] [Nontrivial K]
    (dag : DAG size d (Fin b → Bool)) (degreeBound : ℕ)
    (hdegree : d * b < degreeBound) :
    (OrderedDAG.liftBoolean (K := K) dag.pad).IsLowDegreePolynomial
      degreeBound :=
  Internal.liftBoolean_pad_isLowDegreePolynomial_internal
    dag degreeBound hdegree

/-- Lifting the padded DAG preserves every bounded-DAG value after
coordinatewise zero-one embedding. -/
theorem value_liftBoolean_pad [CommRing K]
    (dag : DAG size d (Fin b → Bool)) (index : Fin size) :
    (OrderedDAG.liftBoolean (K := K) dag.pad).value index =
      CookMertz.BooleanExtension.embed (dag.value index) :=
  Internal.value_liftBoolean_pad_internal dag index

/-- Cook--Mertz evaluation over any sufficiently large explicitly enumerated
finite field returns the embedded bounded-DAG value. -/
theorem cookMertzEvaluate_liftBoolean_pad_eq_embed
    [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : CookMertz.EnumeratesUnits units)
    (dag : DAG size d (Fin b → Bool))
    (hdegree : d * b < Fintype.card K - 1) (index : Fin size) :
    (OrderedDAG.liftBoolean (K := K) dag.pad).cookMertzEvaluate
        units index =
      CookMertz.BooleanExtension.embed (dag.value index) :=
  Internal.cookMertzEvaluate_liftBoolean_pad_eq_embed_internal
    units henum dag hdegree index

/-- The explicit prime field chosen for degree `d * b` discharges all
algebraic side conditions for a variable bounded-fan-in Boolean DAG. -/
theorem cookMertzEvaluate_liftBoolean_pad_primeField_eq_embed
    (choice : CookMertz.PrimeField.Choice (d * b))
    (dag : DAG size d (Fin b → Bool)) (index : Fin size) :
    (OrderedDAG.liftBoolean (K := choice.Field) dag.pad).cookMertzEvaluate
        (CookMertz.PrimeField.units choice.modulus) index =
      CookMertz.BooleanExtension.embed (K := choice.Field)
        (dag.value index) :=
  Internal.cookMertzEvaluate_liftBoolean_pad_primeField_eq_embed_internal
    choice dag index

/-- Every variable bounded-fan-in Boolean DAG admits an explicit-size prime
field for which direct padded Cook--Mertz evaluation is correct. -/
theorem exists_primeField_cookMertzEvaluate_liftBoolean_pad_eq_embed
    (dag : DAG size d (Fin b → Bool)) (index : Fin size) :
    ∃ choice : CookMertz.PrimeField.Choice (d * b),
      (OrderedDAG.liftBoolean (K := choice.Field) dag.pad).cookMertzEvaluate
          (CookMertz.PrimeField.units choice.modulus) index =
        CookMertz.BooleanExtension.embed (K := choice.Field)
          (dag.value index) :=
  Internal.exists_primeField_cookMertzEvaluate_liftBoolean_pad_eq_embed_internal
    dag index

end DAG

end BoundedFanIn

end TreeEval

end Complexity
