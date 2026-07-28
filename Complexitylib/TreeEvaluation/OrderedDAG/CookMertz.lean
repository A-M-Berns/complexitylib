/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Interpolation
import Complexitylib.TreeEvaluation.OrderedDAG
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz.Defs
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz.Internal

/-!
# Cook--Mertz evaluation of ordered computation DAGs

This file composes three checked semantic layers:

1. nodewise low-degree polynomial certificates on a compact ordered DAG;
2. value-preserving unrolling into a bounded-height tree; and
3. correctness of the executable Cook--Mertz catalytic accumulator.

The resulting theorem evaluates any chosen DAG node correctly. The remaining
Williams work is operational: generate node specifications on demand and
compile this traversal to a Turing machine with the claimed workspace bound,
without materializing `dag.unroll index`.

## Main theorems

- `unroll_isLowDegreePolynomial` -- nodewise certificates survive unrolling
- `unroll_lineCompatible` -- the unrolled tree satisfies interpolation
- `cookMertzAccumulate_eq_addAt` -- direct DAG traversal has the catalytic frame
- `cookMertzEvaluate_eq_value` -- direct Cook--Mertz evaluation returns the DAG value
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

variable {size d : ℕ} {ι K : Type*}

/-- Nodewise low-degree polynomial certificates survive tree unrolling. -/
theorem unroll_isLowDegreePolynomial [CommSemiring K]
    (dag : OrderedDAG size d (ι → K)) (degreeBound : ℕ)
    (hdag : dag.IsLowDegreePolynomial degreeBound)
    (index : Fin size) :
    CookMertz.IsLowDegreePolynomial degreeBound (dag.unroll index) :=
  Internal.unroll_isLowDegreePolynomial_internal
    dag degreeBound hdag index

/-- A low-degree computation DAG unrolls to a tree satisfying the exact
Cook--Mertz affine-line identity. -/
theorem unroll_lineCompatible [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : CookMertz.EnumeratesUnits units)
    (dag : OrderedDAG size d (ι → K))
    (hdag : dag.IsLowDegreePolynomial (Fintype.card K - 1))
    (index : Fin size) :
    CookMertz.LineCompatible units (dag.unroll index) :=
  CookMertz.lowDegreePolynomial_lineCompatible units henum
    (dag.unroll index)
    (unroll_isLowDegreePolynomial dag (Fintype.card K - 1) hdag index)

/-- Direct compact-DAG traversal is extensionally equal to evaluating the
semantic unrolling. -/
theorem cookMertzAccumulate_eq_accumulate_unroll {F V : Type*}
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (s : F) (out : Fin (d + 1)) (regs : CookMertz.Registers d V) :
    dag.cookMertzAccumulate units index s out regs =
      CookMertz.accumulate units (dag.unroll index) s out regs :=
  Internal.cookMertzAccumulate_eq_accumulate_unroll_internal
    units dag index s out regs

/-- The direct ordered-DAG traversal adds the scaled node value to its selected
output register and restores every other catalytic register. -/
theorem cookMertzAccumulate_eq_addAt {F V : Type*}
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (hline : CookMertz.LineCompatible units (dag.unroll index))
    (s : F) (out : Fin (d + 1)) (regs : CookMertz.Registers d V) :
    dag.cookMertzAccumulate units index s out regs =
      CookMertz.addAt regs out (s • dag.value index) := by
  calc
    dag.cookMertzAccumulate units index s out regs =
        CookMertz.accumulate units (dag.unroll index) s out regs :=
      cookMertzAccumulate_eq_accumulate_unroll
        units dag index s out regs
    _ = CookMertz.addAt regs out (s • (dag.unroll index).value) :=
      CookMertz.accumulate_eq_addAt units (dag.unroll index)
        hline s out regs
    _ = CookMertz.addAt regs out (s • dag.value index) := by
      rw [value_unroll]

/-- The executable Cook--Mertz evaluator returns the shared-DAG value of any
node whose compact DAG carries sufficiently low-degree polynomial
certificates. -/
theorem cookMertzEvaluateUnroll_eq_value [Field K] [Fintype K]
    [DecidableEq K]
    (units : List Kˣ) (henum : CookMertz.EnumeratesUnits units)
    (dag : OrderedDAG size d (ι → K))
    (hdag : dag.IsLowDegreePolynomial (Fintype.card K - 1))
    (index : Fin size) :
    CookMertz.evaluate units (dag.unroll index) = dag.value index := by
  calc
    CookMertz.evaluate units (dag.unroll index) =
        (dag.unroll index).value :=
      CookMertz.evaluate_lowDegreePolynomial units henum
        (dag.unroll index)
        (unroll_isLowDegreePolynomial dag
          (Fintype.card K - 1) hdag index)
    _ = dag.value index := value_unroll dag index

/-- The direct, non-materializing Cook--Mertz DAG traversal returns the value
of the selected shared computation node. -/
theorem cookMertzEvaluate_eq_value [Field K] [Fintype K] [DecidableEq K]
    (units : List Kˣ) (henum : CookMertz.EnumeratesUnits units)
    (dag : OrderedDAG size d (ι → K))
    (hdag : dag.IsLowDegreePolynomial (Fintype.card K - 1))
    (index : Fin size) :
    dag.cookMertzEvaluate units index = dag.value index := by
  calc
    dag.cookMertzEvaluate units index =
        CookMertz.evaluate units (dag.unroll index) :=
      Internal.cookMertzEvaluate_eq_evaluate_unroll_internal
        units dag index
    _ = dag.value index :=
      cookMertzEvaluateUnroll_eq_value units henum dag hdag index

end OrderedDAG

end TreeEval

end Complexity
