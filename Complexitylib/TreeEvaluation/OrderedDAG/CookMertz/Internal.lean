/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz.Defs

/-!
# Low-degree certificates survive ordered-DAG unrolling

The proof is a strong induction over the structural topological ordering. Each
tree copy of a shared DAG node reuses that node's local polynomial certificate.
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

namespace Internal

variable {size d : ℕ} {ι K : Type*} [CommSemiring K]

private theorem unrollAux_isLowDegreePolynomial
    (dag : OrderedDAG size d (ι → K)) (degreeBound : ℕ)
    (hdag : dag.IsLowDegreePolynomial degreeBound)
    (index : ℕ) (hindex : index < size) :
    CookMertz.IsLowDegreePolynomial degreeBound
      (Aux.unroll dag index hindex) := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [Aux.unroll]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf value => trivial
      | node children combine =>
          have hlocal := hdag ⟨index, hindex⟩
          rw [hspec] at hlocal
          rcases hlocal with ⟨polynomials, hcombine, hdegree⟩
          refine ⟨?_, polynomials, hcombine, hdegree⟩
          intro r
          exact ih (children r).val (children r).isLt _

/-- Internal lift of nodewise low-degree certificates to an unrolled tree. -/
theorem unroll_isLowDegreePolynomial_internal
    (dag : OrderedDAG size d (ι → K)) (degreeBound : ℕ)
    (hdag : dag.IsLowDegreePolynomial degreeBound)
    (index : Fin size) :
    CookMertz.IsLowDegreePolynomial degreeBound (dag.unroll index) :=
  unrollAux_isLowDegreePolynomial dag degreeBound hdag index.val index.isLt

section Accumulator

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private theorem cookMertzAccumulate_eq_unrollAux
    (units : List Fˣ) (dag : OrderedDAG size d V)
    (index : ℕ) (hindex : index < size) (s : F)
    (out : Fin (d + 1)) (regs : CookMertz.Registers d V) :
    Aux.cookMertzAccumulate units dag index hindex s out regs =
      CookMertz.accumulate units (Aux.unroll dag index hindex) s out regs := by
  induction index using Nat.strong_induction_on generalizing s out regs with
  | h index ih =>
      rw [Aux.cookMertzAccumulate, Aux.unroll]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf value => rfl
      | node children combine =>
          rw [CookMertz.accumulate]
          simp_rw [ih (children _).val (children _).isLt]

/-- Internal equivalence between direct DAG traversal and explicit unrolling. -/
theorem cookMertzAccumulate_eq_accumulate_unroll_internal
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (s : F) (out : Fin (d + 1)) (regs : CookMertz.Registers d V) :
    dag.cookMertzAccumulate units index s out regs =
      CookMertz.accumulate units (dag.unroll index) s out regs :=
  cookMertzAccumulate_eq_unrollAux
    units dag index.val index.isLt s out regs

/-- Internal equivalence of the two zero-register evaluator presentations. -/
theorem cookMertzEvaluate_eq_evaluate_unroll_internal
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size) :
    dag.cookMertzEvaluate units index =
      CookMertz.evaluate units (dag.unroll index) := by
  simpa [cookMertzEvaluate, CookMertz.evaluate] using
    congrArg (fun regs => regs (Fin.last d))
      (cookMertzAccumulate_eq_accumulate_unroll_internal units dag index
        1 (Fin.last d) 0)

end Accumulator

end Internal

end OrderedDAG

end TreeEval

end Complexity
