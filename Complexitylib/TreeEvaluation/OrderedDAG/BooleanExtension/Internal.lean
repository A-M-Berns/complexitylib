/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.BooleanExtension.Evaluation
import Complexitylib.TreeEvaluation.OrderedDAG.BooleanExtension.Defs

/-!
# Correctness internals for lifting Boolean ordered DAGs

The lift preserves every Boolean node value after zero-one embedding and
provides the nodewise degree certificate required by Cook--Mertz evaluation.
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

namespace Internal

variable {size d b : ℕ} {K : Type*}

theorem liftBoolean_isLowDegreePolynomial_internal
    [CommRing K] [Nontrivial K]
    (dag : OrderedDAG size d (Fin b → Bool)) (degreeBound : ℕ)
    (hdegree : d * b < degreeBound) :
    (liftBoolean (K := K) dag).IsLowDegreePolynomial degreeBound := by
  intro index
  generalize hspec : dag.spec index = spec
  cases spec with
  | leaf value =>
      simp [liftBoolean, hspec, Node.IsLowDegreePolynomial]
  | node children combine =>
      simp only [liftBoolean, hspec, Node.IsLowDegreePolynomial]
      refine
        ⟨CookMertz.BooleanExtension.nodePolynomials combine,
          CookMertz.BooleanExtension.Evaluation.evaluateNode_eq_polynomialNode
            combine, ?_⟩
      intro j
      exact
        (CookMertz.BooleanExtension.nodePolynomials_totalDegree_le
          combine j).trans_lt hdegree

private theorem value_liftBooleanAux [CommRing K]
    (dag : OrderedDAG size d (Fin b → Bool)) (index : ℕ)
    (hindex : index < size) :
    Aux.value (liftBoolean (K := K) dag) index hindex =
      CookMertz.BooleanExtension.embed (Aux.value dag index hindex) := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [Aux.value, Aux.value]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf value =>
          simp [liftBoolean, hspec]
      | node children combine =>
          simp only [liftBoolean, hspec]
          change CookMertz.BooleanExtension.Evaluation.evaluateNode combine
              (fun r =>
                Aux.value (liftBoolean (K := K) dag) (children r).val
                  (Nat.lt_trans (children r).isLt hindex)) =
            CookMertz.BooleanExtension.embed
              (combine fun r =>
                Aux.value dag (children r).val
                  (Nat.lt_trans (children r).isLt hindex))
          have hchildren :
              (fun r =>
                Aux.value (liftBoolean (K := K) dag) (children r).val
                  (Nat.lt_trans (children r).isLt hindex)) =
                fun r => CookMertz.BooleanExtension.embed
                  (Aux.value dag (children r).val
                    (Nat.lt_trans (children r).isLt hindex)) := by
            funext r
            exact ih (children r).val (children r).isLt _
          rw [hchildren]
          exact
            CookMertz.BooleanExtension.Evaluation.evaluateNode_bool
              combine _

theorem value_liftBoolean_internal [CommRing K]
    (dag : OrderedDAG size d (Fin b → Bool)) (index : Fin size) :
    (liftBoolean (K := K) dag).value index =
      CookMertz.BooleanExtension.embed (dag.value index) :=
  value_liftBooleanAux dag index.val index.isLt

end Internal

end OrderedDAG

end TreeEval

end Complexity
