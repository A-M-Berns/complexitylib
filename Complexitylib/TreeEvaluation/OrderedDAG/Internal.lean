/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG.Defs

/-!
# Correctness of ordered-DAG unrolling

This file proves that tree unrolling preserves the value of every computation
node, that tree height equals dependency depth, and that the structural
topological ordering bounds depth by the number of available nodes.
-/

namespace Complexity

namespace TreeEval

namespace OrderedDAG

namespace Internal

variable {size d : ℕ} {V : Type*}

theorem value_of_spec_leaf_internal (dag : OrderedDAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.value index = leafValue := by
  rw [OrderedDAG.value, Aux.value, h]

theorem value_of_spec_node_internal (dag : OrderedDAG size d V)
    (index : Fin size) (children : Fin d → Fin index.val)
    (combine : (Fin d → V) → V)
    (h : dag.spec index = .node children combine) :
    dag.value index =
      combine (fun r => dag.value (liftChild index (children r))) := by
  rw [OrderedDAG.value, Aux.value, h]
  rfl

theorem unroll_of_spec_leaf_internal (dag : OrderedDAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.unroll index = .leaf leafValue := by
  rw [OrderedDAG.unroll, Aux.unroll, h]

theorem unroll_of_spec_node_internal (dag : OrderedDAG size d V)
    (index : Fin size) (children : Fin d → Fin index.val)
    (combine : (Fin d → V) → V)
    (h : dag.spec index = .node children combine) :
    dag.unroll index =
      .node (fun r => dag.unroll (liftChild index (children r))) combine := by
  rw [OrderedDAG.unroll, Aux.unroll, h]
  rfl

private theorem value_unrollAux (dag : OrderedDAG size d V) (index : ℕ)
    (hindex : index < size) :
    (Aux.unroll dag index hindex).value = Aux.value dag index hindex := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [Aux.unroll, Aux.value]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf value => rfl
      | node children combine =>
          simp only [Tree.value_node]
          apply congrArg combine
          funext r
          exact ih (children r).val (children r).isLt _

/-- Internal proof that unrolling preserves shared-DAG evaluation. -/
theorem value_unroll_internal (dag : OrderedDAG size d V)
    (index : Fin size) :
    (dag.unroll index).value = dag.value index :=
  value_unrollAux dag index.val index.isLt

private theorem height_unrollAux (dag : OrderedDAG size d V) (index : ℕ)
    (hindex : index < size) :
    (Aux.unroll dag index hindex).height = Aux.depth dag index hindex := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [Aux.unroll, Aux.depth]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf value => rfl
      | node children combine =>
          rw [Tree.height_node]
          congr 1
          apply Finset.sup_congr rfl
          intro r _
          exact ih (children r).val (children r).isLt _

/-- Internal proof that unrolled-tree height is exactly DAG dependency depth. -/
theorem height_unroll_internal (dag : OrderedDAG size d V)
    (index : Fin size) :
    (dag.unroll index).height = dag.depth index :=
  height_unrollAux dag index.val index.isLt

private theorem depthAux_le_index_succ (dag : OrderedDAG size d V)
    (index : ℕ) (hindex : index < size) :
    Aux.depth dag index hindex ≤ index + 1 := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [Aux.depth]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf value => simp
      | node children combine =>
          have hsup :
              Finset.univ.sup
                (fun r =>
                  Aux.depth dag (children r).val
                    (Nat.lt_trans (children r).isLt hindex)) ≤ index := by
            rw [Finset.sup_le_iff]
            intro r _
            exact (ih (children r).val (children r).isLt _).trans
              (Nat.succ_le_iff.mpr (children r).isLt)
          simpa [Nat.add_comm] using Nat.add_le_add_left hsup 1

/-- Internal index-sensitive dependency-depth bound. -/
theorem depth_le_index_succ_internal (dag : OrderedDAG size d V)
    (index : Fin size) :
    dag.depth index ≤ index.val + 1 :=
  depthAux_le_index_succ dag index.val index.isLt

/-- Internal whole-DAG dependency-depth bound. -/
theorem depth_le_size_internal (dag : OrderedDAG size d V)
    (index : Fin size) :
    dag.depth index ≤ size :=
  (depth_le_index_succ_internal dag index).trans
    (Nat.succ_le_iff.mpr index.isLt)

end Internal

end OrderedDAG

end TreeEval

end Complexity
