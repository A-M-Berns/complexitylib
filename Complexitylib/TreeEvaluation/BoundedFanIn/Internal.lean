/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.BoundedFanIn.Defs
import Complexitylib.TreeEvaluation.OrderedDAG

/-!
# Correctness internals for variable-fan-in padding

This file proves that exact-arity padding is a semantic retraction on genuine
child positions and preserves tree value, tree height, DAG value, and DAG
dependency depth.
-/

namespace Complexity

namespace TreeEval

namespace BoundedFanIn

namespace Internal

variable {size d : ℕ} {V : Type*}

theorem projectIndex_embedIndex_internal
    (arity : Arity d) (index : Fin arity.width) :
    arity.projectIndex (arity.embedIndex index) = index := by
  simp [Arity.projectIndex, Arity.embedIndex, Fin.ext_iff]

theorem sup_projectIndex_internal (arity : Arity d)
    (f : Fin arity.width → ℕ) :
    Finset.univ.sup (fun index : Fin d => f (arity.projectIndex index)) =
      Finset.univ.sup f := by
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro index _
    exact Finset.le_sup (f := f)
      (Finset.mem_univ (arity.projectIndex index))
  · rw [Finset.sup_le_iff]
    intro index _
    have hle :=
      Finset.le_sup
        (f := fun paddedIndex : Fin d =>
          f (arity.projectIndex paddedIndex))
        (Finset.mem_univ (arity.embedIndex index))
    simpa only [projectIndex_embedIndex_internal] using hle

theorem tree_value_pad_internal (tree : Tree d V) :
    tree.pad.value = tree.value := by
  induction tree with
  | leaf leafValue => rfl
  | node arity children combine ih =>
      simp only [Tree.pad, TreeEval.Tree.value_node, Tree.value]
      apply congrArg combine
      funext index
      simpa only [projectIndex_embedIndex_internal] using
        ih (arity.projectIndex (arity.embedIndex index))

theorem tree_height_pad_internal (tree : Tree d V) :
    tree.pad.height = tree.height := by
  induction tree with
  | leaf leafValue => rfl
  | node arity children combine ih =>
      simp only [Tree.pad, TreeEval.Tree.height_node, Tree.height]
      congr 1
      simp_rw [ih]
      exact sup_projectIndex_internal arity
        (fun index => (children index).height)

theorem value_of_spec_leaf_internal (dag : DAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.value index = leafValue := by
  rw [DAG.value, DAG.Aux.value, h]

theorem value_of_spec_node_internal (dag : DAG size d V)
    (index : Fin size) (arity : Arity d)
    (children : Fin arity.width → Fin index.val)
    (combine : (Fin arity.width → V) → V)
    (h : dag.spec index = .node arity children combine) :
    dag.value index =
      combine (fun childIndex =>
        dag.value (DAG.liftChild index (children childIndex))) := by
  rw [DAG.value, DAG.Aux.value, h]
  rfl

theorem unroll_of_spec_leaf_internal (dag : DAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.unroll index = .leaf leafValue := by
  rw [DAG.unroll, DAG.Aux.unroll, h]

theorem unroll_of_spec_node_internal (dag : DAG size d V)
    (index : Fin size) (arity : Arity d)
    (children : Fin arity.width → Fin index.val)
    (combine : (Fin arity.width → V) → V)
    (h : dag.spec index = .node arity children combine) :
    dag.unroll index =
      .node arity
        (fun childIndex =>
          dag.unroll (DAG.liftChild index (children childIndex)))
        combine := by
  rw [DAG.unroll, DAG.Aux.unroll, h]
  rfl

theorem depth_of_spec_leaf_internal (dag : DAG size d V)
    (index : Fin size) (leafValue : V)
    (h : dag.spec index = .leaf leafValue) :
    dag.depth index = 0 := by
  rw [DAG.depth, DAG.Aux.depth, h]

theorem depth_of_spec_node_internal (dag : DAG size d V)
    (index : Fin size) (arity : Arity d)
    (children : Fin arity.width → Fin index.val)
    (combine : (Fin arity.width → V) → V)
    (h : dag.spec index = .node arity children combine) :
    dag.depth index =
      1 + Finset.univ.sup fun childIndex =>
        dag.depth (DAG.liftChild index (children childIndex)) := by
  rw [DAG.depth, DAG.Aux.depth, h]
  rfl

private theorem value_unrollAux (dag : DAG size d V) (index : ℕ)
    (hindex : index < size) :
    (DAG.Aux.unroll dag index hindex).value =
      DAG.Aux.value dag index hindex := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [DAG.Aux.unroll, DAG.Aux.value]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf leafValue => rfl
      | node arity children combine =>
          simp only [Tree.value_node]
          apply congrArg combine
          funext childIndex
          exact ih (children childIndex).val
            (children childIndex).isLt _

theorem value_unroll_internal (dag : DAG size d V)
    (index : Fin size) :
    (dag.unroll index).value = dag.value index :=
  value_unrollAux dag index.val index.isLt

private theorem height_unrollAux (dag : DAG size d V) (index : ℕ)
    (hindex : index < size) :
    (DAG.Aux.unroll dag index hindex).height =
      DAG.Aux.depth dag index hindex := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [DAG.Aux.unroll, DAG.Aux.depth]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf leafValue => rfl
      | node arity children combine =>
          rw [Tree.height_node]
          congr 1
          apply Finset.sup_congr rfl
          intro childIndex _
          exact ih (children childIndex).val
            (children childIndex).isLt _

theorem height_unroll_internal (dag : DAG size d V)
    (index : Fin size) :
    (dag.unroll index).height = dag.depth index :=
  height_unrollAux dag index.val index.isLt

private theorem depthAux_le_index_succ (dag : DAG size d V)
    (index : ℕ) (hindex : index < size) :
    DAG.Aux.depth dag index hindex ≤ index + 1 := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [DAG.Aux.depth]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf leafValue => simp
      | node arity children combine =>
          have hsup :
              Finset.univ.sup
                (fun childIndex =>
                  DAG.Aux.depth dag (children childIndex).val
                    (Nat.lt_trans (children childIndex).isLt hindex)) ≤
                index := by
            rw [Finset.sup_le_iff]
            intro childIndex _
            exact
              (ih (children childIndex).val
                (children childIndex).isLt _).trans
                (Nat.succ_le_iff.mpr (children childIndex).isLt)
          simpa [Nat.add_comm] using Nat.add_le_add_left hsup 1

theorem depth_le_index_succ_internal (dag : DAG size d V)
    (index : Fin size) :
    dag.depth index ≤ index.val + 1 :=
  depthAux_le_index_succ dag index.val index.isLt

theorem depth_le_size_internal (dag : DAG size d V)
    (index : Fin size) :
    dag.depth index ≤ size :=
  (depth_le_index_succ_internal dag index).trans
    (Nat.succ_le_iff.mpr index.isLt)

private theorem pad_unrollAux (dag : DAG size d V) (index : ℕ)
    (hindex : index < size) :
    (DAG.Aux.unroll dag index hindex).pad =
      OrderedDAG.Aux.unroll dag.pad index hindex := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [DAG.Aux.unroll, OrderedDAG.Aux.unroll]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf leafValue =>
          simp [DAG.pad, hspec]
      | node arity children combine =>
          simp only [Tree.pad, DAG.pad, hspec]
          congr 1
          funext childIndex
          exact ih (children (arity.projectIndex childIndex)).val
            (children (arity.projectIndex childIndex)).isLt _

theorem pad_unroll_internal (dag : DAG size d V)
    (index : Fin size) :
    (dag.unroll index).pad = dag.pad.unroll index :=
  pad_unrollAux dag index.val index.isLt

theorem value_pad_internal (dag : DAG size d V)
    (index : Fin size) :
    dag.pad.value index = dag.value index := by
  rw [← OrderedDAG.value_unroll]
  rw [← pad_unroll_internal]
  rw [tree_value_pad_internal]
  exact value_unroll_internal dag index

theorem depth_pad_internal (dag : DAG size d V)
    (index : Fin size) :
    dag.pad.depth index = dag.depth index := by
  rw [← OrderedDAG.height_unroll]
  rw [← pad_unroll_internal]
  rw [tree_height_pad_internal]
  exact height_unroll_internal dag index

end Internal

end BoundedFanIn

end TreeEval

end Complexity
