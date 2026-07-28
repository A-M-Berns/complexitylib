/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG
import Complexitylib.TreeEvaluation.Workspace.Defs

/-!
# Proof internals for Cook--Mertz workspace profiles

This file proves that the profiled traversals compute the same register state
as the original executable evaluators and that their peak live-frame count is
bounded by semantic tree height. It also identifies the direct ordered-DAG
profile with the profile of its semantic unrolling.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace Workspace

namespace Internal

variable {d size : ℕ} {F V : Type*}

private theorem foldl_result_eq {α ι : Type*}
    (items : List ι) (step : Profile α → ι → Profile α)
    (plainStep : α → ι → α) (initial : Profile α)
    (hstep : ∀ current item,
      (step current item).result = plainStep current.result item) :
    (items.foldl step initial).result =
      items.foldl plainStep initial.result := by
  symm
  exact List.foldl_hom Profile.result fun current item =>
    (hstep current item).symm

private theorem foldl_peakFrames_le {α ι : Type*}
    (items : List ι) (step : Profile α → ι → Profile α)
    (initial : Profile α) (bound : ℕ)
    (hinitial : initial.peakFrames ≤ bound)
    (hstep : ∀ current item,
      current.peakFrames ≤ bound →
        (step current item).peakFrames ≤ bound) :
    (items.foldl step initial).peakFrames ≤ bound := by
  induction items generalizing initial with
  | nil => exact hinitial
  | cons item items ih =>
      exact ih (step initial item) (hstep initial item hinitial)

theorem profileAccumulate_result_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) (scale : F)
    (out : Fin (d + 1)) (regs : Registers d V) :
    (profileAccumulate units tree scale out regs).result =
      accumulate units tree scale out regs := by
  induction tree generalizing scale out regs with
  | leaf value => rfl
  | node children combine ih =>
      rw [profileAccumulate, accumulate]
      apply foldl_result_eq
      intro current unit
      simp only
      let profiledPrepare :=
        (List.finRange d).foldl (fun current childIndex =>
          let target := out.succAbove childIndex
          let child :=
            profileAccumulate units (children childIndex) 1 target
              (scaleAt current.result target (unit : F))
          Profile.recordChild current child) current
      let plainPrepare :=
        (List.finRange d).foldl (fun current childIndex =>
          let target := out.succAbove childIndex
          accumulate units (children childIndex) 1 target
            (scaleAt current target (unit : F))) current.result
      have hprepare : profiledPrepare.result = plainPrepare := by
        apply foldl_result_eq
        intro childCurrent childIndex
        simp only [Profile.recordChild]
        exact ih childIndex 1 (out.succAbove childIndex)
          (scaleAt childCurrent.result (out.succAbove childIndex) (unit : F))
      let profiledCombined :=
        Profile.map
          (fun currentRegs =>
            addAt currentRegs out
              ((-scale) • combine
                (fun childIndex =>
                  profiledPrepare.result (out.succAbove childIndex))))
          profiledPrepare
      let plainCombined :=
        addAt plainPrepare out
          ((-scale) • combine
            (fun childIndex =>
              plainPrepare (out.succAbove childIndex)))
      have hcombined : profiledCombined.result = plainCombined := by
        simp only [profiledCombined, Profile.map]
        rw [hprepare]
      let profiledCleanup :=
        (List.finRange d).foldl (fun cleanupCurrent childIndex =>
          let target := out.succAbove childIndex
          let child :=
            profileAccumulate units (children childIndex) (-1) target
              cleanupCurrent.result
          Profile.map
            (fun currentRegs =>
              scaleAt currentRegs target (↑unit⁻¹ : F))
            (Profile.recordChild cleanupCurrent child)) profiledCombined
      let plainCleanup :=
        (List.finRange d).foldl (fun cleanupCurrent childIndex =>
          let target := out.succAbove childIndex
          scaleAt
            (accumulate units (children childIndex) (-1) target cleanupCurrent)
            target (↑unit⁻¹ : F)) plainCombined
      change profiledCleanup.result = plainCleanup
      calc
        profiledCleanup.result =
            (List.finRange d).foldl (fun cleanupCurrent childIndex =>
              let target := out.succAbove childIndex
              scaleAt
                (accumulate units (children childIndex) (-1) target cleanupCurrent)
                target (↑unit⁻¹ : F)) profiledCombined.result := by
          apply foldl_result_eq
          intro cleanupCurrent childIndex
          simp only [Profile.map, Profile.recordChild]
          rw [ih childIndex]
        _ = plainCleanup := by rw [hcombined]

theorem profileAccumulate_peakFrames_le_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) (scale : F)
    (out : Fin (d + 1)) (regs : Registers d V) :
    (profileAccumulate units tree scale out regs).peakFrames ≤
      tree.height + 1 := by
  induction tree generalizing scale out regs with
  | leaf value => simp [profileAccumulate, Profile.start]
  | node children combine ih =>
      rw [profileAccumulate, Tree.height_node]
      apply foldl_peakFrames_le
      · simp [Profile.start]
      · intro current unit hcurrent
        let prepared :=
          (List.finRange d).foldl (fun childCurrent childIndex =>
            let target := out.succAbove childIndex
            let child :=
              profileAccumulate units (children childIndex) 1 target
                (scaleAt childCurrent.result target (unit : F))
            Profile.recordChild childCurrent child) current
        have hprepared :
            prepared.peakFrames ≤
              1 + Finset.univ.sup (fun i => (children i).height) + 1 := by
          apply foldl_peakFrames_le
          · exact hcurrent
          · intro childCurrent childIndex hchildCurrent
            simp only [Profile.recordChild]
            apply max_le
            · exact hchildCurrent
            · have hrecursive :=
                ih childIndex 1 (out.succAbove childIndex)
                  (scaleAt childCurrent.result
                    (out.succAbove childIndex) (unit : F))
              have hheight :
                  (children childIndex).height ≤
                    Finset.univ.sup (fun i => (children i).height) :=
                Finset.le_sup
                  (f := fun i => (children i).height)
                  (Finset.mem_univ childIndex)
              omega
        let combined :=
          Profile.map
            (fun currentRegs =>
              addAt currentRegs out
                ((-scale) • combine
                  (fun childIndex =>
                    prepared.result (out.succAbove childIndex))))
            prepared
        have hcombined :
            combined.peakFrames ≤
              1 + Finset.univ.sup (fun i => (children i).height) + 1 := by
          exact hprepared
        apply foldl_peakFrames_le
        · exact hcombined
        · intro cleanupCurrent childIndex hcleanupCurrent
          simp only [Profile.map, Profile.recordChild]
          apply max_le
          · exact hcleanupCurrent
          · have hrecursive :=
              ih childIndex (-1) (out.succAbove childIndex)
                cleanupCurrent.result
            have hheight :
                (children childIndex).height ≤
                  Finset.univ.sup (fun i => (children i).height) :=
              Finset.le_sup
                (f := fun i => (children i).height)
                (Finset.mem_univ childIndex)
            omega

theorem profileEvaluate_result_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) :
    (profileEvaluate units tree).result = evaluate units tree := by
  simp only [profileEvaluate, Profile.map, evaluate]
  rw [profileAccumulate_result_internal]

theorem profileEvaluate_peakFrames_le_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) :
    (profileEvaluate units tree).peakFrames ≤ tree.height + 1 := by
  exact profileAccumulate_peakFrames_le_internal
    units tree 1 (Fin.last d) 0

private theorem profileDAGAccumulate_eq_profileUnrollAux
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V)
    (index : ℕ) (hindex : index < size) (scale : F)
    (out : Fin (d + 1)) (regs : Registers d V) :
    Ordered.profileDAGAccumulate units dag index hindex scale out regs =
      profileAccumulate units (OrderedDAG.Aux.unroll dag index hindex)
        scale out regs := by
  induction index using Nat.strong_induction_on generalizing scale out regs with
  | h index ih =>
      rw [Ordered.profileDAGAccumulate, OrderedDAG.Aux.unroll]
      generalize hspec : dag.spec ⟨index, hindex⟩ = spec
      cases spec with
      | leaf value => rfl
      | node children combine =>
          rw [profileAccumulate]
          simp_rw [ih (children _).val (children _).isLt]

theorem profileDAGAccumulate_eq_profileUnroll_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (scale : F) (out : Fin (d + 1)) (regs : Registers d V) :
    profileDAGAccumulate units dag index scale out regs =
      profileAccumulate units (dag.unroll index) scale out regs :=
  profileDAGAccumulate_eq_profileUnrollAux
    units dag index.val index.isLt scale out regs

theorem profileDAGEvaluate_eq_profileUnroll_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size) :
    profileDAGEvaluate units dag index =
      profileEvaluate units (dag.unroll index) := by
  simp only [profileDAGEvaluate, profileEvaluate]
  rw [profileDAGAccumulate_eq_profileUnroll_internal]

theorem registerCell_card_internal (d b : ℕ) :
    Fintype.card (RegisterCell d b) = registerFieldCells d b := by
  simp [RegisterCell, registerFieldCells, Fintype.card_prod]

end Internal

end Workspace

end CookMertz

end TreeEval

end Complexity
