/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz.Defs

/-!
# Correctness of the Cook--Mertz accumulator

This file proves that the executable accumulator in `CookMertz.Defs` adds the
tree value to its selected output register and restores every other global
register. The proof tracks the forward and reverse child passes separately,
then applies the affine-line identity at each internal node.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace Internal

variable {ι κ W : Type*}

private def modifyAt [DecidableEq κ] (regs : κ → W) (i : κ) (f : W → W) : κ → W :=
  Function.update regs i (f (regs i))

private theorem foldl_modifyAt_apply_of_forall_ne [DecidableEq κ]
    (l : List ι) (idx : ι → κ) (f : ι → W → W) (regs : κ → W) (j : κ)
    (h : ∀ i ∈ l, idx i ≠ j) :
    (l.foldl (fun regs i => modifyAt regs (idx i) (f i)) regs) j = regs j := by
  induction l generalizing regs with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldl_cons]
      rw [ih]
      · rw [modifyAt, Function.update_of_ne]
        exact (h a (by simp)).symm
      · intro i hi
        exact h i (by simp [hi])

private theorem foldl_modifyAt_apply_of_mem [DecidableEq κ]
    (l : List ι) (idx : ι → κ) (f : ι → W → W) (regs : κ → W) (target : ι)
    (hl : l.Nodup) (htarget : target ∈ l) (hinj : Function.Injective idx) :
    (l.foldl (fun regs i => modifyAt regs (idx i) (f i)) regs) (idx target) =
      f target (regs (idx target)) := by
  induction l generalizing regs with
  | nil => simp at htarget
  | cons a l ih =>
      simp only [List.foldl_cons]
      by_cases hat : a = target
      · subst a
        rw [foldl_modifyAt_apply_of_forall_ne]
        · simp [modifyAt]
        · intro i hi hidx
          have hit : i = target := hinj hidx
          subst i
          exact (List.nodup_cons.mp hl).1 hi
      · have htmem : target ∈ l := by
          rcases List.mem_cons.mp htarget with hta | hmem
          · exact False.elim (hat hta.symm)
          · exact hmem
        rw [ih _ (List.nodup_cons.mp hl).2 htmem]
        rw [modifyAt, Function.update_of_ne]
        exact fun hidx => hat (hinj hidx.symm)

variable {d : ℕ} {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private theorem addAt_scaleAt_same (regs : Registers d V) (i : Fin (d + 1))
    (a : F) (v : V) :
    addAt (scaleAt regs i a) i v = modifyAt regs i (fun x => a • x + v) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [addAt, scaleAt, modifyAt]
  · simp [addAt, scaleAt, modifyAt, h]

private theorem scaleAt_addAt_same (regs : Registers d V) (i : Fin (d + 1))
    (a : F) (v : V) :
    scaleAt (addAt regs i v) i a = modifyAt regs i (fun x => a • (x + v)) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [addAt, scaleAt, modifyAt]
  · simp [addAt, scaleAt, modifyAt, h]

private theorem prepare_apply_out (units : List Fˣ) (children : Fin d → Tree d V)
    (hchild : ∀ r s out regs,
      accumulate units (children r) s out regs =
        addAt regs out (s • (children r).value))
    (a : Fˣ) (out : Fin (d + 1)) (regs : Registers d V) :
    prepare units children a out regs out = regs out := by
  simp only [prepare]
  have hstep :
      (fun regs r =>
        let i := out.succAbove r
        accumulate units (children r) 1 i (scaleAt regs i (a : F))) =
      (fun regs r =>
        modifyAt regs (out.succAbove r)
          (fun x => (a : F) • x + (children r).value)) := by
    funext current r
    simp only
    rw [hchild]
    simpa using
      addAt_scaleAt_same current (out.succAbove r) (a : F) (children r).value
  rw [hstep]
  apply foldl_modifyAt_apply_of_forall_ne
  intro r _
  exact Fin.succAbove_ne out r

private theorem prepare_apply_scratch (units : List Fˣ)
    (children : Fin d → Tree d V)
    (hchild : ∀ r s out regs,
      accumulate units (children r) s out regs =
        addAt regs out (s • (children r).value))
    (a : Fˣ) (out : Fin (d + 1)) (regs : Registers d V) (r : Fin d) :
    prepare units children a out regs (out.succAbove r) =
      (a : F) • regs (out.succAbove r) + (children r).value := by
  simp only [prepare]
  have hstep :
      (fun regs r =>
        let i := out.succAbove r
        accumulate units (children r) 1 i (scaleAt regs i (a : F))) =
      (fun regs r =>
        modifyAt regs (out.succAbove r)
          (fun x => (a : F) • x + (children r).value)) := by
    funext current q
    simp only
    rw [hchild]
    simpa using
      addAt_scaleAt_same current (out.succAbove q) (a : F) (children q).value
  rw [hstep]
  apply foldl_modifyAt_apply_of_mem
  · exact List.nodup_finRange d
  · exact List.mem_finRange r
  · exact Fin.succAbove_right_injective

private theorem cleanup_apply_out (units : List Fˣ) (children : Fin d → Tree d V)
    (hchild : ∀ r s out regs,
      accumulate units (children r) s out regs =
        addAt regs out (s • (children r).value))
    (a : Fˣ) (out : Fin (d + 1)) (regs : Registers d V) :
    cleanup units children a out regs out = regs out := by
  simp only [cleanup]
  have hstep :
      (fun regs r =>
        let i := out.succAbove r
        scaleAt (accumulate units (children r) (-1) i regs) i (↑a⁻¹ : F)) =
      (fun regs r =>
        modifyAt regs (out.succAbove r)
          (fun x => (↑a⁻¹ : F) • (x + (-1 : F) • (children r).value))) := by
    funext current r
    simp only
    rw [hchild]
    exact scaleAt_addAt_same current (out.succAbove r) (↑a⁻¹ : F)
      ((-1 : F) • (children r).value)
  rw [hstep]
  apply foldl_modifyAt_apply_of_forall_ne
  intro r _
  exact Fin.succAbove_ne out r

private theorem cleanup_apply_scratch (units : List Fˣ)
    (children : Fin d → Tree d V)
    (hchild : ∀ r s out regs,
      accumulate units (children r) s out regs =
        addAt regs out (s • (children r).value))
    (a : Fˣ) (out : Fin (d + 1)) (regs : Registers d V) (r : Fin d) :
    cleanup units children a out regs (out.succAbove r) =
      (↑a⁻¹ : F) •
        (regs (out.succAbove r) + (-1 : F) • (children r).value) := by
  simp only [cleanup]
  have hstep :
      (fun regs r =>
        let i := out.succAbove r
        scaleAt (accumulate units (children r) (-1) i regs) i (↑a⁻¹ : F)) =
      (fun regs r =>
        modifyAt regs (out.succAbove r)
          (fun x => (↑a⁻¹ : F) • (x + (-1 : F) • (children r).value))) := by
    funext current q
    simp only
    rw [hchild]
    exact scaleAt_addAt_same current (out.succAbove q) (↑a⁻¹ : F)
      ((-1 : F) • (children q).value)
  rw [hstep]
  apply foldl_modifyAt_apply_of_mem
  · exact List.nodup_finRange d
  · exact List.mem_finRange r
  · exact Fin.succAbove_right_injective

private theorem addAt_zero (regs : Registers d V) (out : Fin (d + 1)) :
    addAt regs out 0 = regs := by
  ext j
  by_cases h : j = out
  · subst j
    simp [addAt]
  · simp [addAt, h]

private theorem addAt_addAt (regs : Registers d V) (out : Fin (d + 1)) (x y : V) :
    addAt (addAt regs out x) out y = addAt regs out (x + y) := by
  ext j
  by_cases h : j = out
  · subst j
    simp [addAt, add_assoc]
  · simp [addAt, h]

private theorem foldl_addAt_of_frame (l : List ι) (out : Fin (d + 1))
    (payload : Registers d V → ι → V) (regs : Registers d V)
    (hframe : ∀ current z i, payload (addAt current out z) i = payload current i) :
    l.foldl (fun current i => addAt current out (payload current i)) regs =
      addAt regs out (l.map (payload regs)).sum := by
  induction l generalizing regs with
  | nil =>
      simp only [List.foldl_nil, List.map_nil, List.sum_nil]
      exact (addAt_zero regs out).symm
  | cons a l ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      have hmap : l.map (payload (addAt regs out (payload regs a))) =
          l.map (payload regs) := by
        apply List.map_congr_left
        intro i _
        exact hframe regs (payload regs a) i
      rw [hmap, addAt_addAt]

private def nodePass (units : List Fˣ) (children : Fin d → Tree d V)
    (combine : (Fin d → V) → V) (s : F) (out : Fin (d + 1))
    (regs : Registers d V) (a : Fˣ) : Registers d V :=
  let regs := prepare units children a out regs
  let args := fun r => regs (out.succAbove r)
  let regs := addAt regs out ((-s) • combine args)
  cleanup units children a out regs

private theorem nodePass_eq (units : List Fˣ) (children : Fin d → Tree d V)
    (combine : (Fin d → V) → V)
    (hchild : ∀ r s out regs,
      accumulate units (children r) s out regs =
        addAt regs out (s • (children r).value))
    (s : F) (out : Fin (d + 1)) (regs : Registers d V) (a : Fˣ) :
    nodePass units children combine s out regs a =
      addAt regs out
        ((-s) • combine (fun r =>
          (a : F) • regs (out.succAbove r) + (children r).value)) := by
  ext j
  by_cases hj : j = out
  · subst j
    simp only [nodePass]
    rw [cleanup_apply_out units children hchild]
    simp only [addAt, Function.update_self]
    rw [prepare_apply_out units children hchild]
    apply congrArg (fun z => regs out + (-s) • z)
    congr 1
    funext r
    exact prepare_apply_scratch units children hchild a out regs r
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hj
    subst j
    simp only [nodePass]
    rw [cleanup_apply_scratch units children hchild]
    simp [addAt, Fin.succAbove_ne, prepare_apply_scratch units children hchild]

/-- Internal proof of the public accumulator-correctness theorem. -/
theorem accumulate_eq_addAt_internal (units : List Fˣ) (tree : Tree d V) :
    LineCompatible units tree →
      ∀ s out regs,
        accumulate units tree s out regs = addAt regs out (s • tree.value) := by
  induction tree with
  | leaf value =>
      intro _ s out regs
      rfl
  | node children combine ih =>
      intro hcompatible s out regs
      rcases hcompatible with ⟨hchildren, hline⟩
      have hchild : ∀ r s out regs,
          accumulate units (children r) s out regs =
            addAt regs out (s • (children r).value) :=
        fun r => ih r (hchildren r)
      simp only [accumulate, Tree.value]
      change units.foldl (nodePass units children combine s out) regs =
        addAt regs out (s • combine (fun r => (children r).value))
      let payload : Registers d V → Fˣ → V := fun current a =>
        (-s) • combine (fun r =>
          (a : F) • current (out.succAbove r) + (children r).value)
      have hpass : nodePass units children combine s out =
          fun current a => addAt current out (payload current a) := by
        funext current a
        exact nodePass_eq units children combine hchild s out current a
      rw [hpass]
      change units.foldl (fun current a => addAt current out (payload current a)) regs =
        addAt regs out (s • combine (fun r => (children r).value))
      rw [foldl_addAt_of_frame]
      · congr 1
        change (units.map fun (a : Fˣ) =>
          (-s) • combine (fun r =>
            (a : F) • regs (out.succAbove r) + (children r).value)).sum =
              s • combine (fun r => (children r).value)
        let values := units.map fun (a : Fˣ) =>
          combine (fun r =>
            (a : F) • regs (out.succAbove r) + (children r).value)
        calc
          (units.map fun (a : Fˣ) =>
              (-s) • combine (fun r =>
                (a : F) • regs (out.succAbove r) + (children r).value)).sum =
              (values.map fun x => (-s) • x).sum := by
                apply congrArg List.sum
                rw [List.map_map]
                rfl
          _ = (-s) • values.sum := List.smul_sum.symm
          _ = (-s) • -combine (fun r => (children r).value) := by
            rw [show values.sum = -combine (fun r => (children r).value) from
              hline (fun r => regs (out.succAbove r))
                (fun r => (children r).value)]
          _ = s • combine (fun r => (children r).value) := by simp
      · intro current z a
        simp only [payload]
        congr 2
        funext r
        simp [addAt, Fin.succAbove_ne]

end Internal

end CookMertz

end TreeEval

end Complexity
