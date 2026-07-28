/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.CookMertz
import Complexitylib.TreeEvaluation.CookMertz.PrimeField
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.CookMertz.Defs

/-!
# Correctness internals for runtime-residue Cook--Mertz evaluation

The main simulation theorem casts the natural-residue accumulator into
`ZMod p` and identifies it with the generic Cook--Mertz accumulator over the
explicit certificate-side unit enumeration. Separate invariants prove that
all stored runtime registers remain canonical and fit in `p.size` bits.
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace PrimeField

namespace Runtime

namespace CookMertz

namespace Internal

variable {d p : ℕ}

private theorem foldl_preserves
    {State Index : Type*} (property : State → Prop)
    (step : State → Index → State)
    (hstep : ∀ state index, property state →
      property (step state index))
    (indices : List Index) (initial : State)
    (hinitial : property initial) :
    property (indices.foldl step initial) := by
  induction indices generalizing initial with
  | nil =>
      exact hinitial
  | cons index indices ih =>
      simp only [List.foldl_cons]
      exact ih (step initial index)
        (hstep initial index hinitial)

private theorem foldNonzeroLoop_preserves
    {State : Type*} (property : State → Prop)
    (step : State → ℕ → State)
    (hstep : ∀ state candidate, property state →
      property (step state candidate))
    (fuel candidate : ℕ) (initial : State)
    (hinitial : property initial) :
    property
      (Runtime.foldNonzeroLoop step fuel candidate initial) := by
  induction fuel generalizing candidate initial with
  | zero =>
      exact hinitial
  | succ fuel ih =>
      rw [Runtime.foldNonzeroLoop]
      exact ih (candidate + 1) (step initial candidate)
        (hstep initial candidate hinitial)

private theorem cast_foldl
    {RuntimeState FieldState Index : Type*}
    (cast : RuntimeState → FieldState)
    (runtimeStep : RuntimeState → Index → RuntimeState)
    (fieldStep : FieldState → Index → FieldState)
    (hstep : ∀ state index,
      cast (runtimeStep state index) =
        fieldStep (cast state) index)
    (indices : List Index) (initial : RuntimeState) :
    cast (indices.foldl runtimeStep initial) =
      indices.foldl fieldStep (cast initial) := by
  induction indices generalizing initial with
  | nil =>
      rfl
  | cons index indices ih =>
      simp only [List.foldl_cons]
      rw [ih, hstep]

private theorem range'_one_eq_map_finRange (length : ℕ) :
    List.range' 1 length =
      (List.finRange length).map fun index => index.val + 1 := by
  apply List.ext_getElem <;> simp [Nat.add_comm]

private theorem cast_foldNonzero
    [Fact p.Prime]
    {RuntimeState FieldState : Type*}
    (cast : RuntimeState → FieldState)
    (runtimeStep : RuntimeState → ℕ → RuntimeState)
    (fieldStep : FieldState → (ZMod p)ˣ → FieldState)
    (hstep :
      ∀ state (index : Fin (p - 1)),
        cast (runtimeStep state (index.val + 1)) =
          fieldStep (cast state) (PrimeField.unitOfIndex p index))
    (initial : RuntimeState) :
    cast (Runtime.foldNonzero p runtimeStep initial) =
      (PrimeField.units p).foldl fieldStep (cast initial) := by
  rw [Runtime.foldNonzero_eq_foldl_range,
    range'_one_eq_map_finRange, PrimeField.units]
  simp only [List.foldl_map]
  exact cast_foldl cast
    (fun state index =>
      runtimeStep state (index.val + 1))
    (fun state index =>
      fieldStep state (PrimeField.unitOfIndex p index))
    hstep (List.finRange (p - 1)) initial

theorem addAt_inRange_internal
    {regs : Registers d} (hp : 0 < p)
    (hregs : regs.InRange p)
    (index : Fin (d + 1)) (value : ℕ) :
    (addAt p regs index value).InRange p := by
  intro current
  by_cases hcurrent : current = index
  · subst current
    simp [addAt, Runtime.add_lt hp]
  · simp [addAt, hcurrent, hregs current]

theorem scaleAt_inRange_internal
    {regs : Registers d} (hp : 0 < p)
    (hregs : regs.InRange p)
    (index : Fin (d + 1)) (scalar : ℕ) :
    (scaleAt p regs index scalar).InRange p := by
  intro current
  by_cases hcurrent : current = index
  · subst current
    simp [scaleAt, Runtime.mul_lt hp]
  · simp [scaleAt, hcurrent, hregs current]

theorem accumulate_inRange_internal
    (tree : Tree d ℕ) (hp : 0 < p)
    (scalar : ℕ) (out : Fin (d + 1))
    (regs : Registers d) (hregs : regs.InRange p) :
    (accumulate p tree scalar out regs).InRange p := by
  induction tree generalizing scalar out regs with
  | leaf value =>
      exact addAt_inRange_internal hp hregs out
        (Runtime.mul p scalar value)
  | node children combine ih =>
      unfold accumulate Runtime.foldNonzero
      apply foldNonzeroLoop_preserves (Registers.InRange p)
        (fun current residue =>
          let current :=
            (List.finRange d).foldl (fun current childIndex =>
              let target := out.succAbove childIndex
              accumulate p (children childIndex)
                (Runtime.normalize p 1) target
                (scaleAt p current target residue))
              current
          let args := fun childIndex =>
            current (out.succAbove childIndex)
          let current :=
            addAt p current out
              (Runtime.mul p (Runtime.sub p 0 scalar)
                (combine args))
          (List.finRange d).foldl (fun current childIndex =>
            let target := out.succAbove childIndex
            scaleAt p
              (accumulate p (children childIndex)
                (Runtime.sub p 0 1) target current)
              target (Runtime.inverse p residue))
            current)
      · intro current residue hcurrent
        have hprepare :
            ((List.finRange d).foldl (fun current childIndex =>
              let target := out.succAbove childIndex
              accumulate p (children childIndex)
                (Runtime.normalize p 1) target
                (scaleAt p current target residue))
              current).InRange p := by
          apply foldl_preserves (Registers.InRange p)
          · intro current childIndex hcurrent
            exact ih childIndex (Runtime.normalize p 1)
              (out.succAbove childIndex)
              (scaleAt p current (out.succAbove childIndex)
                residue)
              (scaleAt_inRange_internal hp hcurrent
                (out.succAbove childIndex) residue)
          · exact hcurrent
        let prepared :=
          (List.finRange d).foldl (fun current childIndex =>
            let target := out.succAbove childIndex
            accumulate p (children childIndex)
              (Runtime.normalize p 1) target
              (scaleAt p current target residue))
            current
        let args := fun childIndex =>
          prepared (out.succAbove childIndex)
        let updated :=
          addAt p prepared out
            (Runtime.mul p (Runtime.sub p 0 scalar)
              (combine args))
        have hupdated : updated.InRange p :=
          addAt_inRange_internal hp hprepare out _
        change
          ((List.finRange d).foldl (fun current childIndex =>
            let target := out.succAbove childIndex
            scaleAt p
              (accumulate p (children childIndex)
                (Runtime.sub p 0 1) target current)
              target (Runtime.inverse p residue))
            updated).InRange p
        apply foldl_preserves (Registers.InRange p)
        · intro current childIndex hcurrent
          exact scaleAt_inRange_internal hp
            (ih childIndex (Runtime.sub p 0 1)
              (out.succAbove childIndex) current hcurrent)
            (out.succAbove childIndex)
            (Runtime.inverse p residue)
        · exact hupdated
      · exact hregs

theorem inRange_fits_internal
    {regs : Registers d} (hregs : regs.InRange p) :
    regs.Fits p := by
  intro index
  unfold Runtime.bitWidth
  exact Nat.size_le_size (Nat.le_of_lt (hregs index))

theorem accumulate_fits_internal
    (tree : Tree d ℕ) (hp : 0 < p)
    (scalar : ℕ) (out : Fin (d + 1))
    (regs : Registers d) (hregs : regs.InRange p) :
    (accumulate p tree scalar out regs).Fits p :=
  inRange_fits_internal
    (accumulate_inRange_internal tree hp scalar out regs hregs)

theorem evaluate_lt_internal
    (tree : Tree d ℕ) (hp : 0 < p) :
    evaluate p tree < p := by
  have hzero : (0 : Registers d).InRange p := by
    intro index
    exact hp
  exact accumulate_inRange_internal tree hp
    (Runtime.normalize p 1) (Fin.last d) 0 hzero
      (Fin.last d)

theorem evaluate_size_le_internal
    (tree : Tree d ℕ) (hp : 0 < p) :
    (evaluate p tree).size ≤ Runtime.bitWidth p := by
  exact Nat.size_le_size
    (Nat.le_of_lt (evaluate_lt_internal tree hp))

theorem treeCompatible_value_internal
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree) :
    ((runtimeTree.value : ℕ) : ZMod p) =
      fieldTree.value := by
  induction hcompatible with
  | leaf value =>
      rfl
  | node runtimeChildren fieldChildren
      runtimeCombine fieldCombine hchildren hcombine ih =>
      rw [Tree.value_node, Tree.value_node]
      calc
        ((runtimeCombine
            (fun index => (runtimeChildren index).value) : ℕ) :
              ZMod p) =
            fieldCombine (fun index =>
              ((runtimeChildren index).value : ZMod p)) :=
          hcombine _
        _ = fieldCombine
              (fun index => (fieldChildren index).value) := by
          congr 1
          funext index
          exact ih index

theorem castRegisters_addAt_internal
    (regs : Registers d) (index : Fin (d + 1))
    (value : ℕ) :
    castRegisters p (addAt p regs index value) =
      Complexity.TreeEval.CookMertz.addAt
        (castRegisters p regs) index (value : ZMod p) := by
  funext current
  by_cases hcurrent : current = index
  · subst current
    simp [castRegisters, addAt,
      Complexity.TreeEval.CookMertz.addAt]
  · simp [castRegisters, addAt,
      Complexity.TreeEval.CookMertz.addAt, hcurrent]

theorem castRegisters_scaleAt_internal
    (regs : Registers d) (index : Fin (d + 1))
    (scalar : ℕ) :
    castRegisters p (scaleAt p regs index scalar) =
      Complexity.TreeEval.CookMertz.scaleAt
        (castRegisters p regs) index (scalar : ZMod p) := by
  funext current
  by_cases hcurrent : current = index
  · subst current
    simp [castRegisters, scaleAt,
      Complexity.TreeEval.CookMertz.scaleAt]
  · simp [castRegisters, scaleAt,
      Complexity.TreeEval.CookMertz.scaleAt, hcurrent]

theorem accumulate_cast_internal
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree)
    (scalar : ℕ) (out : Fin (d + 1))
    (regs : Registers d) :
    castRegisters p
        (accumulate p runtimeTree scalar out regs) =
      Complexity.TreeEval.CookMertz.accumulate
        (PrimeField.units p) fieldTree
        (scalar : ZMod p) out (castRegisters p regs) := by
  induction hcompatible generalizing scalar out regs with
  | leaf value =>
      simp only [accumulate,
        Complexity.TreeEval.CookMertz.accumulate]
      rw [castRegisters_addAt_internal]
      congr 2
      exact Runtime.coe_mul p scalar value
  | node runtimeChildren fieldChildren
      runtimeCombine fieldCombine hchildren hcombine ih =>
      simp only [accumulate,
        Complexity.TreeEval.CookMertz.accumulate]
      apply cast_foldNonzero (p := p) (castRegisters p)
      intro current index
      let residue := index.val + 1
      let unit := PrimeField.unitOfIndex p index
      let runtimePrepared :=
        (List.finRange d).foldl (fun current childIndex =>
          let target := out.succAbove childIndex
          accumulate p (runtimeChildren childIndex)
            (Runtime.normalize p 1) target
            (scaleAt p current target residue))
          current
      let fieldPrepared :=
        (List.finRange d).foldl (fun current childIndex =>
          let target := out.succAbove childIndex
          Complexity.TreeEval.CookMertz.accumulate
            (PrimeField.units p) (fieldChildren childIndex)
            1 target
            (Complexity.TreeEval.CookMertz.scaleAt
              current target (unit : ZMod p)))
          (castRegisters p current)
      have hprepare :
          castRegisters p runtimePrepared = fieldPrepared := by
        apply cast_foldl (castRegisters p)
        intro current childIndex
        rw [ih childIndex]
        rw [castRegisters_scaleAt_internal]
        simp [residue, unit]
      let runtimeArgs := fun childIndex =>
        runtimePrepared (out.succAbove childIndex)
      let fieldArgs := fun childIndex =>
        fieldPrepared (out.succAbove childIndex)
      have hargs :
          (fun childIndex =>
            (runtimeArgs childIndex : ZMod p)) =
              fieldArgs := by
        funext childIndex
        exact congrFun hprepare (out.succAbove childIndex)
      have hcombineValue :
          ((runtimeCombine runtimeArgs : ℕ) : ZMod p) =
            fieldCombine fieldArgs := by
        rw [hcombine]
        exact congrArg fieldCombine hargs
      let runtimeUpdated :=
        addAt p runtimePrepared out
          (Runtime.mul p (Runtime.sub p 0 scalar)
            (runtimeCombine runtimeArgs))
      let fieldUpdated :=
        Complexity.TreeEval.CookMertz.addAt
          fieldPrepared out
          ((-(scalar : ZMod p)) • fieldCombine fieldArgs)
      have hupdated :
          castRegisters p runtimeUpdated = fieldUpdated := by
        rw [castRegisters_addAt_internal]
        rw [hprepare]
        congr 2
        rw [Runtime.coe_mul, Runtime.coe_sub,
          hcombineValue]
        simp
      change
        castRegisters p
            ((List.finRange d).foldl
              (fun current childIndex =>
                let target := out.succAbove childIndex
                scaleAt p
                  (accumulate p
                    (runtimeChildren childIndex)
                    (Runtime.sub p 0 1) target current)
                  target (Runtime.inverse p residue))
              runtimeUpdated) =
          (List.finRange d).foldl
            (fun current childIndex =>
              let target := out.succAbove childIndex
              Complexity.TreeEval.CookMertz.scaleAt
                (Complexity.TreeEval.CookMertz.accumulate
                  (PrimeField.units p)
                  (fieldChildren childIndex)
                  (-1) target current)
                target (↑unit⁻¹ : ZMod p))
            fieldUpdated
      calc
        castRegisters p
            ((List.finRange d).foldl
              (fun current childIndex =>
                let target := out.succAbove childIndex
                scaleAt p
                  (accumulate p
                    (runtimeChildren childIndex)
                    (Runtime.sub p 0 1) target current)
                  target (Runtime.inverse p residue))
              runtimeUpdated) =
            (List.finRange d).foldl
              (fun current childIndex =>
                let target := out.succAbove childIndex
                Complexity.TreeEval.CookMertz.scaleAt
                  (Complexity.TreeEval.CookMertz.accumulate
                    (PrimeField.units p)
                    (fieldChildren childIndex)
                    (-1) target current)
                  target (↑unit⁻¹ : ZMod p))
              (castRegisters p runtimeUpdated) := by
          apply cast_foldl (castRegisters p)
          intro current childIndex
          rw [castRegisters_scaleAt_internal]
          rw [ih childIndex]
          simp [residue, unit]
        _ = (List.finRange d).foldl
              (fun current childIndex =>
                let target := out.succAbove childIndex
                Complexity.TreeEval.CookMertz.scaleAt
                  (Complexity.TreeEval.CookMertz.accumulate
                    (PrimeField.units p)
                    (fieldChildren childIndex)
                    (-1) target current)
                  target (↑unit⁻¹ : ZMod p))
              fieldUpdated := by
          rw [hupdated]

theorem evaluate_cast_internal
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree) :
    ((evaluate p runtimeTree : ℕ) : ZMod p) =
      Complexity.TreeEval.CookMertz.evaluate
        (PrimeField.units p) fieldTree := by
  unfold evaluate
  have haccumulate :=
    accumulate_cast_internal hcompatible
      (Runtime.normalize p 1) (Fin.last d) 0
  have hzero :
      castRegisters p (0 : Registers d) = 0 := by
    funext index
    simp [castRegisters]
  rw [hzero] at haccumulate
  have hout := congrFun haccumulate (Fin.last d)
  simpa [castRegisters,
    Complexity.TreeEval.CookMertz.evaluate] using hout

theorem evaluate_cast_eq_value_internal
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree)
    (hline :
      Complexity.TreeEval.CookMertz.LineCompatible
        (PrimeField.units p) fieldTree) :
    ((evaluate p runtimeTree : ℕ) : ZMod p) =
      (runtimeTree.value : ZMod p) := by
  calc
    ((evaluate p runtimeTree : ℕ) : ZMod p) =
        Complexity.TreeEval.CookMertz.evaluate
          (PrimeField.units p) fieldTree :=
      evaluate_cast_internal hcompatible
    _ = fieldTree.value :=
      Complexity.TreeEval.CookMertz.evaluate_eq_value
        (PrimeField.units p) fieldTree hline
    _ = (runtimeTree.value : ZMod p) :=
      (treeCompatible_value_internal hcompatible).symm

theorem evaluate_eq_normalize_value_internal
    [Fact p.Prime]
    {runtimeTree : Tree d ℕ}
    {fieldTree : Tree d (ZMod p)}
    (hcompatible :
      TreeCompatible p runtimeTree fieldTree)
    (hline :
      Complexity.TreeEval.CookMertz.LineCompatible
        (PrimeField.units p) fieldTree) :
    evaluate p runtimeTree =
      Runtime.normalize p runtimeTree.value := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply CharP.natCast_injOn_Iio (ZMod p) p
  · exact evaluate_lt_internal runtimeTree hp
  · exact Runtime.normalize_lt hp
  · rw [Runtime.coe_normalize]
    exact evaluate_cast_eq_value_internal hcompatible hline

end Internal

end CookMertz

end Runtime

end PrimeField

end CookMertz

end TreeEval

end Complexity
