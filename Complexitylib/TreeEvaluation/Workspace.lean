/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TreeEvaluation.OrderedDAG.CookMertz
import Complexitylib.TreeEvaluation.CookMertz.PrimeField
import Complexitylib.TreeEvaluation.Workspace.Defs
import Complexitylib.TreeEvaluation.Workspace.Internal

/-!
# Workspace bounds for executable Cook--Mertz traversal

This module exposes the representation-independent part of Cook--Mertz
workspace accounting. The profiled evaluator computes exactly the same result
as the existing executable evaluator, its catalytic bank has exactly
`(d + 1) * b` field cells on `b`-coordinate values, and the direct implicit-DAG
traversal has at most `depth + 1` simultaneously live recursive calls.

`abstractCellUsage` then gives a compositional exact bound after a later
machine implementation supplies the encoded cost `frameCells` of one live
frame. It does not count a resident explicit tree and does not claim a
Turing-machine all-prefix space theorem.

## Main theorems

* `profileAccumulate_result` -- profiling preserves every final register
* `profileEvaluate_result` -- profiled tree evaluation is extensionally exact
* `profileDAGEvaluate_result` -- profiled direct-DAG evaluation is exact
* `profileDAGEvaluate_peakFrames_le` -- peak frames are at most `depth + 1`
* `registerCell_card` -- exact catalytic field-cell count
* `profileDAGEvaluate_abstractCellUsage_le` -- compositional cell bound
* `primeField_registerBitBudget_le` -- current prime-field register-bit budget
-/

namespace Complexity

namespace TreeEval

namespace CookMertz

namespace Workspace

variable {d size : ℕ} {F V : Type*}

/-- Profiling preserves the complete final register bank of the executable
tree accumulator, for arbitrary initial registers and selected output. -/
theorem profileAccumulate_result
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) (scale : F)
    (out : Fin (d + 1)) (regs : Registers d V) :
    (profileAccumulate units tree scale out regs).result =
      accumulate units tree scale out regs :=
  Internal.profileAccumulate_result_internal
    units tree scale out regs

/-- The profiled tree accumulator has at most `height + 1` live recursive
frames for every initial catalytic frame. -/
theorem profileAccumulate_peakFrames_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) (scale : F)
    (out : Fin (d + 1)) (regs : Registers d V) :
    (profileAccumulate units tree scale out regs).peakFrames ≤
      tree.height + 1 :=
  Internal.profileAccumulate_peakFrames_le_internal
    units tree scale out regs

/-- Profiling leaves the executable tree evaluator's result unchanged. -/
theorem profileEvaluate_result
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) :
    (profileEvaluate units tree).result = evaluate units tree :=
  Internal.profileEvaluate_result_internal units tree

/-- The explicit-tree traversal has at most `height + 1` live recursive
frames, including the root call. -/
theorem profileEvaluate_peakFrames_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) :
    (profileEvaluate units tree).peakFrames ≤ tree.height + 1 :=
  Internal.profileEvaluate_peakFrames_le_internal units tree

/-- Direct ordered-DAG profiling agrees exactly with profiling the semantic
unrolling. This is a correctness bridge only; the direct traversal does not
construct or retain that tree. -/
theorem profileDAGAccumulate_eq_profileUnroll
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (scale : F) (out : Fin (d + 1)) (regs : Registers d V) :
    profileDAGAccumulate units dag index scale out regs =
      profileAccumulate units (dag.unroll index) scale out regs :=
  Internal.profileDAGAccumulate_eq_profileUnroll_internal
    units dag index scale out regs

/-- Profiling preserves the complete final register bank of the executable
direct ordered-DAG accumulator. -/
theorem profileDAGAccumulate_result
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (scale : F) (out : Fin (d + 1)) (regs : Registers d V) :
    (profileDAGAccumulate units dag index scale out regs).result =
      dag.cookMertzAccumulate units index scale out regs := by
  calc
    (profileDAGAccumulate units dag index scale out regs).result =
        (profileAccumulate units (dag.unroll index) scale out regs).result := by
      rw [profileDAGAccumulate_eq_profileUnroll]
    _ = accumulate units (dag.unroll index) scale out regs :=
      profileAccumulate_result units (dag.unroll index) scale out regs
    _ = dag.cookMertzAccumulate units index scale out regs := by
      symm
      exact
        OrderedDAG.cookMertzAccumulate_eq_accumulate_unroll
          units dag index scale out regs

/-- The direct profiled ordered-DAG accumulator has at most `depth + 1` live
recursive frames for every initial catalytic frame. -/
theorem profileDAGAccumulate_peakFrames_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (scale : F) (out : Fin (d + 1)) (regs : Registers d V) :
    (profileDAGAccumulate units dag index scale out regs).peakFrames ≤
      dag.depth index + 1 := by
  rw [profileDAGAccumulate_eq_profileUnroll]
  simpa [OrderedDAG.height_unroll] using
    profileAccumulate_peakFrames_le
      units (dag.unroll index) scale out regs

/-- The direct profiled ordered-DAG traversal computes the existing direct
evaluator's result. -/
theorem profileDAGEvaluate_result
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size) :
    (profileDAGEvaluate units dag index).result =
      dag.cookMertzEvaluate units index := by
  calc
    (profileDAGEvaluate units dag index).result =
        (profileEvaluate units (dag.unroll index)).result := by
      rw [Internal.profileDAGEvaluate_eq_profileUnroll_internal]
    _ = evaluate units (dag.unroll index) :=
      profileEvaluate_result units (dag.unroll index)
    _ = dag.cookMertzEvaluate units index := by
      symm
      exact
        OrderedDAG.Internal.cookMertzEvaluate_eq_evaluate_unroll_internal
          units dag index

/-- The direct implicit-DAG traversal has at most `depth + 1` simultaneously
live recursive calls. -/
theorem profileDAGEvaluate_peakFrames_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size) :
    (profileDAGEvaluate units dag index).peakFrames ≤
      dag.depth index + 1 := by
  rw [Internal.profileDAGEvaluate_eq_profileUnroll_internal]
  simpa [OrderedDAG.height_unroll] using
    profileEvaluate_peakFrames_le units (dag.unroll index)

/-- Exact cardinality of the flattened catalytic register-cell index. -/
theorem registerCell_card (d b : ℕ) :
    Fintype.card (RegisterCell d b) = registerFieldCells d b :=
  Internal.registerCell_card_internal d b

/-- With the current Bertrand prime selected for degree `d * b`, the naive
`b`-field-coordinate representation's catalytic bit budget is at most
`(d + 1) * b * (log₂(2 * (d * b + 1)) + 1)`.

This is the checked bound for the current Boolean multilinear layer. Obtaining
the paper's sharper `O(d * b)` catalytic bits requires the still-missing
grouped low-degree representation. -/
theorem primeField_registerBitBudget_le
    (d b : ℕ) (choice : PrimeField.Choice (d * b)) :
    registerBitBudget d b choice.modulus.size ≤
      registerFieldCells d b *
        (Nat.log 2 (2 * (d * b + 1)) + 1) := by
  exact Nat.mul_le_mul_left (registerFieldCells d b)
    (PrimeField.Choice.modulus_size_le choice)

/-- After charging `frameCells` cells per encoded live frame, the profiled
tree evaluator fits the corresponding height-indexed abstract bound. -/
theorem profileEvaluate_abstractCellUsage_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (tree : Tree d V) (b frameCells : ℕ) :
    abstractCellUsage d b frameCells (profileEvaluate units tree) ≤
      abstractCellBound d b frameCells tree.height := by
  simp only [abstractCellUsage, abstractCellBound]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right frameCells
      (profileEvaluate_peakFrames_le units tree))
    (registerFieldCells d b)

/-- After charging `frameCells` cells per encoded live frame, the direct
implicit-DAG evaluator fits the corresponding depth-indexed abstract bound. -/
theorem profileDAGEvaluate_abstractCellUsage_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (b frameCells : ℕ) :
    abstractCellUsage d b frameCells (profileDAGEvaluate units dag index) ≤
      abstractCellBound d b frameCells (dag.depth index) := by
  simp only [abstractCellUsage, abstractCellBound]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right frameCells
      (profileDAGEvaluate_peakFrames_le units dag index))
    (registerFieldCells d b)

/-- After charging `fieldBits` bits per value coordinate and `frameBits` bits
per live call frame, the direct implicit-DAG evaluator fits the corresponding
depth-indexed abstract bit bound. -/
theorem profileDAGEvaluate_abstractBitUsage_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (dag : OrderedDAG size d V) (index : Fin size)
    (b fieldBits frameBits : ℕ) :
    abstractBitUsage d b fieldBits frameBits
        (profileDAGEvaluate units dag index) ≤
      abstractBitBound d b fieldBits frameBits (dag.depth index) := by
  simp only [abstractBitUsage, abstractBitBound]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right frameBits
      (profileDAGEvaluate_peakFrames_le units dag index))
    (registerBitBudget d b fieldBits)

end Workspace

end CookMertz

end TreeEval

end Complexity
