/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CompactValueCodeSemantics.Defs

/-!
# Arithmetic coordinates of compact neighborhood values -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace CompactValueCodeSemantics
namespace Internal

open NeighborhoodExecutableEvaluation

private theorem encodeBits_forward
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q)
    (coordinate :
      ComputationGraph.CompactEncoding.Coordinate blockLength tm.Q) :
    encodeBits (FiniteEncoding.ofStateOrder order blockLength) value
        (FiniteEncoding.coordinateEquiv order blockLength coordinate) =
      coordinateBit tm order blockLength
        (FiniteEncoding.coordinateEquiv order blockLength coordinate).val
        value := by
  cases coordinate with
  | inl state =>
      have hstate := (order.state state).isLt
      simp only [encodeBits, FiniteEncoding.ofStateOrder,
        Equiv.symm_apply_apply,
        ComputationGraph.CompactEncoding.coordinateBits]
      have hcoordinate :
          ((FiniteEncoding.coordinateEquiv order blockLength)
            (.inl state)).val =
            (order.state state).val := by
        simp [FiniteEncoding.coordinateEquiv, finSumFinEquiv,
          finProdFinEquiv]
      rw [hcoordinate]
      simp only [coordinateBit, stateCode]
      rw [if_pos hstate]
      apply decide_eq_decide.mpr
      constructor
      · intro heq
        simp [heq]
      · intro heq
        apply order.state.injective
        apply Fin.ext
        exact heq
  | inr rest =>
      cases rest with
      | inl remainder =>
          have hremainder := remainder.isLt
          simp only [encodeBits, FiniteEncoding.ofStateOrder,
            Equiv.symm_apply_apply,
            ComputationGraph.CompactEncoding.coordinateBits]
          have hcoordinate :
              ((FiniteEncoding.coordinateEquiv order blockLength)
                (.inr (.inl remainder))).val =
                Fintype.card tm.Q + remainder.val := by
            simp [FiniteEncoding.coordinateEquiv, finSumFinEquiv,
              finProdFinEquiv]
          rw [hcoordinate]
          simp only [coordinateBit]
          rw [if_neg (by omega), if_pos (by omega)]
          apply decide_eq_decide.mpr
          constructor
          · intro heq
            have hval := congrArg Fin.val heq
            omega
          · intro heq
            apply Fin.ext
            omega
      | inr cell =>
          rcases cell with ⟨offset, symbol⟩
          have hoffset := offset.isLt
          have hsymbol := (FiniteEncoding.gammaEquiv symbol).isLt
          simp only [encodeBits, FiniteEncoding.ofStateOrder,
            Equiv.symm_apply_apply,
            ComputationGraph.CompactEncoding.coordinateBits]
          have hcoordinate :
              ((FiniteEncoding.coordinateEquiv order blockLength)
                (.inr (.inr (offset, symbol)))).val =
                Fintype.card tm.Q + blockLength +
                  (offset.val * 4 +
                    (FiniteEncoding.gammaEquiv symbol).val) := by
            simp [FiniteEncoding.coordinateEquiv, finSumFinEquiv,
              finProdFinEquiv]
            omega
          rw [hcoordinate]
          simp only [coordinateBit]
          rw [if_neg (by omega), if_neg (by omega)]
          rw [dif_pos (by omega)]
          have hmod :
              (Fintype.card tm.Q + blockLength +
                    (offset.val * 4 +
                      (FiniteEncoding.gammaEquiv symbol).val) -
                  (Fintype.card tm.Q + blockLength)) % 4 =
                (FiniteEncoding.gammaEquiv symbol).val := by
            omega
          have hdiv :
              (Fintype.card tm.Q + blockLength +
                    (offset.val * 4 +
                      (FiniteEncoding.gammaEquiv symbol).val) -
                  (Fintype.card tm.Q + blockLength)) / 4 =
                offset.val := by
            omega
          rw [hmod]
          have hoffsetEq :
              (⟨(Fintype.card tm.Q + blockLength +
                    (offset.val * 4 +
                      (FiniteEncoding.gammaEquiv symbol).val) -
                  (Fintype.card tm.Q + blockLength)) /
                4,
                by omega⟩ : Fin blockLength) =
                offset := by
            apply Fin.ext
            exact hdiv
          rw [hoffsetEq]
          simp only [gammaCode]
          apply decide_eq_decide.mpr
          constructor
          · intro heq
            rw [heq]
          · intro heq
            apply FiniteEncoding.gammaEquiv.injective
            apply Fin.ext
            exact heq

theorem encodeBits_eq_coordinateBit_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q)
    (index : Fin (payloadWidth tm blockLength)) :
    encodeBits (FiniteEncoding.ofStateOrder order blockLength)
        value index =
      coordinateBit tm order blockLength index.val value := by
  let coordinate :=
    (FiniteEncoding.coordinateEquiv order blockLength).symm index
  have h :=
    encodeBits_forward tm order blockLength value coordinate
  simpa [coordinate] using h

end Internal
end CompactValueCodeSemantics
end Runtime
end TimeSpaceSimulation
end Complexity
