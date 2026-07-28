/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding.Defs

/-!
# Correctness of compact Boolean encoding

This file proves the exact width formula and that total decoding is a left
inverse of one-hot encoding.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactEncoding

namespace Internal

theorem width_eq_internal (blockLength : ℕ) (Q : Type*)
    [Fintype Q] :
    width blockLength Q =
      Fintype.card Q + 5 * blockLength := by
  have hcard : Fintype.card Γ = 4 := by decide
  simp [width, Coordinate, hcard]
  omega

theorem firstTrue_oneHot_internal [Fintype α] [DecidableEq α]
    (default value : α) :
    firstTrue default (oneHot value) = value := by
  unfold firstTrue
  generalize hfind :
    Fintype.elems.toList.find? (oneHot value) = found
  cases found with
  | none =>
      have hnone := List.find?_eq_none.mp hfind
      have hmem : value ∈ Fintype.elems.toList := by
        rw [Finset.mem_toList]
        exact Fintype.complete value
      have himpossible := hnone value hmem
      simp [oneHot] at himpossible
  | some selected =>
      have hselected := List.find?_some hfind
      simp [oneHot] at hselected
      simp [hselected]

theorem bitsAt_encode_internal [Fintype Q] [DecidableEq Q]
    (value : CompactContent.Content blockLength Q)
    (coordinate : Coordinate blockLength Q) :
    bitsAt (encode value) coordinate =
      coordinateBits value coordinate := by
  simp [bitsAt, encode]

theorem decode_encode_internal [Fintype Q] [DecidableEq Q]
    (defaultState : Q) (hpositive : 0 < blockLength)
    (value : CompactContent.Content blockLength Q) :
    decode defaultState hpositive (encode value) = value := by
  apply CompactContent.Content.ext
  · simp only [decode, bitsAt_encode_internal, coordinateBits]
    exact firstTrue_oneHot_internal defaultState value.state
  · apply Fin.ext
    simp only [decode, bitsAt_encode_internal, coordinateBits]
    exact congrArg Fin.val
      (firstTrue_oneHot_internal
        ⟨0, hpositive⟩ value.headRemainder)
  · funext offset
    simp only [decode, bitsAt_encode_internal, coordinateBits]
    exact firstTrue_oneHot_internal Γ.blank (value.cells offset)

end Internal

end CompactEncoding

end ComputationGraph

end TimeSpaceSimulation

end Complexity
