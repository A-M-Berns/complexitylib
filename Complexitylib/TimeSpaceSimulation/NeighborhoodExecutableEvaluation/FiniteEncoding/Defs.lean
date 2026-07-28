/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.Defs

/-!
# Fixed finite coordinate orders for executable neighborhood evaluation

A simulator for a fixed source machine hardwires one enumeration of its
finite state type.  From that single choice this module constructs, for every
runtime block length, the compact coordinate order used by
`FiniteEncoding`.  The block and alphabet parts are explicit arithmetic
equivalences, so no input-dependent `Fintype.equivFin` is evaluated.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodExecutableEvaluation

namespace FiniteEncoding

/-- One finite-state ordering hardwired into the simulator for a fixed source
machine. -/
structure StateOrder (tm : TM workTapeCount) where
  /-- Bijection between source states and their fixed numeric codes. -/
  state : tm.Q ≃ Fin (Fintype.card tm.Q)

/-- Explicit order `0, 1, blank, start` on the fixed tape alphabet. -/
def gammaEquiv : Γ ≃ Fin 4 where
  toFun
    | .zero => 0
    | .one => 1
    | .blank => 2
    | .start => 3
  invFun index :=
    if index = 0 then
      .zero
    else if index = 1 then
      .one
    else if index = 2 then
      .blank
    else
      .start
  left_inv symbol := by
    cases symbol <;> decide
  right_inv index := by
    fin_cases index <;> decide

/-- Explicit compact-coordinate order derived from one fixed state order. -/
def coordinateEquiv (order : StateOrder tm) (blockLength : ℕ) :
    ComputationGraph.CompactEncoding.Coordinate blockLength tm.Q ≃
      Fin (payloadWidth tm blockLength) := by
  let cells :
      Fin blockLength × Γ ≃ Fin (blockLength * 4) :=
    (Equiv.prodCongr (Equiv.refl (Fin blockLength))
      gammaEquiv).trans finProdFinEquiv
  let tapeCoordinates :
      Fin blockLength ⊕ (Fin blockLength × Γ) ≃
        Fin (blockLength + blockLength * 4) :=
    (Equiv.sumCongr (Equiv.refl (Fin blockLength))
      cells).trans finSumFinEquiv
  let allCoordinates :
      tm.Q ⊕ (Fin blockLength ⊕ (Fin blockLength × Γ)) ≃
        Fin (Fintype.card tm.Q +
          (blockLength + blockLength * 4)) :=
    (Equiv.sumCongr order.state tapeCoordinates).trans
      finSumFinEquiv
  exact allCoordinates.trans
    (finCongr (by
      change
        Fintype.card tm.Q +
            (blockLength + blockLength * 4) =
          ComputationGraph.CompactEncoding.width
            blockLength tm.Q
      rw [ComputationGraph.CompactEncoding.width_eq]
      omega))

/-- Build every block-dependent finite encoding from one fixed state order. -/
def ofStateOrder (order : StateOrder tm) (blockLength : ℕ) :
    NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength where
  coordinate := coordinateEquiv order blockLength
  state := order.state

end FiniteEncoding

end NeighborhoodExecutableEvaluation

end TimeSpaceSimulation

end Complexity
