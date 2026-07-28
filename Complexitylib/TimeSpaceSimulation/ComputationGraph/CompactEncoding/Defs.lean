/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactContent.Defs
import Mathlib.Data.Fintype.Sum

/-!
# Fixed-width Boolean encoding of compact node values

A compact value is encoded by three one-hot families:

* one coordinate for every machine state;
* one coordinate for every possible head remainder;
* one coordinate for every tape-cell offset and alphabet symbol.

Thus the width is exactly `Fintype.card Q + 5 * blockLength`. One-hot encoding
is deliberately simple: it avoids logarithmic overhead in the block-sized
part of a node value. Decoding arbitrary malformed vectors chooses the first
true coordinate, with explicit defaults when none is true.

Choosing an enumeration of an arbitrary finite state type is noncomputable at
the certificate level. This is harmless for the eventual existence theorem:
the simulated machine is fixed, so one finite enumeration can be hardwired
into its simulator.

## Main definitions

- `Coordinate` -- state, head, or cell-symbol bit coordinates
- `width` -- exact number of coordinates
- `encode` / `decode` -- Boolean representation and total decoding
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactEncoding

/-- Coordinates of the one-hot compact-value encoding. -/
abbrev Coordinate (blockLength : ℕ) (Q : Type*) :=
  Q ⊕ (Fin blockLength ⊕ (Fin blockLength × Γ))

/-- Number of Boolean coordinates in the compact-value encoding. -/
def width (blockLength : ℕ) (Q : Type*) [Fintype Q] : ℕ :=
  Fintype.card (Coordinate blockLength Q)

/-- One-hot Boolean family selecting one value. -/
def oneHot [DecidableEq α] (value : α) : α → Bool :=
  fun candidate => decide (candidate = value)

/-- Select the first true coordinate in a finite type, or return a supplied
default when the vector contains no true coordinate. -/
noncomputable def firstTrue [Fintype α]
    (default : α) (bits : α → Bool) : α :=
  (Fintype.elems.toList.find? bits).getD default

/-- Coordinate-indexed one-hot representation before reindexing by `Fin`. -/
def coordinateBits [DecidableEq Q]
    (value : CompactContent.Content blockLength Q) :
    Coordinate blockLength Q → Bool
  | .inl state => decide (state = value.state)
  | .inr (.inl remainder) =>
      decide (remainder = value.headRemainder)
  | .inr (.inr (offset, symbol)) =>
      decide (symbol = value.cells offset)

/-- Reindex the one-hot representation into a fixed-width Boolean vector. -/
noncomputable def encode [Fintype Q] [DecidableEq Q]
    (value : CompactContent.Content blockLength Q) :
    Fin (width blockLength Q) → Bool :=
  fun index =>
    coordinateBits value
      ((Fintype.equivFin (Coordinate blockLength Q)).symm index)

/-- Interpret a fixed-width vector at a semantic coordinate. -/
noncomputable def bitsAt [Fintype Q]
    (bits : Fin (width blockLength Q) → Bool) :
    Coordinate blockLength Q → Bool :=
  fun coordinate =>
    bits (Fintype.equivFin (Coordinate blockLength Q) coordinate)

/-- Total decoder for compact-value Boolean vectors. Malformed one-hot
families use `defaultState`, remainder zero, or blank symbols. -/
noncomputable def decode [Fintype Q]
    (defaultState : Q) (hpositive : 0 < blockLength)
    (bits : Fin (width blockLength Q) → Bool) :
    CompactContent.Content blockLength Q where
  state :=
    firstTrue defaultState fun state =>
      bitsAt bits (.inl state)
  headRemainder :=
    firstTrue ⟨0, hpositive⟩ fun remainder =>
      bitsAt bits (.inr (.inl remainder))
  cells offset :=
    firstTrue Γ.blank fun symbol =>
      bitsAt bits (.inr (.inr (offset, symbol)))

end CompactEncoding

end ComputationGraph

end TimeSpaceSimulation

end Complexity
