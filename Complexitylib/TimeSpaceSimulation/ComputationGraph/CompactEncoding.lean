/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding.Internal

/-!
# Correct fixed-width Boolean encoding of compact values

The one-hot representation has exactly `Fintype.card Q + 5 * blockLength`
bits, and total decoding recovers every well-formed encoded compact value.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactEncoding

/-- The compact-value encoding uses exactly one state bit and five
block-length-scaled one-hot families. -/
theorem width_eq (blockLength : ℕ) (Q : Type*) [Fintype Q] :
    width blockLength Q =
      Fintype.card Q + 5 * blockLength :=
  Internal.width_eq_internal blockLength Q

/-- Selecting from a one-hot finite family recovers its selected value. -/
theorem firstTrue_oneHot [Fintype α] [DecidableEq α]
    (default value : α) :
    firstTrue default (oneHot value) = value :=
  Internal.firstTrue_oneHot_internal default value

/-- Finite reindexing preserves the semantic coordinate bits. -/
theorem bitsAt_encode [Fintype Q] [DecidableEq Q]
    (value : CompactContent.Content blockLength Q)
    (coordinate : Coordinate blockLength Q) :
    bitsAt (encode value) coordinate =
      coordinateBits value coordinate :=
  Internal.bitsAt_encode_internal value coordinate

/-- Total decoding is a left inverse of compact one-hot encoding. -/
theorem decode_encode [Fintype Q] [DecidableEq Q]
    (defaultState : Q) (hpositive : 0 < blockLength)
    (value : CompactContent.Content blockLength Q) :
    decode defaultState hpositive (encode value) = value :=
  Internal.decode_encode_internal
    defaultState hpositive value

end CompactEncoding

end ComputationGraph

end TimeSpaceSimulation

end Complexity
