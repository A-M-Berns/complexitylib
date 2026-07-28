/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentCodeSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentCodeSemantics.Internal

/-!
# Boolean-coordinate semantics of streamed grouped assignments

These theorems identify the exact low-order binary digit read for one child
payload bit. They also expose the big-endian coordinate supplied to a grouped
node function, such as `NeighborhoodExecutableEvaluation.booleanCombine`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentCodeSemantics

open TreeEval CookMertz

/-- The semantic payload chunk is selected by quotienting by `chunkBits`. -/
theorem payloadChunkIndex_val
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    (payloadChunkIndex payloadWidth fanIn position).val =
      position.val /
        PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn :=
  Internal.payloadChunkIndex_val_internal payloadWidth fanIn position

/-- The semantic within-chunk offset is selected modulo `chunkBits`. -/
theorem payloadChunkOffset_val
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    (payloadChunkOffset payloadWidth fanIn position).val =
      position.val %
        PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn :=
  Internal.payloadChunkOffset_val_internal payloadWidth fanIn position

/-- Unpacking the grouped assignment selects precisely the quotient chunk
and remainder offset. -/
theorem assignmentBits_apply
    (payloadWidth fanIn code : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    assignmentBits payloadWidth fanIn code child position =
      assignmentChunks payloadWidth fanIn code
        (groupedCoordinate payloadWidth fanIn child position)
        (payloadChunkOffset payloadWidth fanIn position) :=
  Internal.assignmentBits_apply_internal
    payloadWidth fanIn code child position

/-- The big-endian assignment encoder stores each child's semantic payload
after one full padded chunk block per preceding child. -/
theorem encodedBitPosition_val
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    (encodedBitPosition payloadWidth fanIn child position).val =
      PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn *
          child.val +
        position.val :=
  Internal.encodedBitPosition_val_internal
    payloadWidth fanIn child position

/-- The low-order chunk index reverses the child-major, chunk-fast semantic
coordinate. -/
theorem lowOrderChunkIndex_eq
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    lowOrderChunkIndex payloadWidth fanIn child position =
      fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn -
        1 -
        ((payloadChunkIndex payloadWidth fanIn position).val +
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn *
            child.val) :=
  Internal.lowOrderChunkIndex_eq_internal
    payloadWidth fanIn child position

/-- The low-order binary index within a chunk reverses its semantic bit
offset. -/
theorem lowOrderBitInChunkIndex_eq
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    lowOrderBitInChunkIndex payloadWidth fanIn position =
      PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn -
        1 -
        (position.val %
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn) :=
  Internal.lowOrderBitInChunkIndex_eq_internal
    payloadWidth fanIn position

/-- Composing the reversed chunk and within-chunk indices is exactly the
reversal of the complete big-endian assignment coordinate. -/
theorem lowOrderBitIndex_eq_reversed
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    lowOrderBitIndex payloadWidth fanIn child position =
      (fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) *
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn -
        1 -
        (encodedBitPosition payloadWidth fanIn child position).val :=
  Internal.lowOrderBitIndex_eq_reversed_internal
    payloadWidth fanIn child position

/-- Closed formula for the exact low-order assignment-bit index. -/
theorem lowOrderBitIndex_eq
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    lowOrderBitIndex payloadWidth fanIn child position =
      (fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) *
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn -
        1 -
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn *
            PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn *
            child.val +
          position.val) :=
  Internal.lowOrderBitIndex_eq_internal
    payloadWidth fanIn child position

/-- One semantic Boolean child bit is exactly the selected low-order binary
digit of the streamed assignment code. -/
theorem assignmentBit_eq_decide_radixDigit
    (payloadWidth fanIn code : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    assignmentBits payloadWidth fanIn code child position =
      decide
        (CombineTerm.radixDigit 2 code
          (lowOrderBitIndex payloadWidth fanIn child position) = 1) :=
  Internal.assignmentBit_eq_decide_radixDigit_internal
    payloadWidth fanIn code child position

/-- Numeric form of the Boolean assignment-bit bridge, matching the output
contract of the uniform assignment-bit reader. -/
theorem assignmentBit_toNat_eq_radixDigit
    (payloadWidth fanIn code : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    (assignmentBits payloadWidth fanIn code child position).toNat =
      CombineTerm.radixDigit 2 code
        (lowOrderBitIndex payloadWidth fanIn child position) :=
  Internal.assignmentBit_toNat_eq_radixDigit_internal
    payloadWidth fanIn code child position

/-- The assignment passed to the packed node function is exactly
`assignmentBits`; specializing `combine` to `booleanCombine` therefore uses
the bits identified above. -/
theorem packedAssignmentValue_eq
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (outputChunk :
      Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (code : ℕ) :
    CombineTerm.packedAssignmentValue
        payloadWidth fanIn combine outputChunk code =
      PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Layout.pack
          (chunkBits :=
            PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          (combine (assignmentBits payloadWidth fanIn code))
          outputChunk) :=
  Internal.packedAssignmentValue_eq_internal
    payloadWidth fanIn combine outputChunk code

end AssignmentCodeSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
