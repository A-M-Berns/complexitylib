/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Defs

/-!
# Boolean coordinates in streamed grouped assignments

The grouped combine loop represents one complete assignment by a fixed-width
natural-number code. The semantic Boolean-node input instead uses one Boolean
payload per child. This module gives the pure bridge between those views.

The fixed-width code is big-endian, whereas runtime digit extraction counts
from the low-order end. Consequently both the child/chunk coordinate and the
bit offset inside that chunk are reversed.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentCodeSemantics

open TreeEval CookMertz

/-- Row-major chunk containing one semantic payload bit. -/
def payloadChunkIndex
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) :=
  ⟨position.val /
      PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn, by
    apply Nat.div_lt_of_lt_mul
    calc
      position.val < payloadWidth := position.isLt
      _ ≤
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn *
            PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn :=
        (PrimeGrouped.Logarithmic.layout payloadWidth fanIn).covers
      _ =
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn *
            PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn :=
        Nat.mul_comm _ _⟩

/-- Row-major offset of one semantic payload bit inside its chunk. -/
def payloadChunkOffset
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) :
    Fin (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn) :=
  ⟨position.val %
      PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn,
    Nat.mod_lt _
      (PrimeGrouped.Logarithmic.layout payloadWidth fanIn).chunkBits_pos⟩

/-- Grouped assignment decoded from one streamed fixed-width code. -/
def assignmentChunks
    (payloadWidth fanIn code : ℕ) :
    Fin fanIn ×
          Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
        GroupedExtension.Chunk
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn) :=
  GroupedExtension.Evaluation.chunkAssignmentOfCode
    finProdFinEquiv
    (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
    code

/-- Boolean child payloads supplied to a grouped node function, including
`NeighborhoodExecutableEvaluation.booleanCombine`. -/
def assignmentBits
    (payloadWidth fanIn code : ℕ) :
    Fin fanIn → Fin payloadWidth → Bool :=
  GroupedExtension.unpackChildren
    (PrimeGrouped.Logarithmic.layout payloadWidth fanIn)
    (assignmentChunks payloadWidth fanIn code)

/-- Grouped coordinate containing one child payload bit. -/
def groupedCoordinate
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    Fin fanIn ×
      Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) :=
  (child, payloadChunkIndex payloadWidth fanIn position)

/-- Big-endian coordinate of one semantic bit in the fixed-width assignment
encoding. -/
def encodedBitPosition
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) :
    Fin
      ((fanIn *
          PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) *
        PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn) :=
  GroupedExtension.Evaluation.bitEncoding
    finProdFinEquiv
    (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
    (groupedCoordinate payloadWidth fanIn child position,
      payloadChunkOffset payloadWidth fanIn position)

/-- Low-order base-`2 ^ chunkBits` digit containing one semantic child bit. -/
def lowOrderChunkIndex
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) : ℕ :=
  CombineTerm.basisCoordinateDigitIndex
    payloadWidth fanIn
    (groupedCoordinate payloadWidth fanIn child position)

/-- Low-order binary digit inside the selected chunk. -/
def lowOrderBitInChunkIndex
    (payloadWidth fanIn : ℕ) (position : Fin payloadWidth) : ℕ :=
  PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn -
    1 - (payloadChunkOffset payloadWidth fanIn position).val

/-- Low-order binary digit of one semantic child payload bit in the complete
assignment code. -/
def lowOrderBitIndex
    (payloadWidth fanIn : ℕ)
    (child : Fin fanIn) (position : Fin payloadWidth) : ℕ :=
  PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn *
      lowOrderChunkIndex payloadWidth fanIn child position +
    lowOrderBitInChunkIndex payloadWidth fanIn position

end AssignmentCodeSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
