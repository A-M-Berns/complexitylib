/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration.Defs

/-!
# Packed output chunks from a finite local configuration

The grouped layout is row-major and big-endian inside each chunk. For a
zero-based runtime chunk cursor `chunk` and grouped width `chunkBits`, bit
offset `offset` has absolute compact coordinate

`chunk * chunkBits + offset`.

This module gives the pure endpoint of the later fixed-register RAM loop.
It scans those coordinates from low offset to high offset, doubles its
accumulator before installing each Boolean bit, and treats coordinates past
the compact payload as trailing zero padding.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedOutputChunkSemantics

open NeighborhoodGraph
open TreeEval CookMertz

/-- First compact coordinate selected by a zero-based output-chunk cursor. -/
def chunkStart (chunkCursor chunkBits : ℕ) : ℕ :=
  chunkCursor * chunkBits

/-- Absolute compact coordinate of one offset in a runtime output chunk. -/
def bitPosition
    (chunkCursor chunkBits offset : ℕ) : ℕ :=
  chunkStart chunkCursor chunkBits + offset

/-- Total output bit with the grouped layout's trailing-zero padding. -/
def boundedOutputBitFromWord
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word coordinate : ℕ) : Bool :=
  if coordinate < NeighborhoodExecutableEvaluation.payloadWidth
      tm blockLength then
    PackedLocalConfiguration.outputBitFromWord
      tm blockLength coordinate center targetTape targetSlot word
  else
    false

/-- Numeric form of one bounded packed-word output bit. -/
def boundedOutputBitValue
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word coordinate : ℕ) : ℕ :=
  if boundedOutputBitFromWord tm blockLength center
      targetTape targetSlot word coordinate then
    1
  else
    0

/-- Big-endian binary fold used by the future output-chunk RAM loop. -/
def forwardBits
    (bit : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, accumulator => accumulator
  | coordinate, remaining + 1, accumulator =>
      forwardBits bit (coordinate + 1) remaining
        (2 * accumulator + bit coordinate)

/-- Natural packed value produced from one runtime output-chunk cursor. -/
def packedOutputChunk
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word chunkCursor chunkBits : ℕ) : ℕ :=
  forwardBits
    (boundedOutputBitValue tm blockLength center
      targetTape targetSlot word)
    (chunkStart chunkCursor chunkBits) chunkBits 0

end PackedOutputChunkSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
