/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.BlockRespecting.Defs
import Mathlib.Algebra.Order.Floor.Div

/-!
# Three-block locality for Turing-machine computations

A head that starts in a block of `b` cells and takes at most `b` steps can
visit only its starting block and the two adjacent blocks. At the one-sided
left boundary, the predecessor block is truncated rather than wrapping.

This file defines the corresponding neighborhood and local-agreement
relations independently of the stronger block-respecting property.

## Main definitions

- `InThreeBlockNeighborhood` -- the truncated union of three adjacent blocks
- `TapeNeighborhoodAgreement` -- equal heads and cells in a fixed neighborhood
- `TapeThreeBlockAgreement` -- agreement centered at the left tape's head
- `CfgNeighborhoodAgreement` -- fixed-neighborhood configuration agreement
- `CfgThreeBlockAgreement` -- configuration agreement at all starting heads
- `localityIntervalCount` -- the ceiling number of length-`b` intervals
-/

namespace Complexity

namespace TimeSpaceSimulation

/-- First cell in the three-block neighborhood centered at `centerBlock`.

Natural subtraction explicitly truncates the predecessor block at the
one-sided tape boundary. -/
def threeBlockLower (blockLength centerBlock : ℕ) : ℕ :=
  (centerBlock - 1) * blockLength

/-- Exclusive upper endpoint of the three-block neighborhood. -/
def threeBlockUpper (blockLength centerBlock : ℕ) : ℕ :=
  (centerBlock + 2) * blockLength

/-- Membership in the contiguous union of the predecessor, center, and
successor blocks. When `centerBlock = 0`, this is `[0, 2 * blockLength)`. -/
def InThreeBlockNeighborhood
    (blockLength centerBlock position : ℕ) : Prop :=
  threeBlockLower blockLength centerBlock ≤ position ∧
    position < threeBlockUpper blockLength centerBlock

/-- Number of length-`blockLength` intervals required to cover `time`
transitions. For positive block length this is `⌈time / blockLength⌉`. -/
def localityIntervalCount (time blockLength : ℕ) : ℕ :=
  time ⌈/⌉ blockLength

/-- Two tapes have the same head and agree on every cell in one fixed
three-block neighborhood. Cells outside the neighborhood are unconstrained. -/
structure TapeNeighborhoodAgreement (blockLength centerBlock : ℕ)
    (left right : Tape) : Prop where
  /-- Both tapes place their heads at the same absolute position. -/
  head_eq : left.head = right.head
  /-- Cells agree throughout the selected three-block neighborhood. -/
  cells_eq : ∀ position,
    InThreeBlockNeighborhood blockLength centerBlock position →
      left.cells position = right.cells position

/-- Three-block tape agreement centered at the block containing the left
head. -/
def TapeThreeBlockAgreement (blockLength : ℕ)
    (left right : Tape) : Prop :=
  TapeNeighborhoodAgreement blockLength
    (blockIndex blockLength left.head) left right

/-- The starting block selected by every named head of a configuration. -/
def startingBlocks (blockLength : ℕ) (cfg : Cfg workTapeCount Q) :
    TapeIndex workTapeCount → ℕ :=
  fun tape => blockIndex blockLength (tapeAt cfg tape).head

/-- Two configurations agree on the state, all named heads, and a fixed
three-block neighborhood for each named tape. -/
structure CfgNeighborhoodAgreement (blockLength : ℕ)
    (centerBlocks : TapeIndex workTapeCount → ℕ)
    (left right : Cfg workTapeCount Q) : Prop where
  /-- Machine states agree. -/
  state_eq : left.state = right.state
  /-- Input tapes agree on their selected neighborhood. -/
  input : TapeNeighborhoodAgreement blockLength
    (centerBlocks (TapeIndex.input workTapeCount))
    left.input right.input
  /-- Every work tape agrees on its selected neighborhood. -/
  work : ∀ index, TapeNeighborhoodAgreement blockLength
    (centerBlocks (TapeIndex.work index))
    (left.work index) (right.work index)
  /-- Output tapes agree on their selected neighborhood. -/
  output : TapeNeighborhoodAgreement blockLength
    (centerBlocks (TapeIndex.output workTapeCount))
    left.output right.output

/-- Configuration agreement on the three-block neighborhoods selected by all
heads of the left configuration. -/
def CfgThreeBlockAgreement (blockLength : ℕ)
    (left right : Cfg workTapeCount Q) : Prop :=
  CfgNeighborhoodAgreement blockLength
    (startingBlocks blockLength left) left right

end TimeSpaceSimulation

end Complexity
