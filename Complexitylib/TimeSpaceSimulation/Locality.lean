/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Locality.Defs
import Complexitylib.TimeSpaceSimulation.Locality.Internal

/-!
# Three-block locality without block-respecting normalization

Every named Turing-machine head moves by at most one cell per transition.
Consequently, during any interval of at most `b` transitions, it remains in
the union of the `b`-cell block where it started and the two adjacent blocks.
On the one-sided tape, the missing predecessor of block zero is explicitly
truncated, leaving only blocks zero and one.

If two starting configurations agree on their state, heads, and these
three-block neighborhoods, their deterministic traces evolve in lockstep for
the whole interval. This yields a local simulation primitive without first
normalizing the machine to be block respecting.

## Main results

- `inThreeBlockNeighborhood_iff_three_blocks` -- exact three-block union
- `TM.configurationAt_head_in_threeBlockNeighborhood` -- head residence
- `TM.trace_threeBlock_noninterference` -- local trace noninterference
- `TM.configurationAt_threeBlock_noninterference` -- interval form
- `localityIntervalCount_le_iff` -- exact ceiling-division interval count
-/

namespace Complexity

namespace TimeSpaceSimulation

/-- The ceiling interval count is at most `intervals` exactly when those
intervals cover all `time` transitions. -/
theorem localityIntervalCount_le_iff
    {time blockLength intervals : ℕ}
    (hpositive : 0 < blockLength) :
    localityIntervalCount time blockLength ≤ intervals ↔
      time ≤ blockLength * intervals :=
  Locality.Internal.localityIntervalCount_le_iff_internal hpositive

/-- Length-`blockLength` intervals indexed by
`localityIntervalCount time blockLength` cover `time` transitions. -/
theorem time_le_blockLength_mul_localityIntervalCount
    {time blockLength : ℕ} (hpositive : 0 < blockLength) :
    time ≤ blockLength * localityIntervalCount time blockLength :=
  Locality.Internal.time_le_blockLength_mul_localityIntervalCount_internal
    hpositive

/-- At center block zero, the lower endpoint is explicitly truncated to
cell zero. -/
@[simp] theorem threeBlockLower_zero (blockLength : ℕ) :
    threeBlockLower blockLength 0 = 0 :=
  Locality.Internal.threeBlockLower_zero_internal blockLength

/-- At center block zero, the neighborhood ends after blocks zero and one. -/
@[simp] theorem threeBlockUpper_zero (blockLength : ℕ) :
    threeBlockUpper blockLength 0 = 2 * blockLength :=
  Locality.Internal.threeBlockUpper_zero_internal blockLength

/-- The neighborhood is exactly the union of the predecessor, center, and
successor canonical blocks. Natural subtraction duplicates block zero when
the center is zero; it never wraps around. -/
theorem inThreeBlockNeighborhood_iff_three_blocks
    {blockLength centerBlock position : ℕ} :
    InThreeBlockNeighborhood blockLength centerBlock position ↔
      InBlock blockLength (centerBlock - 1) position ∨
        InBlock blockLength centerBlock position ∨
        InBlock blockLength (centerBlock + 1) position :=
  Locality.Internal.inThreeBlockNeighborhood_iff_three_blocks_internal

/-- The left-boundary neighborhood is exactly the union of blocks zero and
one. -/
theorem inThreeBlockNeighborhood_zero_iff_two_blocks
    {blockLength position : ℕ} :
    InThreeBlockNeighborhood blockLength 0 position ↔
      InBlock blockLength 0 position ∨
        InBlock blockLength 1 position :=
  Locality.Internal.inThreeBlockNeighborhood_zero_iff_two_blocks_internal

namespace TapeNeighborhoodAgreement

/-- Locally agreeing tapes read the same symbol whenever the left head lies
inside the selected neighborhood. -/
theorem read_eq
    {blockLength centerBlock : ℕ} {left right : Tape}
    (h : TapeNeighborhoodAgreement
      blockLength centerBlock left right)
    (hleft : InThreeBlockNeighborhood
      blockLength centerBlock left.head) :
    left.read = right.read :=
  Locality.Internal.tapeNeighborhoodAgreement_read_eq_internal h hleft

/-- Applying the same move preserves neighborhood agreement. -/
theorem move
    {blockLength centerBlock : ℕ} {left right : Tape}
    (h : TapeNeighborhoodAgreement
      blockLength centerBlock left right)
    (direction : Dir3) :
    TapeNeighborhoodAgreement blockLength centerBlock
      (left.move direction) (right.move direction) :=
  Locality.Internal.tapeNeighborhoodAgreement_move_internal h direction

/-- Applying the same write-and-move action preserves neighborhood
agreement. -/
theorem writeAndMove
    {blockLength centerBlock : ℕ} {left right : Tape}
    (h : TapeNeighborhoodAgreement
      blockLength centerBlock left right)
    (symbol : Γ) (direction : Dir3) :
    TapeNeighborhoodAgreement blockLength centerBlock
      (left.writeAndMove symbol direction)
      (right.writeAndMove symbol direction) :=
  Locality.Internal.tapeNeighborhoodAgreement_writeAndMove_internal
    h symbol direction

end TapeNeighborhoodAgreement

namespace NTM

/-- After `steps` transitions, every named head is within `steps` cells of
its starting position in both directions. -/
theorem trace_head_distance (tm : NTM workTapeCount) (steps : ℕ)
    (choices : Fin steps → Bool)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount) :
    (tapeAt (tm.trace steps choices cfg) tape).head ≤
        (tapeAt cfg tape).head + steps ∧
      (tapeAt cfg tape).head ≤
        (tapeAt (tm.trace steps choices cfg) tape).head + steps :=
  Locality.Internal.tapeAt_trace_head_distance_internal
    tm steps choices cfg tape

/-- During at most `blockLength` transitions, every named head stays in the
three-block neighborhood centered at its starting block. -/
theorem trace_head_in_threeBlockNeighborhood
    (tm : NTM workTapeCount) (blockLength steps : ℕ)
    (choices : Fin steps → Bool)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength) :
    InThreeBlockNeighborhood blockLength
      (blockIndex blockLength (tapeAt cfg tape).head)
      (tapeAt (tm.trace steps choices cfg) tape).head :=
  Locality.Internal.tapeAt_trace_head_in_threeBlockNeighborhood_internal
    tm blockLength steps choices cfg tape hpositive hsteps

end NTM

end TimeSpaceSimulation

namespace TM

open TimeSpaceSimulation

/-- During any interval of at most `blockLength` transitions, every named
head of the frozen deterministic computation stays in the three-block
neighborhood centered at its block at the interval start. -/
theorem configurationAt_head_in_threeBlockNeighborhood
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength) :
    InThreeBlockNeighborhood blockLength
      (blockIndex blockLength
        (tapeAt (tm.configurationAt x start) tape).head)
      (tapeAt (tm.configurationAt x (start + steps)) tape).head :=
  TimeSpaceSimulation.Locality.Internal.configurationAt_head_in_threeBlockNeighborhood_internal
    tm x blockLength start steps tape hpositive hsteps

/-- Three-block agreement at the start of an interval makes its deterministic
traces locally indistinguishable for at most `blockLength` transitions. The
neighborhood centers remain those of the original left configuration. -/
theorem trace_threeBlock_noninterference
    (tm : TM workTapeCount) (blockLength steps : ℕ)
    (left right : Cfg workTapeCount tm.Q)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength)
    (hstart : CfgThreeBlockAgreement blockLength left right) :
    CfgNeighborhoodAgreement blockLength
      (startingBlocks blockLength left)
      (tm.toNTM.trace steps (fun _ => false) left)
      (tm.toNTM.trace steps (fun _ => false) right) :=
  TimeSpaceSimulation.Locality.Internal.trace_cfgThreeBlockAgreement_internal
    tm blockLength steps left right hpositive hsteps hstart

/-- Interval form of three-block noninterference. A seed configuration that
agrees with the real run on the state, heads, and three adjacent blocks at
`start` recovers the real state, heads, and those neighborhoods after
`steps ≤ blockLength`. -/
theorem configurationAt_threeBlock_noninterference
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength)
    (hstart : CfgThreeBlockAgreement blockLength
      (tm.configurationAt x start) seed) :
    CfgNeighborhoodAgreement blockLength
      (startingBlocks blockLength (tm.configurationAt x start))
      (tm.configurationAt x (start + steps))
      (tm.toNTM.trace steps (fun _ => false) seed) :=
  TimeSpaceSimulation.Locality.Internal.configurationAt_threeBlock_noninterference_internal
    tm x blockLength start steps seed hpositive hsteps hstart

end TM

end Complexity
