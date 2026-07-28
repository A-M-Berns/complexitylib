/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Normalization.Defs
import Complexitylib.TimeSpaceSimulation.Normalization.Internal

/-!
# Block-respecting normalization certificates

This module exposes the theorem interface for the
Hopcroft--Paul--Valiant normalization used by Williams.

The checked layer now fixes:

* exact machine-facing parameter hypotheses;
* a proof-carrying target with at most one extra work tape;
* terminal decision-cell preservation and a concrete linear time bound;
* transfer to a block-respecting `DTIME` witness; and
* the exact sanity check that unit blocks impose no restriction.

No existence theorem for nontrivial block lengths is asserted. The remaining
normalization boundary is to construct
`TM.LinearBlockNormalization source timeBound blockLength` from
`HPVParameters timeBound blockLength`.

## Main theorems

- `HPVParameters.binaryWidth_le_blockLength` -- concrete logarithmic lower bound
- `TM.LinearBlockNormalization.decidesInTime` -- semantic/time transfer
- `TM.LinearBlockNormalization.normalizedTime_bigO` -- linear overhead
- `TM.LinearBlockNormalization.mem_blockRespectingDTIME` -- class witness
- `TM.LinearBlockNormalization.mem_blockRespectingDTIME_of_parameters` --
  parameterized class witness
- `TM.blockRespecting_one` -- every machine respects unit blocks
- `blockRespectingDTIME_one_eq_DTIME` -- exact unit-block sanity check
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace HPVParameters

/-- The time bound has a compositional clock implementation. -/
theorem time_clockConstructible {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) :
    TM.ClockConstructible timeBound :=
  time_clockConstructible_internal h

/-- The block length has a compositional clock implementation. -/
theorem block_clockConstructible {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) :
    TM.ClockConstructible blockLength :=
  block_clockConstructible_internal h

/-- The advertised time bound dominates the input length. -/
theorem input_le_time {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    inputLength ≤ timeBound inputLength :=
  input_le_time_internal h inputLength

/-- Every requested block length is positive, including at input length zero. -/
theorem blockLength_pos {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    0 < blockLength inputLength :=
  blockLength_pos_internal h inputLength

/-- A block can store the binary representation of the time horizon. -/
theorem binaryWidth_le_blockLength {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    (timeBound inputLength).size ≤ blockLength inputLength :=
  binaryWidth_le_blockLength_internal h inputLength

/-- The requested block length does not exceed the time horizon. -/
theorem blockLength_le_time {timeBound blockLength : ℕ → ℕ}
    (h : HPVParameters timeBound blockLength) (inputLength : ℕ) :
    blockLength inputLength ≤ timeBound inputLength :=
  blockLength_le_time_internal h inputLength

end HPVParameters

/-- Forgetting block residence gives the ordinary deterministic time class. -/
theorem BlockRespectingDTIME_subset_DTIME
    (timeBound blockLength : ℕ → ℕ) :
    BlockRespectingDTIME timeBound blockLength ⊆ DTIME timeBound :=
  blockRespectingDTIME_subset_DTIME_internal timeBound blockLength

end TimeSpaceSimulation

namespace TM

open TimeSpaceSimulation

/-- Every deterministic machine is block respecting for unit-length blocks. -/
theorem blockRespecting_one (machine : TM workTapeCount) :
    machine.BlockRespecting (fun _ => 1) :=
  blockRespecting_one_internal machine

namespace LinearBlockNormalization

variable {sourceWorkTapeCount : ℕ} {source : TM sourceWorkTapeCount}
  {timeBound blockLength : ℕ → ℕ}

/-- A normalization certificate transports a source time-bounded decider to
its target with the certificate's concrete runtime. -/
theorem decidesInTime
    (normalization : LinearBlockNormalization source timeBound blockLength)
    {L : Language} (hdecides : source.DecidesInTime L timeBound) :
    normalization.machine.DecidesInTime L normalization.normalizedTime :=
  decidesInTime_internal normalization hdecides

/-- The certificate's concrete target runtime has only linear asymptotic
overhead when the source bound dominates the input length. -/
theorem normalizedTime_bigO
    (normalization : LinearBlockNormalization source timeBound blockLength)
    (hinput : ∀ inputLength, inputLength ≤ timeBound inputLength) :
    normalization.normalizedTime =O timeBound :=
  normalizedTime_bigO_internal normalization hinput

/-- The machine-facing parameter package discharges the input-domination
hypothesis needed for the linear asymptotic bound. -/
theorem normalizedTime_bigO_of_parameters
    (normalization : LinearBlockNormalization source timeBound blockLength)
    (hparameters : HPVParameters timeBound blockLength) :
    normalization.normalizedTime =O timeBound :=
  normalizedTime_bigO_of_parameters_internal normalization hparameters

/-- A normalization certificate produces a block-respecting `DTIME` witness. -/
theorem mem_blockRespectingDTIME
    (normalization : LinearBlockNormalization source timeBound blockLength)
    {L : Language} (hdecides : source.DecidesInTime L timeBound)
    (hinput : ∀ inputLength, inputLength ≤ timeBound inputLength) :
    L ∈ BlockRespectingDTIME timeBound blockLength :=
  mem_blockRespectingDTIME_internal normalization hdecides hinput

/-- The full machine-facing parameter package and a normalization certificate
produce a block-respecting `DTIME` witness. -/
theorem mem_blockRespectingDTIME_of_parameters
    (normalization : LinearBlockNormalization source timeBound blockLength)
    {L : Language} (hdecides : source.DecidesInTime L timeBound)
    (hparameters : HPVParameters timeBound blockLength) :
    L ∈ BlockRespectingDTIME timeBound blockLength :=
  mem_blockRespectingDTIME_of_parameters_internal
    normalization hdecides hparameters

/-- The certificate interface is inhabited in the degenerate unit-block case
by the source machine itself. -/
theorem exists_one (source : TM sourceWorkTapeCount)
    (timeBound : ℕ → ℕ) :
    Nonempty
      (LinearBlockNormalization source timeBound (fun _ => 1)) :=
  exists_one_internal source timeBound

end LinearBlockNormalization

end TM

namespace TimeSpaceSimulation

/-- Requiring unit-length blocks leaves `DTIME` unchanged. -/
theorem blockRespectingDTIME_one_eq_DTIME (timeBound : ℕ → ℕ) :
    BlockRespectingDTIME timeBound (fun _ => 1) = DTIME timeBound :=
  blockRespectingDTIME_one_eq_DTIME_internal timeBound

end TimeSpaceSimulation

end Complexity
