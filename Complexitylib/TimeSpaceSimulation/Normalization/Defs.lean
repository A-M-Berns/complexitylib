/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.Time
import Complexitylib.Models.TuringMachine.UTM.ClockConstructible
import Complexitylib.TimeSpaceSimulation.BlockRespecting
import Mathlib.Data.Nat.Size

/-!
# Block-respecting normalization certificates

This file defines the machine-facing statement of the
Hopcroft--Paul--Valiant normalization used in Williams's time-to-space
simulation.

`HPVParameters` fixes concrete versions of the paper's hypotheses. Binary
logarithmic width is represented by `Nat.size`, and constructibility uses the
library's compositional `TM.ClockConstructible` interface. The latter computes
a bound in time proportional to the value plus the input length, which is
absorbed by the explicit hypothesis `n ≤ timeBound n`.

`TM.LinearBlockNormalization` is a proof-carrying result of the normalization
construction. It packages one target machine using at most one additional
work tape, its block-respecting certificate, and a terminal-run simulation
with a concrete linear time bound. The structure deliberately does not assert
that such a result exists; constructing it is the remaining operational
Hopcroft--Paul--Valiant theorem.

`BlockRespectingDTIME` records the class-level target without hiding either
the concrete machine runtime or the block-respecting predicate.

## Main definitions

- `HPVParameters` -- exact constructibility and block-size hypotheses
- `BlockRespectingDTIME` -- `DTIME` with a block-respecting witness
- `TM.LinearBlockNormalization` -- proof-carrying normalization result
- `TM.LinearBlockNormalization.normalizedTime` -- its concrete time bound
-/

namespace Complexity

namespace TimeSpaceSimulation

/-- Machine-facing hypotheses for the Hopcroft--Paul--Valiant normalization.

The `Nat.size` inequality is the concrete binary-width interpretation of
`log timeBound ≤ blockLength`. -/
def HPVParameters (timeBound blockLength : ℕ → ℕ) : Prop :=
  TM.ClockConstructible timeBound ∧
    TM.ClockConstructible blockLength ∧
    (∀ inputLength, inputLength ≤ timeBound inputLength) ∧
    ∀ inputLength,
      0 < blockLength inputLength ∧
        (timeBound inputLength).size ≤ blockLength inputLength ∧
        blockLength inputLength ≤ timeBound inputLength

/-- Languages with a block-respecting deterministic decider running in
`O(timeBound)`.

The concrete runtime remains existential, just as in `DTIME`; block
respecting is required for the stated length-indexed block schedule. -/
def BlockRespectingDTIME (timeBound blockLength : ℕ → ℕ) : Set Language :=
  {L | ∃ (workTapeCount : ℕ) (machine : TM workTapeCount)
      (runtime : ℕ → ℕ),
    machine.DecidesInTime L runtime ∧
      runtime =O timeBound ∧
      machine.BlockRespecting blockLength}

end TimeSpaceSimulation

namespace TM

open TimeSpaceSimulation

/-- A certified linear-overhead block-respecting normalization of `source`
for runs bounded by `timeBound`.

The terminal-run simulation is the exact semantic contract needed to
transport `DecidesInTime`: it preserves the verdict cell and produces a
halted target run. The work-tape inequality records the paper's allowance of
one additional tape. -/
structure LinearBlockNormalization {sourceWorkTapeCount : ℕ}
    (source : TM sourceWorkTapeCount) (timeBound blockLength : ℕ → ℕ) where
  /-- Number of work tapes in the normalized machine. -/
  workTapeCount : ℕ
  /-- The normalized deterministic machine. -/
  machine : TM workTapeCount
  /-- The normalized machine uses at most one additional work tape. -/
  workTapeCount_le : workTapeCount ≤ sourceWorkTapeCount + 1
  /-- Machine-dependent constant in the concrete linear time bound. -/
  constant : ℕ
  /-- The linear-overhead constant is positive. -/
  constant_pos : 0 < constant
  /-- The target machine respects the requested input-length-indexed blocks. -/
  blockRespecting : machine.BlockRespecting blockLength
  /-- Every bounded halted source run has a bounded halted target run with
  the same decision cell. -/
  simulatesBoundedHaltedRun :
    ∀ (x : List Bool) {cfg : Cfg sourceWorkTapeCount source.Q} {time : ℕ},
      time ≤ timeBound x.length →
      source.reachesIn time (source.initCfg x) cfg →
      source.halted cfg →
      ∃ (cfg' : Cfg workTapeCount machine.Q) (time' : ℕ),
        time' ≤ constant * (timeBound x.length + 1) ∧
          machine.reachesIn time' (machine.initCfg x) cfg' ∧
          machine.halted cfg' ∧
          cfg'.output.cells 1 = cfg.output.cells 1

namespace LinearBlockNormalization

variable {sourceWorkTapeCount : ℕ} {source : TM sourceWorkTapeCount}
  {timeBound blockLength : ℕ → ℕ}

/-- Concrete running-time bound supplied by a normalization certificate. -/
def normalizedTime
    (normalization : LinearBlockNormalization source timeBound blockLength)
    (inputLength : ℕ) : ℕ :=
  normalization.constant * (timeBound inputLength + 1)

end LinearBlockNormalization

end TM

end Complexity
