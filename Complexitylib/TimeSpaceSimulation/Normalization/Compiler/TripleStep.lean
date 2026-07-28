/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Normalization.Compiler.TripleStep.Defs
import Complexitylib.TimeSpaceSimulation.Normalization.Compiler.TripleStep.Internal

/-!
# Three-microstep block normalization

This module exposes an executable compiler that simulates one source
transition by exactly three target transitions. The target uses the same work
tapes, preserves halted verdicts, runs with factor-three overhead, and is
block respecting for constant block length three.

This is a genuine constructive normalization layer. It does not by itself
implement the variable-block tape-layout construction used in the full
Hopcroft--Paul--Valiant theorem.

## Main results

- `TM.tripleStepTM_reachesIn` -- exact factor-three run simulation
- `TM.tripleStepTM_blockRespecting` -- length-three block residence
- `TM.tripleStepNormalization` -- packaged normalization certificate
-/

namespace Complexity

namespace TM

open TimeSpaceSimulation TimeSpaceSimulation.NormalizationCompiler

/-- An exact source run is simulated in three target steps per source step. -/
theorem tripleStepTM_reachesIn (source : TM workTapeCount)
    (x : List Bool) {time : ℕ}
    {cfg : Cfg workTapeCount source.Q}
    (hreach : source.reachesIn time (source.initCfg x) cfg) :
    source.tripleStepTM.reachesIn (3 * time)
      (source.tripleStepTM.initCfg x) (boundaryCfg source cfg) :=
  tripleStepTM_reachesIn_init_internal source x hreach

/-- A boundary embedding is halted exactly when its source configuration is
halted. -/
theorem tripleStepTM_boundary_halted_iff
    (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q) :
    source.tripleStepTM.halted (boundaryCfg source cfg) ↔
      source.halted cfg :=
  boundaryCfg_halted_iff_internal source cfg

/-- The compiled machine is block respecting for blocks of length three. -/
theorem tripleStepTM_blockRespecting (source : TM workTapeCount) :
    source.tripleStepTM.BlockRespecting (fun _ => 3) :=
  tripleStepTM_blockRespecting_internal source

/-- The constructive factor-three compiler packaged as a
`LinearBlockNormalization` certificate. -/
def tripleStepNormalization (source : TM workTapeCount)
    (timeBound : ℕ → ℕ) :
    LinearBlockNormalization source timeBound (fun _ => 3) :=
  tripleStepNormalizationInternal source timeBound

@[simp] theorem tripleStepNormalization_machine
    (source : TM workTapeCount) (timeBound : ℕ → ℕ) :
    (source.tripleStepNormalization timeBound).machine =
      source.tripleStepTM :=
  rfl

@[simp] theorem tripleStepNormalization_constant
    (source : TM workTapeCount) (timeBound : ℕ → ℕ) :
    (source.tripleStepNormalization timeBound).constant = 3 :=
  rfl

end TM

end Complexity
