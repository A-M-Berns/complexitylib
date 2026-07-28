/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComplexityBridge
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluation
import Complexitylib.TimeSpaceSimulation.NeighborhoodSimulation.Defs

/-!
# Correctness internals for balanced semantic simulation
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodSimulation

namespace Internal

theorem candidateSnapshot_eq_of_reachesIn_internal
    (tm : TM workTapeCount) (x : List Bool)
    (time haltTime : ℕ) (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (htime : haltTime ≤ time) :
    candidateSnapshot tm x time =
      { state := cfg.state
        verdict := cfg.output.cells 1 } := by
  unfold candidateSnapshot
  exact
    NeighborhoodEvaluation.evaluatedDecisionSnapshot_eq_of_reachesIn
      tm x
        (ComplexityBridge.balancedBlockLength
          time)
        (ComplexityBridge.timeBlockCount
          time)
        haltTime
        (ComplexityBridge.positiveCeilSqrt_pos _)
        cfg hreach hhalt
        (htime.trans (by
          simpa [timeBlockStart] using
            ComplexityBridge.time_le_timeBlockCount_mul_blockLength
              time))

theorem balancedSnapshot_eq_of_reachesIn_internal
    (tm : TM workTapeCount) (x : List Bool)
    (timeBound : ℕ → ℕ)
    (haltTime : ℕ) (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (htime : haltTime ≤ timeBound x.length) :
    balancedSnapshot tm x timeBound =
      { state := cfg.state
        verdict := cfg.output.cells 1 } := by
  unfold balancedSnapshot
  exact candidateSnapshot_eq_of_reachesIn_internal
    tm x (timeBound x.length) haltTime
      cfg hreach hhalt htime

theorem balancedSnapshot_decides_internal
    (tm : TM workTapeCount) (L : Language)
    (timeBound : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L timeBound)
    (x : List Bool) :
    (balancedSnapshot tm x timeBound).state = tm.qhalt ∧
      (x ∈ L →
        (balancedSnapshot tm x timeBound).verdict = Γ.one) ∧
      (x ∉ L →
        (balancedSnapshot tm x timeBound).verdict = Γ.zero) := by
  obtain ⟨cfg, haltTime, htime, hreach, hhalt,
    haccept, hreject⟩ := hdecides x
  have hsnapshot :=
    balancedSnapshot_eq_of_reachesIn_internal
      tm x timeBound haltTime cfg hreach hhalt htime
  rw [hsnapshot]
  exact ⟨hhalt, haccept, hreject⟩

end Internal

end NeighborhoodSimulation

end TimeSpaceSimulation

end Complexity
