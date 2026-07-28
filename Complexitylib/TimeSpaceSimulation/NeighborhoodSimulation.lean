/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodSimulation.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodSimulation.Internal

/-!
# Correct balanced semantic time-to-space simulation

The balanced block length is positive and its interval horizon covers the
entire advertised source time. Therefore the decoded two-root Cook--Mertz
evaluation recovers the exact halted state and verdict of every source
decider.

This theorem closes the semantic and arithmetic portions of the simulation.
`balancedSnapshot` is still an evaluator-level function; a separate
all-prefix machine implementation is required for membership in `DSPACE`.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodSimulation

/-- Every halted run covered by an explicit trial time is recovered exactly. -/
theorem candidateSnapshot_eq_of_reachesIn
    (tm : TM workTapeCount) (x : List Bool)
    (time haltTime : ℕ) (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (htime : haltTime ≤ time) :
    candidateSnapshot tm x time =
      { state := cfg.state
        verdict := cfg.output.cells 1 } :=
  Internal.candidateSnapshot_eq_of_reachesIn_internal
    tm x time haltTime cfg hreach hhalt htime

/-- Every halted run within the advertised source time is recovered exactly
by the balanced evaluator. -/
theorem balancedSnapshot_eq_of_reachesIn
    (tm : TM workTapeCount) (x : List Bool)
    (timeBound : ℕ → ℕ)
    (haltTime : ℕ) (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (htime : haltTime ≤ timeBound x.length) :
    balancedSnapshot tm x timeBound =
      { state := cfg.state
        verdict := cfg.output.cells 1 } :=
  Internal.balancedSnapshot_eq_of_reachesIn_internal
    tm x timeBound haltTime cfg hreach hhalt htime

/-- The balanced evaluator returns the halt state and the correct Boolean
verdict for every input of a time-bounded source decider. -/
theorem balancedSnapshot_decides
    (tm : TM workTapeCount) (L : Language)
    (timeBound : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L timeBound)
    (x : List Bool) :
    (balancedSnapshot tm x timeBound).state = tm.qhalt ∧
      (x ∈ L →
        (balancedSnapshot tm x timeBound).verdict = Γ.one) ∧
      (x ∉ L →
        (balancedSnapshot tm x timeBound).verdict = Γ.zero) :=
  Internal.balancedSnapshot_decides_internal
    tm L timeBound hdecides x

end NeighborhoodSimulation

end TimeSpaceSimulation

end Complexity
