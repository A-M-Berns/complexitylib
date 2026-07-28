/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds.Internal

/-!
# Numeric frame invariants for the neighborhood scheduler

Every prefix of the executable query and two-root decision schedulers keeps
fuel, node indices, field scalars, residue phases, and child cursors inside
their semantic ranges.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace FrameBounds

open NeighborhoodExecutableEvaluation

/-- The canonical searched field modulus is larger than one. -/
theorem fieldModulus_one_lt
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    1 < fieldModulus instanceData :=
  Internal.fieldModulus_one_lt_internal instanceData

/-- Regenerating one child preserves the compact query-node bound. -/
theorem queryBound_childAt
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (query :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    QueryBound instanceData.horizon
      (NeighborhoodEvaluator.childAt instanceData.guess query child) :=
  Internal.queryBound_childAt_internal
    instanceData query child

/-- A bounded parent produces a bounded prepare-fold child. -/
theorem FrameBound.prepareChild
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount))
    (hbound : FrameBound frame) :
    FrameBound (frame.prepareChild child) :=
  Internal.frameBound_prepareChild_internal frame child hbound

/-- A bounded parent produces a bounded cleanup-fold child. -/
theorem FrameBound.cleanupChild
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount))
    (hbound : FrameBound frame) :
    FrameBound (frame.cleanupChild child) :=
  Internal.frameBound_cleanupChild_internal frame child hbound

/-- The state-consistency root has bounded query-node indices. -/
theorem queryBound_stateRoot
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    QueryBound instanceData.horizon
      (NeighborhoodEvaluator.stateRoot instanceData.guess) :=
  Internal.queryBound_stateRoot_internal instanceData

/-- The verdict-consistency root has bounded query-node indices. -/
theorem queryBound_verdictRoot
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    QueryBound instanceData.horizon
      (NeighborhoodEvaluator.verdictRoot
        instanceData.guess instanceData.blockLength) :=
  Internal.queryBound_verdictRoot_internal instanceData

/-- A singleton query scheduler is bounded from bounded initial fields. -/
theorem stateBound_initial
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (fuel : ℕ)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hfuel : fuel ≤ instanceData.horizon)
    (hnode : QueryBound instanceData.horizon node)
    (hscalar : scalar < fieldModulus instanceData) :
    StateBound
      (NeighborhoodScheduler.State.initial
        fuel node scalar out registers) :=
  Internal.stateBound_initial_internal
    fuel node scalar out registers hfuel hnode hscalar

/-- One query-scheduler transition preserves every numeric frame bound. -/
theorem StateBound.next
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateBound state) :
    StateBound state.next :=
  Internal.stateBound_next_internal state hstate

/-- Every prefix of a bounded query scheduler remains bounded. -/
theorem stateBound_iterate
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateBound state)
    (steps : ℕ) :
    StateBound (State.next^[steps] state) :=
  Internal.stateBound_iterate_internal state hstate steps

namespace Decision

/-- A bounded root starts a bounded nested query scheduler. -/
theorem stateBound_queryInitial
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (hnode : QueryBound instanceData.horizon node) :
    FrameBounds.StateBound
      (NeighborhoodScheduler.Decision.queryInitial
        (instanceData := instanceData) node) :=
  Internal.Decision.stateBound_queryInitial_internal node hnode

/-- The initial two-root decision scheduler has bounded frames. -/
theorem stateBound_initial
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm} :
    Decision.StateBound
      (NeighborhoodScheduler.Decision.initial
        (instanceData := instanceData)) :=
  Internal.Decision.stateBound_initial_internal

/-- One decision-scheduler transition preserves every numeric frame bound. -/
theorem StateBound.next
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.Decision.State tm instanceData)
    (hstate : Decision.StateBound state) :
    Decision.StateBound
      (NeighborhoodScheduler.Decision.next state) :=
  Internal.Decision.stateBound_next_internal state hstate

/-- Every prefix of the canonical decision scheduler has bounded frames. -/
theorem stateBound_iterate
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (steps : ℕ) :
    Decision.StateBound
      (NeighborhoodScheduler.Decision.next^[steps]
        (NeighborhoodScheduler.Decision.initial
          (instanceData := instanceData))) :=
  Internal.Decision.stateBound_iterate_internal steps

end Decision
end FrameBounds
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
