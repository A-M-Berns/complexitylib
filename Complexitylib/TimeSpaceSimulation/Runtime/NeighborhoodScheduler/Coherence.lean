/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Coherence.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Coherence.Internal

/-!
# Semantic coherence for the neighborhood scheduler

Every non-entry frame reachable in the executable query scheduler belongs to
an in-horizon computation call and has positive recursion fuel.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace Coherence

open NeighborhoodExecutableEvaluation

/-- Extract the computation node, in-horizon interval, and positive fuel from
a coherent non-entry frame. -/
theorem FrameCoherent.of_not_enter
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {frame : NeighborhoodScheduler.Frame tm instanceData}
    (hframe : FrameCoherent frame)
    (hphase : frame.phase ≠ .enter) :
    ∃ tape slot interval,
      frame.node = .graph (.computation tape slot interval) ∧
        interval < instanceData.horizon ∧
        0 < frame.fuel :=
  Internal.frameCoherent_of_not_enter_internal hframe hphase

/-- Every singleton initial scheduler state is coherent because its sole
frame is in the entry phase. -/
theorem stateCoherent_initial
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
        tm instanceData.blockLength) :
    StateCoherent
      (NeighborhoodScheduler.State.initial
        fuel node scalar out registers) :=
  Internal.stateCoherent_initial_internal
    fuel node scalar out registers

/-- One scheduler microstep preserves semantic frame coherence. -/
theorem StateCoherent.next
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateCoherent state) :
    StateCoherent state.next :=
  Internal.stateCoherent_next_internal state hstate

/-- Every prefix of a coherent scheduler execution remains coherent. -/
theorem stateCoherent_iterate
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateCoherent state)
    (steps : ℕ) :
    StateCoherent (State.next^[steps] state) :=
  Internal.stateCoherent_iterate_internal state hstate steps

/-- Every frame in every prefix reachable from an initial scheduler state is
semantically coherent. -/
theorem stateCoherent_initial_iterate
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (fuel steps : ℕ)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    StateCoherent
      (State.next^[steps]
        (NeighborhoodScheduler.State.initial
          fuel node scalar out registers)) :=
  Internal.stateCoherent_initial_iterate_internal
    fuel steps node scalar out registers

end Coherence
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
