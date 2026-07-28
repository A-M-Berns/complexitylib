/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Defs

/-!
# Semantic coherence for the neighborhood scheduler

This definitions layer records the relation between a live frame's control
phase and its query node. Entry frames may carry any query. Every later phase
must belong to an in-horizon computation call with positive recursion fuel.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace Coherence

/-- A non-entry control phase belongs to an in-horizon computation call with
positive recursion fuel. -/
def FrameCoherent
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData) : Prop :=
  frame.phase ≠ .enter →
    ∃ tape slot interval,
      frame.node = .graph (.computation tape slot interval) ∧
        interval < instanceData.horizon ∧
        0 < frame.fuel

/-- Every live frame in a scheduler state has coherent control and node
data. -/
def StateCoherent
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData) : Prop :=
  ∀ frame ∈ state.stack, FrameCoherent frame

end Coherence
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
