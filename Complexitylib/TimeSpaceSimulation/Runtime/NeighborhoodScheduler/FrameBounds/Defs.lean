/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Defs

/-!
# Numeric frame invariants for the neighborhood scheduler

This definitions layer records the semantic bounds carried by every live
scheduler frame. Source blocks may include the distinguished verdict block
at index one; computation intervals remain strictly below the instance
horizon. Residue phases retain the exact relation
`residue + residuesLeft + 1 = modulus`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace FrameBounds

open NeighborhoodGraph
open NeighborhoodExecutableEvaluation

/-- Query-node indices needed by the concrete frame codec. Source block one
is admitted for the distinguished verdict cell, including at horizon zero. -/
def QueryBound (horizon : ℕ) :
    NeighborhoodEvaluator.QueryNode workTapeCount horizon → Prop
  | .failure => True
  | .graph (.source _ block) => block ≤ max horizon 1
  | .graph (.computation _ _ interval) => interval < horizon

/-- Exact arithmetic and cursor invariant for each non-entry scheduler
phase. -/
def PhaseBound (modulus fanIn : ℕ) :
    NeighborhoodScheduler.Phase workTapeCount → Prop
  | .enter => True
  | .prepare residue residuesLeft childIndex =>
      residue + residuesLeft + 1 = modulus ∧ childIndex ≤ fanIn
  | .combine residue residuesLeft =>
      residue + residuesLeft + 1 = modulus
  | .cleanupCall residue residuesLeft childIndex =>
      residue + residuesLeft + 1 = modulus ∧ childIndex ≤ fanIn
  | .cleanupScale residue residuesLeft _ nextChildIndex =>
      residue + residuesLeft + 1 = modulus ∧ nextChildIndex ≤ fanIn

/-- Numeric invariant for one live scheduler frame. -/
def FrameBound
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData) : Prop :=
  frame.fuel ≤ instanceData.horizon ∧
    QueryBound instanceData.horizon frame.node ∧
    frame.scalar < fieldModulus instanceData ∧
    PhaseBound (fieldModulus instanceData)
      (graphFanIn workTapeCount) frame.phase

/-- Every live frame in one query scheduler satisfies the numeric invariant. -/
def StateBound
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData) : Prop :=
  ∀ frame ∈ state.stack, FrameBound frame

namespace Decision

/-- The nested query of a two-root decision scheduler has bounded frames. -/
def StateBound
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.Decision.State tm instanceData) : Prop :=
  FrameBounds.StateBound state.query

end Decision

end FrameBounds
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
