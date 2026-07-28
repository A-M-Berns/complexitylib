/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CertifiedSearch.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.FiniteEncoding

/-!
# Streamed neighborhood evaluator family

A simulator for a fixed source machine hardwires one finite state order.
This module uses that order to instantiate the fully natural-residue
neighborhood evaluator at every balanced candidate block length and horizon.
The result is the exact engine family consumed by `CertifiedSearch`.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodExecutableEvaluation

namespace Residue

/-- Fully natural-residue trial engines for every input and candidate time,
derived from one fixed order of the source machine's states. -/
def engineFamily (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm) :
    CertifiedSearch.EngineFamily tm where
  engine x candidate :=
    certifiedEngine tm x
      (NeighborhoodGraph.WorkspaceAccounting.blockLength candidate)
      (FiniteEncoding.ofStateOrder order
        (NeighborhoodGraph.WorkspaceAccounting.blockLength candidate))
      (by
        simp [NeighborhoodGraph.WorkspaceAccounting.blockLength,
          ComplexityBridge.balancedBlockLength,
          ComplexityBridge.positiveCeilSqrt])
      (NeighborhoodGraph.WorkspaceAccounting.horizon candidate)
  exact x candidate := by
    exact certifiedEngine_isExact tm x
      (NeighborhoodGraph.WorkspaceAccounting.blockLength candidate)
      (FiniteEncoding.ofStateOrder order
        (NeighborhoodGraph.WorkspaceAccounting.blockLength candidate))
      (by
        simp [NeighborhoodGraph.WorkspaceAccounting.blockLength,
          ComplexityBridge.balancedBlockLength,
          ComplexityBridge.positiveCeilSqrt])
      (NeighborhoodGraph.WorkspaceAccounting.horizon candidate)

end Residue

end NeighborhoodExecutableEvaluation

end TimeSpaceSimulation

end Complexity
