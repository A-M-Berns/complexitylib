/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CandidateSearch.Defs
import Complexitylib.TimeSpaceSimulation.CertifiedTrial.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting.Defs

/-!
# Certified streamed search over candidate times

This layer assembles the executable control flow used by the simulator.  For
each ordinary natural-number candidate it chooses the balanced block length
and the least interval horizon covering that candidate.  A family of exact
trial engines can then be searched from the input length through any finite
endpoint.

The source running-time function is deliberately absent from `trial` and
`runThrough`.  It appears only in the correctness theorem selecting a finite
endpoint at which the search must already have succeeded.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedSearch

open NeighborhoodGraph


/-- Executable trial engines for every input and explicit candidate time. -/
structure EngineFamily (tm : TM workTapeCount) where
  /-- The concrete engine at one input and candidate. -/
  engine : (x : List Bool) → (candidate : ℕ) →
    CertifiedTrial.Engine tm
      (WorkspaceAccounting.blockLength candidate)
      (WorkspaceAccounting.horizon candidate)
  /-- Every supplied engine is exact on the prefix queried by its trial. -/
  exact : ∀ x candidate,
    (engine x candidate).IsExact x
      (by
        simp [WorkspaceAccounting.blockLength,
          ComplexityBridge.balancedBlockLength,
          ComplexityBridge.positiveCeilSqrt])

/-- Run the balanced locally certified trial at one explicit candidate. -/
def trial (tm : TM workTapeCount) (family : EngineFamily tm)
    (x : List Bool) (candidate : ℕ) : Option Bool :=
  CertifiedTrial.run tm x (WorkspaceAccounting.blockLength candidate)
    (family.engine x candidate)

/-- Search candidates from the input length through `endpoint`, inclusive. -/
def runThrough (tm : TM workTapeCount) (family : EngineFamily tm)
    (x : List Bool) (endpoint : ℕ) : Option (ℕ × Bool) :=
  CandidateSearch.searchThrough (trial tm family x) x.length endpoint

/-- Numerical workspace assigned to the streamed search prefix.

The maximum records reuse of one trial's workspace by the next trial. -/
def workspaceThrough (tm : TM workTapeCount)
    (x : List Bool) (endpoint : ℕ) : ℕ :=
  CandidateSearch.streamedWorkspace
    (WorkspaceAccounting.totalBits tm.Q workTapeCount) x.length endpoint

end CertifiedSearch

end TimeSpaceSimulation

end Complexity
