/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting.Defs

/-!
# Asymptotic parameters for certified candidate search

This file records the explicit constant used to transfer an eventual runtime
bound through the streamed-search workspace envelope.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedSearch

namespace Asymptotics

open NeighborhoodGraph

/-- Explicit eventual-bound coefficient used to transfer a runtime bound
through the streamed-search workspace envelope. -/
def envelopeTransferCoefficient
    (Q : Type*) [Fintype Q] (workTapeCount runtimeCoefficient : ℕ) : ℕ :=
  6 * WorkspaceAccounting.workspaceCoefficient Q workTapeCount *
    ((runtimeCoefficient + 1) *
      (Nat.log 2 (runtimeCoefficient + 1) + 2))

end Asymptotics

end CertifiedSearch

end TimeSpaceSimulation

end Complexity
