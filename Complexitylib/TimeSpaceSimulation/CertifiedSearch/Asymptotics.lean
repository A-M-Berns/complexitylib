/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.CertifiedSearch.Asymptotics.Defs
import
  Complexitylib.TimeSpaceSimulation.CertifiedSearch.Asymptotics.Internal

/-!
# Asymptotic workspace bound for certified candidate search

An eventual source-runtime bound transfers through the proof-level endpoint
`max n (actualTime n)`. Consequently, the uniform streamed-trial envelope
remains square-root-logarithmic in the advertised time bound.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedSearch

namespace Asymptotics

open NeighborhoodGraph

/-- If the source runtime is `O(T)` and `T` dominates the input length, then
the workspace envelope at the guaranteed search endpoint is
`O(√(T log T))`. -/
theorem trialEnvelopeBits_max_actualTime_isBigO
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fun n => WorkspaceAccounting.trialEnvelopeBits Q workTapeCount
      (max n (actualTime n))) =O
        ComplexityBridge.sqrtLogSpace T :=
  Internal.trialEnvelopeBits_max_actualTime_isBigO_internal
    Q workTapeCount htime hT

end Asymptotics

end CertifiedSearch

end TimeSpaceSimulation

end Complexity
