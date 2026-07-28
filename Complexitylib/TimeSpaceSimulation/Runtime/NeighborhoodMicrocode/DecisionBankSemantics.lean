/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.DecisionBankSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.DecisionBankSemantics.Internal

/-!
# Retained catalytic-bank semantics for the two decision queries

The state root is evaluated from zero into the last register. The verdict
root is then evaluated over that completed bank into register zero. These
theorems show that the second traversal preserves the first result and that
reading `(last, zero)` gives exactly `Residue.profileDecision.result`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace DecisionBankSemantics

open NeighborhoodExecutableEvaluation

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}

/-- The first zero-bank query puts the state-root value in the last
register. -/
theorem stateBank_last
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    stateBank instanceData (Fin.last (graphFanIn workTapeCount)) =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result.1 :=
  Internal.stateBank_last_internal instanceData

/-- Every non-output register remains zero after the first query. -/
theorem stateBank_eq_zero_of_ne
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (register : Fin (graphFanIn workTapeCount + 1))
    (hne : register ≠ Fin.last (graphFanIn workTapeCount)) :
    stateBank instanceData register =
      Residue.zeroValue tm instanceData.blockLength :=
  Internal.stateBank_eq_zero_of_ne_internal instanceData register hne

/-- Every coordinate of the completed state-root bank is a canonical
representative. -/
theorem stateBank_canonical
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    ∀ register chunk,
      stateBank instanceData register chunk <
        modulus tm instanceData.blockLength :=
  Internal.stateBank_canonical_internal instanceData

/-- Reinitializing and evaluating the verdict root at register zero leaves
the saved state root in the last register. -/
theorem decisionBank_last
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    decisionBank instanceData (Fin.last (graphFanIn workTapeCount)) =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result.1 :=
  Internal.decisionBank_last_internal instanceData

/-- The retained-bank verdict query puts the verdict-root value in register
zero. -/
theorem decisionBank_verdict
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    decisionBank instanceData (verdictOutput workTapeCount) =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result.2 :=
  Internal.decisionBank_verdict_internal instanceData

/-- Reading `(last, zero)` from the retained bank is exactly the ordinary
two-query result. -/
theorem decisionResult_eq_profileDecision
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    decisionResult instanceData =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result :=
  Internal.decisionResult_eq_profileDecision_internal instanceData

end DecisionBankSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
