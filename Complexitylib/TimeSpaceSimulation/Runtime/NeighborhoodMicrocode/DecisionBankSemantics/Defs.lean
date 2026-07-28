/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Defs

/-!
# Pure catalytic-bank states for the two decision queries

The first query starts from the ordinary zero bank and writes the state root
to the distinguished last register. The second query retains that completed
bank, writes the verdict root to register zero, and therefore keeps both
decision values available at once.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace DecisionBankSemantics

open NeighborhoodExecutableEvaluation NeighborhoodEvaluator
open TreeEval CookMertz

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}

/-- Initial scheduler state for the state-consistency root query. -/
def stateInitial
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodScheduler.State tm instanceData :=
  NeighborhoodScheduler.Decision.queryInitial
    (NeighborhoodEvaluator.stateRoot instanceData.guess)

/-- Complete catalytic bank after evaluating the state-consistency root. -/
def stateBank
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Residue.Registers tm instanceData.blockLength :=
  (NeighborhoodScheduler.run (stateInitial instanceData)).registers

/-- Register zero, reserved for the verdict root in the retained bank. -/
def verdictOutput (workTapeCount : ℕ) :
    Fin (graphFanIn workTapeCount + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩

/-- Reinitialized verdict-root query over the completed state-root bank. -/
def verdictInitial
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodScheduler.State tm instanceData :=
  NeighborhoodScheduler.State.initial
    instanceData.horizon
    (NeighborhoodEvaluator.verdictRoot
      instanceData.guess instanceData.blockLength)
    (PrimeField.Runtime.normalize
      (NeighborhoodScheduler.fieldModulus instanceData) 1)
    (verdictOutput workTapeCount)
    (stateBank instanceData)

/-- Complete retained bank after both decision-root queries. -/
def decisionBank
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Residue.Registers tm instanceData.blockLength :=
  (NeighborhoodScheduler.run (verdictInitial instanceData)).registers

/-- The state and verdict values read from `(last, zero)` after both queries. -/
def decisionResult
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    ResidueValue tm instanceData.blockLength ×
      ResidueValue tm instanceData.blockLength :=
  (decisionBank instanceData (Fin.last (graphFanIn workTapeCount)),
    decisionBank instanceData (verdictOutput workTapeCount))

end DecisionBankSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
