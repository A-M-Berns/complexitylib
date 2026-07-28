/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.FiniteEncoding
import
  Complexitylib.TimeSpaceSimulation.Runtime.CertifiedOutcome.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Defs

/-!
# Canonical runtime instance for one neighborhood trial

This definitions layer packages the streamed input, candidate, and bounded
movement code into the exact `ResidueInstance` consumed by the concrete
neighborhood scheduler. The block length, horizon, finite encoding, and typed
guess are all derived canonically rather than supplied as independent data.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodTrialInstance

open NeighborhoodGraph

/-- Canonical scheduler instance decoded from one in-range movement code. -/
def ofCode
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    NeighborhoodProgram.ResidueInstance tm where
  x := input
  candidateTime := candidate
  inputLength_le := hinput
  blockLength := WorkspaceAccounting.blockLength candidate
  encoding :=
    NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
      order (WorkspaceAccounting.blockLength candidate)
  positive := WorkspaceAccounting.blockLength_pos candidate
  horizon := WorkspaceAccounting.horizon candidate
  guess :=
    CertifiedOutcome.decodedGuess
      workTapeCount candidate code hcode
  guessCode := code
  guessCode_lt := hcode
  guess_eq := by
    rfl
  blockLength_eq := by
    rfl
  horizon_eq := by
    rfl

/-- Pair of root residue values produced by the exact-rank decision
scheduler. -/
def schedulerDecisionResult
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength ×
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength :=
  NeighborhoodScheduler.Decision.result
    (NeighborhoodScheduler.Decision.run
      (NeighborhoodScheduler.Decision.initial
        (instanceData := instanceData)))

/-- Decode the scheduler's two terminal root values as the decision snapshot
used by the certified trial semantics. -/
def schedulerDecisionSnapshot
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    DecisionRecovery.Snapshot tm.Q :=
  let result := schedulerDecisionResult tm instanceData
  { state :=
      (NeighborhoodExecutableEvaluation.Residue.decodeValue
        tm instanceData.blockLength instanceData.encoding
          instanceData.positive result.1).state
    verdict :=
      (NeighborhoodExecutableEvaluation.Residue.decodeValue
        tm instanceData.blockLength instanceData.encoding
          instanceData.positive result.2).cells
        (DecisionRecovery.verdictOffset
          instanceData.blockLength instanceData.positive) }

/-- Compact node content obtained by running the concrete scheduler from a
zero bank on one graph-node query and decoding its distinguished root
coordinate. -/
def schedulerNodeContent
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node : Node workTapeCount) :
    Option
      (NeighborhoodContent.Content
        instanceData.blockLength tm.Q) :=
  let final :=
    NeighborhoodScheduler.run
      (NeighborhoodScheduler.Decision.queryInitial
        (instanceData := instanceData) (.graph node))
  some
    (NeighborhoodExecutableEvaluation.Residue.decodeValue
      tm instanceData.blockLength instanceData.encoding
        instanceData.positive
        (final.registers
          (Fin.last
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))))

/-- Runtime node callback obtained by rerunning the concrete scheduler for
each requested graph node. The center guess argument is already fixed by the
canonical residue instance, so the callback ignores any separately supplied
guess. -/
def schedulerNodeCallback
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Guess.EvaluatedProvider.NodeContentCallback workTapeCount tm
      instanceData.blockLength instanceData.horizon :=
  fun _ node => schedulerNodeContent tm instanceData node

end NeighborhoodTrialInstance
end Runtime
end TimeSpaceSimulation
end Complexity
