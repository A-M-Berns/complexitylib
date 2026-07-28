/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.CertifiedSearch
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.InstanceBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrialInstance.Defs

/-!
# Canonical runtime instance for one neighborhood trial -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodTrialInstance
namespace Internal

open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- Every canonical runtime movement code passes the source-center anchor.

The enumeration fixes all initial centers to zero, exactly matching the
library Turing-machine initial configuration. -/
theorem initialCheck_instance_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Consistency.initialCheck tm instanceData.x instanceData.blockLength
        instanceData.guess = true := by
  rw [Consistency.initialCheck_eq_true_iff]
  intro tape
  rw [NeighborhoodProgram.InstanceBounds.guess_initialCenter_eq_zero
    instanceData tape]
  unfold Consistency.sourceCenter headBlock blockIndex
  unfold tapeAt
  split
  · simp
  · split <;> simp

/-- On a canonical runtime instance, the complete consistency predicate is
exactly the streamed conjunction of interval-boundary checks. -/
theorem passes_instance_eq_boundaryChecks_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (provider :
      Consistency.InputProvider tm instanceData.blockLength
        instanceData.horizon) :
    Consistency.passes tm instanceData.x instanceData.blockLength
        provider instanceData.guess =
      (List.finRange instanceData.horizon).all fun interval =>
        Consistency.boundaryCheck tm instanceData.blockLength provider
          instanceData.guess interval := by
  simp [Consistency.passes, initialCheck_instance_internal tm instanceData]

@[simp] theorem ofCode_x_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).x = input :=
  rfl

@[simp] theorem ofCode_candidateTime_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).candidateTime =
      candidate :=
  rfl

@[simp] theorem ofCode_blockLength_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).blockLength =
      WorkspaceAccounting.blockLength candidate :=
  rfl

@[simp] theorem ofCode_horizon_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).horizon =
      WorkspaceAccounting.horizon candidate :=
  rfl

@[simp] theorem ofCode_guess_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).guess =
      CertifiedOutcome.decodedGuess
        workTapeCount candidate code hcode :=
  rfl

@[simp] theorem ofCode_guessCode_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).guessCode =
      code :=
  rfl

@[simp] theorem ofCode_encoding_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).encoding =
      NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
        order (WorkspaceAccounting.blockLength candidate) :=
  rfl

@[simp] theorem fieldModulus_ofCode_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    NeighborhoodScheduler.fieldModulus
        (ofCode tm order input candidate code hinput hcode) =
      NeighborhoodExecutableEvaluation.modulus tm
        (WorkspaceAccounting.blockLength candidate) :=
  rfl

theorem fieldModulus_ofCode_eq_canonicalModulus_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    NeighborhoodScheduler.fieldModulus
        (ofCode tm order input candidate code hinput hcode) =
      CandidateParameters.canonicalModulus
        tm.Q workTapeCount candidate := by
  unfold NeighborhoodScheduler.fieldModulus
  unfold NeighborhoodExecutableEvaluation.modulus
  unfold CandidateParameters.canonicalModulus
  unfold CandidateParameters.degreeEndpoint
  unfold NeighborhoodExecutableEvaluation.payloadWidth
  rw [ComputationGraph.CompactEncoding.width_eq]
  rfl

theorem schedulerDecisionResult_eq_profileDecision_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    schedulerDecisionResult tm instanceData =
      (NeighborhoodExecutableEvaluation.Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result :=
  NeighborhoodScheduler.Decision.schedulerRun_profileDecision

theorem schedulerDecisionSnapshot_eq_decodedDecisionSnapshot_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    schedulerDecisionSnapshot tm instanceData =
      NeighborhoodExecutableEvaluation.Residue.decodedDecisionSnapshot
        tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess := by
  unfold schedulerDecisionSnapshot
  unfold
    NeighborhoodExecutableEvaluation.Residue.decodedDecisionSnapshot
  rw [schedulerDecisionResult_eq_profileDecision_internal]

theorem schedulerNodeContent_eq_nodeCallback_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node : Node workTapeCount) :
    schedulerNodeContent tm instanceData node =
      NeighborhoodExecutableEvaluation.Residue.nodeCallback
        tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess node := by
  unfold schedulerNodeContent
  dsimp only
  unfold NeighborhoodScheduler.Decision.queryInitial
  unfold NeighborhoodScheduler.Decision.zeroRegisters
  unfold NeighborhoodExecutableEvaluation.Residue.nodeCallback
  unfold NeighborhoodExecutableEvaluation.Residue.profileNode
  rw [NeighborhoodScheduler.schedulerRun_profileEvaluate]

theorem engineSnapshot_ofCode_eq_scheduler_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    ((NeighborhoodExecutableEvaluation.Residue.engineFamily
        tm order).engine input candidate).snapshot
        (CertifiedOutcome.decodedGuess
          workTapeCount candidate code hcode) =
      some
        (schedulerDecisionSnapshot tm
          (ofCode tm order input candidate code hinput hcode)) := by
  rw [schedulerDecisionSnapshot_eq_decodedDecisionSnapshot_internal]
  rfl

theorem engineNode_ofCode_eq_scheduler_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate)
    (node : Node workTapeCount) :
    ((NeighborhoodExecutableEvaluation.Residue.engineFamily
        tm order).engine input candidate).node
        (CertifiedOutcome.decodedGuess
          workTapeCount candidate code hcode) node =
      schedulerNodeContent tm
        (ofCode tm order input candidate code hinput hcode) node := by
  rw [schedulerNodeContent_eq_nodeCallback_internal]
  rfl

theorem schedulerNodeCallback_ofCode_eq_engineNode_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate)
    (node : Node workTapeCount) :
    let instanceData :=
      ofCode tm order input candidate code hinput hcode
    schedulerNodeCallback tm instanceData instanceData.guess node =
      ((NeighborhoodExecutableEvaluation.Residue.engineFamily
        tm order).engine input candidate).node
          (CertifiedOutcome.decodedGuess
            workTapeCount candidate code hcode) node := by
  dsimp only
  unfold schedulerNodeCallback
  exact (engineNode_ofCode_eq_scheduler_internal
    tm order input candidate code hinput hcode node).symm

theorem schedulerProvider_ofCode_eq_engine_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    let instanceData :=
      ofCode tm order input candidate code hinput hcode
    EvaluatedProvider.provider (schedulerNodeCallback tm instanceData)
        instanceData.guess =
      EvaluatedProvider.provider
        ((NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order).engine input candidate).node
        (CertifiedOutcome.decodedGuess
          workTapeCount candidate code hcode) := by
  dsimp only
  change
    EvaluatedProvider.provider
        (schedulerNodeCallback tm
          (ofCode tm order input candidate code hinput hcode))
        (CertifiedOutcome.decodedGuess
          workTapeCount candidate code hcode) =
      EvaluatedProvider.provider
        ((NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order).engine input candidate).node
        (CertifiedOutcome.decodedGuess
          workTapeCount candidate code hcode)
  funext interval
  have hinputAt :
      ∀ index : PredecessorIndex workTapeCount,
        EvaluatedProvider.inputAt?
            (schedulerNodeCallback tm
              (ofCode tm order input candidate code hinput hcode))
            (CertifiedOutcome.decodedGuess
              workTapeCount candidate code hcode) interval index =
          EvaluatedProvider.inputAt?
            ((NeighborhoodExecutableEvaluation.Residue.engineFamily
              tm order).engine input candidate).node
            (CertifiedOutcome.decodedGuess
              workTapeCount candidate code hcode) interval index := by
    intro index
    unfold EvaluatedProvider.inputAt?
    congr 1
    funext node
    exact schedulerNodeCallback_ofCode_eq_engineNode_internal
      tm order input candidate code hinput hcode node
  unfold EvaluatedProvider.provider
  simp_rw [hinputAt]
  split <;> rename_i h
  · split <;> rename_i h'
    · rfl
    · exact (h' h).elim
  · split <;> rename_i h'
    · exact (h h').elim
    · rfl

private theorem passes_congr_provider_at_guess
    (tm : TM workTapeCount) (input : List Bool)
    (blockLength : ℕ)
    (provider₁ provider₂ :
      Consistency.InputProvider tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (hprovider : provider₁ guess = provider₂ guess) :
    Consistency.passes tm input blockLength provider₁ guess =
      Consistency.passes tm input blockLength provider₂ guess := by
  have hboundary :
      (fun interval =>
        Consistency.boundaryCheck
          tm blockLength provider₁ guess interval) =
      (fun interval =>
        Consistency.boundaryCheck
          tm blockLength provider₂ guess interval) := by
    funext interval
    unfold Consistency.boundaryCheck
    rw [congrFun hprovider interval]
  unfold Consistency.passes
  rw [hboundary]

/-- Once the movement code is known to be in range, the certified trial
outcome is exactly the local-consistency branch followed by the concrete
scheduler's decoded decision snapshot. -/
theorem outcome_eq_of_consistency_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate prime code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    let family :=
      NeighborhoodExecutableEvaluation.Residue.engineFamily tm order
    let engine := family.engine input candidate
    let guess :=
      CertifiedOutcome.decodedGuess
        workTapeCount candidate code hcode
    let instanceData :=
      ofCode tm order input candidate code hinput hcode
    CertifiedOutcome.outcome
        tm family input candidate prime code =
      match
        Consistency.passes tm input
          (CertifiedOutcome.blockLength candidate)
          (EvaluatedProvider.provider engine.node) guess
      with
      | false => none
      | true =>
          let snapshot :=
            schedulerDecisionSnapshot tm instanceData
          if snapshot.state = tm.qhalt then
            CertifiedTrial.decodeVerdict snapshot.verdict
          else
            none := by
  dsimp only
  unfold CertifiedOutcome.outcome
  rw [dif_pos hcode]
  dsimp only
  rw [engineSnapshot_ofCode_eq_scheduler_internal
    tm order input candidate code hinput hcode]
  simp
  rfl

/-- At an in-range movement code, the abstract certified outcome can be
computed using only the concrete scheduler-backed consistency provider and
the concrete scheduler's decoded decision snapshot. -/
theorem outcome_eq_of_scheduler_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate prime code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    let family :=
      NeighborhoodExecutableEvaluation.Residue.engineFamily tm order
    let instanceData :=
      ofCode tm order input candidate code hinput hcode
    CertifiedOutcome.outcome
        tm family input candidate prime code =
      match
        Consistency.passes tm input
          (CertifiedOutcome.blockLength candidate)
          (EvaluatedProvider.provider
            (schedulerNodeCallback tm instanceData))
          instanceData.guess
      with
      | false => none
      | true =>
          let snapshot :=
            schedulerDecisionSnapshot tm instanceData
          if snapshot.state = tm.qhalt then
            CertifiedTrial.decodeVerdict snapshot.verdict
          else
            none := by
  dsimp only
  rw [outcome_eq_of_consistency_internal
    tm order input candidate prime code hinput hcode]
  have hprovider := schedulerProvider_ofCode_eq_engine_internal
    tm order input candidate code hinput hcode
  have hpasses := passes_congr_provider_at_guess
    tm input (CertifiedOutcome.blockLength candidate)
    (EvaluatedProvider.provider
      ((NeighborhoodExecutableEvaluation.Residue.engineFamily
        tm order).engine input candidate).node)
    (EvaluatedProvider.provider
      (schedulerNodeCallback tm
        (ofCode tm order input candidate code hinput hcode)))
    (CertifiedOutcome.decodedGuess
      workTapeCount candidate code hcode)
    hprovider.symm
  rw [hpasses]
  rw [ofCode_guess_internal]
  rfl

end Internal
end NeighborhoodTrialInstance
end Runtime
end TimeSpaceSimulation
end Complexity
