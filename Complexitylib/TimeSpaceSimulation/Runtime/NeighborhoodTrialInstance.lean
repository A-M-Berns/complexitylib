/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrialInstance.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrialInstance.Internal

/-!
# Canonical runtime instance for one neighborhood trial

This module exposes the projection and semantic bridge used by the concrete
trial kernel. An in-range streamed movement code determines one canonical
residue-scheduler instance, whose exact-rank result decodes to the same
snapshot inspected by `CertifiedOutcome.outcome`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodTrialInstance

open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- Every canonical runtime movement code satisfies the finite
source-configuration anchor. The remaining consistency work therefore
consists only of the streamed interval-boundary checks. -/
theorem initialCheck_instance
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Consistency.initialCheck tm instanceData.x instanceData.blockLength
        instanceData.guess = true :=
  Internal.initialCheck_instance_internal tm instanceData

/-- For a canonical runtime movement code, consistency reduces exactly to
the finite interval-boundary scan; the initial source anchor is automatic. -/
theorem passes_instance_eq_boundaryChecks
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (provider :
      Consistency.InputProvider tm instanceData.blockLength
        instanceData.horizon) :
    Consistency.passes tm instanceData.x instanceData.blockLength
        provider instanceData.guess =
      (List.finRange instanceData.horizon).all fun interval =>
        Consistency.boundaryCheck tm instanceData.blockLength provider
          instanceData.guess interval :=
  Internal.passes_instance_eq_boundaryChecks_internal
    tm instanceData provider

@[simp] theorem ofCode_x
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).x = input :=
  Internal.ofCode_x_internal
    tm order input candidate code hinput hcode

@[simp] theorem ofCode_candidateTime
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).candidateTime =
      candidate :=
  Internal.ofCode_candidateTime_internal
    tm order input candidate code hinput hcode

@[simp] theorem ofCode_blockLength
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).blockLength =
      WorkspaceAccounting.blockLength candidate :=
  Internal.ofCode_blockLength_internal
    tm order input candidate code hinput hcode

@[simp] theorem ofCode_horizon
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).horizon =
      WorkspaceAccounting.horizon candidate :=
  Internal.ofCode_horizon_internal
    tm order input candidate code hinput hcode

@[simp] theorem ofCode_guess
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
  Internal.ofCode_guess_internal
    tm order input candidate code hinput hcode

@[simp] theorem ofCode_guessCode
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate code : ℕ)
    (hinput : input.length ≤ candidate)
    (hcode :
      code < CertifiedOutcome.guessCount workTapeCount candidate) :
    (ofCode tm order input candidate code hinput hcode).guessCode =
      code :=
  Internal.ofCode_guessCode_internal
    tm order input candidate code hinput hcode

@[simp] theorem ofCode_encoding
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
  Internal.ofCode_encoding_internal
    tm order input candidate code hinput hcode

@[simp] theorem fieldModulus_ofCode
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
  Internal.fieldModulus_ofCode_internal
    tm order input candidate code hinput hcode

/-- The scheduler modulus is exactly the canonical modulus computed by the
uniform candidate-parameter program. -/
theorem fieldModulus_ofCode_eq_canonicalModulus
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
        tm.Q workTapeCount candidate :=
  Internal.fieldModulus_ofCode_eq_canonicalModulus_internal
    tm order input candidate code hinput hcode

/-- Exact-rank scheduler execution produces the residue evaluator's two root
values. -/
theorem schedulerDecisionResult_eq_profileDecision
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    schedulerDecisionResult tm instanceData =
      (NeighborhoodExecutableEvaluation.Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result :=
  Internal.schedulerDecisionResult_eq_profileDecision_internal
    tm instanceData

/-- Decoding the scheduler roots yields the certified engine's decision
snapshot. -/
theorem schedulerDecisionSnapshot_eq_decodedDecisionSnapshot
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    schedulerDecisionSnapshot tm instanceData =
      NeighborhoodExecutableEvaluation.Residue.decodedDecisionSnapshot
        tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess :=
  Internal.schedulerDecisionSnapshot_eq_decodedDecisionSnapshot_internal
    tm instanceData

/-- A concrete zero-bank scheduler query decodes to the certified engine's
node callback at the instance guess. -/
theorem schedulerNodeContent_eq_nodeCallback
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node : Node workTapeCount) :
    schedulerNodeContent tm instanceData node =
      NeighborhoodExecutableEvaluation.Residue.nodeCallback
        tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess node :=
  Internal.schedulerNodeContent_eq_nodeCallback_internal
    tm instanceData node

/-- The canonical certified engine returns the concrete scheduler snapshot
for the same decoded movement code. -/
theorem engineSnapshot_ofCode_eq_scheduler
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
          (ofCode tm order input candidate code hinput hcode)) :=
  Internal.engineSnapshot_ofCode_eq_scheduler_internal
    tm order input candidate code hinput hcode

/-- At the decoded movement guess, the canonical engine's node callback is
exactly the compact content returned by a concrete scheduler query. -/
theorem engineNode_ofCode_eq_scheduler
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
        (ofCode tm order input candidate code hinput hcode) node :=
  Internal.engineNode_ofCode_eq_scheduler_internal
    tm order input candidate code hinput hcode node

/-- At the canonical decoded guess, the scheduler-backed callback is
pointwise equal to the certified engine callback. -/
theorem schedulerNodeCallback_ofCode_eq_engineNode
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
            workTapeCount candidate code hcode) node :=
  Internal.schedulerNodeCallback_ofCode_eq_engineNode_internal
    tm order input candidate code hinput hcode node

/-- The concrete scheduler callback supplies exactly the same consistency
inputs as the certified engine at the canonical decoded guess. -/
theorem schedulerProvider_ofCode_eq_engine
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
          workTapeCount candidate code hcode) :=
  Internal.schedulerProvider_ofCode_eq_engine_internal
    tm order input candidate code hinput hcode

/-- For an in-range code, the certified semantic outcome consists exactly of
the local-consistency test followed by decoding the concrete scheduler
snapshot. -/
theorem outcome_eq_of_consistency
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
            none :=
  Internal.outcome_eq_of_consistency_internal
    tm order input candidate prime code hinput hcode

/-- For an in-range code, both runtime branches of the certified outcome are
computed by the concrete scheduler: node queries supply the consistency
provider and the exact-rank decision query supplies the final snapshot. -/
theorem outcome_eq_of_scheduler
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
            none :=
  Internal.outcome_eq_of_scheduler_internal
    tm order input candidate prime code hinput hcode

end NeighborhoodTrialInstance
end Runtime
end TimeSpaceSimulation
end Complexity
