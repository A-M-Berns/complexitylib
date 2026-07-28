/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluator
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.EvaluatedProvider
import
  Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Evaluation
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding

/-!
# Correctness internals for executable neighborhood evaluation

The proofs first certify the explicit finite encoding. They then identify the
executable grouped callback with the logarithmic grouped polynomial lift, only
inside the proof layer. This supplies line compatibility to the direct
profiled traversal without placing a tree or polynomial in a runtime
definition.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodExecutableEvaluation

open NeighborhoodGraph
open TreeEval CookMertz

namespace Internal

theorem firstTrueFin_oneHot_internal {count : ℕ}
    (default value : Fin count) :
    firstTrueFin default (fun candidate =>
      decide (candidate = value)) = value := by
  unfold firstTrueFin
  generalize hfind :
    (List.finRange count).find?
      (fun candidate => decide (candidate = value)) = found
  cases found with
  | none =>
      have hnone := List.find?_eq_none.mp hfind
      have hmem : value ∈ List.finRange count :=
        List.mem_finRange value
      have himpossible := hnone value hmem
      simp at himpossible
  | some selected =>
      have hselected := List.find?_some hfind
      simp at hselected
      simp [hselected]

theorem decodeGamma_oneHot_internal (value : Γ) :
    decodeGamma (fun candidate => decide (candidate = value)) =
      value := by
  cases value <;> decide

theorem bitsAt_encodeBits_internal
    (encoding : FiniteEncoding tm blockLength)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q)
    (coordinate :
      ComputationGraph.CompactEncoding.Coordinate blockLength tm.Q) :
    bitsAt encoding (encodeBits encoding value) coordinate =
      ComputationGraph.CompactEncoding.coordinateBits value coordinate := by
  simp [bitsAt, encodeBits]

theorem decodeBits_encodeBits_internal
    (encoding : FiniteEncoding tm blockLength)
    (defaultState : tm.Q) (hpositive : 0 < blockLength)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q) :
    decodeBits encoding defaultState hpositive
        (encodeBits encoding value) =
      value := by
  apply ComputationGraph.CompactContent.Content.ext
  · simp only [decodeBits, bitsAt_encodeBits_internal,
      ComputationGraph.CompactEncoding.coordinateBits]
    rw [show
      (fun index =>
        decide (encoding.state.symm index = value.state)) =
      (fun candidate =>
        decide (candidate = encoding.state value.state)) by
      funext index
      by_cases hstate :
          encoding.state.symm index = value.state
      · have hindex :
            index = encoding.state value.state :=
          encoding.state.symm_apply_eq.mp hstate
        simp [hindex]
      · have hindex :
            index ≠ encoding.state value.state := by
          intro heq
          exact hstate
            (encoding.state.symm_apply_eq.mpr heq)
        simp [hstate, hindex]]
    simpa using congrArg encoding.state.symm
      (firstTrueFin_oneHot_internal
        (encoding.state defaultState) (encoding.state value.state))
  · apply Fin.ext
    simp only [decodeBits, bitsAt_encodeBits_internal,
      ComputationGraph.CompactEncoding.coordinateBits]
    exact congrArg Fin.val
      (firstTrueFin_oneHot_internal
        ⟨0, hpositive⟩ value.headRemainder)
  · funext offset
    simp only [decodeBits, bitsAt_encodeBits_internal,
      ComputationGraph.CompactEncoding.coordinateBits]
    exact decodeGamma_oneHot_internal (value.cells offset)

theorem booleanCombine_encoded_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        NeighborhoodContent.Content blockLength tm.Q) :
    booleanCombine tm x blockLength encoding hpositive
        tape slot timeBlock
        (fun child => encodeBits encoding (children child)) =
      encodeBits encoding
        (NeighborhoodContent.localNodeFunction
          tm x blockLength hpositive timeBlock tape slot fun index =>
            children (predecessorIndexEquiv workTapeCount index)) := by
  unfold booleanCombine
  congr 2
  funext index
  exact decodeBits_encodeBits_internal
    encoding tm.qstart hpositive
      (children (predecessorIndexEquiv workTapeCount index))

theorem combineValue_encoded_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        Fin (payloadWidth tm blockLength) → Bool) :
    combineValue tm x blockLength encoding hpositive
        tape slot timeBlock
        (fun child =>
          PrimeGrouped.Logarithmic.encodeValue
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount)
            (children child)) =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength)
        (graphFanIn workTapeCount)
        (booleanCombine tm x blockLength encoding hpositive
          tape slot timeBlock children) := by
  unfold combineValue PrimeGrouped.Logarithmic.encodeValue
  exact
    GroupedExtension.Evaluation.evaluateNode_encoded
      (PrimeGrouped.Logarithmic.codebook
        (payloadWidth tm blockLength) (graphFanIn workTapeCount))
      (PrimeGrouped.Logarithmic.layout
        (payloadWidth tm blockLength) (graphFanIn workTapeCount))
      (booleanCombine tm x blockLength encoding hpositive
        tape slot timeBlock)
      children

private theorem booleanNodeValue_eq_encodeBits
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (node : Node workTapeCount) :
    NeighborhoodGraph.nodeValue tm x blockLength
        (sourceBits tm x blockLength encoding hpositive)
        (booleanCombine tm x blockLength encoding hpositive)
        node =
      encodeBits encoding
        (NeighborhoodContent.nodeContent
          tm x blockLength hpositive node) := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [NeighborhoodGraph.nodeValue]
          rfl
      | computation tape slot timeBlock =>
          rw [NeighborhoodGraph.nodeValue]
          have hchildren :
              (fun index =>
                NeighborhoodGraph.nodeValue tm x blockLength
                  (sourceBits tm x blockLength encoding hpositive)
                  (booleanCombine tm x blockLength encoding hpositive)
                  (predecessorAt
                    tm x blockLength timeBlock index)) =
                (fun index =>
                  encodeBits encoding
                    (NeighborhoodContent.predecessorContents
                      tm x blockLength timeBlock hpositive
                      ((predecessorIndexEquiv workTapeCount).symm
                        index))) := by
            funext index
            rw [ih _
              (predecessorAt_rank_lt
                tm x blockLength timeBlock tape slot index)]
            rfl
          rw [hchildren]
          calc
            booleanCombine tm x blockLength encoding hpositive
                tape slot timeBlock
                (fun index =>
                  encodeBits encoding
                    (NeighborhoodContent.predecessorContents
                      tm x blockLength timeBlock hpositive
                      ((predecessorIndexEquiv workTapeCount).symm
                        index))) =
                encodeBits encoding
                  (NeighborhoodContent.localNodeFunction
                    tm x blockLength hpositive timeBlock tape slot
                    fun index =>
                      (NeighborhoodContent.predecessorContents
                        tm x blockLength timeBlock hpositive)
                        index) := by
              simpa using
                booleanCombine_encoded_internal
                  tm x blockLength encoding hpositive
                  tape slot timeBlock
                  (fun index =>
                    NeighborhoodContent.predecessorContents
                      tm x blockLength timeBlock hpositive
                      ((predecessorIndexEquiv workTapeCount).symm
                        index))
            _ = encodeBits encoding
                (NeighborhoodContent.nodeContent tm x blockLength
                  hpositive (.computation tape slot timeBlock)) := by
              exact congrArg (encodeBits encoding)
                (NeighborhoodContent.localNodeFunction_semantic
                  tm x blockLength timeBlock hpositive tape slot)

private theorem groupedUnroll_eq_liftTree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (node : Node workTapeCount) :
    NeighborhoodGraph.unroll tm x blockLength
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        node =
      PrimeGrouped.Logarithmic.liftTree
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (NeighborhoodGraph.unroll tm x blockLength
          (sourceBits tm x blockLength encoding hpositive)
          (booleanCombine tm x blockLength encoding hpositive)
          node) := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [NeighborhoodGraph.unroll, NeighborhoodGraph.unroll]
          rfl
      | computation tape slot timeBlock =>
          rw [NeighborhoodGraph.unroll, NeighborhoodGraph.unroll]
          unfold PrimeGrouped.Logarithmic.liftTree
          rw [GroupedExtension.liftTree.eq_def]
          congr 1
          · funext index
            exact ih _
              (predecessorAt_rank_lt
                tm x blockLength timeBlock tape slot index)
          · exact
              GroupedExtension.Evaluation.evaluateNode_eq_polynomialNode
                (PrimeGrouped.Logarithmic.codebook
                  (payloadWidth tm blockLength)
                  (graphFanIn workTapeCount))
                (PrimeGrouped.Logarithmic.layout
                  (payloadWidth tm blockLength)
                  (graphFanIn workTapeCount))
                (booleanCombine tm x blockLength encoding hpositive
                  tape slot timeBlock)

theorem groupedUnroll_lineCompatible_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (node : Node workTapeCount) :
    LineCompatible
      (PrimeGrouped.Logarithmic.units
        (payloadWidth tm blockLength) (graphFanIn workTapeCount))
      (NeighborhoodGraph.unroll tm x blockLength
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        node) := by
  rw [groupedUnroll_eq_liftTree]
  exact PrimeGrouped.Logarithmic.liftTree_lineCompatible
    (payloadWidth tm blockLength) (graphFanIn workTapeCount)
      (NeighborhoodGraph.unroll tm x blockLength
        (sourceBits tm x blockLength encoding hpositive)
        (booleanCombine tm x blockLength encoding hpositive)
        node)

set_option maxHeartbeats 1000000 in
private theorem combineValue_lineIdentity
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot) (interval : ℕ) :
    ∀ (direction base :
      Fin (graphFanIn workTapeCount) →
        EvaluationValue tm blockLength),
      ((PrimeGrouped.Logarithmic.units
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)).map
        fun (unit : (EvaluationField tm blockLength)ˣ) =>
          combineValue tm x blockLength encoding hpositive
            tape slot interval
            (fun register =>
              (unit : EvaluationField tm blockLength) •
                direction register + base register)).sum =
        -combineValue tm x blockLength encoding hpositive
          tape slot interval base := by
  let tree :
      Tree (graphFanIn workTapeCount)
        (Fin (payloadWidth tm blockLength) → Bool) :=
    .node (fun _ => .leaf (fun _ => false))
      (booleanCombine tm x blockLength encoding hpositive
        tape slot interval)
  have hline :=
    PrimeGrouped.Logarithmic.liftTree_lineCompatible
      (payloadWidth tm blockLength) (graphFanIn workTapeCount) tree
  have hnode := hline.2
  intro direction base
  simpa [tree, PrimeGrouped.Logarithmic.liftTree,
    GroupedExtension.liftTree, combineValue,
    GroupedExtension.Evaluation.evaluateNode_eq_polynomialNode,
    smul_eq_mul] using hnode direction base

theorem queryUnroll_lineCompatible_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    LineCompatible
      (PrimeGrouped.Logarithmic.units
        (payloadWidth tm blockLength) (graphFanIn workTapeCount))
      (NeighborhoodEvaluator.unroll guess
        (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        fuel node) := by
  induction fuel generalizing node with
  | zero =>
      cases node with
      | failure =>
          simp [NeighborhoodEvaluator.unroll, LineCompatible]
      | graph node =>
          cases node <;>
            simp [NeighborhoodEvaluator.unroll, LineCompatible]
  | succ fuel ih =>
      cases node with
      | failure =>
          simp [NeighborhoodEvaluator.unroll, LineCompatible]
      | graph node =>
          cases node with
          | source tape block =>
              simp [NeighborhoodEvaluator.unroll, LineCompatible]
          | computation tape slot interval =>
              rw [NeighborhoodEvaluator.unroll]
              split
              · exact ⟨fun child => ih _, combineValue_lineIdentity
                  tm x blockLength encoding hpositive
                    tape slot interval⟩
              · simp [LineCompatible]

theorem groupedNodeValue_eq_encoded_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (node : Node workTapeCount) :
    NeighborhoodGraph.nodeValue tm x blockLength
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        node =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent
            tm x blockLength hpositive node)) := by
  calc
    NeighborhoodGraph.nodeValue tm x blockLength
          (sourceValue tm x blockLength encoding hpositive)
          (combineValue tm x blockLength encoding hpositive)
          node =
        (NeighborhoodGraph.unroll tm x blockLength
          (sourceValue tm x blockLength encoding hpositive)
          (combineValue tm x blockLength encoding hpositive)
          node).value :=
      (NeighborhoodGraph.value_unroll
        tm x blockLength
          (sourceValue tm x blockLength encoding hpositive)
          (combineValue tm x blockLength encoding hpositive)
          node).symm
    _ =
        (PrimeGrouped.Logarithmic.liftTree
          (payloadWidth tm blockLength) (graphFanIn workTapeCount)
          (NeighborhoodGraph.unroll tm x blockLength
            (sourceBits tm x blockLength encoding hpositive)
            (booleanCombine tm x blockLength encoding hpositive)
            node)).value := by
      exact congrArg TreeEval.Tree.value
        (groupedUnroll_eq_liftTree
          tm x blockLength encoding hpositive node)
    _ = PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (NeighborhoodGraph.unroll tm x blockLength
          (sourceBits tm x blockLength encoding hpositive)
          (booleanCombine tm x blockLength encoding hpositive)
          node).value :=
      PrimeGrouped.Logarithmic.value_liftTree
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (NeighborhoodGraph.unroll tm x blockLength
          (sourceBits tm x blockLength encoding hpositive)
          (booleanCombine tm x blockLength encoding hpositive)
          node)
    _ = PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (NeighborhoodGraph.nodeValue tm x blockLength
          (sourceBits tm x blockLength encoding hpositive)
          (booleanCombine tm x blockLength encoding hpositive)
          node) := by
      exact congrArg
        (PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount))
        (NeighborhoodGraph.value_unroll
          tm x blockLength
            (sourceBits tm x blockLength encoding hpositive)
            (booleanCombine tm x blockLength encoding hpositive)
            node)
    _ = PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent
            tm x blockLength hpositive node)) := by
      exact congrArg
        (PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount))
        (booleanNodeValue_eq_encodeBits
          tm x blockLength encoding hpositive node)

theorem profileNode_result_eq_encoded_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (node : Node workTapeCount)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hrank : node.rank ≤ horizon) :
    (profileNode tm x blockLength encoding hpositive
      horizon guess node).result =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent
            tm x blockLength hpositive node)) := by
  unfold profileNode
  calc
    (NeighborhoodEvaluator.profileEvaluate
        (PrimeGrouped.Logarithmic.units
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount))
        guess (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        horizon (.graph node)).result =
        NeighborhoodGraph.nodeValue tm x blockLength
          (sourceValue tm x blockLength encoding hpositive)
          (combineValue tm x blockLength encoding hpositive)
          node := by
      exact NeighborhoodEvaluator.profileEvaluate_graph_eq_nodeValue
        (PrimeGrouped.Logarithmic.units
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount))
        guess tm x blockLength
        (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        horizon node hvalid hrank (le_refl _)
        (groupedUnroll_lineCompatible_internal
          tm x blockLength encoding hpositive node)
    _ = PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent
            tm x blockLength hpositive node)) :=
      groupedNodeValue_eq_encoded_internal
        tm x blockLength encoding hpositive node

theorem profileDecision_result_eq_encoded_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    (profileDecision tm x blockLength encoding hpositive
      horizon guess).result =
      (PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength) (graphFanIn workTapeCount)
          (encodeBits encoding
            (NeighborhoodContent.nodeContent tm x blockLength hpositive
              (DecisionRecovery.stateNode
                tm x blockLength horizon))),
        PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength) (graphFanIn workTapeCount)
          (encodeBits encoding
            (NeighborhoodContent.nodeContent tm x blockLength hpositive
              (DecisionRecovery.verdictBlockNode
                tm x blockLength horizon)))) := by
  unfold profileDecision
  rw [NeighborhoodEvaluator.profileDecision_result_eq_nodeValues
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    guess tm x blockLength (failureValue tm blockLength)
    (sourceValue tm x blockLength encoding hpositive)
    (combineValue tm x blockLength encoding hpositive)
    hvalid
    (groupedUnroll_lineCompatible_internal
      tm x blockLength encoding hpositive
      (DecisionRecovery.stateNode tm x blockLength horizon))
    (groupedUnroll_lineCompatible_internal
      tm x blockLength encoding hpositive
      (DecisionRecovery.verdictBlockNode tm x blockLength horizon))]
  rw [groupedNodeValue_eq_encoded_internal,
    groupedNodeValue_eq_encoded_internal]

theorem profileState_result_eq_encoded_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    (profileState tm x blockLength encoding hpositive
      horizon guess).result =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent tm x blockLength hpositive
            (DecisionRecovery.stateNode
              tm x blockLength horizon))) := by
  have hpair :=
    congrArg Prod.fst
      (profileDecision_result_eq_encoded_internal
        tm x blockLength encoding hpositive horizon guess hvalid)
  simpa [profileDecision, profileState] using hpair

theorem profileVerdict_result_eq_encoded_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    (profileVerdict tm x blockLength encoding hpositive
      horizon guess).result =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent tm x blockLength hpositive
            (DecisionRecovery.verdictBlockNode
              tm x blockLength horizon))) := by
  have hpair :=
    congrArg Prod.snd
      (profileDecision_result_eq_encoded_internal
        tm x blockLength encoding hpositive horizon guess hvalid)
  simpa [profileDecision, profileVerdict] using hpair

theorem profileDecision_peakFrames_le_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    (profileDecision tm x blockLength encoding hpositive
      horizon guess).peakFrames ≤ horizon + 1 := by
  unfold profileDecision
  exact NeighborhoodEvaluator.profileDecision_peakFrames_le
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    guess blockLength (failureValue tm blockLength)
    (sourceValue tm x blockLength encoding hpositive)
    (combineValue tm x blockLength encoding hpositive)

theorem decodeValue_encodeContent_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (value : NeighborhoodContent.Content blockLength tm.Q) :
    decodeValue tm blockLength encoding hpositive
        (PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength) (graphFanIn workTapeCount)
          (encodeBits encoding value)) =
      value := by
  unfold decodeValue
  rw [PrimeGrouped.Logarithmic.Decoding.decodeValue_encodeValue]
  exact decodeBits_encodeBits_internal
    encoding tm.qstart hpositive value

theorem decodedDecisionSnapshot_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    decodedDecisionSnapshot tm x blockLength encoding hpositive
        horizon guess =
      DecisionRecovery.decisionSnapshot
        tm x blockLength hpositive horizon := by
  unfold decodedDecisionSnapshot
  rw [profileDecision_result_eq_encoded_internal
    tm x blockLength encoding hpositive horizon guess hvalid]
  simp only
  rw [decodeValue_encodeContent_internal,
    decodeValue_encodeContent_internal]
  rfl

theorem decodedDecisionSnapshot_eq_of_reachesIn_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon haltTime : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (hle : haltTime ≤ timeBlockStart blockLength horizon) :
    decodedDecisionSnapshot tm x blockLength encoding hpositive
        horizon guess =
      { state := cfg.state
        verdict := cfg.output.cells 1 } := by
  rw [decodedDecisionSnapshot_eq_internal
    tm x blockLength encoding hpositive horizon guess hvalid]
  exact DecisionRecovery.decisionSnapshot_eq_of_reachesIn
    tm x blockLength horizon haltTime hpositive
      cfg hreach hhalt hle

theorem nodeCallback_isPrefixExact_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    Guess.EvaluatedProvider.IsPrefixExact
      tm x blockLength hpositive
      (nodeCallback tm x blockLength encoding hpositive horizon) := by
  unfold nodeCallback
  apply Guess.EvaluatedProvider.directIsPrefixExact_of_nodeValue
  · intro guess interval index
    exact groupedUnroll_lineCompatible_internal
      tm x blockLength encoding hpositive
        (NeighborhoodGraph.predecessor
          tm x blockLength interval.val index)
  · intro guess interval index
    rw [groupedNodeValue_eq_encoded_internal]
    rw [decodeValue_encodeContent_internal]
    rfl

theorem certifiedEngine_isExact_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    (certifiedEngine tm x blockLength encoding hpositive horizon).IsExact
      x hpositive := by
  constructor
  · exact nodeCallback_isPrefixExact_internal
      tm x blockLength encoding hpositive horizon
  · intro guess hvalid
    change some (decodedDecisionSnapshot
      tm x blockLength encoding hpositive horizon guess) =
        some (DecisionRecovery.decisionSnapshot
          tm x blockLength hpositive horizon)
    exact congrArg some
      (decodedDecisionSnapshot_eq_internal
        tm x blockLength encoding hpositive horizon guess hvalid)

theorem ofResidues_toResidues_internal
    (value : EvaluationValue tm blockLength) :
    ofResidues (toResidues value) = value := by
  funext chunk
  exact ZMod.natCast_zmod_val (value chunk)

theorem toResidues_ofResidues_internal
    (value : ResidueValue tm blockLength) (chunk :
      Fin (PrimeGrouped.Logarithmic.chunkCount
        (payloadWidth tm blockLength) (graphFanIn _))) :
    toResidues (ofResidues value) chunk =
      PrimeField.Runtime.normalize
        (modulus tm blockLength) (value chunk) := by
  exact ZMod.val_natCast _ _

namespace ResidueBridge

open NeighborhoodExecutableEvaluation.Residue

@[simp] private theorem coe_runtime_normalize
    (payloadWidth fanIn value : ℕ) :
    (PrimeField.Runtime.normalize
        (fieldModulus payloadWidth fanIn) value :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      (value :
        PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  simp [fieldModulus]

@[simp] private theorem coe_runtime_add
    (payloadWidth fanIn first second : ℕ) :
    (PrimeField.Runtime.add
        (fieldModulus payloadWidth fanIn) first second :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      (first :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) +
        (second :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  simp [fieldModulus]

@[simp] private theorem coe_runtime_sub
    (payloadWidth fanIn first second : ℕ) :
    (PrimeField.Runtime.sub
        (fieldModulus payloadWidth fanIn) first second :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      (first :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) -
        (second :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  simp [fieldModulus]

@[simp] private theorem coe_runtime_mul
    (payloadWidth fanIn first second : ℕ) :
    (PrimeField.Runtime.mul
        (fieldModulus payloadWidth fanIn) first second :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      (first :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) *
        (second :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  simp [fieldModulus]

@[simp] private theorem coe_runtime_inverse
    (payloadWidth fanIn value : ℕ) :
    (PrimeField.Runtime.inverse
        (fieldModulus payloadWidth fanIn) value :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      (value :
        PrimeGrouped.Logarithmic.Field payloadWidth fanIn)⁻¹ := by
  simp [fieldModulus]

private theorem coe_foldProduct
    (payloadWidth fanIn : ℕ) (term : ℕ → ℕ)
    (count accumulator : ℕ) :
    (foldProduct (fieldModulus payloadWidth fanIn)
        term count accumulator :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      GroupedExtension.Evaluation.foldProductRange
        (fun index =>
          (term index :
            PrimeGrouped.Logarithmic.Field payloadWidth fanIn))
        count
        (accumulator :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  induction count generalizing accumulator with
  | zero =>
      rfl
  | succ count ih =>
      rw [foldProduct,
        GroupedExtension.Evaluation.foldProductRange,
        ih, coe_runtime_mul]

theorem coe_productRange_internal
    (payloadWidth fanIn : ℕ) (term : ℕ → ℕ)
    (count : ℕ) :
    (productRange (fieldModulus payloadWidth fanIn)
        term count :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      GroupedExtension.Evaluation.productRange
        (fun index =>
          (term index :
            PrimeGrouped.Logarithmic.Field payloadWidth fanIn))
        count := by
  unfold productRange GroupedExtension.Evaluation.productRange
  rw [coe_foldProduct, coe_runtime_normalize]
  simp

private theorem coe_foldSum
    (payloadWidth fanIn : ℕ) (term : ℕ → ℕ)
    (count accumulator : ℕ) :
    (foldSum (fieldModulus payloadWidth fanIn)
        term count accumulator :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      BooleanExtension.Evaluation.foldRange
        (fun index =>
          (term index :
            PrimeGrouped.Logarithmic.Field payloadWidth fanIn))
        count
        (accumulator :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  induction count generalizing accumulator with
  | zero =>
      rfl
  | succ count ih =>
      rw [foldSum, BooleanExtension.Evaluation.foldRange,
        ih, coe_runtime_add]

theorem coe_sumRange_internal
    (payloadWidth fanIn : ℕ) (term : ℕ → ℕ)
    (count : ℕ) :
    (sumRange (fieldModulus payloadWidth fanIn)
        term count :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      BooleanExtension.Evaluation.sumRange
        (fun index =>
          (term index :
            PrimeGrouped.Logarithmic.Field payloadWidth fanIn))
        count := by
  unfold sumRange BooleanExtension.Evaluation.sumRange
  rw [coe_foldSum, coe_runtime_normalize]
  simp

theorem coe_productList_internal
    (payloadWidth fanIn : ℕ) (values : List ℕ) :
    (productList (fieldModulus payloadWidth fanIn) values :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      (values.map fun value =>
        (value :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn)).prod := by
  induction values with
  | nil =>
      simp [productList]
  | cons value values ih =>
      rw [productList, coe_runtime_mul, ih]
      rfl

private theorem coe_productList_map
    {σ : Type*} (payloadWidth fanIn : ℕ)
    (coordinates : List σ) (term : σ → ℕ) :
    (productList (fieldModulus payloadWidth fanIn)
        (coordinates.map term) :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      (coordinates.map fun coordinate =>
        (term coordinate :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn)).prod := by
  induction coordinates with
  | nil =>
      simp [productList]
  | cons coordinate coordinates ih =>
      rw [List.map_cons, productList, coe_runtime_mul, ih]
      rfl

theorem coe_lagrangeFactor_internal
    (payloadWidth fanIn : ℕ)
    (selected other :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point : ℕ) :
    (lagrangeFactor payloadWidth fanIn
        selected other point :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      GroupedExtension.Evaluation.lagrangeFactorValue
        (PrimeGrouped.Logarithmic.codebook payloadWidth fanIn)
        selected other
        (point :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  by_cases hsame : selected = other
  · simp [lagrangeFactor,
      GroupedExtension.Evaluation.lagrangeFactorValue,
      hsame]
  · simp [lagrangeFactor,
      GroupedExtension.Evaluation.lagrangeFactorValue,
      hsame, coe_runtime_mul,
      coe_runtime_inverse, coe_runtime_sub,
      PrimeGrouped.Logarithmic.codebook_encode]

theorem coe_chunkBasisValue_internal
    (payloadWidth fanIn : ℕ)
    (selected :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point : ℕ) :
    (chunkBasisValue payloadWidth fanIn selected point :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      GroupedExtension.Evaluation.chunkBasisValue
        (PrimeGrouped.Logarithmic.codebook payloadWidth fanIn)
        selected
        (point :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) := by
  unfold chunkBasisValue
  rw [coe_productRange_internal]
  unfold GroupedExtension.Evaluation.chunkBasisValue
  congr 1
  funext code
  exact coe_lagrangeFactor_internal
    payloadWidth fanIn selected
      (GroupedExtension.Evaluation.chunkOfCode
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
        code)
      point

theorem coe_basisValue_internal
    (payloadWidth fanIn : ℕ)
    (assignment :
      Fin fanIn ×
          Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
        GroupedExtension.Chunk
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point :
      Fin fanIn ×
          Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
        ℕ) :
    (basisValue payloadWidth fanIn assignment point :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      GroupedExtension.Evaluation.basisValue finProdFinEquiv
        (PrimeGrouped.Logarithmic.codebook payloadWidth fanIn)
        assignment
        (fun input =>
          (point input :
            PrimeGrouped.Logarithmic.Field payloadWidth fanIn)) := by
  unfold basisValue GroupedExtension.Evaluation.basisValue
  rw [coe_productList_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro coordinate _
  exact coe_chunkBasisValue_internal
    payloadWidth fanIn (assignment coordinate) (point coordinate)

theorem coe_packedNodeValue_internal
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (assignment :
      Fin fanIn ×
          Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
        GroupedExtension.Chunk
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (outputChunk :
      Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    (packedNodeValue payloadWidth fanIn
        combine assignment outputChunk :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      GroupedExtension.packedNodeFunction
        (PrimeGrouped.Logarithmic.codebook payloadWidth fanIn)
        (PrimeGrouped.Logarithmic.layout payloadWidth fanIn)
        combine assignment outputChunk := by
  unfold packedNodeValue
  unfold GroupedExtension.packedNodeFunction
  rw [PrimeGrouped.Logarithmic.codebook_encode]

theorem coe_evaluateNode_internal
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ) :
    (fun outputChunk =>
      (evaluateNode payloadWidth fanIn combine args outputChunk :
        PrimeGrouped.Logarithmic.Field payloadWidth fanIn)) =
      GroupedExtension.Evaluation.evaluateNode
        (PrimeGrouped.Logarithmic.codebook payloadWidth fanIn)
        (PrimeGrouped.Logarithmic.layout payloadWidth fanIn)
        combine
        (fun child chunk =>
          (args child chunk :
            PrimeGrouped.Logarithmic.Field payloadWidth fanIn)) := by
  funext outputChunk
  unfold evaluateNode
  unfold GroupedExtension.Evaluation.evaluateNode
  unfold GroupedExtension.Evaluation.evaluate
  rw [coe_sumRange_internal]
  congr 1
  funext code
  dsimp only
  rw [coe_runtime_mul]
  rw [coe_packedNodeValue_internal,
    coe_basisValue_internal]

end ResidueBridge

theorem combineValueViaResidues_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        EvaluationValue tm blockLength) :
    combineValueViaResidues tm x blockLength encoding hpositive
        tape slot timeBlock children =
      combineValue tm x blockLength encoding hpositive
        tape slot timeBlock children := by
  unfold combineValueViaResidues combineResidues
  unfold ofResidues toResidues
  rw [ResidueBridge.coe_evaluateNode_internal]
  unfold combineValue
  congr 1
  funext child chunk
  exact ZMod.natCast_zmod_val (children child chunk)

private def castResidueRegisters
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs : Residue.Registers tm blockLength) :
    CookMertz.Registers (graphFanIn workTapeCount)
      (EvaluationValue tm blockLength) :=
  fun index => ofResidues (regs index)

private theorem ofResidues_zeroValue
    (tm : TM workTapeCount) (blockLength : ℕ) :
    ofResidues (Residue.zeroValue tm blockLength) =
      (0 : EvaluationValue tm blockLength) := by
  funext chunk
  change
    ((PrimeField.Runtime.normalize
      (modulus tm blockLength) 0 : ℕ) :
        ZMod (modulus tm blockLength)) = 0
  simp

private theorem ofResidues_sourceValue
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    ofResidues
        (Residue.sourceValue
          tm x blockLength encoding hpositive tape block) =
      sourceValue tm x blockLength encoding hpositive tape block := by
  exact ofResidues_toResidues_internal
    (sourceValue tm x blockLength encoding hpositive tape block)

private theorem ofResidues_failureValue
    (tm : TM workTapeCount) (blockLength : ℕ) :
    ofResidues (Residue.failureValue tm blockLength) =
      failureValue tm blockLength := by
  rw [Residue.failureValue, failureValue]
  exact ofResidues_zeroValue tm blockLength

private theorem ofResidues_addValue
    (tm : TM workTapeCount) (blockLength : ℕ)
    (first second : ResidueValue tm blockLength) :
    ofResidues (Residue.addValue tm blockLength first second) =
      ofResidues first + ofResidues second := by
  funext chunk
  change
    ((PrimeField.Runtime.add (modulus tm blockLength)
      (first chunk) (second chunk) : ℕ) :
        ZMod (modulus tm blockLength)) =
      (first chunk : ZMod (modulus tm blockLength)) +
        (second chunk : ZMod (modulus tm blockLength))
  simp

private theorem ofResidues_scaleValue
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (value : ResidueValue tm blockLength) :
    ofResidues (Residue.scaleValue tm blockLength scalar value) =
      (scalar : EvaluationField tm blockLength) • ofResidues value := by
  funext chunk
  change
    ((PrimeField.Runtime.mul (modulus tm blockLength)
      scalar (value chunk) : ℕ) :
        ZMod (modulus tm blockLength)) =
      (scalar : ZMod (modulus tm blockLength)) *
        (value chunk : ZMod (modulus tm blockLength))
  simp

private theorem castResidueRegisters_addAt
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs : Residue.Registers tm blockLength)
    (index : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength) :
    castResidueRegisters tm blockLength
        (Residue.addAt tm blockLength regs index value) =
      CookMertz.addAt (castResidueRegisters tm blockLength regs)
        index (ofResidues value) := by
  funext current
  by_cases hcurrent : current = index
  · subst current
    simp [castResidueRegisters, Residue.addAt, CookMertz.addAt,
      ofResidues_addValue]
  · simp [castResidueRegisters, Residue.addAt, CookMertz.addAt,
      hcurrent]

private theorem castResidueRegisters_scaleAt
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs : Residue.Registers tm blockLength)
    (index : Fin (graphFanIn workTapeCount + 1)) :
    castResidueRegisters tm blockLength
        (Residue.scaleAt tm blockLength scalar regs index) =
      CookMertz.scaleAt
        (castResidueRegisters tm blockLength regs) index
        (scalar : EvaluationField tm blockLength) := by
  funext current
  by_cases hcurrent : current = index
  · subst current
    simp [castResidueRegisters, Residue.scaleAt, CookMertz.scaleAt,
      ofResidues_scaleValue]
  · simp [castResidueRegisters, Residue.scaleAt, CookMertz.scaleAt,
      hcurrent]

private theorem ofResidues_combineResidues
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        ResidueValue tm blockLength) :
    ofResidues
        (combineResidues tm x blockLength encoding hpositive
          tape slot timeBlock children) =
      combineValue tm x blockLength encoding hpositive
        tape slot timeBlock (fun child => ofResidues (children child)) := by
  unfold combineResidues ofResidues
  exact ResidueBridge.coe_evaluateNode_internal
    (payloadWidth tm blockLength) (graphFanIn workTapeCount)
    (booleanCombine tm x blockLength encoding hpositive
      tape slot timeBlock) children

private theorem castResidueProfile_start
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs : Residue.Registers tm blockLength) :
    Workspace.Profile.map
        (castResidueRegisters tm blockLength)
        (Workspace.Profile.start regs) =
      Workspace.Profile.start
        (castResidueRegisters tm blockLength regs) := by
  rfl

private theorem castResidueProfile_recordChild
    (tm : TM workTapeCount) (blockLength : ℕ)
    (current child :
      Workspace.Profile (Residue.Registers tm blockLength)) :
    Workspace.Profile.map
        (castResidueRegisters tm blockLength)
        (Workspace.Profile.recordChild current child) =
      Workspace.Profile.recordChild
        (Workspace.Profile.map
          (castResidueRegisters tm blockLength) current)
        (Workspace.Profile.map
          (castResidueRegisters tm blockLength) child) := by
  rfl

private theorem castResidueProfile_map
    (tm : TM workTapeCount) (blockLength : ℕ)
    (operation :
      Residue.Registers tm blockLength →
        Residue.Registers tm blockLength)
    (fieldOperation :
      CookMertz.Registers (graphFanIn workTapeCount)
          (EvaluationValue tm blockLength) →
        CookMertz.Registers (graphFanIn workTapeCount)
          (EvaluationValue tm blockLength))
    (hoperation :
      ∀ regs,
        castResidueRegisters tm blockLength (operation regs) =
          fieldOperation (castResidueRegisters tm blockLength regs))
    (profile :
      Workspace.Profile (Residue.Registers tm blockLength)) :
    Workspace.Profile.map
        (castResidueRegisters tm blockLength)
        (Workspace.Profile.map operation profile) =
      Workspace.Profile.map fieldOperation
        (Workspace.Profile.map
          (castResidueRegisters tm blockLength) profile) := by
  cases profile
  simp only [Workspace.Profile.map]
  congr
  exact hoperation _

private theorem castFoldl
    {RuntimeState FieldState Index : Type*}
    (cast : RuntimeState → FieldState)
    (runtimeStep : RuntimeState → Index → RuntimeState)
    (fieldStep : FieldState → Index → FieldState)
    (hstep : ∀ state index,
      cast (runtimeStep state index) =
        fieldStep (cast state) index)
    (indices : List Index) (initial : RuntimeState) :
    cast (indices.foldl runtimeStep initial) =
      indices.foldl fieldStep (cast initial) := by
  induction indices generalizing initial with
  | nil =>
      rfl
  | cons index indices ih =>
      simp only [List.foldl_cons]
      rw [ih, hstep]

private theorem range'_one_eq_map_finRange (length : ℕ) :
    List.range' 1 length =
      (List.finRange length).map fun index => index.val + 1 := by
  apply List.ext_getElem <;> simp [Nat.add_comm]

private theorem castFoldNonzero
    {RuntimeState FieldState : Type*}
    (p : ℕ) [Fact p.Prime]
    (cast : RuntimeState → FieldState)
    (runtimeStep : RuntimeState → ℕ → RuntimeState)
    (fieldStep : FieldState → (ZMod p)ˣ → FieldState)
    (hstep :
      ∀ state (index : Fin (p - 1)),
        cast (runtimeStep state (index.val + 1)) =
          fieldStep (cast state) (PrimeField.unitOfIndex p index))
    (initial : RuntimeState) :
    cast (PrimeField.Runtime.foldNonzero p runtimeStep initial) =
      (PrimeField.units p).foldl fieldStep (cast initial) := by
  rw [PrimeField.Runtime.foldNonzero_eq_foldl_range,
    range'_one_eq_map_finRange, PrimeField.units]
  simp only [List.foldl_map]
  exact castFoldl cast
    (fun state index =>
      runtimeStep state (index.val + 1))
    (fun state index =>
      fieldStep state (PrimeField.unitOfIndex p index))
    hstep (List.finRange (p - 1)) initial

private theorem coeRuntimeNormalizeOne
    (tm : TM workTapeCount) (blockLength : ℕ) :
    (PrimeField.Runtime.normalize
        (modulus tm blockLength) 1 :
      EvaluationField tm blockLength) = 1 := by
  change
    ((PrimeField.Runtime.normalize
      (modulus tm blockLength) 1 : ℕ) :
        ZMod (modulus tm blockLength)) = 1
  simp

private theorem coeRuntimeSubZero
    (tm : TM workTapeCount) (blockLength scalar : ℕ) :
    (PrimeField.Runtime.sub
        (modulus tm blockLength) 0 scalar :
      EvaluationField tm blockLength) =
      -(scalar : EvaluationField tm blockLength) := by
  change
    ((PrimeField.Runtime.sub
      (modulus tm blockLength) 0 scalar : ℕ) :
        ZMod (modulus tm blockLength)) =
      -(scalar : ZMod (modulus tm blockLength))
  simp

private theorem coeRuntimeInverseUnit
    (tm : TM workTapeCount) (blockLength : ℕ)
    (index : Fin (modulus tm blockLength - 1)) :
    (PrimeField.Runtime.inverse
        (modulus tm blockLength) (index.val + 1) :
      EvaluationField tm blockLength) =
      ((↑(PrimeField.unitOfIndex
          (modulus tm blockLength) index)⁻¹ :
        EvaluationField tm blockLength)) := by
  change
    ((PrimeField.Runtime.inverse
      (modulus tm blockLength) (index.val + 1) : ℕ) :
        ZMod (modulus tm blockLength)) =
      (↑(PrimeField.unitOfIndex
        (modulus tm blockLength) index)⁻¹ :
          ZMod (modulus tm blockLength))
  simp [PrimeField.unitOfIndex]

private def CanonicalResidueRegisters
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs : Residue.Registers tm blockLength) : Prop :=
  ∀ register chunk,
    regs register chunk < modulus tm blockLength

private theorem canonicalResidueRegisters_addAt
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs : Residue.Registers tm blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength)
    (hregs : CanonicalResidueRegisters tm blockLength regs) :
    CanonicalResidueRegisters tm blockLength
      (Residue.addAt tm blockLength regs out value) := by
  intro register chunk
  by_cases hregister : register = out
  · subst register
    simp only [Residue.addAt, Function.update_self,
      Residue.addValue]
    exact PrimeField.Runtime.normalize_lt
      (PrimeField.Search.searchModulus_prime _).pos
  · rw [Residue.addAt, Function.update_of_ne hregister]
    exact hregs register chunk

private theorem canonicalResidueRegisters_scaleAt
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs : Residue.Registers tm blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (hregs : CanonicalResidueRegisters tm blockLength regs) :
    CanonicalResidueRegisters tm blockLength
      (Residue.scaleAt tm blockLength scalar regs out) := by
  intro register chunk
  by_cases hregister : register = out
  · subst register
    simp only [Residue.scaleAt, Function.update_self,
      Residue.scaleValue]
    exact PrimeField.Runtime.normalize_lt
      (PrimeField.Search.searchModulus_prime _).pos
  · rw [Residue.scaleAt, Function.update_of_ne hregister]
    exact hregs register chunk

private theorem foldl_canonicalResidueRegisters
    (tm : TM workTapeCount) (blockLength : ℕ)
    (items : List ι)
    (step :
      Workspace.Profile (Residue.Registers tm blockLength) → ι →
        Workspace.Profile (Residue.Registers tm blockLength))
    (initial :
      Workspace.Profile (Residue.Registers tm blockLength))
    (hinitial :
      CanonicalResidueRegisters tm blockLength initial.result)
    (hstep :
      ∀ current item,
        CanonicalResidueRegisters tm blockLength current.result →
        CanonicalResidueRegisters tm blockLength
          (step current item).result) :
    CanonicalResidueRegisters tm blockLength
      (items.foldl step initial).result := by
  induction items generalizing initial with
  | nil => exact hinitial
  | cons item items ih =>
      exact ih (step initial item)
        (hstep initial item hinitial)

private theorem foldNonzeroLoop_canonicalResidueRegisters
    (tm : TM workTapeCount) (blockLength : ℕ)
    (step :
      Workspace.Profile (Residue.Registers tm blockLength) → ℕ →
        Workspace.Profile (Residue.Registers tm blockLength))
    (fuel candidate : ℕ)
    (initial :
      Workspace.Profile (Residue.Registers tm blockLength))
    (hinitial :
      CanonicalResidueRegisters tm blockLength initial.result)
    (hstep :
      ∀ current residue,
        CanonicalResidueRegisters tm blockLength current.result →
        CanonicalResidueRegisters tm blockLength
          (step current residue).result) :
    CanonicalResidueRegisters tm blockLength
      (PrimeField.Runtime.foldNonzeroLoop step fuel candidate
        initial).result := by
  induction fuel generalizing candidate initial with
  | zero => exact hinitial
  | succ fuel ih =>
      exact ih (candidate + 1) (step initial candidate)
        (hstep initial candidate hinitial)

private theorem foldNonzero_canonicalResidueRegisters
    (tm : TM workTapeCount) (blockLength : ℕ)
    (p : ℕ)
    (step :
      Workspace.Profile (Residue.Registers tm blockLength) → ℕ →
        Workspace.Profile (Residue.Registers tm blockLength))
    (initial :
      Workspace.Profile (Residue.Registers tm blockLength))
    (hinitial :
      CanonicalResidueRegisters tm blockLength initial.result)
    (hstep :
      ∀ current residue,
        CanonicalResidueRegisters tm blockLength current.result →
        CanonicalResidueRegisters tm blockLength
          (step current residue).result) :
    CanonicalResidueRegisters tm blockLength
      (PrimeField.Runtime.foldNonzero p step initial).result := by
  exact foldNonzeroLoop_canonicalResidueRegisters
    tm blockLength step (p - 1) 1 initial hinitial hstep

theorem residueProfileAccumulate_canonical_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (regs : Residue.Registers tm blockLength)
    (hregs : CanonicalResidueRegisters tm blockLength regs) :
    CanonicalResidueRegisters tm blockLength
      (Residue.profileAccumulate tm x blockLength encoding hpositive
        horizon guess fuel node scalar out regs).result := by
  induction fuel generalizing node scalar out regs with
  | zero =>
      cases node with
      | failure =>
          simpa [Residue.profileAccumulate, Workspace.Profile.start] using
            canonicalResidueRegisters_addAt tm blockLength regs out
              (Residue.scaleValue tm blockLength scalar
                (Residue.failureValue tm blockLength)) hregs
      | graph node =>
          cases node with
          | source tape block =>
              simpa [Residue.profileAccumulate,
                Workspace.Profile.start] using
                canonicalResidueRegisters_addAt tm blockLength regs out
                  (Residue.scaleValue tm blockLength scalar
                    (Residue.sourceValue tm x blockLength encoding
                      hpositive tape block)) hregs
          | computation tape slot interval =>
              simpa [Residue.profileAccumulate,
                Workspace.Profile.start] using
                canonicalResidueRegisters_addAt tm blockLength regs out
                  (Residue.scaleValue tm blockLength scalar
                    (Residue.failureValue tm blockLength)) hregs
  | succ fuel ih =>
      cases node with
      | failure =>
          simpa [Residue.profileAccumulate, Workspace.Profile.start] using
            canonicalResidueRegisters_addAt tm blockLength regs out
              (Residue.scaleValue tm blockLength scalar
                (Residue.failureValue tm blockLength)) hregs
      | graph node =>
          cases node with
          | source tape block =>
              simpa [Residue.profileAccumulate,
                Workspace.Profile.start] using
                canonicalResidueRegisters_addAt tm blockLength regs out
                  (Residue.scaleValue tm blockLength scalar
                    (Residue.sourceValue tm x blockLength encoding
                      hpositive tape block)) hregs
          | computation tape slot interval =>
              rw [Residue.profileAccumulate]
              split <;> rename_i hinterval
              · apply foldNonzero_canonicalResidueRegisters
                  tm blockLength
                · simpa [Workspace.Profile.start] using hregs
                · intro current residue hcurrent
                  let prepared :=
                    (List.finRange
                      (graphFanIn workTapeCount)).foldl
                      (fun current childIndex =>
                        let target := out.succAbove childIndex
                        let child :=
                          Residue.profileAccumulate
                            tm x blockLength encoding hpositive
                            horizon guess fuel
                            (NeighborhoodEvaluator.childAt guess
                              (.graph (.computation
                                tape slot interval))
                              childIndex)
                            (PrimeField.Runtime.normalize
                              (modulus tm blockLength) 1)
                            target
                            (Residue.scaleAt tm blockLength residue
                              current.result target)
                        Workspace.Profile.recordChild current child)
                      current
                  have hprepared :
                      CanonicalResidueRegisters tm blockLength
                        prepared.result := by
                    apply foldl_canonicalResidueRegisters
                      tm blockLength
                      (List.finRange
                        (graphFanIn workTapeCount)) _ current hcurrent
                    intro childCurrent childIndex hchildCurrent
                    have hscaled :=
                      canonicalResidueRegisters_scaleAt
                        tm blockLength residue childCurrent.result
                        (out.succAbove childIndex) hchildCurrent
                    have hchild :=
                      ih
                        (NeighborhoodEvaluator.childAt guess
                          (.graph (.computation tape slot interval))
                          childIndex)
                        (PrimeField.Runtime.normalize
                          (modulus tm blockLength) 1)
                        (out.succAbove childIndex)
                        (Residue.scaleAt tm blockLength residue
                          childCurrent.result
                          (out.succAbove childIndex))
                        hscaled
                    simpa [Workspace.Profile.recordChild] using hchild
                  let args := fun childIndex =>
                    prepared.result (out.succAbove childIndex)
                  let updated :=
                    Workspace.Profile.map
                      (fun currentRegs =>
                        Residue.addAt tm blockLength currentRegs out
                          (Residue.scaleValue tm blockLength
                            (PrimeField.Runtime.sub
                              (modulus tm blockLength) 0 scalar)
                            (combineResidues tm x blockLength encoding
                              hpositive tape slot interval args)))
                      prepared
                  have hupdated :
                      CanonicalResidueRegisters tm blockLength
                        updated.result := by
                    simpa [updated, Workspace.Profile.map] using
                      canonicalResidueRegisters_addAt
                        tm blockLength prepared.result out
                        (Residue.scaleValue tm blockLength
                          (PrimeField.Runtime.sub
                            (modulus tm blockLength) 0 scalar)
                          (combineResidues tm x blockLength encoding
                            hpositive tape slot interval args))
                        hprepared
                  apply foldl_canonicalResidueRegisters
                    tm blockLength
                    (List.finRange
                      (graphFanIn workTapeCount)) _ updated hupdated
                  intro cleanupCurrent childIndex hcleanupCurrent
                  let target := out.succAbove childIndex
                  let child :=
                    Residue.profileAccumulate
                      tm x blockLength encoding hpositive
                      horizon guess fuel
                      (NeighborhoodEvaluator.childAt guess
                        (.graph (.computation tape slot interval))
                        childIndex)
                      (PrimeField.Runtime.sub
                        (modulus tm blockLength) 0 1)
                      target cleanupCurrent.result
                  have hchild :
                      CanonicalResidueRegisters tm blockLength
                        child.result :=
                    ih
                      (NeighborhoodEvaluator.childAt guess
                        (.graph (.computation tape slot interval))
                        childIndex)
                      (PrimeField.Runtime.sub
                        (modulus tm blockLength) 0 1)
                      target cleanupCurrent.result hcleanupCurrent
                  have hrecorded :
                      CanonicalResidueRegisters tm blockLength
                        (Workspace.Profile.recordChild
                          cleanupCurrent child).result := by
                    simpa [Workspace.Profile.recordChild] using hchild
                  simpa [target, child, Workspace.Profile.map] using
                    canonicalResidueRegisters_scaleAt
                      tm blockLength
                      (PrimeField.Runtime.inverse
                        (modulus tm blockLength) residue)
                      (Workspace.Profile.recordChild
                        cleanupCurrent child).result
                      target hrecorded
              · simpa [Workspace.Profile.start] using
                  canonicalResidueRegisters_addAt tm blockLength regs out
                    (Residue.scaleValue tm blockLength scalar
                      (Residue.failureValue tm blockLength)) hregs

set_option maxHeartbeats 1000000 in
theorem residueProfileAccumulate_cast_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (regs : Residue.Registers tm blockLength) :
    Workspace.Profile.map
        (castResidueRegisters tm blockLength)
        (Residue.profileAccumulate tm x blockLength encoding hpositive
          horizon guess fuel node scalar out regs) =
      NeighborhoodEvaluator.profileAccumulate
        (PrimeGrouped.Logarithmic.units
          (payloadWidth tm blockLength) (graphFanIn workTapeCount))
        guess (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        fuel node (scalar : EvaluationField tm blockLength) out
        (castResidueRegisters tm blockLength regs) := by
  induction fuel generalizing node scalar out regs with
  | zero =>
      cases node with
      | failure =>
          simp only [Residue.profileAccumulate,
            NeighborhoodEvaluator.profileAccumulate]
          rw [castResidueProfile_start,
            castResidueRegisters_addAt,
            ofResidues_scaleValue,
            ofResidues_failureValue]
      | graph node =>
          cases node with
          | source tape block =>
              simp only [Residue.profileAccumulate,
                NeighborhoodEvaluator.profileAccumulate]
              rw [castResidueProfile_start,
                castResidueRegisters_addAt,
                ofResidues_scaleValue,
                ofResidues_sourceValue]
          | computation tape slot interval =>
              simp only [Residue.profileAccumulate,
                NeighborhoodEvaluator.profileAccumulate]
              rw [castResidueProfile_start,
                castResidueRegisters_addAt,
                ofResidues_scaleValue,
                ofResidues_failureValue]
  | succ fuel ih =>
      cases node with
      | failure =>
          simp only [Residue.profileAccumulate,
            NeighborhoodEvaluator.profileAccumulate]
          rw [castResidueProfile_start,
            castResidueRegisters_addAt,
            ofResidues_scaleValue,
            ofResidues_failureValue]
      | graph node =>
          cases node with
          | source tape block =>
              simp only [Residue.profileAccumulate,
                NeighborhoodEvaluator.profileAccumulate]
              rw [castResidueProfile_start,
                castResidueRegisters_addAt,
                ofResidues_scaleValue,
                ofResidues_sourceValue]
          | computation tape slot interval =>
              letI : Fact (modulus tm blockLength).Prime :=
                ⟨by
                  simpa [modulus] using
                    PrimeField.Search.searchModulus_prime
                      (PrimeGrouped.Logarithmic.degreeEndpoint
                        (payloadWidth tm blockLength)
                        (graphFanIn workTapeCount))⟩
              simp only [Residue.profileAccumulate,
                NeighborhoodEvaluator.profileAccumulate]
              by_cases hinterval : interval < horizon
              · simp only [dif_pos hinterval]
                rw [show PrimeGrouped.Logarithmic.units
                  (payloadWidth tm blockLength)
                    (graphFanIn workTapeCount) =
                  PrimeField.units (modulus tm blockLength) by rfl]
                apply castFoldNonzero
                  (p := modulus tm blockLength)
                intro current index
                let residue := index.val + 1
                let unit :
                    (EvaluationField tm blockLength)ˣ :=
                  PrimeField.unitOfIndex
                    (modulus tm blockLength) index
                let runtimePrepared :=
                  (List.finRange
                    (graphFanIn workTapeCount)).foldl
                    (fun current childIndex =>
                      let target := out.succAbove childIndex
                      let child :=
                        Residue.profileAccumulate
                          tm x blockLength encoding hpositive
                          horizon guess fuel
                          (NeighborhoodEvaluator.childAt guess
                            (.graph
                              (.computation tape slot interval))
                            childIndex)
                          (PrimeField.Runtime.normalize
                            (modulus tm blockLength) 1)
                          target
                          (Residue.scaleAt tm blockLength residue
                            current.result target)
                      Workspace.Profile.recordChild current child)
                    current
                let fieldPrepared :=
                  (List.finRange
                    (graphFanIn workTapeCount)).foldl
                    (fun current childIndex =>
                      let target := out.succAbove childIndex
                      let child :=
                        NeighborhoodEvaluator.profileAccumulate
                          (show
                            List
                              (EvaluationField tm blockLength)ˣ
                            from
                              PrimeField.units
                                (modulus tm blockLength))
                          guess (failureValue tm blockLength)
                          (sourceValue tm x blockLength encoding
                            hpositive)
                          (combineValue tm x blockLength encoding
                            hpositive)
                          fuel
                          (NeighborhoodEvaluator.childAt guess
                            (.graph
                              (.computation tape slot interval))
                            childIndex)
                          1 target
                          (CookMertz.scaleAt current.result target
                            (↑unit :
                              EvaluationField tm blockLength))
                      Workspace.Profile.recordChild current child)
                    (Workspace.Profile.map
                      (castResidueRegisters tm blockLength) current)
                have hprepare :
                    Workspace.Profile.map
                        (castResidueRegisters tm blockLength)
                        runtimePrepared =
                      fieldPrepared := by
                  apply castFoldl
                  intro current childIndex
                  rw [castResidueProfile_recordChild, ih,
                    castResidueRegisters_scaleAt]
                  apply congrArg
                    (Workspace.Profile.recordChild
                      (Workspace.Profile.map
                        (castResidueRegisters tm blockLength)
                        current))
                  simp [PrimeGrouped.Logarithmic.units,
                    PrimeField.searchUnits, Workspace.Profile.map,
                    residue, unit]
                let runtimeArgs := fun childIndex =>
                  runtimePrepared.result
                    (out.succAbove childIndex)
                let fieldArgs := fun childIndex =>
                  fieldPrepared.result
                    (out.succAbove childIndex)
                have hargs :
                    (fun childIndex =>
                      ofResidues (runtimeArgs childIndex)) =
                      fieldArgs := by
                  funext childIndex
                  exact congrFun
                    (congrArg Workspace.Profile.result hprepare)
                    (out.succAbove childIndex)
                let runtimeUpdated :=
                  Workspace.Profile.map
                    (fun currentRegs =>
                      Residue.addAt tm blockLength currentRegs out
                        (Residue.scaleValue tm blockLength
                          (PrimeField.Runtime.sub
                            (modulus tm blockLength) 0 scalar)
                          (combineResidues tm x blockLength encoding
                            hpositive tape slot interval runtimeArgs)))
                    runtimePrepared
                let fieldUpdated :=
                  Workspace.Profile.map
                    (fun currentRegs =>
                      CookMertz.addAt currentRegs out
                        ((-(scalar :
                            EvaluationField tm blockLength)) •
                          combineValue tm x blockLength encoding
                            hpositive tape slot interval fieldArgs))
                    fieldPrepared
                have hupdated :
                    Workspace.Profile.map
                        (castResidueRegisters tm blockLength)
                        runtimeUpdated =
                      fieldUpdated := by
                  unfold runtimeUpdated fieldUpdated
                  calc
                    _ = Workspace.Profile.map
                        (fun currentRegs =>
                          CookMertz.addAt currentRegs out
                            ((-(scalar :
                                EvaluationField tm blockLength)) •
                              combineValue tm x blockLength encoding
                                hpositive tape slot interval fieldArgs))
                        (Workspace.Profile.map
                          (castResidueRegisters tm blockLength)
                          runtimePrepared) := by
                      apply castResidueProfile_map
                      intro currentRegs
                      rw [castResidueRegisters_addAt,
                        ofResidues_scaleValue,
                        ofResidues_combineResidues, hargs,
                        coeRuntimeSubZero, neg_smul]
                    _ = _ := by
                      rw [hprepare]
                let runtimeCleanup :=
                  fun (current :
                      Workspace.Profile
                        (Residue.Registers tm blockLength))
                      (childIndex :
                        Fin (graphFanIn workTapeCount)) =>
                    let target := out.succAbove childIndex
                    Workspace.Profile.map
                      (fun currentRegs =>
                        Residue.scaleAt tm blockLength
                          (PrimeField.Runtime.inverse
                            (modulus tm blockLength) residue)
                          currentRegs target)
                      (Workspace.Profile.recordChild current
                        (Residue.profileAccumulate
                          tm x blockLength encoding hpositive
                          horizon guess fuel
                          (NeighborhoodEvaluator.childAt guess
                            (.graph
                              (.computation tape slot interval))
                            childIndex)
                          (PrimeField.Runtime.sub
                            (modulus tm blockLength) 0 1)
                          target current.result))
                let fieldCleanup :=
                  fun (current :
                      Workspace.Profile
                        (CookMertz.Registers
                          (graphFanIn workTapeCount)
                          (EvaluationValue tm blockLength)))
                      (childIndex :
                        Fin (graphFanIn workTapeCount)) =>
                    let target := out.succAbove childIndex
                    Workspace.Profile.map
                      (fun currentRegs =>
                        CookMertz.scaleAt currentRegs target
                          (↑unit⁻¹ :
                            EvaluationField tm blockLength))
                      (Workspace.Profile.recordChild current
                        (NeighborhoodEvaluator.profileAccumulate
                          (show
                            List
                              (EvaluationField tm blockLength)ˣ
                            from
                              PrimeField.units
                                (modulus tm blockLength))
                          guess (failureValue tm blockLength)
                          (sourceValue tm x blockLength encoding
                            hpositive)
                          (combineValue tm x blockLength encoding
                            hpositive)
                          fuel
                          (NeighborhoodEvaluator.childAt guess
                            (.graph
                              (.computation tape slot interval))
                            childIndex)
                          (-1) target current.result))
                change Workspace.Profile.map
                    (castResidueRegisters tm blockLength)
                    ((List.finRange
                      (graphFanIn workTapeCount)).foldl
                        runtimeCleanup runtimeUpdated) =
                  (List.finRange
                    (graphFanIn workTapeCount)).foldl
                      fieldCleanup fieldUpdated
                calc
                  _ = (List.finRange
                        (graphFanIn workTapeCount)).foldl
                      fieldCleanup
                      (Workspace.Profile.map
                        (castResidueRegisters tm blockLength)
                        runtimeUpdated) := by
                    apply castFoldl
                    intro current childIndex
                    unfold runtimeCleanup fieldCleanup
                    calc
                      _ = Workspace.Profile.map
                          (fun currentRegs =>
                            CookMertz.scaleAt currentRegs
                              (out.succAbove childIndex)
                              (↑unit⁻¹ :
                                EvaluationField tm blockLength))
                          (Workspace.Profile.map
                            (castResidueRegisters tm blockLength)
                            (Workspace.Profile.recordChild current
                              (Residue.profileAccumulate
                                tm x blockLength encoding hpositive
                                horizon guess fuel
                                (NeighborhoodEvaluator.childAt guess
                                  (.graph (.computation
                                    tape slot interval))
                                  childIndex)
                                (PrimeField.Runtime.sub
                                  (modulus tm blockLength) 0 1)
                                (out.succAbove childIndex)
                                current.result))) := by
                            apply castResidueProfile_map
                            intro currentRegs
                            rw [castResidueRegisters_scaleAt,
                              coeRuntimeInverseUnit]
                      _ = _ := by
                            rw [castResidueProfile_recordChild, ih,
                              coeRuntimeSubZero]
                            simp only [Nat.cast_one]
                            unfold PrimeGrouped.Logarithmic.units
                              PrimeField.searchUnits
                            rfl
                  _ = _ := by
                    rw [hupdated]
              · simp only [dif_neg hinterval]
                rw [castResidueProfile_start,
                  castResidueRegisters_addAt,
                  ofResidues_scaleValue,
                  ofResidues_failureValue]

theorem residueProfileEvaluate_cast_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    Workspace.Profile.map ofResidues
        (Residue.profileEvaluate tm x blockLength encoding hpositive
          horizon guess fuel node) =
      NeighborhoodEvaluator.profileEvaluate
        (PrimeGrouped.Logarithmic.units
          (payloadWidth tm blockLength) (graphFanIn workTapeCount))
        guess (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        fuel node := by
  unfold Residue.profileEvaluate
  unfold NeighborhoodEvaluator.profileEvaluate
  let output := Fin.last (graphFanIn workTapeCount)
  let zeroRegs : Residue.Registers tm blockLength :=
    fun _ => Residue.zeroValue tm blockLength
  let runtime :=
    Residue.profileAccumulate tm x blockLength encoding hpositive
      horizon guess fuel node
      (PrimeField.Runtime.normalize (modulus tm blockLength) 1)
      output zeroRegs
  have hcast :
      Workspace.Profile.map (castResidueRegisters tm blockLength) runtime =
        NeighborhoodEvaluator.profileAccumulate
          (PrimeGrouped.Logarithmic.units
            (payloadWidth tm blockLength) (graphFanIn workTapeCount))
          guess (failureValue tm blockLength)
          (sourceValue tm x blockLength encoding hpositive)
          (combineValue tm x blockLength encoding hpositive)
          fuel node
          ((PrimeField.Runtime.normalize
            (modulus tm blockLength) 1 :
              EvaluationField tm blockLength))
          output (castResidueRegisters tm blockLength zeroRegs) :=
    residueProfileAccumulate_cast_internal
      tm x blockLength encoding hpositive horizon guess fuel node
        (PrimeField.Runtime.normalize (modulus tm blockLength) 1)
        output zeroRegs
  have hzero :
      castResidueRegisters tm blockLength zeroRegs =
        (0 : CookMertz.Registers (graphFanIn workTapeCount)
          (EvaluationValue tm blockLength)) := by
    funext index
    exact ofResidues_zeroValue tm blockLength
  calc
    Workspace.Profile.map ofResidues
        (Workspace.Profile.map (fun regs => regs output) runtime) =
      Workspace.Profile.map (fun regs => regs output)
        (Workspace.Profile.map
          (castResidueRegisters tm blockLength) runtime) := by
      cases runtime
      rfl
    _ = Workspace.Profile.map (fun regs => regs output)
        (NeighborhoodEvaluator.profileAccumulate
          (PrimeGrouped.Logarithmic.units
            (payloadWidth tm blockLength) (graphFanIn workTapeCount))
          guess (failureValue tm blockLength)
          (sourceValue tm x blockLength encoding hpositive)
          (combineValue tm x blockLength encoding hpositive)
          fuel node
          ((PrimeField.Runtime.normalize
            (modulus tm blockLength) 1 :
              EvaluationField tm blockLength))
          output (castResidueRegisters tm blockLength zeroRegs)) := by
      rw [hcast]
    _ = _ := by
      rw [coeRuntimeNormalizeOne, hzero]

set_option maxHeartbeats 1000000 in
theorem residueProfileAccumulate_result_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (regs : Residue.Registers tm blockLength)
    (hregs :
      ∀ register chunk,
        regs register chunk < modulus tm blockLength) :
    (Residue.profileAccumulate tm x blockLength encoding hpositive
      horizon guess fuel node scalar out regs).result =
      Residue.addAt tm blockLength regs out
        (Residue.scaleValue tm blockLength scalar
          (Residue.profileEvaluate tm x blockLength encoding hpositive
            horizon guess fuel node).result) := by
  let units :=
    PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount)
  let fieldTree :=
    NeighborhoodEvaluator.unroll guess
      (failureValue tm blockLength)
      (sourceValue tm x blockLength encoding hpositive)
      (combineValue tm x blockLength encoding hpositive)
      fuel node
  let fieldRegs := castResidueRegisters tm blockLength regs
  have hline : LineCompatible units fieldTree := by
    exact queryUnroll_lineCompatible_internal
      tm x blockLength encoding hpositive horizon guess fuel node
  have haccCast := congrArg Workspace.Profile.result
    (residueProfileAccumulate_cast_internal
      tm x blockLength encoding hpositive horizon guess fuel node
        scalar out regs)
  have hfieldAccumulate :
      (NeighborhoodEvaluator.profileAccumulate units guess
        (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        fuel node (scalar : EvaluationField tm blockLength)
        out fieldRegs).result =
      CookMertz.addAt fieldRegs out
        ((scalar : EvaluationField tm blockLength) •
          fieldTree.value) := by
    rw [NeighborhoodEvaluator.Internal.profileAccumulate_eq_profileUnroll_internal]
    rw [Workspace.profileAccumulate_result]
    exact CookMertz.accumulate_eq_addAt
      units fieldTree hline
        (scalar : EvaluationField tm blockLength) out fieldRegs
  have hfieldEvaluate :
      (NeighborhoodEvaluator.profileEvaluate units guess
        (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        fuel node).result =
      fieldTree.value := by
    rw [NeighborhoodEvaluator.profileEvaluate_result]
    exact CookMertz.evaluate_eq_value units fieldTree hline
  have hevaluateCast := congrArg Workspace.Profile.result
    (residueProfileEvaluate_cast_internal
      tm x blockLength encoding hpositive horizon guess fuel node)
  change
    ofResidues
        (Residue.profileEvaluate tm x blockLength encoding hpositive
          horizon guess fuel node).result =
      (NeighborhoodEvaluator.profileEvaluate units guess
        (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        fuel node).result at hevaluateCast
  have hcast :
      castResidueRegisters tm blockLength
          (Residue.profileAccumulate tm x blockLength encoding hpositive
            horizon guess fuel node scalar out regs).result =
        castResidueRegisters tm blockLength
          (Residue.addAt tm blockLength regs out
            (Residue.scaleValue tm blockLength scalar
              (Residue.profileEvaluate tm x blockLength encoding
                hpositive horizon guess fuel node).result)) := by
    calc
      _ = (NeighborhoodEvaluator.profileAccumulate units guess
          (failureValue tm blockLength)
          (sourceValue tm x blockLength encoding hpositive)
          (combineValue tm x blockLength encoding hpositive)
          fuel node (scalar : EvaluationField tm blockLength)
          out fieldRegs).result := haccCast
      _ = CookMertz.addAt fieldRegs out
          ((scalar : EvaluationField tm blockLength) •
            fieldTree.value) := hfieldAccumulate
      _ = CookMertz.addAt fieldRegs out
          ((scalar : EvaluationField tm blockLength) •
            (NeighborhoodEvaluator.profileEvaluate units guess
              (failureValue tm blockLength)
              (sourceValue tm x blockLength encoding hpositive)
              (combineValue tm x blockLength encoding hpositive)
              fuel node).result) := by
            rw [hfieldEvaluate]
      _ = CookMertz.addAt fieldRegs out
          ((scalar : EvaluationField tm blockLength) •
            ofResidues
              (Residue.profileEvaluate tm x blockLength encoding
                hpositive horizon guess fuel node).result) := by
            rw [hevaluateCast]
      _ = _ := by
            rw [castResidueRegisters_addAt,
              ofResidues_scaleValue]
  have hleft :=
    residueProfileAccumulate_canonical_internal
      tm x blockLength encoding hpositive horizon guess fuel node
        scalar out regs hregs
  have hright :=
    canonicalResidueRegisters_addAt
      tm blockLength regs out
        (Residue.scaleValue tm blockLength scalar
          (Residue.profileEvaluate tm x blockLength encoding hpositive
            horizon guess fuel node).result) hregs
  funext register chunk
  apply CharP.natCast_injOn_Iio
    (EvaluationField tm blockLength) (modulus tm blockLength)
  · exact hleft register chunk
  · exact hright register chunk
  · exact congrFun (congrFun hcast register) chunk

theorem residueProfileEvaluate_canonical_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    ∀ chunk,
      (Residue.profileEvaluate tm x blockLength encoding hpositive
        horizon guess fuel node).result chunk <
        modulus tm blockLength := by
  let output := Fin.last (graphFanIn workTapeCount)
  let zeroRegs : Residue.Registers tm blockLength :=
    fun _ => Residue.zeroValue tm blockLength
  have hzero :
      CanonicalResidueRegisters tm blockLength zeroRegs := by
    intro register chunk
    exact PrimeField.Runtime.normalize_lt
      (PrimeField.Search.searchModulus_prime _).pos
  have hcanonical :=
    residueProfileAccumulate_canonical_internal
      tm x blockLength encoding hpositive horizon guess fuel node
        (PrimeField.Runtime.normalize (modulus tm blockLength) 1)
        output zeroRegs hzero
  intro chunk
  exact hcanonical output chunk

theorem residueProfileEvaluate_peakFrames_le_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    (Residue.profileEvaluate tm x blockLength encoding hpositive
      horizon guess fuel node).peakFrames ≤ fuel + 1 := by
  have hpeak := congrArg Workspace.Profile.peakFrames
    (residueProfileEvaluate_cast_internal
      tm x blockLength encoding hpositive horizon guess fuel node)
  change
    (Residue.profileEvaluate tm x blockLength encoding hpositive
      horizon guess fuel node).peakFrames =
      (NeighborhoodEvaluator.profileEvaluate
        (PrimeGrouped.Logarithmic.units
          (payloadWidth tm blockLength) (graphFanIn workTapeCount))
        guess (failureValue tm blockLength)
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        fuel node).peakFrames at hpeak
  rw [hpeak]
  exact NeighborhoodEvaluator.profileEvaluate_peakFrames_le
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    guess (failureValue tm blockLength)
    (sourceValue tm x blockLength encoding hpositive)
    (combineValue tm x blockLength encoding hpositive)
    fuel node

theorem residueProfileNode_cast_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (node : Node workTapeCount) :
    Workspace.Profile.map ofResidues
        (Residue.profileNode tm x blockLength encoding hpositive
          horizon guess node) =
      profileNode tm x blockLength encoding hpositive
        horizon guess node := by
  unfold Residue.profileNode profileNode
  exact residueProfileEvaluate_cast_internal
    tm x blockLength encoding hpositive horizon guess horizon (.graph node)

theorem residueProfileDecision_cast_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    Workspace.Profile.map
        (fun result => (ofResidues result.1, ofResidues result.2))
        (Residue.profileDecision tm x blockLength encoding hpositive
          horizon guess) =
      profileDecision tm x blockLength encoding hpositive
        horizon guess := by
  unfold Residue.profileDecision profileDecision
    NeighborhoodEvaluator.profileDecision
  dsimp only
  rw [← residueProfileEvaluate_cast_internal
    tm x blockLength encoding hpositive horizon guess horizon
      (NeighborhoodEvaluator.stateRoot guess)]
  rw [← residueProfileEvaluate_cast_internal
    tm x blockLength encoding hpositive horizon guess horizon
      (NeighborhoodEvaluator.verdictRoot guess blockLength)]
  rfl

theorem residueProfileDecision_peakFrames_le_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    (Residue.profileDecision tm x blockLength encoding hpositive
      horizon guess).peakFrames ≤ horizon + 1 := by
  have hpeak := congrArg Workspace.Profile.peakFrames
    (residueProfileDecision_cast_internal
      tm x blockLength encoding hpositive horizon guess)
  change
    (Residue.profileDecision tm x blockLength encoding hpositive
      horizon guess).peakFrames =
      (profileDecision tm x blockLength encoding hpositive
        horizon guess).peakFrames at hpeak
  rw [hpeak]
  exact profileDecision_peakFrames_le_internal
    tm x blockLength encoding hpositive horizon guess

theorem residueDecodeValue_cast_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (value : ResidueValue tm blockLength) :
    Residue.decodeValue tm blockLength encoding hpositive value =
      decodeValue tm blockLength encoding hpositive
        (ofResidues value) := by
  unfold Residue.decodeValue decodeValue
  apply congrArg
    (decodeBits encoding tm.qstart hpositive)
  unfold PrimeGrouped.Logarithmic.Decoding.decodeValue
  apply congrArg
    (PrimeGrouped.Logarithmic.layout
      (payloadWidth tm blockLength)
      (graphFanIn workTapeCount)).unpack
  funext chunk
  unfold PrimeGrouped.Logarithmic.Decoding.decodeChunk
  unfold ofResidues
  rw [ZMod.val_natCast]
  rfl

theorem residueDecodedDecisionSnapshot_eq_typed_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    Residue.decodedDecisionSnapshot
        tm x blockLength encoding hpositive horizon guess =
      decodedDecisionSnapshot
        tm x blockLength encoding hpositive horizon guess := by
  unfold Residue.decodedDecisionSnapshot decodedDecisionSnapshot
  have hresult := congrArg Workspace.Profile.result
    (residueProfileDecision_cast_internal
      tm x blockLength encoding hpositive horizon guess)
  change
    (ofResidues
        (Residue.profileDecision tm x blockLength encoding hpositive
          horizon guess).result.1,
      ofResidues
        (Residue.profileDecision tm x blockLength encoding hpositive
          horizon guess).result.2) =
      (profileDecision tm x blockLength encoding hpositive
        horizon guess).result at hresult
  rw [← hresult]
  simp only
  rw [residueDecodeValue_cast_internal,
    residueDecodeValue_cast_internal]

theorem residueDecodedDecisionSnapshot_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    Residue.decodedDecisionSnapshot
        tm x blockLength encoding hpositive horizon guess =
      DecisionRecovery.decisionSnapshot
        tm x blockLength hpositive horizon := by
  rw [residueDecodedDecisionSnapshot_eq_typed_internal]
  exact decodedDecisionSnapshot_eq_internal
    tm x blockLength encoding hpositive horizon guess hvalid

theorem residueNodeCallback_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    Residue.nodeCallback
        tm x blockLength encoding hpositive horizon =
      nodeCallback
        tm x blockLength encoding hpositive horizon := by
  funext guess node
  change
    some (Residue.decodeValue tm blockLength encoding hpositive
      (Residue.profileNode tm x blockLength encoding hpositive
        horizon guess node).result) =
      some (decodeValue tm blockLength encoding hpositive
        (profileNode tm x blockLength encoding hpositive
          horizon guess node).result)
  have hresult := congrArg Workspace.Profile.result
    (residueProfileNode_cast_internal
      tm x blockLength encoding hpositive horizon guess node)
  change
    ofResidues
        (Residue.profileNode tm x blockLength encoding hpositive
          horizon guess node).result =
      (profileNode tm x blockLength encoding hpositive
        horizon guess node).result at hresult
  rw [← hresult, residueDecodeValue_cast_internal]

theorem residueNodeCallback_isPrefixExact_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    Guess.EvaluatedProvider.IsPrefixExact
      tm x blockLength hpositive
      (Residue.nodeCallback
        tm x blockLength encoding hpositive horizon) := by
  rw [residueNodeCallback_eq_internal]
  exact nodeCallback_isPrefixExact_internal
    tm x blockLength encoding hpositive horizon

theorem residueCertifiedEngine_isExact_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    (Residue.certifiedEngine
      tm x blockLength encoding hpositive horizon).IsExact
        x hpositive := by
  constructor
  · exact residueNodeCallback_isPrefixExact_internal
      tm x blockLength encoding hpositive horizon
  · intro guess hvalid
    change some (Residue.decodedDecisionSnapshot
      tm x blockLength encoding hpositive horizon guess) =
        some (DecisionRecovery.decisionSnapshot
          tm x blockLength hpositive horizon)
    exact congrArg some
      (residueDecodedDecisionSnapshot_eq_internal
        tm x blockLength encoding hpositive horizon guess hvalid)

end Internal

end NeighborhoodExecutableEvaluation

end TimeSpaceSimulation

end Complexity
