/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluator.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess
import Complexitylib.TreeEvaluation.CookMertz
import Complexitylib.TreeEvaluation.Workspace

/-!
# Correctness internals for the direct neighborhood evaluator
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodEvaluator

open NeighborhoodGraph
open TreeEval CookMertz

namespace Internal

variable {workTapeCount horizon : ℕ}

theorem childAt_rank_lt_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (index : Fin (fanIn workTapeCount)) :
    (childAt guess
      (.graph (.computation tape slot interval)) index).rank <
        interval + 1 := by
  rw [childAt]
  simp only [hinterval, dite_true]
  unfold Guess.CenterGuess.predecessorAt?
  unfold Guess.CenterGuess.predecessor?
  generalize hdecoded :
    (predecessorIndexEquiv workTapeCount).symm index = decoded
  cases decoded with
  | mk kind sourceTape =>
      cases kind with
      | content sourceSlot =>
          generalize hcenter :
            guess.derivedCenter sourceTape interval = center
          cases center with
          | none =>
              simp [Guess.CenterGuess.contentPredecessor?,
                hcenter, QueryNode.rank]
          | some center =>
              generalize hprevious :
                guess.previousInterval sourceTape
                  (neighborBlock center sourceSlot) interval = previous
              cases previous with
              | none =>
                  simp [Guess.CenterGuess.contentPredecessor?,
                    hcenter, hprevious, QueryNode.rank, Node.rank]
              | some previous =>
                  generalize hpreviousCenter :
                    guess.derivedCenter sourceTape previous.val =
                      previousCenter
                  cases previousCenter with
                  | none =>
                      simp [Guess.CenterGuess.contentPredecessor?,
                        hcenter, hprevious, hpreviousCenter,
                        QueryNode.rank]
                  | some previousCenter =>
                      simp only [Guess.CenterGuess.contentPredecessor?,
                        hcenter, hprevious, hpreviousCenter,
                        QueryNode.rank, Node.rank]
                      omega
      | chronological =>
          generalize hcenter :
            guess.derivedCenter sourceTape interval = center
          cases center with
          | none =>
              simp [Guess.CenterGuess.chronologicalPredecessor?,
                hcenter, QueryNode.rank]
          | some center =>
              cases interval <;>
                simp [Guess.CenterGuess.chronologicalPredecessor?,
                  hcenter, QueryNode.rank, Node.rank]

theorem childStep_rank_lt_internal
    {guess : Guess.CenterGuess workTapeCount horizon}
    {child parent : QueryNode workTapeCount horizon}
    (hstep : ChildStep guess child parent) :
    child.rank < parent.rank := by
  cases hstep with
  | computation tape slot interval hinterval index =>
      exact childAt_rank_lt_internal
        guess tape slot interval hinterval index

theorem unroll_height_le_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon) :
    (unroll guess failureValue sourceValue combine fuel node).height ≤
      fuel := by
  induction fuel generalizing node with
  | zero =>
      cases node with
      | failure => simp [unroll]
      | graph node =>
          cases node <;> simp [unroll]
  | succ fuel ih =>
      cases node with
      | failure => simp [unroll]
      | graph node =>
          cases node with
          | source tape block =>
              simp [unroll]
          | computation tape slot interval =>
              rw [unroll]
              split <;> rename_i hinterval
              · rw [TreeEval.Tree.height_node]
                have hsup :
                    Finset.univ.sup (fun index =>
                      (unroll guess failureValue sourceValue combine fuel
                        (childAt guess
                          (.graph (.computation tape slot interval))
                          index)).height) ≤ fuel := by
                  apply Finset.sup_le
                  intro index _
                  exact ih (childAt guess
                    (.graph (.computation tape slot interval)) index)
                omega
              · simp

theorem profileAccumulate_eq_profileUnroll_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon)
    (scale : F) (out : Fin (fanIn workTapeCount + 1))
    (regs : Registers (fanIn workTapeCount) V) :
    profileAccumulate units guess failureValue sourceValue combine
        fuel node scale out regs =
      Workspace.profileAccumulate units
        (unroll guess failureValue sourceValue combine fuel node)
        scale out regs := by
  induction fuel generalizing node scale out regs with
  | zero =>
      cases node with
      | failure => rfl
      | graph node =>
          cases node <;> rfl
  | succ fuel ih =>
      cases node with
      | failure => rfl
      | graph node =>
          cases node with
          | source tape block => rfl
          | computation tape slot interval =>
              rw [profileAccumulate, unroll]
              split <;> rename_i hinterval
              · rw [Workspace.profileAccumulate]
                simp_rw [ih]
              · rfl

theorem profileEvaluate_eq_profileUnroll_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon) :
    profileEvaluate units guess failureValue sourceValue combine fuel node =
      Workspace.profileEvaluate units
        (unroll guess failureValue sourceValue combine fuel node) := by
  simp only [profileEvaluate, Workspace.profileEvaluate]
  rw [profileAccumulate_eq_profileUnroll_internal]

theorem profileEvaluate_peakFrames_le_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel node).peakFrames ≤ fuel + 1 := by
  rw [profileEvaluate_eq_profileUnroll_internal]
  exact
    (Workspace.profileEvaluate_peakFrames_le units
      (unroll guess failureValue sourceValue combine fuel node)).trans
      (Nat.add_le_add_right
        (unroll_height_le_internal
          guess failureValue sourceValue combine fuel node) 1)

theorem profileEvaluate_result_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel node).result =
      CookMertz.evaluate units
        (unroll guess failureValue sourceValue combine fuel node) := by
  rw [profileEvaluate_eq_profileUnroll_internal]
  exact Workspace.profileEvaluate_result units
    (unroll guess failureValue sourceValue combine fuel node)

theorem unroll_eq_graphUnroll_of_prefix_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (cutoff fuel : ℕ) (node : Node workTapeCount)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ cutoff →
          ∀ tape : TapeIndex workTapeCount,
            guess.derivedCenter tape boundary.val =
              some (Guess.actualCenterTrajectory
                tm x blockLength tape boundary.val))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon)
    (hrankCutoff : node.rank ≤ cutoff + 1) :
    unroll guess failureValue sourceValue combine fuel (.graph node) =
      NeighborhoodGraph.unroll
        tm x blockLength sourceValue combine node := by
  induction fuel generalizing node with
  | zero =>
      cases node with
      | source tape block =>
          simp [unroll, NeighborhoodGraph.unroll, fanIn]
      | computation tape slot interval =>
          simp [Node.rank] at hrank
  | succ fuel ih =>
      cases node with
      | source tape block =>
          simp [unroll, NeighborhoodGraph.unroll, fanIn]
      | computation tape slot interval =>
          have hinterval : interval < horizon := by
            simp only [Node.rank] at hrank
            omega
          have hcutoff : interval ≤ cutoff := by
            simp only [Node.rank] at hrankCutoff
            omega
          have hlocalPrefix :
              ∀ boundary : Fin (horizon + 1),
                boundary.val ≤ interval →
                  ∀ currentTape : TapeIndex workTapeCount,
                    guess.derivedCenter
                        currentTape boundary.val =
                      some (Guess.actualCenterTrajectory
                        tm x blockLength currentTape
                          boundary.val) := by
            intro boundary hboundary currentTape
            exact hprefix boundary
              (hboundary.trans hcutoff) currentTape
          rw [unroll, dif_pos hinterval, NeighborhoodGraph.unroll]
          congr 1
          funext index
          have hpredecessor :=
            guess.predecessorAt?_eq_of_prefix
              tm x blockLength ⟨interval, hinterval⟩
                index hlocalPrefix
          have hrankChild :
              (NeighborhoodGraph.predecessorAt
                tm x blockLength interval index).rank ≤ fuel := by
            have hlt :=
              NeighborhoodGraph.predecessorAt_rank_lt
                tm x blockLength interval tape slot index
            have hlt' :
                (NeighborhoodGraph.predecessorAt
                  tm x blockLength interval index).rank <
                    interval + 1 := by
              simpa only [Node.rank] using hlt
            simp only [Node.rank] at hrank
            omega
          have hrankChildCutoff :
              (NeighborhoodGraph.predecessorAt
                tm x blockLength interval index).rank ≤
                  cutoff + 1 := by
            have hlt :=
              NeighborhoodGraph.predecessorAt_rank_lt
                tm x blockLength interval tape slot index
            have hlt' :
                (NeighborhoodGraph.predecessorAt
                  tm x blockLength interval index).rank <
                    interval + 1 := by
              simpa only [Node.rank] using hlt
            omega
          rw [show childAt guess
              (.graph (.computation tape slot interval)) index =
                .graph (NeighborhoodGraph.predecessorAt
                  tm x blockLength interval index) by
            simp [childAt, hinterval, hpredecessor]]
          exact ih
            (NeighborhoodGraph.predecessorAt
              tm x blockLength interval index)
            hrankChild (by omega) hrankChildCutoff

theorem unroll_eq_graphUnroll_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : Node workTapeCount)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon) :
    unroll guess failureValue sourceValue combine fuel (.graph node) =
      NeighborhoodGraph.unroll tm x blockLength sourceValue combine node := by
  induction fuel generalizing node with
  | zero =>
      cases node with
      | source tape block =>
          simp [unroll, NeighborhoodGraph.unroll, fanIn]
      | computation tape slot interval =>
          simp [Node.rank] at hrank
  | succ fuel ih =>
      cases node with
      | source tape block =>
          simp [unroll, NeighborhoodGraph.unroll, fanIn]
      | computation tape slot interval =>
          have hinterval : interval < horizon := by
            simp only [Node.rank] at hrank
            omega
          rw [unroll, dif_pos hinterval, NeighborhoodGraph.unroll]
          congr 1
          funext index
          have hpredecessor :=
            guess.predecessorAt?_eq tm x blockLength
              ⟨interval, hinterval⟩ index hvalid
          have hrankChild :
              (NeighborhoodGraph.predecessorAt tm x blockLength
                interval index).rank ≤ fuel := by
            have hlt :=
              NeighborhoodGraph.predecessorAt_rank_lt
                tm x blockLength interval tape slot index
            have hlt' :
                (NeighborhoodGraph.predecessorAt tm x blockLength
                  interval index).rank < interval + 1 := by
              simpa only [Node.rank] using hlt
            simp only [Node.rank] at hrank
            omega
          rw [show childAt guess
              (.graph (.computation tape slot interval)) index =
                .graph (NeighborhoodGraph.predecessorAt
                  tm x blockLength interval index) by
            simp [childAt, hinterval, hpredecessor]]
          exact ih
            (NeighborhoodGraph.predecessorAt
              tm x blockLength interval index)
            hrankChild (by omega)

theorem profileEvaluate_graph_eq_nodeValue_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : Node workTapeCount)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon)
    (hline : LineCompatible units
      (NeighborhoodGraph.unroll
        tm x blockLength sourceValue combine node)) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel (.graph node)).result =
      NeighborhoodGraph.nodeValue
        tm x blockLength sourceValue combine node := by
  rw [profileEvaluate_result_internal]
  rw [unroll_eq_graphUnroll_internal
    guess tm x blockLength failureValue sourceValue combine
    fuel node hvalid hrank hfuel]
  calc
    CookMertz.evaluate units
        (NeighborhoodGraph.unroll
          tm x blockLength sourceValue combine node) =
        (NeighborhoodGraph.unroll
          tm x blockLength sourceValue combine node).value :=
      CookMertz.evaluate_eq_value units _ hline
    _ = NeighborhoodGraph.nodeValue
          tm x blockLength sourceValue combine node :=
      NeighborhoodGraph.value_unroll
        tm x blockLength sourceValue combine node

theorem profileEvaluate_graph_eq_nodeValue_of_prefix_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (cutoff fuel : ℕ) (node : Node workTapeCount)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ cutoff →
          ∀ tape : TapeIndex workTapeCount,
            guess.derivedCenter tape boundary.val =
              some (Guess.actualCenterTrajectory
                tm x blockLength tape boundary.val))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon)
    (hrankCutoff : node.rank ≤ cutoff + 1)
    (hline : LineCompatible units
      (NeighborhoodGraph.unroll
        tm x blockLength sourceValue combine node)) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel (.graph node)).result =
      NeighborhoodGraph.nodeValue
        tm x blockLength sourceValue combine node := by
  rw [profileEvaluate_result_internal]
  rw [unroll_eq_graphUnroll_of_prefix_internal
    guess tm x blockLength failureValue sourceValue combine
    cutoff fuel node hprefix hrank hfuel hrankCutoff]
  calc
    CookMertz.evaluate units
        (NeighborhoodGraph.unroll
          tm x blockLength sourceValue combine node) =
        (NeighborhoodGraph.unroll
          tm x blockLength sourceValue combine node).value :=
      CookMertz.evaluate_eq_value units _ hline
    _ = NeighborhoodGraph.nodeValue
          tm x blockLength sourceValue combine node :=
      NeighborhoodGraph.value_unroll
        tm x blockLength sourceValue combine node

theorem stateRoot_eq_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    stateRoot guess =
      .graph
        (NeighborhoodGraph.DecisionRecovery.stateNode
          tm x blockLength horizon) := by
  cases horizon with
  | zero =>
      have hzero :=
        guess.isValidFor_iff.mp hvalid
          (⟨0, by omega⟩ : Fin (0 + 1))
          (TapeIndex.input workTapeCount)
      simpa [stateRoot,
        NeighborhoodGraph.DecisionRecovery.stateNode,
        NeighborhoodGraph.chronologicalPredecessor,
        Guess.CenterGuess.derivedCenter,
        Guess.actualCenterTrajectory] using hzero
  | succ previous =>
      rfl

private theorem priorIntervals_boundary_eq
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    guess.priorIntervals tape block horizon =
      NeighborhoodGraph.priorIntervals tm x blockLength tape block horizon := by
  ext previous
  simp only [Guess.CenterGuess.priorIntervals,
    NeighborhoodGraph.priorIntervals, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hagree :=
    guess.isValidFor_iff.mp hvalid
      (⟨previous.val, by omega⟩ : Fin (horizon + 1)) tape
  rw [hagree]
  simp [Guess.actualCenterTrajectory]

private theorem previousInterval_boundary_eq
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    guess.previousInterval tape block horizon =
      NeighborhoodGraph.previousInterval
        tm x blockLength tape block horizon := by
  unfold Guess.CenterGuess.previousInterval
  unfold NeighborhoodGraph.previousInterval
  rw [priorIntervals_boundary_eq
    guess tm x blockLength tape block hvalid]

theorem latestBlockRoot_eq_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    latestBlockRoot guess tape block =
      .graph
        (NeighborhoodGraph.DecisionRecovery.latestBlockNode
          tm x blockLength horizon tape block) := by
  unfold latestBlockRoot
  unfold NeighborhoodGraph.DecisionRecovery.latestBlockNode
  rw [previousInterval_boundary_eq
    guess tm x blockLength tape block hvalid]
  generalize hprevious :
    NeighborhoodGraph.previousInterval
      tm x blockLength tape block horizon = previous
  cases previous with
  | none => rfl
  | some previous =>
      have hagree :=
        guess.isValidFor_iff.mp hvalid
          (⟨previous.val, by omega⟩ : Fin (horizon + 1)) tape
      simp only [Guess.actualCenterTrajectory] at hagree
      simp [hagree]

theorem verdictRoot_eq_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    verdictRoot guess blockLength =
      .graph
        (NeighborhoodGraph.DecisionRecovery.verdictBlockNode
          tm x blockLength horizon) := by
  exact latestBlockRoot_eq_internal
    guess tm x blockLength
      (TapeIndex.output workTapeCount)
      (blockIndex blockLength 1) hvalid

theorem stateRoot_rank_le_internal
    (guess : Guess.CenterGuess workTapeCount horizon) :
    (stateRoot guess).rank ≤ horizon := by
  cases horizon <;> simp [stateRoot, QueryNode.rank, Node.rank]

theorem latestBlockRoot_rank_le_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    (latestBlockRoot guess tape block).rank ≤ horizon := by
  unfold latestBlockRoot
  split <;> rename_i hprevious
  · simp [QueryNode.rank, Node.rank]
  · split <;> rename_i hcenter
    · simp [QueryNode.rank]
    · simp only [QueryNode.rank, Node.rank]
      omega

theorem verdictRoot_rank_le_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (blockLength : ℕ) :
    (verdictRoot guess blockLength).rank ≤ horizon :=
  latestBlockRoot_rank_le_internal guess
    (TapeIndex.output workTapeCount) (blockIndex blockLength 1)

theorem profileDecision_result_eq_nodeValues_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hstateLine : LineCompatible units
      (NeighborhoodGraph.unroll tm x blockLength sourceValue combine
        (NeighborhoodGraph.DecisionRecovery.stateNode
          tm x blockLength horizon)))
    (hverdictLine : LineCompatible units
      (NeighborhoodGraph.unroll tm x blockLength sourceValue combine
        (NeighborhoodGraph.DecisionRecovery.verdictBlockNode
          tm x blockLength horizon))) :
    (profileDecision units guess blockLength failureValue
      sourceValue combine).result =
      (NeighborhoodGraph.nodeValue tm x blockLength sourceValue combine
          (NeighborhoodGraph.DecisionRecovery.stateNode
            tm x blockLength horizon),
        NeighborhoodGraph.nodeValue tm x blockLength sourceValue combine
          (NeighborhoodGraph.DecisionRecovery.verdictBlockNode
            tm x blockLength horizon)) := by
  change
    ((profileEvaluate units guess failureValue sourceValue combine horizon
        (stateRoot guess)).result,
      (profileEvaluate units guess failureValue sourceValue combine horizon
        (verdictRoot guess blockLength)).result) = _
  apply Prod.ext
  · have hrank := stateRoot_rank_le_internal guess
    rw [stateRoot_eq_internal
      guess tm x blockLength hvalid] at hrank ⊢
    exact profileEvaluate_graph_eq_nodeValue_internal
      units guess tm x blockLength failureValue sourceValue combine
      horizon
      (NeighborhoodGraph.DecisionRecovery.stateNode
        tm x blockLength horizon)
      hvalid hrank (le_refl _) hstateLine
  · have hrank := verdictRoot_rank_le_internal guess blockLength
    rw [verdictRoot_eq_internal
      guess tm x blockLength hvalid] at hrank ⊢
    exact profileEvaluate_graph_eq_nodeValue_internal
      units guess tm x blockLength failureValue sourceValue combine
      horizon
      (NeighborhoodGraph.DecisionRecovery.verdictBlockNode
        tm x blockLength horizon)
      hvalid hrank (le_refl _) hverdictLine

theorem profileDecision_peakFrames_le_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (blockLength : ℕ) (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    (profileDecision units guess blockLength failureValue
      sourceValue combine).peakFrames ≤ horizon + 1 := by
  simp only [profileDecision]
  apply max_le
  · exact profileEvaluate_peakFrames_le_internal
      units guess failureValue sourceValue combine horizon (stateRoot guess)
  · exact profileEvaluate_peakFrames_le_internal
      units guess failureValue sourceValue combine horizon
        (verdictRoot guess blockLength)

theorem profileCandidate_peakFrames_le_internal
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (candidateTime : ℕ)
    (guess : Guess.CenterGuess workTapeCount
      (candidateHorizon candidateTime))
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    (profileCandidate units candidateTime guess failureValue
      sourceValue combine).peakFrames ≤
      candidateHorizon candidateTime + 1 := by
  exact profileDecision_peakFrames_le_internal
    units guess (candidateBlockLength candidateTime)
      failureValue sourceValue combine

theorem streamedPeak_append_internal (first second : List ℕ) :
    streamedPeak (first ++ second) =
      second.foldl max (streamedPeak first) := by
  simp [streamedPeak, List.foldl_append]

theorem streamedPeak_le_internal
    (peaks : List ℕ) (bound : ℕ)
    (hpeaks : ∀ peak ∈ peaks, peak ≤ bound) :
    streamedPeak peaks ≤ bound := by
  have aux :
      ∀ (items : List ℕ) (accumulator : ℕ),
        (∀ peak ∈ items, peak ≤ bound) →
        accumulator ≤ bound →
        items.foldl max accumulator ≤ bound := by
    intro items
    induction items with
    | nil =>
        intro accumulator _ haccumulator
        exact haccumulator
    | cons peak items ih =>
        intro accumulator hitems haccumulator
        rw [List.foldl_cons]
        apply ih
        · intro item hitem
          exact hitems item (by simp [hitem])
        · apply max_le haccumulator
          exact hitems peak (by simp)
  exact aux peaks 0 hpeaks (Nat.zero_le _)

private theorem activeStack_length_add_headRank_le
    {guess : Guess.CenterGuess workTapeCount horizon}
    {root : QueryNode workTapeCount horizon}
    {stack : List (QueryNode workTapeCount horizon)}
    (hstack : ActiveStack guess root stack) :
    stack.length + (stack.headD root).rank ≤ root.rank + 1 := by
  induction hstack with
  | root =>
      simp only [List.length_cons, List.length_nil, List.headD_cons]
      omega
  | push hstack hchild ih =>
      have hrank := childStep_rank_lt_internal hchild
      simp only [List.length_cons, List.headD_cons] at ih ⊢
      omega

theorem activeStack_length_add_rank_le_internal
    {guess : Guess.CenterGuess workTapeCount horizon}
    {root current : QueryNode workTapeCount horizon}
    {tail : List (QueryNode workTapeCount horizon)}
    (hstack : ActiveStack guess root (current :: tail)) :
    (current :: tail).length + current.rank ≤ root.rank + 1 := by
  simpa using activeStack_length_add_headRank_le hstack

theorem activeStack_length_le_internal
    {guess : Guess.CenterGuess workTapeCount horizon}
    {root current : QueryNode workTapeCount horizon}
    {tail : List (QueryNode workTapeCount horizon)}
    (hstack : ActiveStack guess root (current :: tail)) :
    (current :: tail).length ≤ root.rank + 1 := by
  have h :=
    activeStack_length_add_rank_le_internal hstack
  omega

theorem activeStack_prefixBitUsage_le_internal
    (layout : StorageLayout)
    {guess : Guess.CenterGuess workTapeCount horizon}
    {root current : QueryNode workTapeCount horizon}
    {tail : List (QueryNode workTapeCount horizon)}
    (hroot : root.rank ≤ horizon)
    (hstack : ActiveStack guess root (current :: tail)) :
    prefixBitUsage layout workTapeCount horizon
        (current :: tail).length ≤
      peakBitBound layout workTapeCount horizon := by
  unfold prefixBitUsage peakBitBound
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_right
    (frameBitBudget layout workTapeCount)
    ((activeStack_length_le_internal hstack).trans
      (Nat.add_le_add_right hroot 1))

theorem profileDecision_prefixBitUsage_le_internal
    [Field F] [AddCommGroup V] [Module F V]
    (layout : StorageLayout)
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (blockLength : ℕ) (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    prefixBitUsage layout workTapeCount horizon
        (profileDecision units guess blockLength failureValue
          sourceValue combine).peakFrames ≤
      peakBitBound layout workTapeCount horizon := by
  unfold prefixBitUsage peakBitBound
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_right
    (frameBitBudget layout workTapeCount)
    (profileDecision_peakFrames_le_internal
      units guess blockLength failureValue sourceValue combine)

theorem profileCandidate_prefixBitUsage_le_internal
    [Field F] [AddCommGroup V] [Module F V]
    (layout : StorageLayout)
    (units : List Fˣ) (candidateTime : ℕ)
    (guess : Guess.CenterGuess workTapeCount
      (candidateHorizon candidateTime))
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    prefixBitUsage layout workTapeCount
        (candidateHorizon candidateTime)
        (profileCandidate units candidateTime guess failureValue
          sourceValue combine).peakFrames ≤
      candidatePeakBitBound layout workTapeCount candidateTime := by
  exact profileDecision_prefixBitUsage_le_internal
    layout units guess (candidateBlockLength candidateTime)
      failureValue sourceValue combine

theorem semanticCenterOracle_agreesWith_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) :
    (semanticCenterOracle tm x blockLength horizon).AgreesWith
      (Guess.actualCenterTrajectory tm x blockLength) := by
  constructor
  · intro tape
    rfl
  · intro interval tape
    rfl

theorem actualCenterGuess_passesSemanticChecks_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength) :
    passesLocalChecks
      (Guess.actualCenterGuess tm x blockLength horizon)
      (semanticCenterOracle tm x blockLength horizon) = true := by
  apply decide_eq_true
  constructor
  · intro tape
    rfl
  · intro interval tape
    exact Guess.actualCenterGuess_derivedCenter
      tm x blockLength horizon (interval.val + 1) tape
      hpositive (by omega)

theorem agreesWith_isPrefixSoundFor_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (oracle : CenterOracle workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (hagrees : oracle.AgreesWith trajectory) :
    oracle.IsPrefixSoundFor guess trajectory := by
  rcases hagrees with ⟨hinitial, hend⟩
  exact ⟨hinitial, fun interval _ tape => hend interval tape⟩

theorem passesLocalChecks_prefixSound_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (oracle : CenterOracle workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (hpasses : passesLocalChecks guess oracle = true)
    (horacle : oracle.IsPrefixSoundFor guess trajectory) :
    guess.IsValidFor trajectory := by
  have hchecks :
      (∀ tape, guess.initialCenter tape = oracle.initialCenter tape) ∧
      ∀ interval tape,
        guess.derivedCenter tape (interval.val + 1) =
          some (oracle.endCenter interval tape) := by
    exact of_decide_eq_true hpasses
  have hagree :
      ∀ boundary, boundary ≤ horizon →
        ∀ tape,
          guess.derivedCenter tape boundary =
            some (trajectory tape boundary) := by
    intro boundary
    induction boundary using Nat.strong_induction_on with
    | h boundary ih =>
        intro hboundary tape
        cases boundary with
        | zero =>
            simp [Guess.CenterGuess.derivedCenter,
              hchecks.1 tape, horacle.1 tape]
        | succ previous =>
            have hprevious : previous < horizon := by omega
            have hprefix :
                ∀ (earlier : Fin (horizon + 1)),
                  earlier.val ≤ previous →
                  ∀ earlierTape,
                    guess.derivedCenter earlierTape earlier.val =
                      some (trajectory earlierTape earlier.val) := by
              intro earlier hearlier earlierTape
              exact ih earlier.val (by omega) (by omega) earlierTape
            have hend :=
              horacle.2 (⟨previous, hprevious⟩ : Fin horizon)
                hprefix tape
            have hcheck :=
              hchecks.2
                (⟨previous, hprevious⟩ : Fin horizon) tape
            rw [hend] at hcheck
            exact hcheck
  apply guess.isValidFor_iff.mpr
  intro boundary tape
  exact hagree boundary.val (by omega) tape

theorem passesLocalChecks_sound_internal
    (guess : Guess.CenterGuess workTapeCount horizon)
    (oracle : CenterOracle workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (hpasses : passesLocalChecks guess oracle = true)
    (horacle : oracle.AgreesWith trajectory) :
    guess.IsValidFor trajectory := by
  exact passesLocalChecks_prefixSound_internal
    guess oracle trajectory hpasses
      (agreesWith_isPrefixSoundFor_internal
        guess oracle trajectory horacle)

end Internal

end NeighborhoodEvaluator

end TimeSpaceSimulation

end Complexity
