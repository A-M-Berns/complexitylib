/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.InstanceBounds.Defs

/-!
# Operational bounds for runtime neighborhood instances -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodProgram
namespace InstanceBounds
namespace Internal

open NeighborhoodGraph
open NeighborhoodGraph.Guess

theorem guess_initialCenter_eq_zero_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : ResidueInstance tm)
    (tape : TapeIndex workTapeCount) :
    instanceData.guess.initialCenter tape = 0 := by
  rw [instanceData.guess_eq]
  rfl

private theorem CenterMove.apply_le_succ
    (move : CenterMove) {center next : ℕ}
    (happly : move.apply center = some next) :
    next ≤ center + 1 := by
  cases move with
  | left =>
      cases center with
      | zero =>
          simp [CenterMove.apply] at happly
      | succ center =>
          simp [CenterMove.apply] at happly
          omega
  | stay =>
      simp [CenterMove.apply] at happly
      omega
  | right =>
      simp [CenterMove.apply] at happly
      omega

theorem derivedCenter_le_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    {boundary center : ℕ}
    (hcenter :
      instanceData.guess.derivedCenter tape boundary = some center) :
    center ≤ boundary := by
  induction boundary generalizing center with
  | zero =>
      simp [CenterGuess.derivedCenter,
        guess_initialCenter_eq_zero_internal instanceData tape] at hcenter
      omega
  | succ boundary ih =>
      simp only [CenterGuess.derivedCenter] at hcenter
      split at hcenter
      · next hboundary =>
          cases hprevious :
              instanceData.guess.derivedCenter tape boundary with
          | none =>
              simp [hprevious] at hcenter
          | some previous =>
              simp only [hprevious, Option.bind_some] at hcenter
              have hpreviousLe : previous ≤ boundary :=
                ih hprevious
              have hstep :
                  center ≤ previous + 1 :=
                CenterMove.apply_le_succ
                  (instanceData.guess.movement
                    ⟨boundary, hboundary⟩ tape)
                  hcenter
              omega
      · simp at hcenter

private theorem neighborBlock_le_succ
    (center : ℕ) (slot : Slot) :
    neighborBlock center slot ≤ center + 1 := by
  cases slot <;> simp [neighborBlock]
  all_goals omega

theorem contentPredecessor?_within_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    {node : Node workTapeCount}
    (hnode :
      instanceData.guess.contentPredecessor?
        interval tape slot = some node) :
    NodeWithin instanceData.horizon node := by
  unfold CenterGuess.contentPredecessor? at hnode
  cases hcenter :
      instanceData.guess.derivedCenter tape interval.val with
  | none =>
      simp [hcenter] at hnode
  | some center =>
      simp only [hcenter] at hnode
      cases hprevious :
          instanceData.guess.previousInterval tape
            (neighborBlock center slot) interval.val with
      | none =>
          simp only [hprevious, Option.some.injEq] at hnode
          subst node
          simp only [NodeWithin]
          have hcenterLe :=
            derivedCenter_le_internal instanceData tape hcenter
          exact
            (neighborBlock_le_succ center slot).trans
              (by omega)
      | some previous =>
          simp only [hprevious] at hnode
          cases hpreviousCenter :
              instanceData.guess.derivedCenter tape previous.val with
          | none =>
              simp [hpreviousCenter] at hnode
          | some previousCenter =>
              simp only [hpreviousCenter, Option.some.injEq] at hnode
              subst node
              simp only [NodeWithin]
              exact previous.isLt.trans interval.isLt

theorem chronologicalPredecessor?_within_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (tape : TapeIndex workTapeCount)
    {node : Node workTapeCount}
    (hnode :
      instanceData.guess.chronologicalPredecessor?
        interval tape = some node) :
    NodeWithin instanceData.horizon node := by
  unfold CenterGuess.chronologicalPredecessor? at hnode
  cases hcenter :
      instanceData.guess.derivedCenter tape interval.val with
  | none =>
      simp [hcenter] at hnode
  | some center =>
      simp only [hcenter] at hnode
      cases hinterval : interval.val with
      | zero =>
          simp [hinterval] at hnode
          subst node
          simp only [NodeWithin]
          have hcenterLe :=
            derivedCenter_le_internal instanceData tape hcenter
          omega
      | succ previous =>
          simp [hinterval] at hnode
          subst node
          simp only [NodeWithin]
          omega

theorem predecessor?_within_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (index : PredecessorIndex workTapeCount)
    {node : Node workTapeCount}
    (hnode :
      instanceData.guess.predecessor? interval index = some node) :
    NodeWithin instanceData.horizon node := by
  rcases index with ⟨kind, tape⟩
  cases kind with
  | content slot =>
      exact
        contentPredecessor?_within_internal
          instanceData interval tape slot
            (by simpa [CenterGuess.predecessor?] using hnode)
  | chronological =>
      exact
        chronologicalPredecessor?_within_internal
          instanceData interval tape
            (by simpa [CenterGuess.predecessor?] using hnode)

theorem predecessorAt?_within_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (index :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    {node : Node workTapeCount}
    (hnode :
      instanceData.guess.predecessorAt? interval index = some node) :
    NodeWithin instanceData.horizon node := by
  exact
    predecessor?_within_internal instanceData interval
      ((predecessorIndexEquiv workTapeCount).symm index) hnode

theorem childAt_within_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : ResidueInstance tm)
    (query :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (index :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)) :
    QueryNodeWithin instanceData.horizon
      (NeighborhoodEvaluator.childAt instanceData.guess query index) := by
  cases query with
  | failure =>
      simp [NeighborhoodEvaluator.childAt, QueryNodeWithin]
  | graph node =>
      cases node with
      | source tape block =>
          simp [NeighborhoodEvaluator.childAt, QueryNodeWithin]
      | computation tape slot interval =>
          simp only [NeighborhoodEvaluator.childAt]
          split
          · next hinterval =>
              cases hpredecessor :
                  instanceData.guess.predecessorAt?
                    ⟨interval, hinterval⟩ index with
              | none =>
                  simp [QueryNodeWithin]
              | some predecessor =>
                  simp only [QueryNodeWithin]
                  exact
                    predecessorAt?_within_internal
                      instanceData ⟨interval, hinterval⟩
                        index hpredecessor
          · simp [QueryNodeWithin]

end Internal
end InstanceBounds
end NeighborhoodProgram
end Runtime
end TimeSpaceSimulation
end Complexity
