/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.FrameBounds.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.InstanceBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial
import Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime

/-!
# Numeric frame invariants for the neighborhood scheduler -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace FrameBounds
namespace Internal

open NeighborhoodGraph
open NeighborhoodExecutableEvaluation

theorem fieldModulus_one_lt_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    1 < fieldModulus instanceData := by
  unfold fieldModulus NeighborhoodExecutableEvaluation.modulus
  exact
    (TreeEval.CookMertz.PrimeField.Search.searchModulus_prime _).one_lt

theorem queryBound_childAt_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (query :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    QueryBound instanceData.horizon
      (NeighborhoodEvaluator.childAt instanceData.guess query child) := by
  have hbound :=
    NeighborhoodProgram.InstanceBounds.childAt_within
      instanceData query child
  generalize hchild :
      NeighborhoodEvaluator.childAt instanceData.guess query child =
        childNode at hbound ⊢
  cases childNode with
  | failure =>
      simp [QueryBound]
  | graph node =>
      cases node with
      | source tape block =>
          simp only [
            NeighborhoodProgram.InstanceBounds.QueryNodeWithin,
            NeighborhoodProgram.InstanceBounds.NodeWithin] at hbound
          simp only [QueryBound]
          exact hbound.trans (Nat.le_max_left _ _)
      | computation tape slot interval =>
          simpa only [QueryBound,
            NeighborhoodProgram.InstanceBounds.QueryNodeWithin,
            NeighborhoodProgram.InstanceBounds.NodeWithin] using hbound

theorem frameBound_prepareChild_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount))
    (hbound : FrameBound frame) :
    FrameBound (frame.prepareChild child) := by
  have hmodulus : 0 < fieldModulus instanceData := by
    have hone := fieldModulus_one_lt_internal instanceData
    omega
  rcases hbound with ⟨hfuel, hnode, hscalar, hphase⟩
  refine
    ⟨(Nat.sub_le frame.fuel 1).trans hfuel,
      queryBound_childAt_internal instanceData frame.node child,
      TreeEval.CookMertz.PrimeField.Runtime.normalize_lt hmodulus,
      ?_⟩
  simp [Frame.prepareChild, PhaseBound]

theorem frameBound_cleanupChild_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount))
    (hbound : FrameBound frame) :
    FrameBound (frame.cleanupChild child) := by
  have hmodulus : 0 < fieldModulus instanceData := by
    have hone := fieldModulus_one_lt_internal instanceData
    omega
  rcases hbound with ⟨hfuel, hnode, hscalar, hphase⟩
  refine
    ⟨(Nat.sub_le frame.fuel 1).trans hfuel,
      queryBound_childAt_internal instanceData frame.node child,
      TreeEval.CookMertz.PrimeField.Runtime.sub_lt hmodulus,
      ?_⟩
  simp [Frame.cleanupChild, PhaseBound]

private theorem queryBound_stateRoot_of_initialCenter
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hinitial :
      guess.initialCenter (TapeIndex.input workTapeCount) = 0) :
    QueryBound horizon (NeighborhoodEvaluator.stateRoot guess) := by
  cases horizon with
  | zero =>
      simp [NeighborhoodEvaluator.stateRoot, QueryBound, hinitial]
  | succ previous =>
      simp [NeighborhoodEvaluator.stateRoot, QueryBound]

theorem queryBound_stateRoot_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    QueryBound instanceData.horizon
      (NeighborhoodEvaluator.stateRoot instanceData.guess) := by
  exact queryBound_stateRoot_of_initialCenter instanceData.guess
    (NeighborhoodProgram.InstanceBounds.guess_initialCenter_eq_zero
      instanceData (TapeIndex.input workTapeCount))

theorem queryBound_verdictRoot_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    QueryBound instanceData.horizon
      (NeighborhoodEvaluator.verdictRoot
        instanceData.guess instanceData.blockLength) := by
  unfold NeighborhoodEvaluator.verdictRoot
  unfold NeighborhoodEvaluator.latestBlockRoot
  split
  · simp only [QueryBound]
    have hblock :
        blockIndex instanceData.blockLength 1 ≤ 1 := by
      unfold blockIndex
      exact Nat.div_le_self 1 instanceData.blockLength
    exact hblock.trans (Nat.le_max_right _ _)
  · split
    · simp [QueryBound]
    · simp only [QueryBound]
      exact ‹Fin instanceData.horizon›.isLt

theorem stateBound_initial_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (fuel : ℕ)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hfuel : fuel ≤ instanceData.horizon)
    (hnode : QueryBound instanceData.horizon node)
    (hscalar : scalar < fieldModulus instanceData) :
    StateBound
      (NeighborhoodScheduler.State.initial
        fuel node scalar out registers) := by
  simp [StateBound, NeighborhoodScheduler.State.initial, FrameBound,
    PhaseBound, hfuel, hnode, hscalar]

private theorem stateBound_drop
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (oldFrame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hstate : StateBound ⟨oldFrame :: tail, registers⟩) :
    StateBound ⟨tail, registers'⟩ := by
  intro frame hframe
  exact hstate frame (by simp [hframe])

private theorem stateBound_replace
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (oldFrame newFrame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hstate : StateBound ⟨oldFrame :: tail, registers⟩)
    (hnew : FrameBound newFrame) :
    StateBound ⟨newFrame :: tail, registers'⟩ := by
  intro frame hframe
  simp only [List.mem_cons] at hframe
  rcases hframe with rfl | htail
  · exact hnew
  · exact hstate frame (by simp [htail])

private theorem stateBound_push
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (oldFrame child parent : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hstate : StateBound ⟨oldFrame :: tail, registers⟩)
    (hchild : FrameBound child)
    (hparent : FrameBound parent) :
    StateBound ⟨child :: parent :: tail, registers'⟩ := by
  intro frame hframe
  simp only [List.mem_cons] at hframe
  rcases hframe with rfl | rfl | htail
  · exact hchild
  · exact hparent
  · exact hstate frame (by simp [htail])

theorem stateBound_next_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateBound state) :
    StateBound state.next := by
  rcases state with ⟨stack, registers⟩
  cases stack with
  | nil =>
      simp [StateBound, State.next]
  | cons frame tail =>
      cases frame with
      | mk fuel node scalar out phase =>
          cases phase with
          | enter =>
              cases node with
              | failure =>
                  simpa [State.next] using
                    (stateBound_drop
                      { fuel := fuel, node := .failure,
                        scalar := scalar, out := out, phase := .enter }
                      tail registers
                      (addScaledAt instanceData registers out scalar
                        (Residue.failureValue
                          tm instanceData.blockLength))
                      hstate)
              | graph graphNode =>
                  cases graphNode with
                  | source tape block =>
                      simpa [State.next] using
                        (stateBound_drop
                          { fuel := fuel,
                            node := .graph (.source tape block),
                            scalar := scalar, out := out,
                            phase := .enter }
                          tail registers
                          (addScaledAt instanceData registers out scalar
                            (Residue.sourceValue
                              (tm := tm) (x := instanceData.x)
                              (blockLength := instanceData.blockLength)
                              (encoding := instanceData.encoding)
                              (hpositive := instanceData.positive)
                              tape block))
                          hstate)
                  | computation tape slot interval =>
                      cases fuel with
                      | zero =>
                          simpa [State.next] using
                            (stateBound_drop
                              { fuel := 0,
                                node := .graph
                                  (.computation tape slot interval),
                                scalar := scalar, out := out,
                                phase := .enter }
                              tail registers
                              (addScaledAt instanceData registers out scalar
                                (Residue.failureValue
                                  tm instanceData.blockLength))
                              hstate)
                      | succ fuel =>
                          by_cases hinterval :
                              interval < instanceData.horizon
                          · cases hresidues :
                              Frame.residueCount instanceData with
                            | zero =>
                                simpa [State.next, hinterval, hresidues] using
                                  (stateBound_drop
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase := .enter }
                                    tail registers registers hstate)
                            | succ residuesLeft =>
                                have hold :=
                                  hstate
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase := .enter }
                                    (by simp)
                                have hmodulus :=
                                  fieldModulus_one_lt_internal
                                    instanceData
                                have hnew :
                                    FrameBound
                                      ({
                                          fuel := fuel + 1,
                                          node := .graph
                                            (.computation tape slot interval),
                                          scalar := scalar, out := out,
                                          phase :=
                                            .prepare 1 residuesLeft 0
                                        } : Frame tm instanceData) := by
                                  simp only [FrameBound, PhaseBound] at hold ⊢
                                  rcases hold with
                                    ⟨hfuel, hnode, hscalar, _⟩
                                  refine
                                    ⟨hfuel, hnode, hscalar, ?_,
                                      by omega⟩
                                  unfold Frame.residueCount at hresidues
                                  omega
                                simpa [State.next, hinterval, hresidues] using
                                  (stateBound_replace
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase := .enter }
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase :=
                                        .prepare 1 residuesLeft 0 }
                                    tail registers registers hstate hnew)
                          · simpa [State.next, hinterval] using
                              (stateBound_drop
                                { fuel := fuel + 1,
                                  node := .graph
                                    (.computation tape slot interval),
                                  scalar := scalar, out := out,
                                  phase := .enter }
                                tail registers
                                (addScaledAt instanceData registers out scalar
                                  (Residue.failureValue
                                    tm instanceData.blockLength))
                                hstate)
          | prepare residue residuesLeft childIndex =>
              by_cases hchild :
                  childIndex < graphFanIn workTapeCount
              · let oldFrame : Frame tm instanceData :=
                  { fuel := fuel, node := node, scalar := scalar,
                    out := out,
                    phase := .prepare residue residuesLeft childIndex }
                let child : Fin (graphFanIn workTapeCount) :=
                  ⟨childIndex, hchild⟩
                let parent : Frame tm instanceData :=
                  { oldFrame with
                    phase :=
                      .prepare residue residuesLeft (childIndex + 1) }
                have hold : FrameBound oldFrame :=
                  hstate oldFrame (by simp [oldFrame])
                have hmodulus :
                    0 < fieldModulus instanceData := by
                  have hone :=
                    fieldModulus_one_lt_internal instanceData
                  omega
                have hchildBound :
                    FrameBound (oldFrame.prepareChild child) := by
                  rcases hold with
                    ⟨hfuel, hnode, hscalar, hphase⟩
                  refine
                    ⟨(Nat.sub_le fuel 1).trans hfuel,
                      queryBound_childAt_internal
                        instanceData node child,
                      TreeEval.CookMertz.PrimeField.Runtime.normalize_lt
                        hmodulus,
                      ?_⟩
                  simp [Frame.prepareChild, PhaseBound]
                have hparentBound : FrameBound parent := by
                  simpa [FrameBound, PhaseBound, oldFrame, parent] using
                    ⟨hold.1, hold.2.1, hold.2.2.1,
                      hold.2.2.2.1, by omega⟩
                simpa [State.next, hchild, oldFrame, child, parent] using
                  (stateBound_push oldFrame
                    (oldFrame.prepareChild child) parent tail registers
                    (Residue.scaleAt
                      tm instanceData.blockLength residue registers
                      (oldFrame.childTarget child))
                    hstate hchildBound hparentBound)
              · let oldFrame : Frame tm instanceData :=
                  { fuel := fuel, node := node, scalar := scalar,
                    out := out,
                    phase := .prepare residue residuesLeft childIndex }
                let nextFrame : Frame tm instanceData :=
                  { oldFrame with
                    phase := .combine residue residuesLeft }
                have hold : FrameBound oldFrame :=
                  hstate oldFrame (by simp [oldFrame])
                have hnext : FrameBound nextFrame := by
                  rcases hold with
                    ⟨hfuel, hnode, hscalar, hphase⟩
                  exact
                    ⟨hfuel, hnode, hscalar, hphase.1⟩
                simpa [State.next, hchild, oldFrame, nextFrame] using
                  (stateBound_replace oldFrame nextFrame tail registers
                    registers hstate hnext)
          | combine residue residuesLeft =>
              let oldFrame : Frame tm instanceData :=
                { fuel := fuel, node := node, scalar := scalar,
                  out := out, phase := .combine residue residuesLeft }
              let nextFrame : Frame tm instanceData :=
                { oldFrame with
                  phase := .cleanupCall residue residuesLeft 0 }
              have hold : FrameBound oldFrame :=
                hstate oldFrame (by simp [oldFrame])
              have hnext : FrameBound nextFrame := by
                rcases hold with
                  ⟨hfuel, hnode, hscalar, hphase⟩
                exact
                  ⟨hfuel, hnode, hscalar, hphase, by omega⟩
              cases node with
              | failure =>
                  simpa [State.next, oldFrame, nextFrame] using
                    (stateBound_replace oldFrame nextFrame tail registers
                      registers hstate hnext)
              | graph graphNode =>
                  cases graphNode with
                  | source tape block =>
                      simpa [State.next, oldFrame, nextFrame] using
                        (stateBound_replace oldFrame nextFrame tail registers
                          registers hstate hnext)
                  | computation tape slot interval =>
                      simpa [State.next, oldFrame, nextFrame] using
                        (stateBound_replace oldFrame nextFrame tail registers
                          (addScaledAt instanceData registers out
                            (TreeEval.CookMertz.PrimeField.Runtime.sub
                              (fieldModulus instanceData) 0 scalar)
                            (combineResidues
                              (tm := tm) (x := instanceData.x)
                              (blockLength := instanceData.blockLength)
                              (encoding := instanceData.encoding)
                              (hpositive := instanceData.positive)
                              tape slot interval
                              (fun child =>
                                registers
                                  (oldFrame.childTarget child))))
                          hstate hnext)
          | cleanupCall residue residuesLeft childIndex =>
              by_cases hchild :
                  childIndex < graphFanIn workTapeCount
              · let oldFrame : Frame tm instanceData :=
                  { fuel := fuel, node := node, scalar := scalar,
                    out := out,
                    phase :=
                      .cleanupCall residue residuesLeft childIndex }
                let child : Fin (graphFanIn workTapeCount) :=
                  ⟨childIndex, hchild⟩
                let parent : Frame tm instanceData :=
                  { oldFrame with
                    phase :=
                      .cleanupScale residue residuesLeft child
                        (childIndex + 1) }
                have hold : FrameBound oldFrame :=
                  hstate oldFrame (by simp [oldFrame])
                have hmodulus :
                    0 < fieldModulus instanceData := by
                  have hone :=
                    fieldModulus_one_lt_internal instanceData
                  omega
                have hchildBound :
                    FrameBound (oldFrame.cleanupChild child) := by
                  rcases hold with
                    ⟨hfuel, hnode, hscalar, hphase⟩
                  refine
                    ⟨(Nat.sub_le fuel 1).trans hfuel,
                      queryBound_childAt_internal
                        instanceData node child,
                      TreeEval.CookMertz.PrimeField.Runtime.sub_lt
                        hmodulus,
                      ?_⟩
                  simp [Frame.cleanupChild, PhaseBound]
                have hparentBound : FrameBound parent := by
                  simpa [FrameBound, PhaseBound, oldFrame, parent] using
                    ⟨hold.1, hold.2.1, hold.2.2.1,
                      hold.2.2.2.1, by omega⟩
                simpa [State.next, hchild, oldFrame, child, parent] using
                  (stateBound_push oldFrame
                    (oldFrame.cleanupChild child) parent tail registers
                    registers hstate hchildBound hparentBound)
              · cases residuesLeft with
                | zero =>
                    simpa [State.next, hchild, State.finishResidue] using
                      (stateBound_drop
                        { fuel := fuel, node := node, scalar := scalar,
                          out := out,
                          phase :=
                            .cleanupCall residue 0 childIndex }
                        tail registers registers hstate)
                | succ residuesLeft =>
                    let oldFrame : Frame tm instanceData :=
                      { fuel := fuel, node := node, scalar := scalar,
                        out := out,
                        phase :=
                          .cleanupCall residue (residuesLeft + 1)
                            childIndex }
                    let nextFrame : Frame tm instanceData :=
                      { oldFrame with
                        phase :=
                          .prepare (residue + 1) residuesLeft 0 }
                    have hold : FrameBound oldFrame :=
                      hstate oldFrame (by simp [oldFrame])
                    have hnext : FrameBound nextFrame := by
                      rcases hold with
                        ⟨hfuel, hnode, hscalar, hphase⟩
                      simp only [oldFrame, PhaseBound] at hphase
                      refine
                        ⟨hfuel, hnode, hscalar, ?_⟩
                      change
                        residue + 1 + residuesLeft + 1 =
                            fieldModulus instanceData ∧
                          0 ≤ graphFanIn workTapeCount
                      constructor <;> omega
                    simpa [State.next, hchild, State.finishResidue,
                      oldFrame, nextFrame] using
                      (stateBound_replace oldFrame nextFrame tail registers
                        registers hstate hnext)
          | cleanupScale residue residuesLeft child nextChildIndex =>
              let oldFrame : Frame tm instanceData :=
                { fuel := fuel, node := node, scalar := scalar,
                  out := out,
                  phase := .cleanupScale residue residuesLeft child
                    nextChildIndex }
              let nextFrame : Frame tm instanceData :=
                { oldFrame with
                  phase :=
                    .cleanupCall residue residuesLeft nextChildIndex }
              have hold : FrameBound oldFrame :=
                hstate oldFrame (by simp [oldFrame])
              have hnext : FrameBound nextFrame := by
                simpa [FrameBound, PhaseBound, oldFrame, nextFrame] using
                  hold
              simpa [State.next, oldFrame, nextFrame] using
                (stateBound_replace oldFrame nextFrame tail registers
                  (Residue.scaleAt
                    tm instanceData.blockLength
                    (TreeEval.CookMertz.PrimeField.Runtime.inverse
                      (fieldModulus instanceData) residue)
                    registers (oldFrame.childTarget child))
                  hstate hnext)

theorem stateBound_iterate_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateBound state)
    (steps : ℕ) :
    StateBound (State.next^[steps] state) := by
  induction steps generalizing state with
  | zero =>
      simpa using hstate
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih state.next
        (stateBound_next_internal state hstate)

namespace Decision

theorem stateBound_queryInitial_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (hnode : QueryBound instanceData.horizon node) :
    StateBound
      (NeighborhoodScheduler.Decision.queryInitial
        (instanceData := instanceData) node) := by
  apply stateBound_initial_internal
  · exact le_rfl
  · exact hnode
  · apply TreeEval.CookMertz.PrimeField.Runtime.normalize_lt
    have hone :=
      fieldModulus_one_lt_internal instanceData
    omega

theorem stateBound_initial_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm} :
    Decision.StateBound
      (NeighborhoodScheduler.Decision.initial
        (instanceData := instanceData)) := by
  apply stateBound_queryInitial_internal
  exact queryBound_stateRoot_internal instanceData

theorem stateBound_next_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.Decision.State tm instanceData)
    (hstate : Decision.StateBound state) :
    Decision.StateBound
      (NeighborhoodScheduler.Decision.next state) := by
  rcases state with
    ⟨phase, query, stateValue, verdictValue⟩
  cases phase with
  | done =>
      simpa [NeighborhoodScheduler.Decision.next] using hstate
  | state =>
      by_cases hempty : query.stack.length = 0
      · simpa [NeighborhoodScheduler.Decision.next, hempty,
          Decision.StateBound] using
          stateBound_queryInitial_internal
            (NeighborhoodEvaluator.verdictRoot
              instanceData.guess instanceData.blockLength)
            (queryBound_verdictRoot_internal instanceData)
      · simpa [NeighborhoodScheduler.Decision.next, hempty,
          Decision.StateBound] using
          FrameBounds.Internal.stateBound_next_internal
            query hstate
  | verdict =>
      by_cases hempty : query.stack.length = 0
      · simpa [NeighborhoodScheduler.Decision.next, hempty] using
          hstate
      · simpa [NeighborhoodScheduler.Decision.next, hempty,
          Decision.StateBound] using
          FrameBounds.Internal.stateBound_next_internal
            query hstate

private theorem stateBound_iterate_of_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.Decision.State tm instanceData)
    (hstate : Decision.StateBound state)
    (steps : ℕ) :
    Decision.StateBound
      (NeighborhoodScheduler.Decision.next^[steps] state) := by
  induction steps generalizing state with
  | zero =>
      simpa using hstate
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih (NeighborhoodScheduler.Decision.next state)
        (stateBound_next_internal state hstate)

theorem stateBound_iterate_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (steps : ℕ) :
    Decision.StateBound
      (NeighborhoodScheduler.Decision.next^[steps]
        (NeighborhoodScheduler.Decision.initial
          (instanceData := instanceData))) := by
  exact stateBound_iterate_of_internal
    (NeighborhoodScheduler.Decision.initial
      (instanceData := instanceData))
    stateBound_initial_internal steps

end Decision

end Internal
end FrameBounds
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
