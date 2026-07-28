/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Coherence.Defs

/-!
# Semantic coherence for the neighborhood scheduler -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace Coherence
namespace Internal

open NeighborhoodExecutableEvaluation

theorem frameCoherent_of_not_enter_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    {frame : NeighborhoodScheduler.Frame tm instanceData}
    (hframe : FrameCoherent frame)
    (hphase : frame.phase ≠ .enter) :
    ∃ tape slot interval,
      frame.node = .graph (.computation tape slot interval) ∧
        interval < instanceData.horizon ∧
        0 < frame.fuel := by
  exact hframe hphase

theorem stateCoherent_initial_internal
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
        tm instanceData.blockLength) :
    StateCoherent
      (NeighborhoodScheduler.State.initial
        fuel node scalar out registers) := by
  simp [StateCoherent, NeighborhoodScheduler.State.initial,
    FrameCoherent]

private theorem stateCoherent_drop
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (oldFrame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hstate : StateCoherent ⟨oldFrame :: tail, registers⟩) :
    StateCoherent ⟨tail, registers'⟩ := by
  intro frame hframe
  exact hstate frame (by simp [hframe])

private theorem stateCoherent_replace
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (oldFrame newFrame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hstate : StateCoherent ⟨oldFrame :: tail, registers⟩)
    (hnew : FrameCoherent newFrame) :
    StateCoherent ⟨newFrame :: tail, registers'⟩ := by
  intro frame hframe
  simp only [List.mem_cons] at hframe
  rcases hframe with rfl | htail
  · exact hnew
  · exact hstate frame (by simp [htail])

private theorem stateCoherent_push
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (oldFrame child parent : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hstate : StateCoherent ⟨oldFrame :: tail, registers⟩)
    (hchild : FrameCoherent child)
    (hparent : FrameCoherent parent) :
    StateCoherent ⟨child :: parent :: tail, registers'⟩ := by
  intro frame hframe
  simp only [List.mem_cons] at hframe
  rcases hframe with rfl | rfl | htail
  · exact hchild
  · exact hparent
  · exact hstate frame (by simp [htail])

theorem stateCoherent_next_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateCoherent state) :
    StateCoherent state.next := by
  rcases state with ⟨stack, registers⟩
  cases stack with
  | nil =>
      simp [StateCoherent, State.next]
  | cons frame tail =>
      cases frame with
      | mk fuel node scalar out phase =>
          cases phase with
          | enter =>
              cases node with
              | failure =>
                  simpa [State.next] using
                    (stateCoherent_drop
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
                        (stateCoherent_drop
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
                            (stateCoherent_drop
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
                                  (stateCoherent_drop
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase := .enter }
                                    tail registers registers hstate)
                            | succ residuesLeft =>
                                have hnew :
                                    FrameCoherent
                                      ({
                                          fuel := fuel + 1,
                                          node := .graph
                                            (.computation tape slot interval),
                                          scalar := scalar, out := out,
                                          phase :=
                                            .prepare 1 residuesLeft 0
                                        } : Frame tm instanceData) := by
                                  simp [FrameCoherent, hinterval]
                                simpa [State.next, hinterval, hresidues] using
                                  (stateCoherent_replace
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
                              (stateCoherent_drop
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
              let oldFrame : Frame tm instanceData :=
                { fuel := fuel, node := node, scalar := scalar,
                  out := out,
                  phase := .prepare residue residuesLeft childIndex }
              have hold : FrameCoherent oldFrame :=
                hstate oldFrame (by simp [oldFrame])
              by_cases hchild :
                  childIndex < graphFanIn workTapeCount
              · let child : Fin (graphFanIn workTapeCount) :=
                  ⟨childIndex, hchild⟩
                let parent : Frame tm instanceData :=
                  { oldFrame with
                    phase :=
                      .prepare residue residuesLeft (childIndex + 1) }
                have hchildCoherent :
                    FrameCoherent (oldFrame.prepareChild child) := by
                  simp [FrameCoherent, Frame.prepareChild]
                have hparentCoherent : FrameCoherent parent := by
                  simpa [FrameCoherent, oldFrame, parent] using hold
                simpa [State.next, hchild, oldFrame, child, parent] using
                  (stateCoherent_push oldFrame
                    (oldFrame.prepareChild child) parent tail registers
                    (Residue.scaleAt
                      tm instanceData.blockLength residue registers
                      (oldFrame.childTarget child))
                    hstate hchildCoherent hparentCoherent)
              · let nextFrame : Frame tm instanceData :=
                  { oldFrame with
                    phase := .combine residue residuesLeft }
                have hnext : FrameCoherent nextFrame := by
                  simpa [FrameCoherent, oldFrame, nextFrame] using hold
                simpa [State.next, hchild, oldFrame, nextFrame] using
                  (stateCoherent_replace oldFrame nextFrame tail registers
                    registers hstate hnext)
          | combine residue residuesLeft =>
              let oldFrame : Frame tm instanceData :=
                { fuel := fuel, node := node, scalar := scalar,
                  out := out, phase := .combine residue residuesLeft }
              let nextFrame : Frame tm instanceData :=
                { oldFrame with
                  phase := .cleanupCall residue residuesLeft 0 }
              have hold : FrameCoherent oldFrame :=
                hstate oldFrame (by simp [oldFrame])
              have hnext : FrameCoherent nextFrame := by
                simpa [FrameCoherent, oldFrame, nextFrame] using hold
              cases node with
              | failure =>
                  simpa [State.next, oldFrame, nextFrame] using
                    (stateCoherent_replace oldFrame nextFrame tail registers
                      registers hstate hnext)
              | graph graphNode =>
                  cases graphNode with
                  | source tape block =>
                      simpa [State.next, oldFrame, nextFrame] using
                        (stateCoherent_replace oldFrame nextFrame tail
                          registers registers hstate hnext)
                  | computation tape slot interval =>
                      simpa [State.next, oldFrame, nextFrame] using
                        (stateCoherent_replace oldFrame nextFrame tail
                          registers
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
              let oldFrame : Frame tm instanceData :=
                { fuel := fuel, node := node, scalar := scalar,
                  out := out,
                  phase :=
                    .cleanupCall residue residuesLeft childIndex }
              have hold : FrameCoherent oldFrame :=
                hstate oldFrame (by simp [oldFrame])
              by_cases hchild :
                  childIndex < graphFanIn workTapeCount
              · let child : Fin (graphFanIn workTapeCount) :=
                  ⟨childIndex, hchild⟩
                let parent : Frame tm instanceData :=
                  { oldFrame with
                    phase :=
                      .cleanupScale residue residuesLeft child
                        (childIndex + 1) }
                have hchildCoherent :
                    FrameCoherent (oldFrame.cleanupChild child) := by
                  simp [FrameCoherent, Frame.cleanupChild]
                have hparentCoherent : FrameCoherent parent := by
                  simpa [FrameCoherent, oldFrame, parent] using hold
                simpa [State.next, hchild, oldFrame, child, parent] using
                  (stateCoherent_push oldFrame
                    (oldFrame.cleanupChild child) parent tail registers
                    registers hstate hchildCoherent hparentCoherent)
              · cases residuesLeft with
                | zero =>
                    simpa [State.next, hchild, State.finishResidue] using
                      (stateCoherent_drop
                        { fuel := fuel, node := node, scalar := scalar,
                          out := out,
                          phase :=
                            .cleanupCall residue 0 childIndex }
                        tail registers registers hstate)
                | succ residuesLeft =>
                    let nextFrame : Frame tm instanceData :=
                      { oldFrame with
                        phase :=
                          .prepare (residue + 1) residuesLeft 0 }
                    have hnext : FrameCoherent nextFrame := by
                      simpa [FrameCoherent, oldFrame, nextFrame] using hold
                    simpa [State.next, hchild, State.finishResidue,
                      oldFrame, nextFrame] using
                      (stateCoherent_replace oldFrame nextFrame tail
                        registers registers hstate hnext)
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
              have hold : FrameCoherent oldFrame :=
                hstate oldFrame (by simp [oldFrame])
              have hnext : FrameCoherent nextFrame := by
                simpa [FrameCoherent, oldFrame, nextFrame] using hold
              simpa [State.next, oldFrame, nextFrame] using
                (stateCoherent_replace oldFrame nextFrame tail registers
                  (Residue.scaleAt
                    tm instanceData.blockLength
                    (TreeEval.CookMertz.PrimeField.Runtime.inverse
                      (fieldModulus instanceData) residue)
                    registers (oldFrame.childTarget child))
                  hstate hnext)

theorem stateCoherent_iterate_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : NeighborhoodScheduler.State tm instanceData)
    (hstate : StateCoherent state)
    (steps : ℕ) :
    StateCoherent (State.next^[steps] state) := by
  induction steps generalizing state with
  | zero =>
      simpa using hstate
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih state.next
        (stateCoherent_next_internal state hstate)

theorem stateCoherent_initial_iterate_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (fuel steps : ℕ)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    StateCoherent
      (State.next^[steps]
        (NeighborhoodScheduler.State.initial
          fuel node scalar out registers)) := by
  exact stateCoherent_iterate_internal
    (NeighborhoodScheduler.State.initial
      fuel node scalar out registers)
    (stateCoherent_initial_internal
      fuel node scalar out registers)
    steps

end Internal
end Coherence
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
