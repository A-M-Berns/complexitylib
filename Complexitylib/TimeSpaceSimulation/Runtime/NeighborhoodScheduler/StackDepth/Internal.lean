/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.StackDepth.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits

/-!
# Suspended-stack depth for the neighborhood scheduler -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace StackDepth
namespace Internal

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

theorem stackInvariant_initial_internal
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    StackInvariant fuel
      (State.initial fuel node scalar out registers) := by
  simp [StackInvariant, State.initial, Frame.PhaseValid, FuelChain,
    headFuel, Nat.add_comm]

private theorem fuelChain_tail
    (frame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (hchain : FuelChain (frame :: tail)) :
    FuelChain tail := by
  cases tail with
  | nil => trivial
  | cons parent rest => exact hchain.2

private theorem fuelChain_replace
    (oldFrame newFrame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (hchain : FuelChain (oldFrame :: tail))
    (hfuel : newFrame.fuel = oldFrame.fuel) :
    FuelChain (newFrame :: tail) := by
  cases tail with
  | nil => trivial
  | cons parent rest =>
      refine ⟨?_, hchain.2⟩
      rw [hfuel]
      exact hchain.1

private theorem stackInvariant_drop
    (initialFuel : ℕ)
    (frame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hinvariant :
      StackInvariant initialFuel ⟨frame :: tail, registers⟩) :
    StackInvariant initialFuel ⟨tail, registers'⟩ := by
  rcases hinvariant with ⟨hvalid, hchain, hcapacity⟩
  refine ⟨?_, fuelChain_tail frame tail hchain, ?_⟩
  · intro current hcurrent
    exact hvalid current (by simp [hcurrent])
  · cases tail with
    | nil => simp [headFuel]
    | cons parent rest =>
        change rest.length + 1 + parent.fuel ≤ initialFuel + 1
        change rest.length + 1 + 1 + frame.fuel ≤
          initialFuel + 1 at hcapacity
        have hfuel : parent.fuel = frame.fuel + 1 := hchain.1
        omega

private theorem stackInvariant_replace
    (initialFuel : ℕ)
    (oldFrame newFrame : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hinvariant :
      StackInvariant initialFuel ⟨oldFrame :: tail, registers⟩)
    (hvalid : Frame.PhaseValid newFrame)
    (hfuel : newFrame.fuel = oldFrame.fuel) :
    StackInvariant initialFuel ⟨newFrame :: tail, registers'⟩ := by
  rcases hinvariant with ⟨hvalidOld, hchain, hcapacity⟩
  refine ⟨?_, fuelChain_replace oldFrame newFrame tail hchain hfuel, ?_⟩
  · intro current hcurrent
    simp only [List.mem_cons] at hcurrent
    rcases hcurrent with rfl | htail
    · exact hvalid
    · exact hvalidOld current (by simp [htail])
  · simpa [headFuel, hfuel] using hcapacity

private theorem stackInvariant_push
    (initialFuel : ℕ)
    (oldFrame child parent : Frame tm instanceData)
    (tail : List (Frame tm instanceData))
    (registers registers' :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (hinvariant :
      StackInvariant initialFuel ⟨oldFrame :: tail, registers⟩)
    (hchildValid : Frame.PhaseValid child)
    (hparentValid : Frame.PhaseValid parent)
    (hparentFuel : parent.fuel = oldFrame.fuel)
    (hchildFuel : child.fuel + 1 = oldFrame.fuel) :
    StackInvariant initialFuel
      ⟨child :: parent :: tail, registers'⟩ := by
  rcases hinvariant with ⟨hvalidOld, hchain, hcapacity⟩
  refine ⟨?_, ?_, ?_⟩
  · intro current hcurrent
    simp only [List.mem_cons] at hcurrent
    rcases hcurrent with rfl | rfl | htail
    · exact hchildValid
    · exact hparentValid
    · exact hvalidOld current (by simp [htail])
  · exact ⟨by omega,
      fuelChain_replace oldFrame parent tail hchain hparentFuel⟩
  · change tail.length + 1 + 1 + child.fuel ≤ initialFuel + 1
    change tail.length + 1 + oldFrame.fuel ≤
      initialFuel + 1 at hcapacity
    omega

theorem stackInvariant_next_internal
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hinvariant : StackInvariant initialFuel state) :
    StackInvariant initialFuel state.next := by
  rcases state with ⟨stack, registers⟩
  cases stack with
  | nil =>
      simp [StackInvariant, State.next, FuelChain, headFuel] at hinvariant ⊢
  | cons frame tail =>
      cases frame with
      | mk fuel node scalar out phase =>
          cases phase with
          | enter =>
              cases node with
              | failure =>
                  simpa [State.next] using
                    (stackInvariant_drop initialFuel
                      { fuel := fuel, node := .failure, scalar := scalar,
                        out := out, phase := .enter }
                      tail registers
                      (addScaledAt instanceData registers out scalar
                        (NeighborhoodExecutableEvaluation.Residue.failureValue
                          tm instanceData.blockLength))
                      hinvariant)
              | graph graphNode =>
                  cases graphNode with
                  | source tape block =>
                      simpa [State.next] using
                        (stackInvariant_drop initialFuel
                          { fuel := fuel, node := .graph (.source tape block),
                            scalar := scalar, out := out, phase := .enter }
                          tail registers
                          (addScaledAt instanceData registers out scalar
                            (NeighborhoodExecutableEvaluation.Residue.sourceValue
                              (tm := tm) (x := instanceData.x)
                              (blockLength := instanceData.blockLength)
                              (encoding := instanceData.encoding)
                              (hpositive := instanceData.positive)
                              tape block))
                          hinvariant)
                  | computation tape slot interval =>
                      cases fuel with
                      | zero =>
                          simpa [State.next] using
                            (stackInvariant_drop initialFuel
                              { fuel := 0,
                                node := .graph
                                  (.computation tape slot interval),
                                scalar := scalar, out := out,
                                phase := .enter }
                              tail registers
                              (addScaledAt instanceData registers out scalar
                                (NeighborhoodExecutableEvaluation.Residue.failureValue
                                  tm instanceData.blockLength))
                              hinvariant)
                      | succ fuel =>
                          by_cases hinterval :
                              interval < instanceData.horizon
                          · cases hresidues :
                              Frame.residueCount instanceData with
                            | zero =>
                                simpa [State.next, hinterval, hresidues] using
                                  (stackInvariant_drop initialFuel
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase := .enter }
                                    tail registers registers hinvariant)
                            | succ residuesLeft =>
                                simpa [State.next, hinterval, hresidues] using
                                  (stackInvariant_replace initialFuel
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase := .enter }
                                    { fuel := fuel + 1,
                                      node := .graph
                                        (.computation tape slot interval),
                                      scalar := scalar, out := out,
                                      phase := .prepare 1 residuesLeft 0 }
                                    tail registers registers hinvariant
                                    (by simp [Frame.PhaseValid]) rfl)
                          · simpa [State.next, hinterval] using
                              (stackInvariant_drop initialFuel
                                { fuel := fuel + 1,
                                  node := .graph
                                    (.computation tape slot interval),
                                  scalar := scalar, out := out,
                                  phase := .enter }
                                tail registers
                                (addScaledAt instanceData registers out scalar
                                  (NeighborhoodExecutableEvaluation.Residue.failureValue
                                    tm instanceData.blockLength))
                                hinvariant)
          | prepare residue residuesLeft childIndex =>
              by_cases hchild :
                  childIndex <
                    NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount
              · let oldFrame : Frame tm instanceData :=
                  { fuel := fuel, node := node, scalar := scalar,
                    out := out,
                    phase := .prepare residue residuesLeft childIndex }
                have hpositive : 0 < fuel := by
                  simpa [oldFrame, Frame.PhaseValid] using
                    hinvariant.1 oldFrame (by simp [oldFrame])
                let child : Fin
                    (NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount) :=
                  ⟨childIndex, hchild⟩
                let parent : Frame tm instanceData :=
                  { oldFrame with
                    phase :=
                      .prepare residue residuesLeft (childIndex + 1) }
                simpa [State.next, hchild, oldFrame, child, parent] using
                  (stackInvariant_push initialFuel oldFrame
                    (oldFrame.prepareChild child) parent tail registers
                    (NeighborhoodExecutableEvaluation.Residue.scaleAt
                      tm instanceData.blockLength residue registers
                      (oldFrame.childTarget child))
                    hinvariant (by simp [Frame.PhaseValid,
                      Frame.prepareChild])
                    (by simpa [Frame.PhaseValid, parent] using hpositive)
                    rfl (by
                      change fuel - 1 + 1 = fuel
                      omega))
              · let oldFrame : Frame tm instanceData :=
                  { fuel := fuel, node := node, scalar := scalar,
                    out := out,
                    phase := .prepare residue residuesLeft childIndex }
                let nextFrame : Frame tm instanceData :=
                  { oldFrame with phase := .combine residue residuesLeft }
                simpa [State.next, hchild, oldFrame, nextFrame] using
                  (stackInvariant_replace initialFuel oldFrame nextFrame
                    tail registers registers hinvariant
                    (by simpa [Frame.PhaseValid, nextFrame] using
                      hinvariant.1 oldFrame (by simp [oldFrame]))
                    rfl)
          | combine residue residuesLeft =>
              let oldFrame : Frame tm instanceData :=
                { fuel := fuel, node := node, scalar := scalar,
                  out := out, phase := .combine residue residuesLeft }
              let nextFrame : Frame tm instanceData :=
                { oldFrame with phase := .cleanupCall residue residuesLeft 0 }
              have hnextValid : Frame.PhaseValid nextFrame := by
                simpa [Frame.PhaseValid, oldFrame, nextFrame] using
                  hinvariant.1 oldFrame (by simp [oldFrame])
              cases node with
              | failure =>
                  simpa [State.next, oldFrame, nextFrame] using
                    (stackInvariant_replace initialFuel oldFrame nextFrame
                      tail registers registers hinvariant hnextValid rfl)
              | graph graphNode =>
                  cases graphNode with
                  | source tape block =>
                      simpa [State.next, oldFrame, nextFrame] using
                        (stackInvariant_replace initialFuel
                          oldFrame nextFrame tail registers registers
                          hinvariant hnextValid rfl)
                  | computation tape slot interval =>
                      simpa [State.next, oldFrame, nextFrame] using
                        (stackInvariant_replace initialFuel oldFrame
                          nextFrame tail registers
                          (addScaledAt instanceData registers out
                            (TreeEval.CookMertz.PrimeField.Runtime.sub
                              (fieldModulus instanceData) 0 scalar)
                            (NeighborhoodExecutableEvaluation.combineResidues
                              (tm := tm) (x := instanceData.x)
                              (blockLength := instanceData.blockLength)
                              (encoding := instanceData.encoding)
                              (hpositive := instanceData.positive)
                              tape slot interval
                              (fun child =>
                                registers
                                  (oldFrame.childTarget child))))
                          hinvariant hnextValid rfl)
          | cleanupCall residue residuesLeft childIndex =>
              by_cases hchild :
                  childIndex <
                    NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount
              · let oldFrame : Frame tm instanceData :=
                  { fuel := fuel, node := node, scalar := scalar,
                    out := out,
                    phase := .cleanupCall residue residuesLeft childIndex }
                have hpositive : 0 < fuel := by
                  simpa [oldFrame, Frame.PhaseValid] using
                    hinvariant.1 oldFrame (by simp [oldFrame])
                let child : Fin
                    (NeighborhoodExecutableEvaluation.graphFanIn
                      workTapeCount) :=
                  ⟨childIndex, hchild⟩
                let parent : Frame tm instanceData :=
                  { oldFrame with phase :=
                      .cleanupScale residue residuesLeft child (childIndex + 1) }
                simpa [State.next, hchild, oldFrame, child, parent] using
                  (stackInvariant_push initialFuel oldFrame
                    (oldFrame.cleanupChild child) parent tail registers
                    registers hinvariant
                    (by simp [Frame.PhaseValid, Frame.cleanupChild])
                    (by simpa [Frame.PhaseValid, parent] using hpositive)
                    rfl (by
                      change fuel - 1 + 1 = fuel
                      omega))
              · cases residuesLeft with
                | zero =>
                    simpa [State.next, hchild, State.finishResidue] using
                      (stackInvariant_drop initialFuel
                        { fuel := fuel, node := node, scalar := scalar,
                          out := out,
                          phase := .cleanupCall residue 0 childIndex }
                        tail registers registers hinvariant)
                | succ residuesLeft =>
                    let oldFrame : Frame tm instanceData :=
                      { fuel := fuel, node := node, scalar := scalar,
                        out := out,
                        phase := .cleanupCall residue (residuesLeft + 1)
                          childIndex }
                    let nextFrame : Frame tm instanceData :=
                      { oldFrame with
                        phase := .prepare (residue + 1) residuesLeft 0 }
                    simpa [State.next, hchild, State.finishResidue,
                      oldFrame, nextFrame] using
                      (stackInvariant_replace initialFuel
                        oldFrame nextFrame tail registers registers
                        hinvariant
                        (by simpa [Frame.PhaseValid, nextFrame] using
                          hinvariant.1 oldFrame (by simp [oldFrame]))
                        rfl)
          | cleanupScale residue residuesLeft child nextChildIndex =>
              let oldFrame : Frame tm instanceData :=
                { fuel := fuel, node := node, scalar := scalar,
                  out := out,
                  phase := .cleanupScale residue residuesLeft child
                    nextChildIndex }
              let nextFrame : Frame tm instanceData :=
                { oldFrame with
                  phase := .cleanupCall residue residuesLeft nextChildIndex }
              simpa [State.next, oldFrame, nextFrame] using
                (stackInvariant_replace initialFuel oldFrame nextFrame tail
                  registers
                  (NeighborhoodExecutableEvaluation.Residue.scaleAt
                    tm instanceData.blockLength
                    (TreeEval.CookMertz.PrimeField.Runtime.inverse
                      (fieldModulus instanceData) residue)
                    registers (oldFrame.childTarget child))
                  hinvariant
                  (by simpa [Frame.PhaseValid, nextFrame] using
                    hinvariant.1 oldFrame (by simp [oldFrame]))
                  rfl)

private theorem stackInvariant_iterate_of_internal
    (initialFuel steps : ℕ)
    (state : State tm instanceData)
    (hinvariant : StackInvariant initialFuel state) :
    StackInvariant initialFuel (State.next^[steps] state) := by
  induction steps generalizing state with
  | zero => simpa using hinvariant
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih state.next
        (stackInvariant_next_internal initialFuel state hinvariant)

theorem stackInvariant_iterate_internal
    (fuel steps : ℕ)
    (node : NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    StackInvariant fuel
      (State.next^[steps]
        (State.initial fuel node scalar out registers)) := by
  exact stackInvariant_iterate_of_internal fuel steps _
    (stackInvariant_initial_internal
      fuel node scalar out registers)

theorem suspendedDepth_le_of_stackInvariant_internal
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hinvariant : StackInvariant initialFuel state) :
    suspendedDepth state ≤ initialFuel := by
  rcases hinvariant with ⟨_, _, hcapacity⟩
  unfold suspendedDepth
  omega

theorem suspendedDepth_iterate_le_internal
    (fuel steps : ℕ)
    (node : NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    suspendedDepth
        (State.next^[steps]
          (State.initial fuel node scalar out registers)) ≤
      fuel :=
  suspendedDepth_le_of_stackInvariant_internal fuel _
    (stackInvariant_iterate_internal
      fuel steps node scalar out registers)

theorem packFrames_lt_pow_internal
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (frames : List (Frame tm instanceData))
    (hdigit : ∀ frame ∈ frames, encode frame < base) :
    packFrames base encode frames < base ^ frames.length := by
  induction frames with
  | nil => simp [packFrames]
  | cons frame tail ih =>
      apply PackedDigits.push_lt_pow
      · exact ih (fun current hcurrent =>
          hdigit current (by simp [hcurrent]))
      · exact hdigit frame (by simp)

theorem packSuspended_lt_pow_internal
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (state : State tm instanceData)
    (hdigit :
      ∀ frame ∈ state.stack.tail, encode frame < base) :
    packSuspended base encode state <
      base ^ suspendedDepth state := by
  simpa [packSuspended, suspendedDepth] using
    packFrames_lt_pow_internal
      base encode state.stack.tail hdigit

theorem packSuspended_lt_pow_of_stackInvariant_internal
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hbase : 1 ≤ base)
    (hinvariant : StackInvariant initialFuel state)
    (hdigit :
      ∀ frame ∈ state.stack.tail, encode frame < base) :
    packSuspended base encode state < base ^ initialFuel := by
  exact (packSuspended_lt_pow_internal
    base encode state hdigit).trans_le
      (Nat.pow_le_pow_right hbase
        (suspendedDepth_le_of_stackInvariant_internal
          initialFuel state hinvariant))

private theorem queryStackInvariant_initial
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    StackInvariant fuel
      (State.initial fuel node scalar out registers) :=
  stackInvariant_initial_internal fuel node scalar out registers

private theorem queryStackInvariant_next
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hinvariant : StackInvariant initialFuel state) :
    StackInvariant initialFuel state.next :=
  stackInvariant_next_internal initialFuel state hinvariant

private theorem querySuspendedDepth_le
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hinvariant : StackInvariant initialFuel state) :
    suspendedDepth state ≤ initialFuel :=
  suspendedDepth_le_of_stackInvariant_internal
    initialFuel state hinvariant

namespace Decision

theorem stackInvariant_initial_internal :
    Decision.StackInvariant
      (NeighborhoodScheduler.Decision.initial
        (instanceData := instanceData)) := by
  unfold Decision.StackInvariant
  apply queryStackInvariant_initial

theorem stackInvariant_next_internal
    (state : NeighborhoodScheduler.Decision.State tm instanceData)
    (hinvariant : Decision.StackInvariant state) :
    Decision.StackInvariant
      (NeighborhoodScheduler.Decision.next state) := by
  rcases state with ⟨phase, query, stateValue, verdictValue⟩
  cases phase with
  | done =>
      simpa [Decision.StackInvariant,
        NeighborhoodScheduler.Decision.next] using hinvariant
  | state =>
      by_cases hquery : query.stack.length = 0
      · simpa [Decision.StackInvariant,
          NeighborhoodScheduler.Decision.next, hquery,
          NeighborhoodScheduler.Decision.queryInitial] using
            (queryStackInvariant_initial
              (tm := tm) instanceData.horizon
              (NeighborhoodEvaluator.verdictRoot
                instanceData.guess instanceData.blockLength)
              (TreeEval.CookMertz.PrimeField.Runtime.normalize
                (fieldModulus instanceData) 1)
              (Fin.last
                (NeighborhoodExecutableEvaluation.graphFanIn
                  workTapeCount))
              NeighborhoodScheduler.Decision.zeroRegisters)
      · simpa [Decision.StackInvariant,
          NeighborhoodScheduler.Decision.next, hquery] using
            (queryStackInvariant_next
              instanceData.horizon query hinvariant)
  | verdict =>
      by_cases hquery : query.stack.length = 0
      · simpa [Decision.StackInvariant,
          NeighborhoodScheduler.Decision.next, hquery] using hinvariant
      · simpa [Decision.StackInvariant,
          NeighborhoodScheduler.Decision.next, hquery] using
            (queryStackInvariant_next
              instanceData.horizon query hinvariant)

private theorem stackInvariant_iterate_of_internal
    (steps : ℕ)
    (state : NeighborhoodScheduler.Decision.State tm instanceData)
    (hinvariant : Decision.StackInvariant state) :
    Decision.StackInvariant
      (NeighborhoodScheduler.Decision.next^[steps] state) := by
  induction steps generalizing state with
  | zero => simpa using hinvariant
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih (NeighborhoodScheduler.Decision.next state)
        (stackInvariant_next_internal state hinvariant)

theorem stackInvariant_iterate_internal
    (steps : ℕ) :
    Decision.StackInvariant
      (NeighborhoodScheduler.Decision.next^[steps]
        (NeighborhoodScheduler.Decision.initial
          (instanceData := instanceData))) :=
  stackInvariant_iterate_of_internal steps _
    stackInvariant_initial_internal

theorem suspendedDepth_iterate_le_internal
    (steps : ℕ) :
    Decision.suspendedDepth
        (NeighborhoodScheduler.Decision.next^[steps]
          (NeighborhoodScheduler.Decision.initial
            (instanceData := instanceData))) ≤
      instanceData.horizon := by
  exact querySuspendedDepth_le instanceData.horizon _
    (stackInvariant_iterate_internal steps)

theorem packSuspended_iterate_lt_pow_internal
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (steps : ℕ)
    (hbase : 1 ≤ base)
    (hdigit :
      let state :=
        NeighborhoodScheduler.Decision.next^[steps]
          (NeighborhoodScheduler.Decision.initial
            (instanceData := instanceData))
      ∀ frame ∈ state.query.stack.tail, encode frame < base) :
    Decision.packSuspended base encode
        (NeighborhoodScheduler.Decision.next^[steps]
          (NeighborhoodScheduler.Decision.initial
            (instanceData := instanceData))) <
      base ^ instanceData.horizon := by
  let state :=
    NeighborhoodScheduler.Decision.next^[steps]
      (NeighborhoodScheduler.Decision.initial
        (instanceData := instanceData))
  change packSuspended base encode state.query <
    base ^ instanceData.horizon
  exact packSuspended_lt_pow_of_stackInvariant_internal
    base encode instanceData.horizon state.query hbase
    (stackInvariant_iterate_internal steps) hdigit

end Decision

end Internal
end StackDepth
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
