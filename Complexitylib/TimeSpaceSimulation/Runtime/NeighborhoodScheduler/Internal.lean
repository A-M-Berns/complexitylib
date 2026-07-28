/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Defs

/-!
# Correctness of the concrete neighborhood scheduler

This internal module proves termination and semantic preservation for the
finite-phase scheduler.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler

open NeighborhoodExecutableEvaluation NeighborhoodEvaluator
open TreeEval CookMertz

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

private theorem Frame.children_drop_eq_cons
    (childIndex : ℕ)
    (hchild : childIndex < graphFanIn workTapeCount) :
    (Frame.children :
      List (Fin (graphFanIn workTapeCount))).drop childIndex =
      (⟨childIndex, hchild⟩ : Fin (graphFanIn workTapeCount)) ::
        (Frame.children :
          List (Fin (graphFanIn workTapeCount))).drop (childIndex + 1) := by
  rw [List.drop_eq_getElem_cons]
  · congr 1
    apply Fin.ext
    simp [Frame.children]
  · simpa [Frame.children] using hchild

private theorem Frame.children_drop_eq_nil
    (childIndex : ℕ)
    (hchild : ¬childIndex < graphFanIn workTapeCount) :
    (Frame.children :
      List (Fin (graphFanIn workTapeCount))).drop childIndex = [] := by
  apply List.drop_eq_nil_of_le
  simp only [Frame.children, List.length_finRange]
  omega

theorem Work.stackTokens_next
    (state : State tm instanceData)
    (hstate : ¬ state.Terminal) :
    Work.stackTokens state.stack =
      () :: Work.stackTokens state.next.stack := by
  rcases state with ⟨stack, registers⟩
  cases stack with
  | nil => simp [State.Terminal] at hstate
  | cons frame tail =>
      cases frame with
      | mk fuel node scalar out phase =>
          cases phase
          · cases node with
            | failure =>
                simp [State.next, Work.stackTokens, Work.frameTokens,
                  Work.callTokens]
            | graph graphNode =>
                cases graphNode with
                | source tape block =>
                    simp [State.next, Work.stackTokens, Work.frameTokens,
                      Work.callTokens]
                | computation tape slot interval =>
                    cases fuel with
                    | zero =>
                        simp [State.next, Work.stackTokens, Work.frameTokens,
                          Work.callTokens]
                    | succ fuel =>
                        by_cases hinterval : interval < instanceData.horizon
                        · cases hresidues :
                            Frame.residueCount instanceData with
                          | zero =>
                              simp [State.next, Work.stackTokens,
                                Work.frameTokens, Work.callTokens,
                                Work.residuesTokens,
                                hinterval, hresidues]
                          | succ residuesLeft =>
                              simp [State.next, Work.stackTokens,
                                Work.frameTokens, Work.callTokens,
                                Work.residuesTokens,
                                Work.residueTokensWith,
                                Work.prepareChildrenTokens,
                                Work.cleanupChildrenTokens,
                                Work.laterResidueTokens,
                                List.replicate_succ, List.append_assoc,
                                hinterval, hresidues]
                        · simp [State.next, Work.stackTokens,
                            Work.frameTokens, Work.callTokens, hinterval]
          · rename_i residue residuesLeft childIndex
            by_cases hchild :
                childIndex < graphFanIn workTapeCount
            · simp [State.next, Work.stackTokens, Work.frameTokens,
                Work.prepareChildrenTokens,
                Frame.children_drop_eq_cons childIndex hchild,
                Work.laterResidueTokens, Frame.prepareChild,
                Frame.childNode, hchild]
            · simp [State.next, Work.stackTokens, Work.frameTokens,
                Work.prepareChildrenTokens,
                Frame.children_drop_eq_nil childIndex hchild,
                Work.laterResidueTokens, hchild]
          · rename_i residue residuesLeft
            cases node with
            | failure =>
                simp [State.next, Work.stackTokens, Work.frameTokens,
                  Work.cleanupChildrenTokens, Work.laterResidueTokens]
            | graph graphNode =>
                cases graphNode <;>
                  simp [State.next, Work.stackTokens, Work.frameTokens,
                    Work.cleanupChildrenTokens, Work.laterResidueTokens]
          · rename_i residue residuesLeft childIndex
            by_cases hchild :
                childIndex < graphFanIn workTapeCount
            · simp [State.next, Work.stackTokens, Work.frameTokens,
                Work.cleanupChildrenTokens,
                Frame.children_drop_eq_cons childIndex hchild,
                Work.laterResidueTokens, Frame.cleanupChild,
                Frame.childNode, hchild]
            · cases residuesLeft <;>
                simp [State.next, State.finishResidue,
                  Work.stackTokens, Work.frameTokens,
                  Work.cleanupChildrenTokens,
                  Frame.children_drop_eq_nil childIndex hchild,
                  Work.laterResidueTokens, Work.residuesTokens,
                  Work.residueTokensWith, List.replicate_succ,
                  List.append_assoc, hchild]
          · rename_i residue residuesLeft child nextChildIndex
            simp [State.next, Work.stackTokens, Work.frameTokens,
              Work.cleanupChildrenTokens, Work.laterResidueTokens]

theorem Work.rank_next
    (state : State tm instanceData)
    (hstate : ¬ state.Terminal) :
    Work.rank state.next + 1 = Work.rank state := by
  have htokens := Work.stackTokens_next state hstate
  simp [Work.rank, htokens]

theorem Work.rank_next_lt
    (state : State tm instanceData)
    (hstate : ¬ state.Terminal) :
    Work.rank state.next < Work.rank state := by
  have hrank := Work.rank_next state hstate
  omega

private theorem Work.callTokens_ne_nil
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon) :
    Work.callTokens (instanceData := instanceData) fuel node ≠ [] := by
  cases node with
  | failure => simp [Work.callTokens]
  | graph graphNode =>
      cases graphNode with
      | source tape block => simp [Work.callTokens]
      | computation tape slot interval =>
          cases fuel with
          | zero => simp [Work.callTokens]
          | succ fuel =>
              by_cases hinterval : interval < instanceData.horizon <;>
                simp [Work.callTokens, hinterval]

private theorem Work.frameTokens_ne_nil
    (frame : Frame tm instanceData) :
    Work.frameTokens frame ≠ [] := by
  cases frame with
  | mk fuel node scalar out phase =>
      cases phase with
      | enter =>
          exact Work.callTokens_ne_nil fuel node
      | prepare residue residuesLeft childIndex =>
          simp [Work.frameTokens, Work.prepareChildrenTokens]
      | combine residue residuesLeft =>
          simp [Work.frameTokens]
      | cleanupCall residue residuesLeft childIndex =>
          simp [Work.frameTokens, Work.cleanupChildrenTokens]
      | cleanupScale residue residuesLeft child nextChildIndex =>
          simp [Work.frameTokens]

theorem Work.rank_eq_zero_iff
    (state : State tm instanceData) :
    Work.rank state = 0 ↔ state.Terminal := by
  constructor
  · intro hrank
    rcases state with ⟨stack, registers⟩
    cases stack with
    | nil => rfl
    | cons frame tail =>
        exfalso
        apply Work.frameTokens_ne_nil frame
        have happend :
            Work.frameTokens frame ++ Work.stackTokens tail = [] := by
          exact List.length_eq_zero_iff.mp (by
            simpa [Work.rank, Work.stackTokens] using hrank)
        exact (List.append_eq_nil_iff.mp happend).1
  · intro hterminal
    rcases state with ⟨stack, registers⟩
    simp [State.Terminal] at hterminal
    simp [hterminal, Work.rank, Work.stackTokens]

theorem run_terminal
    (state : State tm instanceData) :
    (run state).Terminal := by
  induction hrank : Work.rank state using Nat.strong_induction_on generalizing state with
  | h rank ih =>
      by_cases hterminal : state.Terminal
      · have hzero : Work.rank state = 0 :=
          (Work.rank_eq_zero_iff state).2 hterminal
        simp [run, hzero, hterminal]
      · have hnext := Work.rank_next state hterminal
        have hlt := Work.rank_next_lt state hterminal
        rw [hrank] at hlt
        have hterminalNext : (run state.next).Terminal :=
          ih (Work.rank state.next) hlt state.next rfl
        rw [run, ← hnext, Function.iterate_succ_apply]
        exact hterminalNext

namespace Semantics

local notation "Regs" =>
  NeighborhoodExecutableEvaluation.Residue.Registers
    tm instanceData.blockLength

local notation "ChildRun" =>
  QueryNode workTapeCount instanceData.horizon →
    ℕ → Fin (graphFanIn workTapeCount + 1) →
      Regs → Regs

private def prepareChildren
    (node : QueryNode workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (childRun : ChildRun)
    (residue childIndex : ℕ)
    (registers : Regs) :
    Regs :=
  (Frame.children.drop childIndex).foldl
    (fun current child =>
      let target := out.succAbove child
      childRun (NeighborhoodEvaluator.childAt instanceData.guess node child)
        (PrimeField.Runtime.normalize (fieldModulus instanceData) 1)
        target
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm instanceData.blockLength residue current target))
    registers

private def combine
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers : Regs) :
    Regs :=
  match node with
  | .graph (.computation tape slot interval) =>
      let value :=
        NeighborhoodExecutableEvaluation.combineResidues
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          tape slot interval
          (fun child => registers (out.succAbove child))
      addScaledAt instanceData registers out
        (PrimeField.Runtime.sub
          (fieldModulus instanceData) 0 scalar)
        value
  | _ => registers

private def cleanupChildren
    (node : QueryNode workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (childRun : ChildRun)
    (residue childIndex : ℕ)
    (registers : Regs) :
    Regs :=
  (Frame.children.drop childIndex).foldl
    (fun current child =>
      let target := out.succAbove child
      let current :=
        childRun (NeighborhoodEvaluator.childAt instanceData.guess node child)
          (PrimeField.Runtime.sub (fieldModulus instanceData) 0 1)
          target current
      NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm instanceData.blockLength
        (PrimeField.Runtime.inverse (fieldModulus instanceData) residue)
        current target)
    registers

private def residue
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (childRun : ChildRun)
    (residueValue : ℕ)
    (registers : Regs) :
    Regs :=
  cleanupChildren node out childRun residueValue 0
    (combine node scalar out
      (prepareChildren node out childRun residueValue 0 registers))

private def residues
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (childRun : ChildRun) :
    ℕ → ℕ → Regs → Regs
  | _, 0, registers => registers
  | residueValue, residuesLeft + 1, registers =>
      residues node scalar out childRun (residueValue + 1) residuesLeft
        (residue node scalar out childRun residueValue registers)

private def callResult :
    (fuel : ℕ) →
    (node : QueryNode workTapeCount instanceData.horizon) →
    (scalar : ℕ) →
    (out : Fin (graphFanIn workTapeCount + 1)) →
    Regs → Regs
  | _, .failure, scalar, out, registers =>
      addScaledAt instanceData registers out scalar
        (NeighborhoodExecutableEvaluation.Residue.failureValue
          tm instanceData.blockLength)
  | _, .graph (.source tape block), scalar, out, registers =>
      addScaledAt instanceData registers out scalar
        (NeighborhoodExecutableEvaluation.Residue.sourceValue
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive tape block)
  | 0, .graph (.computation _ _ _), scalar, out, registers =>
      addScaledAt instanceData registers out scalar
        (NeighborhoodExecutableEvaluation.Residue.failureValue
          tm instanceData.blockLength)
  | fuel + 1, node@(.graph (.computation _ _ interval)),
      scalar, out, registers =>
      if _hinterval : interval < instanceData.horizon then
        residues node scalar out
          (callResult fuel)
          1 (Frame.residueCount instanceData) registers
      else
        addScaledAt instanceData registers out scalar
          (NeighborhoodExecutableEvaluation.Residue.failureValue
            tm instanceData.blockLength)
termination_by fuel _ => fuel

private def profilePrepareStep
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (residueValue : ℕ)
    (current : Workspace.Profile Regs)
    (child : Fin (graphFanIn workTapeCount)) :
    Workspace.Profile Regs :=
  let target := out.succAbove child
  let childProfile :=
    NeighborhoodExecutableEvaluation.Residue.profileAccumulate
      tm instanceData.x instanceData.blockLength
      instanceData.encoding instanceData.positive
      instanceData.horizon instanceData.guess fuel
      (NeighborhoodEvaluator.childAt instanceData.guess node child)
      (PrimeField.Runtime.normalize (fieldModulus instanceData) 1)
      target
      (NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm instanceData.blockLength residueValue current.result target)
  Workspace.Profile.recordChild current childProfile

private def profileCleanupStep
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (residueValue : ℕ)
    (current : Workspace.Profile Regs)
    (child : Fin (graphFanIn workTapeCount)) :
    Workspace.Profile Regs :=
  let target := out.succAbove child
  let childProfile :=
    NeighborhoodExecutableEvaluation.Residue.profileAccumulate
      tm instanceData.x instanceData.blockLength
      instanceData.encoding instanceData.positive
      instanceData.horizon instanceData.guess fuel
      (NeighborhoodEvaluator.childAt instanceData.guess node child)
      (PrimeField.Runtime.sub (fieldModulus instanceData) 0 1)
      target current.result
  Workspace.Profile.map
    (fun registers =>
      NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm instanceData.blockLength
        (PrimeField.Runtime.inverse (fieldModulus instanceData) residueValue)
        registers target)
    (Workspace.Profile.recordChild current childProfile)

private def profileResidueStep
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (current : Workspace.Profile Regs)
    (residueValue : ℕ) :
    Workspace.Profile Regs :=
  let current :=
    Frame.children.foldl
      (profilePrepareStep fuel node out residueValue)
      current
  let current :=
    Workspace.Profile.map
      (combine node scalar out)
      current
  Frame.children.foldl
    (profileCleanupStep fuel node out residueValue)
    current

private theorem prepareFold_result
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (residueValue : ℕ)
    (children : List (Fin (graphFanIn workTapeCount)))
    (current : Workspace.Profile Regs)
    (ih : ∀ (childNode : QueryNode workTapeCount instanceData.horizon)
        (scalar : ℕ) (childOut : Fin (graphFanIn workTapeCount + 1))
        (registers : Regs),
      callResult (instanceData := instanceData) fuel childNode
          scalar childOut registers =
        (NeighborhoodExecutableEvaluation.Residue.profileAccumulate
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess fuel childNode
          scalar childOut registers).result) :
    (children.foldl
      (profilePrepareStep fuel node out residueValue) current).result =
      children.foldl
        (fun registers child =>
          let target := out.succAbove child
          callResult fuel
            (NeighborhoodEvaluator.childAt instanceData.guess node child)
            (PrimeField.Runtime.normalize (fieldModulus instanceData) 1)
            target
            (NeighborhoodExecutableEvaluation.Residue.scaleAt
              tm instanceData.blockLength residueValue registers target))
        current.result := by
  induction children generalizing current with
  | nil => rfl
  | cons child children ihChildren =>
      simp only [List.foldl_cons]
      rw [ihChildren]
      simp [profilePrepareStep, Workspace.Profile.recordChild, ih]

private theorem cleanupFold_result
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (out : Fin (graphFanIn workTapeCount + 1))
    (residueValue : ℕ)
    (children : List (Fin (graphFanIn workTapeCount)))
    (current : Workspace.Profile Regs)
    (ih : ∀ (childNode : QueryNode workTapeCount instanceData.horizon)
        (scalar : ℕ) (childOut : Fin (graphFanIn workTapeCount + 1))
        (registers : Regs),
      callResult (instanceData := instanceData) fuel childNode
          scalar childOut registers =
        (NeighborhoodExecutableEvaluation.Residue.profileAccumulate
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess fuel childNode
          scalar childOut registers).result) :
    (children.foldl
      (profileCleanupStep fuel node out residueValue) current).result =
      children.foldl
        (fun registers child =>
          let target := out.succAbove child
          let registers :=
            callResult fuel
              (NeighborhoodEvaluator.childAt instanceData.guess node child)
              (PrimeField.Runtime.sub (fieldModulus instanceData) 0 1)
              target registers
          NeighborhoodExecutableEvaluation.Residue.scaleAt
            tm instanceData.blockLength
            (PrimeField.Runtime.inverse
              (fieldModulus instanceData) residueValue)
            registers target)
        current.result := by
  induction children generalizing current with
  | nil => rfl
  | cons child children ihChildren =>
      simp only [List.foldl_cons]
      rw [ihChildren]
      simp [profileCleanupStep, Workspace.Profile.map,
        Workspace.Profile.recordChild, ih]

private theorem profileFoldl_result
    (children : List (Fin (graphFanIn workTapeCount)))
    (profileStep :
      Workspace.Profile Regs →
        Fin (graphFanIn workTapeCount) → Workspace.Profile Regs)
    (pureStep :
      Regs → Fin (graphFanIn workTapeCount) → Regs)
    (current : Workspace.Profile Regs)
    (hstep : ∀ (profile : Workspace.Profile Regs)
        (child : Fin (graphFanIn workTapeCount)),
      (profileStep profile child).result =
        pureStep profile.result child) :
    (children.foldl profileStep current).result =
      children.foldl pureStep current.result := by
  induction children generalizing current with
  | nil => rfl
  | cons child children ihChildren =>
      simp only [List.foldl_cons]
      rw [ihChildren, hstep]

private theorem profileResidueStep_result
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (residueValue : ℕ)
    (current : Workspace.Profile Regs)
    (ih : ∀ (childNode : QueryNode workTapeCount instanceData.horizon)
        (childScalar : ℕ)
        (childOut : Fin (graphFanIn workTapeCount + 1))
        (registers : Regs),
      callResult (instanceData := instanceData) fuel childNode
          childScalar childOut registers =
        (NeighborhoodExecutableEvaluation.Residue.profileAccumulate
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess fuel childNode
          childScalar childOut registers).result) :
    (profileResidueStep fuel node scalar out current residueValue).result =
      residue node scalar out (callResult fuel) residueValue current.result := by
  unfold profileResidueStep residue prepareChildren cleanupChildren
  rw [cleanupFold_result (ih := ih)]
  simp only [Workspace.Profile.map]
  rw [prepareFold_result (ih := ih)]
  simp [Frame.children]

private theorem profileResiduesLoop_result
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (step : Workspace.Profile Regs → ℕ → Workspace.Profile Regs)
    (residueValue residuesLeft : ℕ)
    (current : Workspace.Profile Regs)
    (hstep : ∀ (profile : Workspace.Profile Regs) (residueValue : ℕ),
      (step profile residueValue).result =
        residue node scalar out (callResult fuel)
          residueValue profile.result) :
    (PrimeField.Runtime.foldNonzeroLoop
      step
      residuesLeft residueValue current).result =
      residues node scalar out (callResult fuel)
        residueValue residuesLeft current.result := by
  induction residuesLeft generalizing residueValue current with
  | zero => rfl
  | succ residuesLeft ihResidues =>
      rw [PrimeField.Runtime.foldNonzeroLoop]
      rw [ihResidues]
      rw [hstep]
      rfl

set_option maxHeartbeats 800000 in
private theorem callResult_eq_profile
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers : Regs) :
    callResult (instanceData := instanceData)
        fuel node scalar out registers =
      (NeighborhoodExecutableEvaluation.Residue.profileAccumulate
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess
        fuel node scalar out registers).result := by
  induction fuel generalizing node scalar out registers with
  | zero =>
      cases node with
      | failure =>
          simp [callResult,
            NeighborhoodExecutableEvaluation.Residue.profileAccumulate,
            addScaledAt, Workspace.Profile.start]
      | graph graphNode =>
          cases graphNode with
          | source tape block =>
              simp [callResult,
                NeighborhoodExecutableEvaluation.Residue.profileAccumulate,
                addScaledAt, Workspace.Profile.start]
          | computation tape slot interval =>
              simp [callResult,
                NeighborhoodExecutableEvaluation.Residue.profileAccumulate,
                addScaledAt, Workspace.Profile.start]
  | succ fuel ih =>
      cases node with
      | failure =>
          simp [callResult,
            NeighborhoodExecutableEvaluation.Residue.profileAccumulate,
            addScaledAt, Workspace.Profile.start]
      | graph graphNode =>
          cases graphNode with
          | source tape block =>
              simp [callResult,
                NeighborhoodExecutableEvaluation.Residue.profileAccumulate,
                addScaledAt, Workspace.Profile.start]
          | computation tape slot interval =>
              by_cases hinterval : interval < instanceData.horizon
              · rw [callResult.eq_4,
                  NeighborhoodExecutableEvaluation.Residue.profileAccumulate.eq_4]
                simp only [hinterval, dite_true]
                unfold PrimeField.Runtime.foldNonzero
                symm
                apply profileResiduesLoop_result
                  (fuel := fuel)
                  (node := .graph
                    (.computation tape slot interval))
                  (scalar := scalar) (out := out)
                  (residueValue := 1)
                  (residuesLeft := Frame.residueCount instanceData)
                  (current := Workspace.Profile.start registers)
                intro current residueValue
                unfold residue prepareChildren cleanupChildren
                rw [profileFoldl_result
                  (pureStep := fun childRegisters child =>
                    let target := out.succAbove child
                    let childRegisters :=
                      callResult fuel
                        (NeighborhoodEvaluator.childAt instanceData.guess
                          (.graph (.computation tape slot interval)) child)
                        (PrimeField.Runtime.sub
                          (fieldModulus instanceData) 0 1)
                        target childRegisters
                    NeighborhoodExecutableEvaluation.Residue.scaleAt
                      tm instanceData.blockLength
                      (PrimeField.Runtime.inverse
                        (fieldModulus instanceData) residueValue)
                      childRegisters target)
                  (hstep := by
                    intro profile child
                    simp [Workspace.Profile.map,
                      Workspace.Profile.recordChild, fieldModulus, ih])]
                simp only [Workspace.Profile.map]
                rw [profileFoldl_result
                  (pureStep := fun childRegisters child =>
                    let target := out.succAbove child
                    callResult fuel
                      (NeighborhoodEvaluator.childAt instanceData.guess
                        (.graph (.computation tape slot interval)) child)
                      (PrimeField.Runtime.normalize
                        (fieldModulus instanceData) 1)
                      target
                      (NeighborhoodExecutableEvaluation.Residue.scaleAt
                        tm instanceData.blockLength residueValue
                        childRegisters target))
                  (hstep := by
                    intro profile child
                    simp [Workspace.Profile.recordChild,
                      fieldModulus, ih])]
                simp [combine, Frame.children, fieldModulus, addScaledAt]
              · simp [callResult,
                  NeighborhoodExecutableEvaluation.Residue.profileAccumulate,
                  hinterval, addScaledAt, Workspace.Profile.start]

private def completeFrame
    (frame : Frame tm instanceData)
    (registers : Regs) :
    Regs :=
  let childRun := callResult (instanceData := instanceData) (frame.fuel - 1)
  match frame.phase with
  | .enter =>
      callResult frame.fuel frame.node frame.scalar frame.out registers
  | .prepare residue residuesLeft childIndex =>
      residues frame.node frame.scalar frame.out childRun
        (residue + 1) residuesLeft
        (cleanupChildren frame.node frame.out childRun residue 0
          (combine frame.node frame.scalar frame.out
            (prepareChildren frame.node frame.out childRun
              residue childIndex registers)))
  | .combine residue residuesLeft =>
      residues frame.node frame.scalar frame.out childRun
        (residue + 1) residuesLeft
        (cleanupChildren frame.node frame.out childRun residue 0
          (combine frame.node frame.scalar frame.out registers))
  | .cleanupCall residue residuesLeft childIndex =>
      residues frame.node frame.scalar frame.out childRun
        (residue + 1) residuesLeft
        (cleanupChildren frame.node frame.out childRun
          residue childIndex registers)
  | .cleanupScale residue residuesLeft child nextChildIndex =>
      let registers :=
        NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm instanceData.blockLength
          (PrimeField.Runtime.inverse (fieldModulus instanceData) residue)
          registers (frame.out.succAbove child)
      residues frame.node frame.scalar frame.out childRun
        (residue + 1) residuesLeft
        (cleanupChildren frame.node frame.out childRun
          residue nextChildIndex registers)

private def completeStack :
    List (Frame tm instanceData) → Regs → Regs
  | [], registers => registers
  | frame :: tail, registers =>
      completeStack tail (completeFrame frame registers)

private theorem completeStack_next
    (state : State tm instanceData) :
    completeStack state.next.stack state.next.registers =
      completeStack state.stack state.registers := by
  rcases state with ⟨stack, registers⟩
  cases stack with
  | nil => rfl
  | cons frame tail =>
      cases frame with
      | mk fuel node scalar out phase =>
          cases phase
          · cases node with
            | failure =>
                simp [State.next, completeStack, completeFrame, callResult]
            | graph graphNode =>
                cases graphNode with
                | source tape block =>
                    simp [State.next, completeStack, completeFrame, callResult]
                | computation tape slot interval =>
                    cases fuel with
                    | zero =>
                        simp [State.next, completeStack, completeFrame,
                          callResult]
                    | succ fuel =>
                        by_cases hinterval :
                            interval < instanceData.horizon
                        · cases hresidues :
                            Frame.residueCount instanceData with
                          | zero =>
                              simp [State.next, completeStack, completeFrame,
                                callResult, residues, hinterval, hresidues]
                          | succ residuesLeft =>
                              simp [State.next, completeStack, completeFrame,
                                callResult, residues, residue, hinterval,
                                hresidues]
                        · simp [State.next, completeStack, completeFrame,
                            callResult, hinterval]
          · rename_i residueValue residuesLeft childIndex
            by_cases hchild :
                childIndex < graphFanIn workTapeCount
            · simp [State.next, completeStack, completeFrame,
                prepareChildren,
                Frame.children_drop_eq_cons childIndex hchild,
                Frame.prepareChild, Frame.childNode,
                cleanupChildren, combine,
                Frame.childTarget, hchild]
            · simp [State.next, completeStack, completeFrame,
                prepareChildren,
                Frame.children_drop_eq_nil childIndex hchild,
                hchild]
          · rename_i residueValue residuesLeft
            cases node with
            | failure =>
                simp [State.next, completeStack, completeFrame, combine]
            | graph graphNode =>
                cases graphNode with
                | source tape block =>
                    simp [State.next, completeStack, completeFrame, combine]
                | computation tape slot interval =>
                    simp [State.next, completeStack, completeFrame, combine,
                      Frame.childTarget]
          · rename_i residueValue residuesLeft childIndex
            by_cases hchild :
                childIndex < graphFanIn workTapeCount
            · simp [State.next, completeStack, completeFrame,
                cleanupChildren,
                Frame.children_drop_eq_cons childIndex hchild,
                Frame.cleanupChild, Frame.childNode, Frame.childTarget,
                hchild]
            · cases residuesLeft <;>
                simp [State.next, State.finishResidue,
                  completeStack, completeFrame, cleanupChildren,
                  Frame.children_drop_eq_nil childIndex hchild,
                  residues, residue, hchild]
          · rename_i residueValue residuesLeft child nextChildIndex
            simp [State.next, completeStack, completeFrame,
              cleanupChildren, Frame.childTarget]

private theorem completeStack_iterate
    (steps : ℕ)
    (state : State tm instanceData) :
    completeStack (State.next^[steps] state).stack
        (State.next^[steps] state).registers =
      completeStack state.stack state.registers := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      calc
        completeStack (State.next^[steps] (State.next state)).stack
            (State.next^[steps] (State.next state)).registers =
            completeStack (State.next state).stack
              (State.next state).registers :=
          ih (State.next state)
        _ = completeStack state.stack state.registers :=
          completeStack_next state

theorem run_registers_eq
    (state : State tm instanceData) :
    (run state).registers =
      completeStack state.stack state.registers := by
  have hterminal := run_terminal state
  have hstack : (run state).stack = [] :=
    List.length_eq_zero_iff.mp hterminal
  have hinvariant :=
    completeStack_iterate (Work.rank state) state
  change
    completeStack (run state).stack (run state).registers =
      completeStack state.stack state.registers at hinvariant
  rw [hstack] at hinvariant
  simpa [completeStack] using hinvariant

theorem run_initial_registers_eq_profileAccumulate
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers : Regs) :
    (run (State.initial fuel node scalar out registers)).registers =
      (NeighborhoodExecutableEvaluation.Residue.profileAccumulate
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess
        fuel node scalar out registers).result := by
  rw [run_registers_eq]
  simp [State.initial, completeStack, completeFrame]
  exact callResult_eq_profile fuel node scalar out registers

theorem run_initial_evaluate_result
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon) :
    (run
      (State.initial fuel node
        (PrimeField.Runtime.normalize (fieldModulus instanceData) 1)
        (Fin.last (graphFanIn workTapeCount))
        (fun _ =>
          NeighborhoodExecutableEvaluation.Residue.zeroValue
            tm instanceData.blockLength))).registers
        (Fin.last (graphFanIn workTapeCount)) =
      (NeighborhoodExecutableEvaluation.Residue.profileEvaluate
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess fuel node).result := by
  have hregisters :=
    run_initial_registers_eq_profileAccumulate
      (instanceData := instanceData)
      fuel node
      (PrimeField.Runtime.normalize (fieldModulus instanceData) 1)
      (Fin.last (graphFanIn workTapeCount))
      (fun _ =>
        NeighborhoodExecutableEvaluation.Residue.zeroValue
          tm instanceData.blockLength)
  simpa [NeighborhoodExecutableEvaluation.Residue.profileEvaluate,
    Workspace.Profile.map, fieldModulus] using
      congrFun hregisters (Fin.last (graphFanIn workTapeCount))

theorem run_next_registers_eq
    (state : State tm instanceData) :
    (run state.next).registers = (run state).registers := by
  rw [run_registers_eq, run_registers_eq]
  exact completeStack_next state

end Semantics

namespace Decision

theorem rank_next
    (state : State tm instanceData)
    (hstate : ¬Terminal state) :
    rank (next state) + 1 = rank state := by
  rcases state with ⟨phase, query, stateValue, verdictValue⟩
  cases phase with
  | done => simp [Terminal] at hstate
  | state =>
      by_cases hquery : query.stack.length = 0
      · have hzero : Work.rank query = 0 :=
          (Work.rank_eq_zero_iff query).2 hquery
        simp [next, rank, hquery, hzero]
      · have hqueryTerminal : ¬query.Terminal := hquery
        have hrank := Work.rank_next query hqueryTerminal
        simp [next, rank, hquery]
        omega
  | verdict =>
      by_cases hquery : query.stack.length = 0
      · have hzero : Work.rank query = 0 :=
          (Work.rank_eq_zero_iff query).2 hquery
        simp [next, rank, hquery, hzero]
      · have hqueryTerminal : ¬query.Terminal := hquery
        have hrank := Work.rank_next query hqueryTerminal
        simp [next, rank, hquery, hrank]

theorem rank_next_lt
    (state : State tm instanceData)
    (hstate : ¬Terminal state) :
    rank (next state) < rank state := by
  have hrank := rank_next state hstate
  omega

theorem rank_eq_zero_iff
    (state : State tm instanceData) :
    rank state = 0 ↔ Terminal state := by
  rcases state with ⟨phase, query, stateValue, verdictValue⟩
  cases phase <;> simp [rank, Terminal]

theorem run_terminal
    (state : State tm instanceData) :
    Terminal (run state) := by
  induction hrank : rank state using Nat.strong_induction_on generalizing state with
  | h currentRank ih =>
      by_cases hterminal : Terminal state
      · have hzero : rank state = 0 :=
          (rank_eq_zero_iff state).2 hterminal
        simp [run, hzero, hterminal]
      · have hnext := rank_next state hterminal
        have hlt := rank_next_lt state hterminal
        rw [hrank] at hlt
        have hterminalNext : Terminal (run (next state)) :=
          ih (rank (next state)) hlt (next state) rfl
        rw [run, ← hnext, Function.iterate_succ_apply]
        exact hterminalNext

private def denotation (state : State tm instanceData) :
    NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength ×
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength :=
  match state.phase with
  | .state =>
      ((NeighborhoodScheduler.run state.query).registers
          (Fin.last (graphFanIn workTapeCount)),
        (NeighborhoodScheduler.run
          (queryInitial
            (NeighborhoodEvaluator.verdictRoot
              instanceData.guess instanceData.blockLength))).registers
          (Fin.last (graphFanIn workTapeCount)))
  | .verdict =>
      (state.stateValue,
        (NeighborhoodScheduler.run state.query).registers
          (Fin.last (graphFanIn workTapeCount)))
  | .done => result state

private theorem denotation_next
    (state : State tm instanceData) :
    denotation (next state) = denotation state := by
  rcases state with ⟨phase, query, stateValue, verdictValue⟩
  cases phase with
  | done => rfl
  | state =>
      by_cases hquery : query.stack.length = 0
      · have hzero : Work.rank query = 0 :=
          (Work.rank_eq_zero_iff query).2 hquery
        simp [next, denotation, NeighborhoodScheduler.run, hquery, hzero]
      · simp [next, denotation, hquery,
          Semantics.run_next_registers_eq]
  | verdict =>
      by_cases hquery : query.stack.length = 0
      · have hzero : Work.rank query = 0 :=
          (Work.rank_eq_zero_iff query).2 hquery
        simp [next, denotation, NeighborhoodScheduler.run, hquery, hzero,
          result]
      · simp [next, denotation, hquery,
          Semantics.run_next_registers_eq]

private theorem denotation_iterate
    (steps : ℕ)
    (state : State tm instanceData) :
    denotation (next^[steps] state) = denotation state := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply, ih, denotation_next]

theorem run_result
    (state : State tm instanceData) :
    result (run state) = denotation state := by
  have hterminal := run_terminal state
  have hinvariant := denotation_iterate (rank state) state
  change denotation (run state) = denotation state at hinvariant
  have hdone : (run state).phase = .done := hterminal
  rw [denotation, hdone] at hinvariant
  exact hinvariant

theorem run_initial_result_eq_profileDecision :
    result (run (initial (instanceData := instanceData))) =
      (NeighborhoodExecutableEvaluation.Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result := by
  rw [run_result]
  simp only [initial, denotation]
  simp only [NeighborhoodExecutableEvaluation.Residue.profileDecision]
  apply Prod.ext
  · exact Semantics.run_initial_evaluate_result
      (instanceData := instanceData)
      instanceData.horizon
      (NeighborhoodEvaluator.stateRoot instanceData.guess)
  · exact Semantics.run_initial_evaluate_result
      (instanceData := instanceData)
      instanceData.horizon
      (NeighborhoodEvaluator.verdictRoot
        instanceData.guess instanceData.blockLength)

end Decision

end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
