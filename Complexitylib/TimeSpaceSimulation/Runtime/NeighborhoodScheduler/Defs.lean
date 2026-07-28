/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# A concrete scheduler for neighborhood evaluation

This file defunctionalizes the recursive residue evaluator into a small-step
machine. Recursive calls are represented by an explicit stack of frames.
The residue and child folds are represented by five first-order phases.

The scheduler is deliberately independent of the RAM command lowering. Its
stack is the logical frame stack represented by the packed-stack word in
`Runtime.NeighborhoodProgram`; the command compiler can therefore treat one
transition here as its semantic unit.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler

open NeighborhoodExecutableEvaluation
open NeighborhoodEvaluator
open TreeEval CookMertz

variable {workTapeCount : ℕ}

/-- The canonical field modulus used by one runtime instance. -/
def fieldModulus
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) : ℕ :=
  NeighborhoodExecutableEvaluation.modulus tm instanceData.blockLength

/-- Scale a residue vector and add it to one catalytic register. -/
def addScaledAt
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers tm instanceData.blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (scalar : ℕ)
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue tm instanceData.blockLength) :
    NeighborhoodExecutableEvaluation.Residue.Registers tm instanceData.blockLength :=
  NeighborhoodExecutableEvaluation.Residue.addAt
    tm instanceData.blockLength registers out
    (NeighborhoodExecutableEvaluation.Residue.scaleValue
      tm instanceData.blockLength scalar value)

/-- The five control phases needed after entering a recursive call. -/
inductive Phase (workTapeCount : ℕ) where
  | enter
  | prepare
      (residue : ℕ)
      (residuesLeft : ℕ)
      (childIndex : ℕ)
  | combine
      (residue : ℕ)
      (residuesLeft : ℕ)
  | cleanupCall
      (residue : ℕ)
      (residuesLeft : ℕ)
      (childIndex : ℕ)
  | cleanupScale
      (residue : ℕ)
      (residuesLeft : ℕ)
      (child : Fin (graphFanIn workTapeCount))
      (nextChildIndex : ℕ)
  deriving DecidableEq

/-- A defunctionalized recursive-call frame. -/
structure Frame
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) where
  /-- Remaining recursion depth available to this call. -/
  fuel : ℕ
  /-- Implicit computation-graph query evaluated by this call. -/
  node : QueryNode workTapeCount instanceData.horizon
  /-- Field scalar multiplying this call's contribution. -/
  scalar : ℕ
  /-- Catalytic register receiving this call's contribution. -/
  out : Fin (graphFanIn workTapeCount + 1)
  /-- Current point in the residue-and-child fold schedule. -/
  phase : Phase workTapeCount
  deriving DecidableEq

/-- The finite-phase scheduler state. The head of `stack` is active. -/
structure State
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) where
  /-- Active frame followed by its suspended parent continuations. -/
  stack : List (Frame tm instanceData)
  /-- Current catalytic bank of grouped field residues. -/
  registers :
    NeighborhoodExecutableEvaluation.Residue.Registers tm instanceData.blockLength

namespace Frame

variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

/-- The children of a computation node, in the evaluator's fold order. -/
def children : List (Fin (graphFanIn workTapeCount)) :=
  List.finRange (graphFanIn workTapeCount)

/-- The number of nonzero residues streamed by the evaluator. -/
def residueCount (instanceData : NeighborhoodProgram.ResidueInstance tm) : ℕ :=
  fieldModulus instanceData - 1

/-- The recursively queried child selected by a child slot. -/
def childNode
    (frame : Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount)) :
    QueryNode workTapeCount instanceData.horizon :=
  NeighborhoodEvaluator.childAt instanceData.guess frame.node child

/-- The register assigned to a child slot. -/
def childTarget
    (frame : Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount)) :
    Fin (graphFanIn workTapeCount + 1) :=
  frame.out.succAbove child

/-- The frame for a recursive child call during the prepare fold. -/
def prepareChild
    (frame : Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount)) :
    Frame tm instanceData where
  fuel := frame.fuel - 1
  node := frame.childNode child
  scalar := PrimeField.Runtime.normalize (fieldModulus instanceData) 1
  out := frame.childTarget child
  phase := .enter

/-- The frame for a recursive child call during the cleanup fold. -/
def cleanupChild
    (frame : Frame tm instanceData)
    (child : Fin (graphFanIn workTapeCount)) :
    Frame tm instanceData where
  fuel := frame.fuel - 1
  node := frame.childNode child
  scalar := PrimeField.Runtime.sub (fieldModulus instanceData) 0 1
  out := frame.childTarget child
  phase := .enter

end Frame

namespace State

variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

/-- The initial state for one evaluator query. -/
def initial
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers tm instanceData.blockLength) :
    State tm instanceData where
  stack := [{
    fuel := fuel
    node := node
    scalar := scalar
    out := out
    phase := .enter
  }]
  registers := registers

/-- A state is terminal exactly when its continuation stack is empty. -/
def Terminal (state : State tm instanceData) : Prop :=
  state.stack.length = 0

/-- Finish one residue, either returning or advancing to the next residue. -/
def finishResidue
    (frame : Frame tm instanceData)
    (residue : ℕ)
    (residuesLeft : ℕ)
    (tail : List (Frame tm instanceData))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers tm instanceData.blockLength) :
    State tm instanceData :=
  match residuesLeft with
  | 0 => ⟨tail, registers⟩
  | residuesLeft + 1 =>
      ⟨{ frame with
          phase :=
            .prepare (residue + 1) residuesLeft 0 } :: tail,
        registers⟩

/-- One small step of the defunctionalized evaluator. -/
def next (state : State tm instanceData) : State tm instanceData :=
  match state.stack with
  | [] => state
  | frame :: tail =>
      match frame.phase with
      | .enter =>
          match frame.node with
          | .failure =>
              ⟨tail,
                addScaledAt
                  instanceData state.registers frame.out frame.scalar
                  (NeighborhoodExecutableEvaluation.Residue.failureValue
                    tm instanceData.blockLength)⟩
          | .graph (.source tape block) =>
              ⟨tail,
                addScaledAt
                  instanceData state.registers frame.out frame.scalar
                  (NeighborhoodExecutableEvaluation.Residue.sourceValue
                    (tm := tm) (x := instanceData.x)
                    (blockLength := instanceData.blockLength)
                    (encoding := instanceData.encoding)
                    (hpositive := instanceData.positive)
                    tape block)⟩
          | .graph (.computation _ _ interval) =>
              match frame.fuel with
              | 0 =>
                  ⟨tail,
                    addScaledAt
                      instanceData state.registers frame.out frame.scalar
                      (NeighborhoodExecutableEvaluation.Residue.failureValue
                        tm instanceData.blockLength)⟩
              | _ + 1 =>
                  if interval < instanceData.horizon then
                    match Frame.residueCount instanceData with
                    | 0 => ⟨tail, state.registers⟩
                    | residuesLeft + 1 =>
                        ⟨{ frame with
                            phase :=
                              .prepare 1 residuesLeft 0 } :: tail,
                          state.registers⟩
                  else
                    ⟨tail,
                    addScaledAt
                      instanceData state.registers frame.out frame.scalar
                        (NeighborhoodExecutableEvaluation.Residue.failureValue
                          tm instanceData.blockLength)⟩
      | .prepare residue residuesLeft childIndex =>
          if hchild : childIndex < graphFanIn workTapeCount then
            let child : Fin (graphFanIn workTapeCount) :=
              ⟨childIndex, hchild⟩
            let target := frame.childTarget child
            let registers :=
              NeighborhoodExecutableEvaluation.Residue.scaleAt
                tm instanceData.blockLength residue state.registers target
            let parent :=
              { frame with
                phase :=
                  .prepare residue residuesLeft (childIndex + 1) }
            ⟨frame.prepareChild child :: parent :: tail, registers⟩
          else
            ⟨{ frame with phase := .combine residue residuesLeft } :: tail,
              state.registers⟩
      | .combine residue residuesLeft =>
          match frame.node with
          | .graph (.computation tape slot interval) =>
              let value :=
                NeighborhoodExecutableEvaluation.combineResidues
                  (tm := tm) (x := instanceData.x)
                  (blockLength := instanceData.blockLength)
                  (encoding := instanceData.encoding)
                  (hpositive := instanceData.positive)
                  tape slot interval
                  (fun child => state.registers (frame.childTarget child))
              let registers :=
                addScaledAt
                  instanceData state.registers frame.out
                  (PrimeField.Runtime.sub
                    (fieldModulus instanceData) 0 frame.scalar) value
              ⟨{ frame with
                  phase :=
                    .cleanupCall residue residuesLeft 0 } :: tail,
                registers⟩
          | _ =>
              ⟨{ frame with
                  phase :=
                    .cleanupCall residue residuesLeft 0 } :: tail,
                state.registers⟩
      | .cleanupCall residue residuesLeft childIndex =>
          if hchild : childIndex < graphFanIn workTapeCount then
            let child : Fin (graphFanIn workTapeCount) :=
              ⟨childIndex, hchild⟩
            let parent :=
              { frame with
                phase :=
                  .cleanupScale residue residuesLeft child
                    (childIndex + 1) }
            ⟨frame.cleanupChild child :: parent :: tail, state.registers⟩
          else
            finishResidue frame residue residuesLeft tail state.registers
      | .cleanupScale residue residuesLeft child nextChildIndex =>
          let registers :=
            NeighborhoodExecutableEvaluation.Residue.scaleAt
              tm instanceData.blockLength
              (PrimeField.Runtime.inverse (fieldModulus instanceData) residue)
              state.registers (frame.childTarget child)
          ⟨{ frame with
              phase :=
                .cleanupCall residue residuesLeft nextChildIndex } :: tail,
            registers⟩

end State

namespace Work

variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

/-- Tokens for the remaining prepare-child cursor. -/
def prepareChildrenTokens
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node : QueryNode workTapeCount instanceData.horizon)
    (childTokens :
      QueryNode workTapeCount instanceData.horizon → List Unit) :
    ℕ → List Unit
  | childIndex =>
      ((Frame.children.drop childIndex).flatMap fun child =>
          () ::
            childTokens
              (NeighborhoodEvaluator.childAt instanceData.guess node child)) ++
        [()]

/-- Tokens for the remaining cleanup-child cursor. -/
def cleanupChildrenTokens
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node : QueryNode workTapeCount instanceData.horizon)
    (childTokens :
      QueryNode workTapeCount instanceData.horizon → List Unit) :
    ℕ → List Unit
  | childIndex =>
      ((Frame.children.drop childIndex).flatMap fun child =>
          () ::
            childTokens
              (NeighborhoodEvaluator.childAt instanceData.guess node child) ++ [()]) ++
        [()]

/-- Tokens for one complete residue iteration. -/
def residueTokensWith
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node : QueryNode workTapeCount instanceData.horizon)
    (childTokens :
      QueryNode workTapeCount instanceData.horizon → List Unit) :
    List Unit :=
  prepareChildrenTokens instanceData node childTokens 0
      ++
    [()] ++
    cleanupChildrenTokens instanceData node childTokens 0

/-- Repeat a residue token trace a numeric number of times. -/
def residuesTokens (residueTokens : List Unit) (count : ℕ) : List Unit :=
  (List.replicate count ()).flatMap fun _ => residueTokens

/--
The token trace of a fresh recursive call. Tokens carry no semantic data; they
are a proof-relevant exact countdown for the concrete scheduler.
-/
def callTokens :
    (fuel : ℕ) →
    QueryNode workTapeCount instanceData.horizon →
    List Unit
  | _, .failure => [()]
  | _, .graph (.source _ _) => [()]
  | 0, .graph (.computation _ _ _) => [()]
  | fuel + 1, node@(.graph (.computation _ _ interval)) =>
      if interval < instanceData.horizon then
        () ::
          residuesTokens
            (residueTokensWith instanceData node
              (callTokens fuel))
            (Frame.residueCount instanceData)
      else
        [()]
termination_by fuel _ => fuel

/-- The tokens consumed by all later residues. -/
def laterResidueTokens
    (frame : Frame tm instanceData)
    (residuesLeft : ℕ) :
    List Unit :=
  residuesTokens
    (residueTokensWith instanceData frame.node
      (callTokens (instanceData := instanceData) (frame.fuel - 1)))
    residuesLeft

/-- The exact remaining transition tokens in one frame. -/
def frameTokens (frame : Frame tm instanceData) : List Unit :=
  match frame.phase with
  | .enter => callTokens (instanceData := instanceData) frame.fuel frame.node
  | .prepare _ residuesLeft childIndex =>
      prepareChildrenTokens instanceData frame.node
          (callTokens (instanceData := instanceData) (frame.fuel - 1))
          childIndex ++
        [()] ++
        cleanupChildrenTokens instanceData frame.node
          (callTokens (instanceData := instanceData) (frame.fuel - 1))
          0 ++
        laterResidueTokens frame residuesLeft
  | .combine _ residuesLeft =>
      () ::
        cleanupChildrenTokens instanceData frame.node
            (callTokens (instanceData := instanceData) (frame.fuel - 1))
            0 ++
          laterResidueTokens frame residuesLeft
  | .cleanupCall _ residuesLeft childIndex =>
      cleanupChildrenTokens instanceData frame.node
          (callTokens (instanceData := instanceData) (frame.fuel - 1))
          childIndex ++
        laterResidueTokens frame residuesLeft
  | .cleanupScale _ residuesLeft _ nextChildIndex =>
      () ::
        cleanupChildrenTokens instanceData frame.node
            (callTokens (instanceData := instanceData) (frame.fuel - 1))
            nextChildIndex ++
          laterResidueTokens frame residuesLeft

/-- The exact remaining transition tokens in a scheduler stack. -/
def stackTokens (stack : List (Frame tm instanceData)) : List Unit :=
  stack.flatMap frameTokens

/-- A strictly decreasing natural-number rank for scheduler execution. -/
def rank (state : State tm instanceData) : ℕ :=
  (stackTokens state.stack).length

end Work

/-- The terminal state obtained by iterating for the exact scheduler rank. -/
def run
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (state : State tm instanceData) :
    State tm instanceData :=
  State.next^[Work.rank state] state

namespace Decision

variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

/-- The sequential state-query, verdict-query, and terminal phases. -/
inductive Phase where
  | state
  | verdict
  | done
  deriving DecidableEq

/-- Concrete iterative state for the two queries in `Residue.profileDecision`. -/
structure State
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) where
  /-- Current one of the state query, verdict query, or terminal phases. -/
  phase : Phase
  /-- Nested query scheduler whose bank contains the current root value. -/
  query : NeighborhoodScheduler.State tm instanceData
  /-- Root value saved after the state-consistency query. -/
  stateValue :
    NeighborhoodExecutableEvaluation.ResidueValue
      tm instanceData.blockLength
  /-- Root value saved after the verdict-consistency query. -/
  verdictValue :
    NeighborhoodExecutableEvaluation.ResidueValue
      tm instanceData.blockLength

/-- The shared zero register bank used at the start of each query. -/
def zeroRegisters :
    NeighborhoodExecutableEvaluation.Residue.Registers
      tm instanceData.blockLength :=
  fun _ =>
    NeighborhoodExecutableEvaluation.Residue.zeroValue
      tm instanceData.blockLength

/-- Construct the initial scheduler state for one root query. -/
def queryInitial
    (node : QueryNode workTapeCount instanceData.horizon) :
    NeighborhoodScheduler.State tm instanceData :=
  NeighborhoodScheduler.State.initial
    instanceData.horizon node
    (PrimeField.Runtime.normalize (fieldModulus instanceData) 1)
    (Fin.last (graphFanIn workTapeCount))
    zeroRegisters

/-- Initial state of the sequential decision scheduler. -/
def initial : State tm instanceData where
  phase := .state
  query := queryInitial (NeighborhoodEvaluator.stateRoot instanceData.guess)
  stateValue :=
    NeighborhoodExecutableEvaluation.Residue.zeroValue
      tm instanceData.blockLength
  verdictValue :=
    NeighborhoodExecutableEvaluation.Residue.zeroValue
      tm instanceData.blockLength

/-- The decision scheduler is terminal exactly in its `done` phase. -/
def Terminal (state : State tm instanceData) : Prop :=
  state.phase = .done

/-- One small step of the sequential decision scheduler. -/
def next (state : State tm instanceData) : State tm instanceData :=
  match state.phase with
  | .done => state
  | .state =>
      if state.query.stack.length = 0 then
        { state with
          phase := .verdict
          query :=
            queryInitial
              (NeighborhoodEvaluator.verdictRoot
                instanceData.guess instanceData.blockLength)
          stateValue :=
            state.query.registers
              (Fin.last (graphFanIn workTapeCount)) }
      else
        { state with query := state.query.next }
  | .verdict =>
      if state.query.stack.length = 0 then
        { state with
          phase := .done
          verdictValue :=
            state.query.registers
              (Fin.last (graphFanIn workTapeCount)) }
      else
        { state with query := state.query.next }

/-- Exact remaining transition rank for the sequential decision scheduler. -/
def rank (state : State tm instanceData) : ℕ :=
  match state.phase with
  | .state =>
      Work.rank state.query +
        Work.rank
          (queryInitial
            (NeighborhoodEvaluator.verdictRoot
              instanceData.guess instanceData.blockLength)) + 2
  | .verdict => Work.rank state.query + 1
  | .done => 0

/-- Iterate the decision scheduler for its exact rank. -/
def run (state : State tm instanceData) : State tm instanceData :=
  next^[rank state] state

/-- The two natural-residue values exposed by a terminal decision state. -/
def result (state : State tm instanceData) :
    NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength ×
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength :=
  (state.stateValue, state.verdictValue)

end Decision

end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
