/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.TimeSpaceSimulation.Normalization.Defs

/-!
# A three-microstep block-normalization compiler

This file defines an executable compiler that replaces each source transition
by three target transitions. At the start of each three-step block, every head
on the left-end marker makes a reversible one-cell excursion. The second
microstep restores every tape exactly, and the third performs the source
transition. Consequently, source transitions occur only at time-block
boundaries, while the two administrative configurations remain in the same
length-three tape block as the boundary configuration.

The construction is a concrete base layer for block-respecting normalization:
it has exact semantics and constant-factor overhead, without using an
unproved normalization oracle.

## Main definitions

- `NormalizationCompiler.TripleStepState` -- target control states
- `TM.tripleStepTM` -- the executable three-microstep compiler
- `NormalizationCompiler.boundaryCfg` -- source configurations at boundaries
- `NormalizationCompiler.phase1Cfg` and `phase2Cfg` -- administrative states
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NormalizationCompiler

/-- Control states for the three-microstep normalization.

`phase1` stores which heads were on the left-end marker before their mandatory
right move, so that the next microstep can restore them. -/
inductive TripleStepState (workTapeCount : ℕ) (Q : Type) where
  | phase0 (state : Q)
  | phase1 (state : Q) (atOrigin : TapeIndex workTapeCount → Bool)
  | phase2 (state : Q)
  | halt
  deriving DecidableEq, Fintype

/-- Read a named tape from the three transition-function arguments. -/
def namedRead (inputHead : Γ) (workHeads : Fin workTapeCount → Γ)
    (outputHead : Γ) (tape : TapeIndex workTapeCount) : Γ :=
  if hinput : tape.val = 0 then
    inputHead
  else if houtput : tape.val = workTapeCount + 1 then
    outputHead
  else
    workHeads ⟨tape.val - 1, by omega⟩

/-- Record exactly which named heads currently read the left-end marker. -/
def originFlags (inputHead : Γ) (workHeads : Fin workTapeCount → Γ)
    (outputHead : Γ) : TapeIndex workTapeCount → Bool :=
  fun tape => decide (namedRead inputHead workHeads outputHead tape = Γ.start)

/-- Restore a head that made the mandatory right move from the left-end
marker; leave all other well-formed heads fixed. -/
def bounceBackDir (atOrigin : Bool) (head : Γ) : Dir3 :=
  if head = Γ.start then .right
  else if atOrigin then .left
  else .stay

theorem bounceBackDir_right_of_start (atOrigin : Bool)
    {head : Γ} (hhead : head = Γ.start) :
    bounceBackDir atOrigin head = .right := by
  simp [bounceBackDir, hhead]

/-- Embed a source state at a three-step block boundary. -/
def wrapState (source : TM workTapeCount) (state : source.Q) :
    TripleStepState workTapeCount source.Q :=
  if state = source.qhalt then .halt else .phase0 state

/-- The first administrative action on a writable tape. It writes back the
current symbol and performs the mandatory right move exactly at cell zero. -/
def bounceOutTape (tape : Tape) : Tape :=
  tape.writeAndMove (TM.readBackWrite tape.read) (TM.idleDir tape.read)

/-- The second administrative action on a writable tape. -/
def bounceBackTape (atOrigin : Bool) (tape : Tape) : Tape :=
  tape.writeAndMove (TM.readBackWrite tape.read)
    (bounceBackDir atOrigin tape.read)

/-- All named tapes in a configuration have the unique left-end marker
invariant. -/
def CfgStartInvariant (cfg : Cfg workTapeCount Q) : Prop :=
  cfg.input.StartInvariant ∧
    (∀ i, (cfg.work i).StartInvariant) ∧
    cfg.output.StartInvariant

end NormalizationCompiler

end TimeSpaceSimulation

namespace TM

open TimeSpaceSimulation TimeSpaceSimulation.NormalizationCompiler

/-- Replace every source transition by two reversible administrative
microsteps followed by the original transition.

The compiler uses the same work tapes as the source machine. -/
def tripleStepTM (source : TM workTapeCount) : TM workTapeCount where
  Q := TripleStepState workTapeCount source.Q
  qstart := wrapState source source.qstart
  qhalt := .halt
  δ := fun state inputHead workHeads outputHead =>
    match state with
    | .phase0 sourceState =>
        (.phase1 sourceState (originFlags inputHead workHeads outputHead),
          fun i => readBackWrite (workHeads i), readBackWrite outputHead,
          idleDir inputHead, fun i => idleDir (workHeads i), idleDir outputHead)
    | .phase1 sourceState atOrigin =>
        (.phase2 sourceState,
          fun i => readBackWrite (workHeads i), readBackWrite outputHead,
          bounceBackDir (atOrigin (TapeIndex.input workTapeCount)) inputHead,
          fun i => bounceBackDir (atOrigin (TapeIndex.work i)) (workHeads i),
          bounceBackDir (atOrigin (TapeIndex.output workTapeCount)) outputHead)
    | .phase2 sourceState =>
        if sourceState = source.qhalt then
          allReadBack .halt inputHead workHeads outputHead
        else
          let result := source.δ sourceState inputHead workHeads outputHead
          (wrapState source result.1, result.2.1, result.2.2.1,
            result.2.2.2.1, result.2.2.2.2.1, result.2.2.2.2.2)
    | .halt => allReadBack .halt inputHead workHeads outputHead
  δ_right_of_start := by
    intro state inputHead workHeads outputHead
    cases state with
    | phase0 sourceState =>
        exact rightOfStart_allReadBack inputHead workHeads outputHead
    | phase1 sourceState atOrigin =>
        exact ⟨bounceBackDir_right_of_start _,
          fun i => bounceBackDir_right_of_start _,
          bounceBackDir_right_of_start _⟩
    | phase2 sourceState =>
        dsimp only
        split
        · exact rightOfStart_allReadBack inputHead workHeads outputHead
        · exact source.δ_right_of_start sourceState inputHead workHeads outputHead
    | halt =>
        exact rightOfStart_allReadBack inputHead workHeads outputHead

end TM

namespace TimeSpaceSimulation

namespace NormalizationCompiler

open TM

/-- Embed a source configuration at a three-step block boundary. -/
def boundaryCfg (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q) :
    Cfg workTapeCount source.tripleStepTM.Q where
  state := wrapState source cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- The configuration after the first administrative microstep. -/
def phase1Cfg (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q) :
    Cfg workTapeCount source.tripleStepTM.Q where
  state := .phase1 cfg.state
    (originFlags cfg.input.read (fun i => (cfg.work i).read) cfg.output.read)
  input := cfg.input.move (TM.idleDir cfg.input.read)
  work := fun i => bounceOutTape (cfg.work i)
  output := bounceOutTape cfg.output

/-- The restored configuration immediately before its source transition. -/
def phase2Cfg (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q) :
    Cfg workTapeCount source.tripleStepTM.Q where
  state := .phase2 cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

end NormalizationCompiler

end TimeSpaceSimulation

end Complexity
