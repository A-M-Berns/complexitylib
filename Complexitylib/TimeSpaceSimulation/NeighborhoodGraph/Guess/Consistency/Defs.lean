/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Defs

/-!
# Executable self-consistency checks for guessed centers

The runtime checker in this module never reads `actualCenterTrajectory`.
It anchors interval zero to the source configuration and checks every later
boundary against a genuinely local length-`blockLength` simulation.

The remaining callback boundary is explicit. For a guess and interval, an
`InputProvider` supplies either failure or exactly one compact value for each
of the `4 * (workTapeCount + 2)` neighborhood-graph predecessor roles.
`localEndCenter` reconstructs a configuration from:

* the centers derived from the movement guess;
* one chronological state and one head remainder per named tape;
* three length-`blockLength` content blocks per named tape.

It then executes the machine for one interval and returns the block
containing each final head. No absolute center is part of a Boolean node
value: each callback value has the existing compact width
`Fintype.card Q + 5 * blockLength`, while every later center update is one
three-valued `CenterMove`.

`IsExactProvider` is a proof certificate, not part of runtime checking. It
states the precise obligation on a future guessed-tree evaluator: whenever
the guessed prefix is correct, its compact predecessor vector equals the
semantic predecessor vector.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Consistency

/-- One compact value for every fixed predecessor role, or explicit local
reconstruction failure. -/
abbrev InputProvider (tm : TM workTapeCount)
    (blockLength horizon : ℕ) :=
  CenterGuess workTapeCount horizon →
    Fin horizon →
      Option (PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)

/-- Source-configuration block containing one named initial head. -/
def sourceCenter (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount) : ℕ :=
  headBlock blockLength (tm.initCfg x) tape

/-- Total center metadata derived from a guess. The default is observable
only after an invalid movement prefix; a passing boundary check proves that
the relevant prefix is defined. -/
def guessedCenters (guess : CenterGuess workTapeCount horizon)
    (boundary : ℕ) : TapeIndex workTapeCount → ℕ :=
  fun tape => (guess.derivedCenter tape boundary).getD 0

/-- Reconstruct the complete local interval-start configuration from the
derived center metadata and the fixed predecessor-value vector. -/
def localStartCfg (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs : PredecessorIndex workTapeCount →
      NeighborhoodContent.Content blockLength tm.Q) :
    Cfg workTapeCount tm.Q :=
  NeighborhoodContent.cfgFromNeighborhoods blockLength centers
    (inputs
      (.chronological, TapeIndex.input workTapeCount)).state
    (fun tape =>
      centers tape * blockLength +
        (inputs (.chronological, tape)).headRemainder.val)
    (fun tape slot => (inputs (.content slot, tape)).cells)

/-- Execute one local interval and return the final block of one named head.
All arguments are runtime data; there is no reference to the actual center
trajectory. -/
def localEndCenter (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs : PredecessorIndex workTapeCount →
      NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) : ℕ :=
  blockIndex blockLength
    (tapeAt
      (tm.toNTM.trace blockLength (fun _ => false)
        (localStartCfg tm blockLength centers inputs))
      tape).head

/-- Finite source-anchor check for all named tapes. -/
def initialCheck (tm : TM workTapeCount) (x : List Bool)
  (blockLength : ℕ) (guess : CenterGuess workTapeCount horizon) :
    Bool :=
  (List.finRange (workTapeCount + 2)).all fun tape =>
    guess.initialCenter tape == sourceCenter tm x blockLength tape

/-- Check one interval boundary against the locally reconstructed final head
blocks supplied through the compact predecessor callback. -/
def boundaryCheck (tm : TM workTapeCount) (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon) : Bool :=
  match provider guess interval with
  | none => false
  | some inputs =>
      (List.finRange (workTapeCount + 2)).all fun tape =>
        guess.derivedCenter tape (interval.val + 1) ==
          some (localEndCenter tm blockLength
            (guessedCenters guess interval.val) inputs tape)

/-- Executable conjunction of the initial anchor and every finite interval
boundary check. -/
def passes (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
  (guess : CenterGuess workTapeCount horizon) : Bool :=
  initialCheck tm x blockLength guess &&
    (List.finRange horizon).all fun interval =>
      boundaryCheck tm blockLength provider guess interval

/-- Proposition asserting that the executable finite checker accepts. -/
def Passes (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon) : Prop :=
  passes tm x blockLength provider guess = true

/-- Proof-only callback obligation. Correct guessed prefixes must yield the
actual compact predecessor vector for the next local simulation. -/
def IsExactProvider (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon) : Prop :=
  ∀ (guess : CenterGuess workTapeCount horizon)
      (interval : Fin horizon),
    (∀ boundary : Fin (horizon + 1),
      boundary.val ≤ interval.val →
        ∀ tape : TapeIndex workTapeCount,
          guess.derivedCenter tape boundary.val =
            some (actualCenterTrajectory
              tm x blockLength tape boundary.val)) →
    provider guess interval =
      some (NeighborhoodContent.predecessorContents
        tm x blockLength interval.val hpositive)

/-- Boolean width of each compact value requested from the callback. -/
def callbackValueWidth (tm : TM workTapeCount)
    (blockLength : ℕ) : ℕ :=
  Fintype.card tm.Q + 5 * blockLength

end Consistency

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
