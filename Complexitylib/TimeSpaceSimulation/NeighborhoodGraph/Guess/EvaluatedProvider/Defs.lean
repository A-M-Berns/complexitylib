/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluator.Defs

/-!
# Node-evaluation callbacks as consistency input providers

This module turns the weakest useful node-evaluation callback into the
fixed-vector callback consumed by `Consistency`.

At runtime, a `NodeContentCallback` receives only a finite center guess and
one guessed graph node. It returns either one compact value or explicit
failure. `inputAt?` first regenerates the requested predecessor from the
guess, then invokes the callback. `provider` succeeds only when all fixed
predecessor roles succeed.

The actual center trajectory appears only in the proof-only
`IsPrefixExact` contract. No runtime definition reads it.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace EvaluatedProvider

/-- Option-valued evaluation of one node in one guessed neighborhood graph.

This is the minimal runtime callback: no semantic trajectory, correctness
proof, or entire predecessor vector is part of the interface. -/
abbrev NodeContentCallback (workTapeCount : ℕ) (tm : TM workTapeCount)
    (blockLength horizon : ℕ) :=
  CenterGuess workTapeCount horizon →
    Node workTapeCount →
      Option (NeighborhoodContent.Content blockLength tm.Q)

/-- Regenerate one typed predecessor and evaluate its compact content.

Failure of either predecessor regeneration or node evaluation propagates as
`none`. -/
def inputAt?
    (callback : NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount) :
    Option (NeighborhoodContent.Content blockLength tm.Q) :=
  (guess.predecessor? interval index).bind (callback guess)

/-- Collect every fixed predecessor role into a consistency input vector.

The provider returns `none` unless every regenerated-node callback succeeds.
The finite availability test and subsequent `Option.get` are executable;
the proof arguments are erased. -/
def provider
    (callback : NodeContentCallback workTapeCount tm blockLength horizon) :
    Consistency.InputProvider tm blockLength horizon :=
  fun guess interval =>
    if havailable :
        ∀ index : PredecessorIndex workTapeCount,
          (inputAt? callback guess interval index).isSome = true then
      some fun index =>
        (inputAt? callback guess interval index).get
          (havailable index)
    else
      none

/-- Proof-only prefix contract sufficient for the collected provider.

On a correct center prefix, every regenerated callback input must be the
corresponding semantic predecessor value. The trajectory occurs only in this
certificate, never in `inputAt?` or `provider`. -/
def IsPrefixExact (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon) : Prop :=
  ∀ (guess : CenterGuess workTapeCount horizon)
      (interval : Fin horizon),
    (∀ boundary : Fin (horizon + 1),
      boundary.val ≤ interval.val →
        ∀ tape : TapeIndex workTapeCount,
          guess.derivedCenter tape boundary.val =
            some (actualCenterTrajectory
              tm x blockLength tape boundary.val)) →
    ∀ index : PredecessorIndex workTapeCount,
      inputAt? callback guess interval index =
        some (NeighborhoodContent.predecessorContents
          tm x blockLength interval.val hpositive index)

/-- Adapt any total value evaluator followed by an Option-valued decoder. -/
def ofValueEvaluator
    (evaluate :
      CenterGuess workTapeCount horizon → Node workTapeCount → V)
    (decode :
      V → Option (NeighborhoodContent.Content blockLength tm.Q)) :
    NodeContentCallback workTapeCount tm blockLength horizon :=
  fun guess node => decode (evaluate guess node)

/-- Parametric adapter from the direct profiled neighborhood evaluator.

The source and combine callbacks may depend on the finite center guess.
Grouped arithmetic and final compact decoding remain explicit arguments. -/
def directCallback [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (failureValue : V)
    (sourceValue :
      CenterGuess workTapeCount horizon →
        TapeIndex workTapeCount → ℕ → V)
    (combine :
      CenterGuess workTapeCount horizon →
        TapeIndex workTapeCount → Slot → ℕ →
          (Fin (NeighborhoodEvaluator.fanIn workTapeCount) → V) → V)
    (decode :
      V → Option (NeighborhoodContent.Content blockLength tm.Q)) :
    NodeContentCallback workTapeCount tm blockLength horizon :=
  ofValueEvaluator
    (fun guess node =>
      (NeighborhoodEvaluator.profileEvaluate units guess failureValue
        (sourceValue guess) (combine guess) horizon
        (.graph node)).result)
    decode

/-- Proof-only exactness obligation for the parametric direct adapter.

This isolates the remaining grouped-arithmetic and decoding theorem without
placing it in the runtime callback. -/
def DirectIsPrefixExact [Field F] [AddCommGroup V] [Module F V]
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (units : List Fˣ) (failureValue : V)
    (sourceValue :
      CenterGuess workTapeCount horizon →
        TapeIndex workTapeCount → ℕ → V)
    (combine :
      CenterGuess workTapeCount horizon →
        TapeIndex workTapeCount → Slot → ℕ →
          (Fin (NeighborhoodEvaluator.fanIn workTapeCount) → V) → V)
    (decode :
      V → Option (NeighborhoodContent.Content blockLength tm.Q)) : Prop :=
  IsPrefixExact tm x blockLength hpositive
    (directCallback units failureValue sourceValue combine decode)

end EvaluatedProvider

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
