/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.EvaluatedProvider.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.EvaluatedProvider.Internal

/-!
# Evaluated-node consistency providers

`NodeContentCallback` is the runtime boundary between guessed neighborhood
graphs and the consistency checker. It evaluates one regenerated graph node
to either one compact content value or `none`; `provider` collects the fixed
predecessor vector and propagates every failure.

The semantic trajectory occurs only in `IsPrefixExact`. That proof-only
contract implies `Consistency.IsExactProvider`, so the existing completeness
and soundness theorems apply without placing a true-trajectory oracle in the
executable callback.

`directCallback` instantiates the boundary with the profiled direct
`NeighborhoodEvaluator`. Its grouped source/combine arithmetic and compact
decoder remain parameters; `DirectIsPrefixExact` is precisely the residual
semantic obligation.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace EvaluatedProvider

/-- Missing guessed-node regeneration propagates to one callback input. -/
theorem inputAt?_eq_none_of_predecessor?_eq_none
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hpredecessor : guess.predecessor? interval index = none) :
    inputAt? callback guess interval index = none :=
  Internal.inputAt?_eq_none_of_predecessor?_eq_none_internal
    callback guess interval index hpredecessor

/-- A failed node evaluator propagates to one callback input. -/
theorem inputAt?_eq_none_of_callback_eq_none
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (node : Node workTapeCount)
    (hpredecessor : guess.predecessor? interval index = some node)
    (hcallback : callback guess node = none) :
    inputAt? callback guess interval index = none :=
  Internal.inputAt?_eq_none_of_callback_eq_none_internal
    callback guess interval index node hpredecessor hcallback

/-- Failure of any one collected input makes the whole provider fail. -/
theorem provider_eq_none_of_inputAt?_eq_none
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hinput : inputAt? callback guess interval index = none) :
    provider callback guess interval = none :=
  Internal.provider_eq_none_of_inputAt?_eq_none_internal
    callback guess interval index hinput

/-- Missing predecessor regeneration makes the whole provider fail. -/
theorem provider_eq_none_of_predecessor?_eq_none
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hpredecessor : guess.predecessor? interval index = none) :
    provider callback guess interval = none :=
  Internal.provider_eq_none_of_predecessor?_eq_none_internal
    callback guess interval index hpredecessor

/-- Failure returned by any regenerated-node callback makes the whole
provider fail. -/
theorem provider_eq_none_of_callback_eq_none
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (node : Node workTapeCount)
    (hpredecessor : guess.predecessor? interval index = some node)
    (hcallback : callback guess node = none) :
    provider callback guess interval = none :=
  Internal.provider_eq_none_of_callback_eq_none_internal
    callback guess interval index node hpredecessor hcallback

/-- Pointwise prefix exactness is sufficient for the consistency checker's
provider contract. -/
theorem IsPrefixExact.isExactProvider
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (hexact :
      IsPrefixExact tm x blockLength hpositive callback) :
    Consistency.IsExactProvider tm x blockLength hpositive
      (provider callback) :=
  Internal.isExactProvider_internal
    tm x blockLength hpositive callback hexact

/-- Prefix-local evaluator soundness plus exact decoding discharges the
direct adapter's semantic obligation. These are precisely the grouped
arithmetic and compact-decoding hypotheses left to a concrete encoding. -/
theorem directIsPrefixExact_of_nodeValue
    [Field F] [AddCommGroup V] [Module F V]
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
      V → Option (NeighborhoodContent.Content blockLength tm.Q))
    (hline :
      ∀ (guess : CenterGuess workTapeCount horizon)
          (interval : Fin horizon)
          (index : PredecessorIndex workTapeCount),
        TreeEval.CookMertz.LineCompatible units
          (NeighborhoodGraph.unroll tm x blockLength
            (sourceValue guess) (combine guess)
            (NeighborhoodGraph.predecessor
              tm x blockLength interval.val index)))
    (hdecode :
      ∀ (guess : CenterGuess workTapeCount horizon)
          (interval : Fin horizon)
          (index : PredecessorIndex workTapeCount),
        decode (NeighborhoodGraph.nodeValue tm x blockLength
          (sourceValue guess) (combine guess)
          (NeighborhoodGraph.predecessor
            tm x blockLength interval.val index)) =
          some (NeighborhoodContent.predecessorContents
            tm x blockLength interval.val hpositive index)) :
    DirectIsPrefixExact tm x blockLength hpositive
      units failureValue sourceValue combine decode :=
  Internal.directIsPrefixExact_of_nodeValue_internal
    tm x blockLength hpositive units failureValue
      sourceValue combine decode hline hdecode

/-- The direct profiled evaluator supplies an exact consistency provider
once its explicit grouped-arithmetic and decoding obligation is proved. -/
theorem DirectIsPrefixExact.provider_isExact
    [Field F] [AddCommGroup V] [Module F V]
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
      V → Option (NeighborhoodContent.Content blockLength tm.Q))
    (hexact : DirectIsPrefixExact tm x blockLength hpositive
      units failureValue sourceValue combine decode) :
    Consistency.IsExactProvider tm x blockLength hpositive
      (provider (directCallback
        units failureValue sourceValue combine decode)) :=
  Internal.directProvider_isExact_internal
    tm x blockLength hpositive units failureValue
      sourceValue combine decode hexact

end EvaluatedProvider

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
