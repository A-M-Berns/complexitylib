/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.EvaluatedProvider.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluator

/-!
# Proof internals for evaluated consistency providers

This module proves that node-level failure propagates through the collected
provider and that pointwise prefix exactness is sufficient for the
`Consistency.IsExactProvider` contract.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace EvaluatedProvider

namespace Internal

theorem inputAt?_eq_none_of_predecessor?_eq_none_internal
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hpredecessor : guess.predecessor? interval index = none) :
    inputAt? callback guess interval index = none := by
  simp [inputAt?, hpredecessor]

theorem inputAt?_eq_none_of_callback_eq_none_internal
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (node : Node workTapeCount)
    (hpredecessor : guess.predecessor? interval index = some node)
    (hcallback : callback guess node = none) :
    inputAt? callback guess interval index = none := by
  simp [inputAt?, hpredecessor, hcallback]

theorem provider_eq_none_of_inputAt?_eq_none_internal
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hinput : inputAt? callback guess interval index = none) :
    provider callback guess interval = none := by
  unfold provider
  split
  · next havailable =>
      have : (none :
          Option (NeighborhoodContent.Content blockLength tm.Q)).isSome =
          true := by
        simpa [hinput] using havailable index
      simp at this
  · rfl

theorem provider_eq_none_of_predecessor?_eq_none_internal
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hpredecessor : guess.predecessor? interval index = none) :
    provider callback guess interval = none :=
  provider_eq_none_of_inputAt?_eq_none_internal
    callback guess interval index
      (inputAt?_eq_none_of_predecessor?_eq_none_internal
        callback guess interval index hpredecessor)

theorem provider_eq_none_of_callback_eq_none_internal
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (node : Node workTapeCount)
    (hpredecessor : guess.predecessor? interval index = some node)
    (hcallback : callback guess node = none) :
    provider callback guess interval = none :=
  provider_eq_none_of_inputAt?_eq_none_internal
    callback guess interval index
      (inputAt?_eq_none_of_callback_eq_none_internal
        callback guess interval index node hpredecessor hcallback)

theorem isExactProvider_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (callback :
      NodeContentCallback workTapeCount tm blockLength horizon)
    (hexact :
      IsPrefixExact tm x blockLength hpositive callback) :
    Consistency.IsExactProvider tm x blockLength hpositive
      (provider callback) := by
  intro guess interval hprefix
  have hinput :
      ∀ index : PredecessorIndex workTapeCount,
        inputAt? callback guess interval index =
          some (NeighborhoodContent.predecessorContents
            tm x blockLength interval.val hpositive index) :=
    hexact guess interval hprefix
  have havailable :
      ∀ index : PredecessorIndex workTapeCount,
        (inputAt? callback guess interval index).isSome = true := by
    intro index
    rw [hinput index]
    rfl
  simp only [provider, dif_pos havailable]
  congr 1
  funext index
  exact Option.get_of_eq_some
    (havailable index) (hinput index)

theorem directIsPrefixExact_of_nodeValue_internal
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
      units failureValue sourceValue combine decode := by
  intro guess interval hprefix index
  have hpredecessor :=
    guess.predecessor?_eq_of_prefix
      tm x blockLength interval index hprefix
  have hrankLt :=
    NeighborhoodGraph.predecessor_rank_lt
      tm x blockLength interval.val
      (TapeIndex.input workTapeCount) .center index
  have hrankInterval :
      (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index).rank ≤
          interval.val := by
    simpa only [Node.rank, Nat.lt_succ_iff] using hrankLt
  have hrank :
      (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index).rank ≤ horizon := by
    exact hrankInterval.trans (Nat.le_of_lt interval.isLt)
  have hrankCutoff :
      (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index).rank ≤
          interval.val + 1 := by
    omega
  have hevaluate :=
    NeighborhoodEvaluator.profileEvaluate_graph_eq_nodeValue_of_prefix
      units guess tm x blockLength failureValue
      (sourceValue guess) (combine guess)
      interval.val horizon
      (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index)
      hprefix hrank le_rfl hrankCutoff
      (hline guess interval index)
  simp only [inputAt?, hpredecessor, Option.bind_some,
    directCallback, ofValueEvaluator]
  rw [hevaluate]
  exact hdecode guess interval index

theorem directProvider_isExact_internal
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
  isExactProvider_internal tm x blockLength hpositive
    (directCallback units failureValue sourceValue combine decode) hexact

end Internal

end EvaluatedProvider

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
