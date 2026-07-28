/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluator.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluator.Internal

/-!
# Direct profiled evaluation of guessed neighborhood graphs

This module exposes an executable, fuel-bounded Cook--Mertz traversal which
regenerates every child from a finite center guess. It does not receive an
explicit tree and it does not read a source time-bound function. The
`profileCandidate` wrapper takes one concrete trial time, so a future fixed
simulator can stream trials and reuse its workspace.

For a semantically valid guess, the direct evaluator agrees with the ordinary
neighborhood-graph unrolling and its two roots are exactly the state and
verdict roots used by decision recovery. Semantic validity is not presented
as an executable check. `passesLocalChecks` instead exposes a finite callback
interface for locally replayed end centers; its soundness theorem requires a
separate proof that the callback agrees with the actual trajectory.

The workspace theorem charges the guessed movements and catalytic bank once,
one fixed-width frame per live recursive call, and callback scratch once.
Every possible recursive prefix and the complete two-query profile fit the
height-indexed bound. This remains an abstract evaluator-state theorem, not a
`TM.DecidesInSpace` theorem: the locally sound replay callback, grouped node
callback/modular arithmetic, and fixed-TM compilation are still required.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodEvaluator

open NeighborhoodGraph
open TreeEval CookMertz

/-- Every regenerated child strictly lowers the target interval rank. -/
theorem childAt_rank_lt
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (interval : ℕ) (hinterval : interval < horizon)
    (index : Fin (fanIn workTapeCount)) :
    (childAt guess
      (.graph (.computation tape slot interval)) index).rank <
        interval + 1 :=
  Internal.childAt_rank_lt_internal
    guess tape slot interval hinterval index

/-- Fuel bounds the height of the semantic certificate tree. -/
theorem unroll_height_le
    (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon) :
    (unroll guess failureValue sourceValue combine fuel node).height ≤
      fuel :=
  Internal.unroll_height_le_internal
    guess failureValue sourceValue combine fuel node

/-- The direct profiled traversal computes Cook--Mertz evaluation of its
semantic certificate tree. -/
theorem profileEvaluate_result
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel node).result =
      CookMertz.evaluate units
        (unroll guess failureValue sourceValue combine fuel node) :=
  Internal.profileEvaluate_result_internal
    units guess failureValue sourceValue combine fuel node

/-- At most `fuel + 1` recursive calls are live at any point. -/
theorem profileEvaluate_peakFrames_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : QueryNode workTapeCount horizon) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel node).peakFrames ≤ fuel + 1 :=
  Internal.profileEvaluate_peakFrames_le_internal
    units guess failureValue sourceValue combine fuel node

/-- A valid guessed prefix gives exactly the ordinary neighborhood-graph
unrolling. This is semantic soundness, not a runtime validity test. -/
theorem unroll_eq_graphUnroll
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : Node workTapeCount)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon) :
    unroll guess failureValue sourceValue combine fuel (.graph node) =
      NeighborhoodGraph.unroll tm x blockLength sourceValue combine node :=
  Internal.unroll_eq_graphUnroll_internal
    guess tm x blockLength failureValue sourceValue combine
      fuel node hvalid hrank hfuel

/-- Center agreement only through `cutoff` suffices for every recursive
query whose rank is at most `cutoff + 1`. Later guessed centers are not
consulted. -/
theorem unroll_eq_graphUnroll_of_prefix
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (cutoff fuel : ℕ) (node : Node workTapeCount)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ cutoff →
          ∀ tape : TapeIndex workTapeCount,
            guess.derivedCenter tape boundary.val =
              some (Guess.actualCenterTrajectory
                tm x blockLength tape boundary.val))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon)
    (hrankCutoff : node.rank ≤ cutoff + 1) :
    unroll guess failureValue sourceValue combine fuel (.graph node) =
      NeighborhoodGraph.unroll
        tm x blockLength sourceValue combine node :=
  Internal.unroll_eq_graphUnroll_of_prefix_internal
    guess tm x blockLength failureValue sourceValue combine
      cutoff fuel node hprefix hrank hfuel hrankCutoff

/-- Under the algebraic line identity, direct traversal returns the recursive
neighborhood-node value. -/
theorem profileEvaluate_graph_eq_nodeValue
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (fuel : ℕ) (node : Node workTapeCount)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon)
    (hline : LineCompatible units
      (NeighborhoodGraph.unroll
        tm x blockLength sourceValue combine node)) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel (.graph node)).result =
      NeighborhoodGraph.nodeValue
        tm x blockLength sourceValue combine node :=
  Internal.profileEvaluate_graph_eq_nodeValue_internal
    units guess tm x blockLength failureValue sourceValue combine
      fuel node hvalid hrank hfuel hline

/-- Prefix-local evaluator soundness: a query of rank at most
`cutoff + 1` depends only on guessed centers through `cutoff`. -/
theorem profileEvaluate_graph_eq_nodeValue_of_prefix
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (cutoff fuel : ℕ) (node : Node workTapeCount)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ cutoff →
          ∀ tape : TapeIndex workTapeCount,
            guess.derivedCenter tape boundary.val =
              some (Guess.actualCenterTrajectory
                tm x blockLength tape boundary.val))
    (hrank : node.rank ≤ fuel) (hfuel : fuel ≤ horizon)
    (hrankCutoff : node.rank ≤ cutoff + 1)
    (hline : LineCompatible units
      (NeighborhoodGraph.unroll
        tm x blockLength sourceValue combine node)) :
    (profileEvaluate units guess failureValue sourceValue combine
      fuel (.graph node)).result =
      NeighborhoodGraph.nodeValue
        tm x blockLength sourceValue combine node :=
  Internal.profileEvaluate_graph_eq_nodeValue_of_prefix_internal
    units guess tm x blockLength failureValue sourceValue combine
      cutoff fuel node hprefix hrank hfuel hrankCutoff hline

/-- A valid guessed chronological query is the decision-recovery state root. -/
theorem stateRoot_eq
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    stateRoot guess =
      .graph
        (NeighborhoodGraph.DecisionRecovery.stateNode
          tm x blockLength horizon) :=
  Internal.stateRoot_eq_internal
    guess tm x blockLength hvalid

/-- A valid latest-output query is the decision-recovery verdict root. -/
theorem verdictRoot_eq
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    verdictRoot guess blockLength =
      .graph
        (NeighborhoodGraph.DecisionRecovery.verdictBlockNode
          tm x blockLength horizon) :=
  Internal.verdictRoot_eq_internal
    guess tm x blockLength hvalid

/-- The sequential two-query execution returns the two semantic root values. -/
theorem profileDecision_result_eq_nodeValues
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hstateLine : LineCompatible units
      (NeighborhoodGraph.unroll tm x blockLength sourceValue combine
        (NeighborhoodGraph.DecisionRecovery.stateNode
          tm x blockLength horizon)))
    (hverdictLine : LineCompatible units
      (NeighborhoodGraph.unroll tm x blockLength sourceValue combine
        (NeighborhoodGraph.DecisionRecovery.verdictBlockNode
          tm x blockLength horizon))) :
    (profileDecision units guess blockLength failureValue
      sourceValue combine).result =
      (NeighborhoodGraph.nodeValue tm x blockLength sourceValue combine
          (NeighborhoodGraph.DecisionRecovery.stateNode
            tm x blockLength horizon),
        NeighborhoodGraph.nodeValue tm x blockLength sourceValue combine
          (NeighborhoodGraph.DecisionRecovery.verdictBlockNode
            tm x blockLength horizon)) :=
  Internal.profileDecision_result_eq_nodeValues_internal
    units guess tm x blockLength failureValue sourceValue combine
      hvalid hstateLine hverdictLine

/-- The two sequential decision queries reuse a stack of at most
`horizon + 1` frames. -/
theorem profileDecision_peakFrames_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (blockLength : ℕ) (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    (profileDecision units guess blockLength failureValue
      sourceValue combine).peakFrames ≤ horizon + 1 :=
  Internal.profileDecision_peakFrames_le_internal
    units guess blockLength failureValue sourceValue combine

/-- One explicit candidate-time trial has the corresponding finite horizon
bound and receives no time-bound function as input. -/
theorem profileCandidate_peakFrames_le
    [Field F] [AddCommGroup V] [Module F V]
    (units : List Fˣ) (candidateTime : ℕ)
    (guess : Guess.CenterGuess workTapeCount
      (candidateHorizon candidateTime))
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    (profileCandidate units candidateTime guess failureValue
      sourceValue combine).peakFrames ≤
      candidateHorizon candidateTime + 1 :=
  Internal.profileCandidate_peakFrames_le_internal
    units candidateTime guess failureValue sourceValue combine

/-- Sequential trial batches compose by reusing storage and taking a maximum. -/
theorem streamedPeak_append (first second : List ℕ) :
    streamedPeak (first ++ second) =
      second.foldl max (streamedPeak first) :=
  Internal.streamedPeak_append_internal first second

/-- If every streamed trial fits one bound, the complete streamed run fits
the same bound. -/
theorem streamedPeak_le
    (peaks : List ℕ) (bound : ℕ)
    (hpeaks : ∀ peak ∈ peaks, peak ≤ bound) :
    streamedPeak peaks ≤ bound :=
  Internal.streamedPeak_le_internal peaks bound hpeaks

/-- Every active recursive-call prefix fits the assigned stack/bank/scratch
accounting when its root rank is within the trial horizon. -/
theorem ActiveStack.prefixBitUsage_le
    (layout : StorageLayout)
    {guess : Guess.CenterGuess workTapeCount horizon}
    {root current : QueryNode workTapeCount horizon}
    {tail : List (QueryNode workTapeCount horizon)}
    (hroot : root.rank ≤ horizon)
    (hstack : ActiveStack guess root (current :: tail)) :
    prefixBitUsage layout workTapeCount horizon
        (current :: tail).length ≤
      peakBitBound layout workTapeCount horizon :=
  Internal.activeStack_prefixBitUsage_le_internal
    layout hroot hstack

/-- The measured peak of the complete two-query execution fits the same
assigned storage accounting. -/
theorem profileDecision_prefixBitUsage_le
    [Field F] [AddCommGroup V] [Module F V]
    (layout : StorageLayout)
    (units : List Fˣ) (guess : Guess.CenterGuess workTapeCount horizon)
    (blockLength : ℕ) (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    prefixBitUsage layout workTapeCount horizon
        (profileDecision units guess blockLength failureValue
          sourceValue combine).peakFrames ≤
      peakBitBound layout workTapeCount horizon :=
  Internal.profileDecision_prefixBitUsage_le_internal
    layout units guess blockLength failureValue sourceValue combine

/-- One explicit candidate trial fits its assigned stack/bank/scratch
accounting. -/
theorem profileCandidate_prefixBitUsage_le
    [Field F] [AddCommGroup V] [Module F V]
    (layout : StorageLayout)
    (units : List Fˣ) (candidateTime : ℕ)
    (guess : Guess.CenterGuess workTapeCount
      (candidateHorizon candidateTime))
    (failureValue : V)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → Slot → ℕ →
      (Fin (fanIn workTapeCount) → V) → V) :
    prefixBitUsage layout workTapeCount
        (candidateHorizon candidateTime)
        (profileCandidate units candidateTime guess failureValue
          sourceValue combine).peakFrames ≤
      candidatePeakBitBound layout workTapeCount candidateTime :=
  Internal.profileCandidate_prefixBitUsage_le_internal
    layout units candidateTime guess failureValue sourceValue combine

/-- The frozen-run reference oracle describes the true center trajectory.
It is a semantic reference, not the promised local-replay implementation. -/
theorem semanticCenterOracle_agreesWith
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) :
    (semanticCenterOracle tm x blockLength horizon).AgreesWith
      (Guess.actualCenterTrajectory tm x blockLength) :=
  Internal.semanticCenterOracle_agreesWith_internal
    tm x blockLength horizon

/-- The canonical true-center guess passes all checks against the semantic
reference oracle. This is a completeness fact, not a space bound for the
reference oracle. -/
theorem actualCenterGuess_passesSemanticChecks
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength) :
    passesLocalChecks
      (Guess.actualCenterGuess tm x blockLength horizon)
      (semanticCenterOracle tm x blockLength horizon) = true :=
  Internal.actualCenterGuess_passesSemanticChecks_internal
    tm x blockLength horizon hpositive

/-- A globally correct reference oracle satisfies the weaker prefix-local
replay contract. -/
theorem CenterOracle.AgreesWith.isPrefixSoundFor
    (guess : Guess.CenterGuess workTapeCount horizon)
    (oracle : CenterOracle workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (hagrees : oracle.AgreesWith trajectory) :
    oracle.IsPrefixSoundFor guess trajectory :=
  Internal.agreesWith_isPrefixSoundFor_internal
    guess oracle trajectory hagrees

/-- First-mismatch soundness: finite checks force the complete guessed
trajectory to be correct when each local replay is sound under correctness of
the preceding prefix. -/
theorem passesLocalChecks_prefixSound
    (guess : Guess.CenterGuess workTapeCount horizon)
    (oracle : CenterOracle workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (hpasses : passesLocalChecks guess oracle = true)
    (horacle : oracle.IsPrefixSoundFor guess trajectory) :
    guess.IsValidFor trajectory :=
  Internal.passesLocalChecks_prefixSound_internal
    guess oracle trajectory hpasses horacle

/-- Passing all finite local checks is sound once the separate end-center
callback has been proved to describe the target trajectory. -/
theorem passesLocalChecks_sound
    (guess : Guess.CenterGuess workTapeCount horizon)
    (oracle : CenterOracle workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (hpasses : passesLocalChecks guess oracle = true)
    (horacle : oracle.AgreesWith trajectory) :
    guess.IsValidFor trajectory :=
  Internal.passesLocalChecks_sound_internal
    guess oracle trajectory hpasses horacle

/-- In particular, checks against the semantic reference imply validity.
This corollary is not an executable-space claim about that reference oracle. -/
theorem passesSemanticCenterChecks_sound
    (guess : Guess.CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (hpasses :
      passesLocalChecks guess
        (semanticCenterOracle tm x blockLength horizon) = true) :
    guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength) :=
  passesLocalChecks_sound guess
    (semanticCenterOracle tm x blockLength horizon)
    (Guess.actualCenterTrajectory tm x blockLength) hpasses
    (semanticCenterOracle_agreesWith
      tm x blockLength horizon)

end NeighborhoodEvaluator

end TimeSpaceSimulation

end Complexity
