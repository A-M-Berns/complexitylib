/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.Internal

/-!
# Correct executable grouped evaluation of neighborhood graphs

This module exposes the direct, tree-free neighborhood evaluator instantiated
with the streaming grouped Lagrange callback. A finite source-machine
encoding is an explicit argument. For every valid center guess, node queries
return the grouped encoding of the exact semantic compact value, and the two
decision queries decode to `DecisionRecovery.decisionSnapshot`.

The searched `ZMod` type depends on the explicit block length and fixed
machine state count; `EvaluationField` records that dependency directly.
The `Residue` namespace contains the fully natural-residue traversal. It
streams the nonzero scalars with `PrimeField.Runtime.foldNonzero`, rather
than allocating the typed evaluator's modulus-sized unit list. Its cast
theorems identify the complete profiled traversal, decoded snapshot, and
certified engine with their typed correctness reference.

## Main theorems

- `decodeBits_encodeBits` -- explicit executable compact decoding is exact
- `combineValue_encoded` -- the grouped callback preserves encoded nodes
- `profileNode_result_eq_encoded` -- valid direct queries are semantically exact
- `profileDecision_result_eq_encoded` -- both decision roots are exact
- `decodedDecisionSnapshot_eq` -- decoding recovers the semantic snapshot
- `Residue.coe_evaluateNode` -- natural-residue and typed callbacks agree
- `Residue.profileDecision_peakFrames_le` -- streamed traversal uses the
  same bounded recursive-frame peak
- `Residue.certifiedEngine_isExact` -- the fully natural engine is exact
- `combineValueViaResidues_eq` -- the Nat callback is a drop-in typed callback
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodExecutableEvaluation

open NeighborhoodGraph
open TreeEval CookMertz

theorem firstTrueFin_oneHot {count : ℕ}
    (default value : Fin count) :
    firstTrueFin default (fun candidate =>
      decide (candidate = value)) = value :=
  Internal.firstTrueFin_oneHot_internal default value

theorem decodeGamma_oneHot (value : Γ) :
    decodeGamma (fun candidate => decide (candidate = value)) =
      value :=
  Internal.decodeGamma_oneHot_internal value

/-- Explicit finite reindexing preserves semantic coordinate bits. -/
theorem bitsAt_encodeBits
    (encoding : FiniteEncoding tm blockLength)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q)
    (coordinate :
      ComputationGraph.CompactEncoding.Coordinate blockLength tm.Q) :
    bitsAt encoding (encodeBits encoding value) coordinate =
      ComputationGraph.CompactEncoding.coordinateBits value coordinate :=
  Internal.bitsAt_encodeBits_internal encoding value coordinate

/-- Total executable decoding is a left inverse of explicit compact
encoding. -/
theorem decodeBits_encodeBits
    (encoding : FiniteEncoding tm blockLength)
    (defaultState : tm.Q) (hpositive : 0 < blockLength)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q) :
    decodeBits encoding defaultState hpositive
        (encodeBits encoding value) =
      value :=
  Internal.decodeBits_encodeBits_internal
    encoding defaultState hpositive value

/-- The executable Boolean local transition maps encoded children to the
encoding of their compact local transition. -/
theorem booleanCombine_encoded
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        NeighborhoodContent.Content blockLength tm.Q) :
    booleanCombine tm x blockLength encoding hpositive
        tape slot timeBlock
        (fun child => encodeBits encoding (children child)) =
      encodeBits encoding
        (NeighborhoodContent.localNodeFunction
          tm x blockLength hpositive timeBlock tape slot fun index =>
            children (predecessorIndexEquiv workTapeCount index)) :=
  Internal.booleanCombine_encoded_internal
    tm x blockLength encoding hpositive
      tape slot timeBlock children

/-- The streaming grouped callback maps grouped Boolean encodings to the
grouped encoding of the Boolean local result. -/
theorem combineValue_encoded
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        Fin (payloadWidth tm blockLength) → Bool) :
    combineValue tm x blockLength encoding hpositive
        tape slot timeBlock
        (fun child =>
          PrimeGrouped.Logarithmic.encodeValue
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount)
            (children child)) =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength)
        (graphFanIn workTapeCount)
        (booleanCombine tm x blockLength encoding hpositive
          tape slot timeBlock children) :=
  Internal.combineValue_encoded_internal
    tm x blockLength encoding hpositive
      tape slot timeBlock children

/-- The proof-only unrolling of the executable callback satisfies the
Cook--Mertz line identity. -/
theorem groupedUnroll_lineCompatible
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (node : Node workTapeCount) :
    LineCompatible
      (PrimeGrouped.Logarithmic.units
        (payloadWidth tm blockLength) (graphFanIn workTapeCount))
      (NeighborhoodGraph.unroll tm x blockLength
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        node) :=
  Internal.groupedUnroll_lineCompatible_internal
    tm x blockLength encoding hpositive node

/-- Recursive grouped node evaluation equals the grouped encoding of the
semantic compact node value. -/
theorem groupedNodeValue_eq_encoded
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (node : Node workTapeCount) :
    NeighborhoodGraph.nodeValue tm x blockLength
        (sourceValue tm x blockLength encoding hpositive)
        (combineValue tm x blockLength encoding hpositive)
        node =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent
            tm x blockLength hpositive node)) :=
  Internal.groupedNodeValue_eq_encoded_internal
    tm x blockLength encoding hpositive node

/-- A valid guessed-graph query returns the exact grouped semantic node
value whenever its rank fits the explicit horizon. -/
theorem profileNode_result_eq_encoded
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (node : Node workTapeCount)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (hrank : node.rank ≤ horizon) :
    (profileNode tm x blockLength encoding hpositive
      horizon guess node).result =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent
            tm x blockLength hpositive node)) :=
  Internal.profileNode_result_eq_encoded_internal
    tm x blockLength encoding hpositive horizon
      guess node hvalid hrank

/-- The direct state-root query returns its exact grouped semantic value. -/
theorem profileState_result_eq_encoded
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    (profileState tm x blockLength encoding hpositive
      horizon guess).result =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent tm x blockLength hpositive
            (DecisionRecovery.stateNode tm x blockLength horizon))) :=
  Internal.profileState_result_eq_encoded_internal
    tm x blockLength encoding hpositive horizon guess hvalid

/-- The direct verdict-root query returns its exact grouped semantic value. -/
theorem profileVerdict_result_eq_encoded
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    (profileVerdict tm x blockLength encoding hpositive
      horizon guess).result =
      PrimeGrouped.Logarithmic.encodeValue
        (payloadWidth tm blockLength) (graphFanIn workTapeCount)
        (encodeBits encoding
          (NeighborhoodContent.nodeContent tm x blockLength hpositive
            (DecisionRecovery.verdictBlockNode
              tm x blockLength horizon))) :=
  Internal.profileVerdict_result_eq_encoded_internal
    tm x blockLength encoding hpositive horizon guess hvalid

/-- Both sequential decision queries return their exact grouped semantic
root values. -/
theorem profileDecision_result_eq_encoded
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    (profileDecision tm x blockLength encoding hpositive
      horizon guess).result =
      (PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength) (graphFanIn workTapeCount)
          (encodeBits encoding
            (NeighborhoodContent.nodeContent tm x blockLength hpositive
              (DecisionRecovery.stateNode
                tm x blockLength horizon))),
        PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength) (graphFanIn workTapeCount)
          (encodeBits encoding
            (NeighborhoodContent.nodeContent tm x blockLength hpositive
              (DecisionRecovery.verdictBlockNode
                tm x blockLength horizon)))) :=
  Internal.profileDecision_result_eq_encoded_internal
    tm x blockLength encoding hpositive horizon guess hvalid

/-- Sequential state and verdict traversal reuses at most `horizon + 1`
recursive frames. -/
theorem profileDecision_peakFrames_le
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    (profileDecision tm x blockLength encoding hpositive
      horizon guess).peakFrames ≤ horizon + 1 :=
  Internal.profileDecision_peakFrames_le_internal
    tm x blockLength encoding hpositive horizon guess

/-- Grouped field decoding followed by explicit compact decoding recovers
every encoded compact value. -/
theorem decodeValue_encodeContent
    (tm : TM workTapeCount) (blockLength : ℕ)
    (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (value : NeighborhoodContent.Content blockLength tm.Q) :
    decodeValue tm blockLength encoding hpositive
        (PrimeGrouped.Logarithmic.encodeValue
          (payloadWidth tm blockLength) (graphFanIn workTapeCount)
          (encodeBits encoding value)) =
      value :=
  Internal.decodeValue_encodeContent_internal
    tm blockLength encoding hpositive value

/-- Valid direct state/verdict queries decode to the exact semantic horizon
snapshot. -/
theorem decodedDecisionSnapshot_eq
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    decodedDecisionSnapshot tm x blockLength encoding hpositive
        horizon guess =
      DecisionRecovery.decisionSnapshot
        tm x blockLength hpositive horizon :=
  Internal.decodedDecisionSnapshot_eq_internal
    tm x blockLength encoding hpositive horizon guess hvalid

/-- If a halted run is covered by the horizon, the direct executable queries
recover its state and verdict cell exactly. -/
theorem decodedDecisionSnapshot_eq_of_reachesIn
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon haltTime : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength))
    (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (hle : haltTime ≤ timeBlockStart blockLength horizon) :
    decodedDecisionSnapshot tm x blockLength encoding hpositive
        horizon guess =
      { state := cfg.state
        verdict := cfg.output.cells 1 } :=
  Internal.decodedDecisionSnapshot_eq_of_reachesIn_internal
    tm x blockLength encoding hpositive horizon haltTime
      guess hvalid cfg hreach hhalt hle

/-- The concrete node callback is definitionally the decoded profiled
node query. -/
theorem nodeCallback_apply
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (node : Node workTapeCount) :
    nodeCallback tm x blockLength encoding hpositive horizon guess node =
      some (decodeValue tm blockLength encoding hpositive
        (profileNode tm x blockLength encoding hpositive
          horizon guess node).result) := by
  rfl

/-- The decoded direct-node callback is exact on every semantically correct
center prefix required by the local consistency checker. -/
theorem nodeCallback_isPrefixExact
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    Guess.EvaluatedProvider.IsPrefixExact
      tm x blockLength hpositive
      (nodeCallback tm x blockLength encoding hpositive horizon) :=
  Internal.nodeCallback_isPrefixExact_internal
    tm x blockLength encoding hpositive horizon

/-- The concrete decoded evaluator/snapshot pair satisfies the complete
proof-only contract expected by one certified trial. -/
theorem certifiedEngine_isExact
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    (certifiedEngine tm x blockLength encoding hpositive horizon).IsExact
      x hpositive :=
  Internal.certifiedEngine_isExact_internal
    tm x blockLength encoding hpositive horizon

/-- Casting canonical residues back into the searched field recovers the
typed value. -/
@[simp] theorem ofResidues_toResidues
    (value : EvaluationValue tm blockLength) :
    ofResidues (toResidues value) = value :=
  Internal.ofResidues_toResidues_internal value

/-- Casting natural representatives and reading them back performs runtime
normalization. -/
theorem toResidues_ofResidues
    (value : ResidueValue tm blockLength) (chunk :
      Fin (PrimeGrouped.Logarithmic.chunkCount
        (payloadWidth tm blockLength) (graphFanIn _))) :
    toResidues (ofResidues value) chunk =
      PrimeField.Runtime.normalize
        (modulus tm blockLength) (value chunk) :=
  Internal.toResidues_ofResidues_internal value chunk

namespace Residue

/-- Casting the natural-residue Lagrange factor gives the typed executable
factor exactly. -/
theorem coe_lagrangeFactor
    (payloadWidth fanIn : ℕ)
    (selected other :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point : ℕ) :
    (lagrangeFactor payloadWidth fanIn
        selected other point :
      PrimeGrouped.Logarithmic.Field payloadWidth fanIn) =
      GroupedExtension.Evaluation.lagrangeFactorValue
        (PrimeGrouped.Logarithmic.codebook payloadWidth fanIn)
        selected other
        (point :
          PrimeGrouped.Logarithmic.Field payloadWidth fanIn) :=
  Internal.ResidueBridge.coe_lagrangeFactor_internal
    payloadWidth fanIn selected other point

/-- Casting the complete natural-residue grouped node evaluator gives the
typed grouped callback exactly. -/
theorem coe_evaluateNode
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ) :
    (fun outputChunk =>
      (evaluateNode payloadWidth fanIn combine args outputChunk :
        PrimeGrouped.Logarithmic.Field payloadWidth fanIn)) =
      GroupedExtension.Evaluation.evaluateNode
        (PrimeGrouped.Logarithmic.codebook payloadWidth fanIn)
        (PrimeGrouped.Logarithmic.layout payloadWidth fanIn)
        combine
        (fun child chunk =>
          (args child chunk :
            PrimeGrouped.Logarithmic.Field payloadWidth fanIn)) :=
  Internal.ResidueBridge.coe_evaluateNode_internal
    payloadWidth fanIn combine args

/-- A natural-residue query preserves canonical representatives throughout
the complete catalytic register bank. -/
theorem profileAccumulate_canonical
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (regs : Registers tm blockLength)
    (hregs :
      ∀ register chunk,
        regs register chunk < modulus tm blockLength) :
    ∀ register chunk,
      (profileAccumulate tm x blockLength encoding hpositive
        horizon guess fuel node scalar out regs).result register chunk <
        modulus tm blockLength :=
  Internal.residueProfileAccumulate_canonical_internal
    tm x blockLength encoding hpositive horizon guess fuel node
      scalar out regs hregs

/-- On canonical natural representatives, one profiled query adds its
scaled zero-bank query result at exactly the selected register and restores
every other catalytic register. -/
theorem profileAccumulate_result
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (regs : Registers tm blockLength)
    (hregs :
      ∀ register chunk,
        regs register chunk < modulus tm blockLength) :
    (profileAccumulate tm x blockLength encoding hpositive
      horizon guess fuel node scalar out regs).result =
      addAt tm blockLength regs out
        (scaleValue tm blockLength scalar
          (profileEvaluate tm x blockLength encoding hpositive
            horizon guess fuel node).result) :=
  Internal.residueProfileAccumulate_result_internal
    tm x blockLength encoding hpositive horizon guess fuel node
      scalar out regs hregs

/-- A zero-bank natural-residue query returns canonical representatives. -/
theorem profileEvaluate_canonical
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    ∀ chunk,
      (profileEvaluate tm x blockLength encoding hpositive
        horizon guess fuel node).result chunk <
        modulus tm blockLength :=
  Internal.residueProfileEvaluate_canonical_internal
    tm x blockLength encoding hpositive horizon guess fuel node

/-- Casting a complete natural-residue query profile gives the typed direct
query profile, including its peak-frame count. -/
theorem profileEvaluate_cast
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    Workspace.Profile.map ofResidues
        (profileEvaluate tm x blockLength encoding hpositive
          horizon guess fuel node) =
      NeighborhoodEvaluator.profileEvaluate
        (PrimeGrouped.Logarithmic.units
          (payloadWidth tm blockLength) (graphFanIn workTapeCount))
        guess (NeighborhoodExecutableEvaluation.failureValue
          tm blockLength)
        (NeighborhoodExecutableEvaluation.sourceValue
          tm x blockLength encoding hpositive)
        (NeighborhoodExecutableEvaluation.combineValue
          tm x blockLength encoding hpositive)
        fuel node :=
  Internal.residueProfileEvaluate_cast_internal
    tm x blockLength encoding hpositive horizon guess fuel node

/-- A streamed natural-residue query has at most `fuel + 1` simultaneously
live recursive calls. -/
theorem profileEvaluate_peakFrames_le
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    (profileEvaluate tm x blockLength encoding hpositive
      horizon guess fuel node).peakFrames ≤ fuel + 1 :=
  Internal.residueProfileEvaluate_peakFrames_le_internal
    tm x blockLength encoding hpositive horizon guess fuel node

/-- Casting one natural-residue graph-node query gives the typed query. -/
theorem profileNode_cast
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (node : Node workTapeCount) :
    Workspace.Profile.map ofResidues
        (profileNode tm x blockLength encoding hpositive
          horizon guess node) =
      NeighborhoodExecutableEvaluation.profileNode
        tm x blockLength encoding hpositive horizon guess node :=
  Internal.residueProfileNode_cast_internal
    tm x blockLength encoding hpositive horizon guess node

/-- Casting both streamed decision queries gives both typed queries and
preserves their shared peak. -/
theorem profileDecision_cast
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    Workspace.Profile.map
        (fun result => (ofResidues result.1, ofResidues result.2))
        (profileDecision tm x blockLength encoding hpositive
          horizon guess) =
      NeighborhoodExecutableEvaluation.profileDecision
        tm x blockLength encoding hpositive horizon guess :=
  Internal.residueProfileDecision_cast_internal
    tm x blockLength encoding hpositive horizon guess

/-- Sequential streamed state and verdict traversal reuses at most
`horizon + 1` recursive frames. -/
theorem profileDecision_peakFrames_le
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    (profileDecision tm x blockLength encoding hpositive
      horizon guess).peakFrames ≤ horizon + 1 :=
  Internal.residueProfileDecision_peakFrames_le_internal
    tm x blockLength encoding hpositive horizon guess

/-- Direct natural decoding agrees with decoding after casting into the
searched field. -/
theorem decodeValue_cast
    (tm : TM workTapeCount) (blockLength : ℕ)
    (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (value : ResidueValue tm blockLength) :
    decodeValue tm blockLength encoding hpositive value =
      NeighborhoodExecutableEvaluation.decodeValue
        tm blockLength encoding hpositive (ofResidues value) :=
  Internal.residueDecodeValue_cast_internal
    tm blockLength encoding hpositive value

/-- The streamed and typed evaluators decode to the same decision
snapshot. -/
theorem decodedDecisionSnapshot_eq_typed
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    decodedDecisionSnapshot
        tm x blockLength encoding hpositive horizon guess =
      NeighborhoodExecutableEvaluation.decodedDecisionSnapshot
        tm x blockLength encoding hpositive horizon guess :=
  Internal.residueDecodedDecisionSnapshot_eq_typed_internal
    tm x blockLength encoding hpositive horizon guess

/-- A valid guessed prefix makes the streamed decision snapshot semantically
exact. -/
theorem decodedDecisionSnapshot_eq
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (hvalid : guess.IsValidFor
      (Guess.actualCenterTrajectory tm x blockLength)) :
    decodedDecisionSnapshot
        tm x blockLength encoding hpositive horizon guess =
      DecisionRecovery.decisionSnapshot
        tm x blockLength hpositive horizon :=
  Internal.residueDecodedDecisionSnapshot_eq_internal
    tm x blockLength encoding hpositive horizon guess hvalid

/-- The streamed decoded-node callback is extensionally equal to its typed
correctness reference. -/
theorem nodeCallback_eq_typed
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    nodeCallback tm x blockLength encoding hpositive horizon =
      NeighborhoodExecutableEvaluation.nodeCallback
        tm x blockLength encoding hpositive horizon :=
  Internal.residueNodeCallback_eq_internal
    tm x blockLength encoding hpositive horizon

/-- The streamed decoded-node callback is exact on every required correct
center prefix. -/
theorem nodeCallback_isPrefixExact
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    Guess.EvaluatedProvider.IsPrefixExact
      tm x blockLength hpositive
      (nodeCallback tm x blockLength encoding hpositive horizon) :=
  Internal.residueNodeCallback_isPrefixExact_internal
    tm x blockLength encoding hpositive horizon

/-- The fully natural-residue evaluator and snapshot pair satisfy the
complete certified-trial exactness contract. -/
theorem certifiedEngine_isExact
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    (certifiedEngine
      tm x blockLength encoding hpositive horizon).IsExact x hpositive :=
  Internal.residueCertifiedEngine_isExact_internal
    tm x blockLength encoding hpositive horizon

end Residue

/-- The natural-residue local callback, cast back into the searched field, is
extensionally equal to the primary typed callback. -/
theorem combineValueViaResidues_eq
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        EvaluationValue tm blockLength) :
    combineValueViaResidues tm x blockLength encoding hpositive
        tape slot timeBlock children =
      combineValue tm x blockLength encoding hpositive
        tape slot timeBlock children :=
  Internal.combineValueViaResidues_eq_internal
    tm x blockLength encoding hpositive
      tape slot timeBlock children

end NeighborhoodExecutableEvaluation

end TimeSpaceSimulation

end Complexity
