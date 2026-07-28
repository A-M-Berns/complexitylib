/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding.Defs
import Complexitylib.TimeSpaceSimulation.CertifiedTrial.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluator.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.GroupedExtension.Evaluation.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeField.Runtime.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding.Defs

/-!
# Executable grouped evaluation of guessed neighborhood graphs

This definitions layer instantiates the direct neighborhood evaluator with
the executable grouped Lagrange callback. Source compact values are encoded
through an explicit finite-coordinate equivalence. Internal Boolean nodes
decode their children, run the local machine transition, re-encode the
result, and are extended by `GroupedExtension.Evaluation.evaluateNode`.

The searched prime field depends on the machine state count and the explicit
block length. That dependency remains visible in `EvaluationField` and
`EvaluationValue`; it is not hidden behind a chosen type. Runtime definitions
construct neither semantic trees nor multivariate polynomials.

`FiniteEncoding` is the only hardwired finite-machine choice. Its two
equivalences replace the certificate-side uses of `Fintype.equivFin`, making
source encoding and total decoding executable.

## Main definitions

- `encodeBits` / `decodeBits` -- explicit executable compact-value coding
- `booleanCombine` -- the local Boolean neighborhood transition
- `combineValue` -- executable grouped Lagrange node callback
- `profileState` / `profileVerdict` -- direct guessed-graph queries
- `profileDecision` -- sequential state/verdict query with a shared peak
- `decodedDecisionSnapshot` -- executable field, chunk, and compact decoding
- `certifiedEngine` -- the decoded direct evaluator as one trial engine
- `Residue.profileAccumulate` -- fully natural direct traversal with streamed
  nonzero scalars
- `Residue.certifiedEngine` -- fully natural decoded trial engine
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodExecutableEvaluation

open NeighborhoodGraph
open TreeEval CookMertz

/-- Boolean payload width of one compact neighborhood value. -/
abbrev payloadWidth (tm : TM workTapeCount) (blockLength : ℕ) : ℕ :=
  ComputationGraph.CompactEncoding.width blockLength tm.Q

/-- Direct neighborhood-graph fan-in. -/
abbrev graphFanIn (workTapeCount : ℕ) : ℕ :=
  NeighborhoodEvaluator.fanIn workTapeCount

/-- Executably searched prime modulus for this machine and block length. -/
abbrev modulus (tm : TM workTapeCount) (blockLength : ℕ) : ℕ :=
  PrimeField.Search.searchModulus
    (PrimeGrouped.Logarithmic.degreeEndpoint
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))

/-- The typed searched prime field. Its type depends on the runtime block
length and the fixed machine state count. -/
abbrev EvaluationField (tm : TM workTapeCount) (blockLength : ℕ) :=
  PrimeGrouped.Logarithmic.Field
    (payloadWidth tm blockLength) (graphFanIn workTapeCount)

/-- One grouped compact value over the searched prime field. -/
abbrev EvaluationValue (tm : TM workTapeCount) (blockLength : ℕ) :=
  Fin (PrimeGrouped.Logarithmic.chunkCount
      (payloadWidth tm blockLength) (graphFanIn workTapeCount)) →
    EvaluationField tm blockLength

/-- Natural canonical-residue view of one grouped value. -/
abbrev ResidueValue (tm : TM workTapeCount) (blockLength : ℕ) :=
  Fin (PrimeGrouped.Logarithmic.chunkCount
      (payloadWidth tm blockLength) (graphFanIn workTapeCount)) →
    ℕ

/-- Explicit finite encodings hardwired for one fixed source machine.

`coordinate` orders every compact Boolean coordinate. `state` separately
orders the state family for executable total decoding. Proof fields of the
equivalences erase during execution. -/
structure FiniteEncoding (tm : TM workTapeCount)
    (blockLength : ℕ) where
  /-- Fixed ordering of all compact Boolean coordinates. -/
  coordinate :
    ComputationGraph.CompactEncoding.Coordinate blockLength tm.Q ≃
      Fin (payloadWidth tm blockLength)
  /-- Fixed ordering used to scan the finite state family. -/
  state : tm.Q ≃ Fin (Fintype.card tm.Q)

/-- Scan a fixed `Fin` range and return its first true index. -/
def firstTrueFin {count : ℕ} (default : Fin count)
    (bits : Fin count → Bool) : Fin count :=
  ((List.finRange count).find? bits).getD default

/-- Fixed-order total decoder for one tape symbol. -/
def decodeGamma (bits : Γ → Bool) : Γ :=
  if bits .zero then
    .zero
  else if bits .one then
    .one
  else if bits .blank then
    .blank
  else if bits .start then
    .start
  else
    .blank

/-- Encode a compact value using the supplied finite coordinate order. -/
def encodeBits (encoding : FiniteEncoding tm blockLength)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q) :
    Fin (payloadWidth tm blockLength) → Bool :=
  fun index =>
    ComputationGraph.CompactEncoding.coordinateBits value
      (encoding.coordinate.symm index)

/-- Read an explicitly encoded bit vector at a semantic compact coordinate. -/
def bitsAt (encoding : FiniteEncoding tm blockLength)
    (bits : Fin (payloadWidth tm blockLength) → Bool) :
    ComputationGraph.CompactEncoding.Coordinate blockLength tm.Q → Bool :=
  fun coordinate => bits (encoding.coordinate coordinate)

/-- Total executable decoder for the explicit compact encoding. -/
def decodeBits (encoding : FiniteEncoding tm blockLength)
    (defaultState : tm.Q) (hpositive : 0 < blockLength)
    (bits : Fin (payloadWidth tm blockLength) → Bool) :
    ComputationGraph.CompactContent.Content blockLength tm.Q where
  state :=
    encoding.state.symm
      (firstTrueFin (encoding.state defaultState) fun index =>
        bitsAt encoding bits (.inl (encoding.state.symm index)))
  headRemainder :=
    firstTrueFin ⟨0, hpositive⟩ fun remainder =>
      bitsAt encoding bits (.inr (.inl remainder))
  cells := fun offset =>
    decodeGamma fun symbol =>
      bitsAt encoding bits (.inr (.inr (offset, symbol)))

/-- Explicit Boolean encoding of one source neighborhood block. -/
def sourceBits (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    Fin (payloadWidth tm blockLength) → Bool :=
  encodeBits encoding
    (NeighborhoodContent.nodeContent tm x blockLength hpositive
      (.source tape block))

/-- Boolean local transition used at every internal neighborhood node.

Every child is totally decoded, the compact local transition is run, and the
result is re-encoded with the same explicit coordinate order. -/
def booleanCombine (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        Fin (payloadWidth tm blockLength) → Bool) :
    Fin (payloadWidth tm blockLength) → Bool :=
  encodeBits encoding
    (NeighborhoodContent.localNodeFunction
      tm x blockLength hpositive timeBlock tape slot fun index =>
        decodeBits encoding tm.qstart hpositive
          (children
            (predecessorIndexEquiv workTapeCount index)))

/-- Grouped searched-field encoding of one source neighborhood block. -/
def sourceValue (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    EvaluationValue tm blockLength :=
  PrimeGrouped.Logarithmic.encodeValue
    (payloadWidth tm blockLength) (graphFanIn workTapeCount)
    (sourceBits tm x blockLength encoding hpositive tape block)

/-- Executable grouped Lagrange callback for one local Boolean transition. -/
def combineValue (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        EvaluationValue tm blockLength) :
    EvaluationValue tm blockLength :=
  GroupedExtension.Evaluation.evaluateNode
    (PrimeGrouped.Logarithmic.codebook
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    (PrimeGrouped.Logarithmic.layout
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    (booleanCombine tm x blockLength encoding hpositive
      tape slot timeBlock)
    children

/-- Explicit failure leaf used only for malformed guesses or exhausted fuel. -/
def failureValue (tm : TM workTapeCount) (blockLength : ℕ) :
    EvaluationValue tm blockLength :=
  0

/-- Direct profiled query for one guessed graph node. -/
def profileNode (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (node : Node workTapeCount) :
    Workspace.Profile (EvaluationValue tm blockLength) :=
  NeighborhoodEvaluator.profileEvaluate
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    guess (failureValue tm blockLength)
    (sourceValue tm x blockLength encoding hpositive)
    (combineValue tm x blockLength encoding hpositive)
    horizon (.graph node)

/-- Direct chronological state-root query for one explicit guessed graph. -/
def profileState (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    Workspace.Profile (EvaluationValue tm blockLength) :=
  NeighborhoodEvaluator.profileEvaluate
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    guess (failureValue tm blockLength)
    (sourceValue tm x blockLength encoding hpositive)
    (combineValue tm x blockLength encoding hpositive)
    horizon (NeighborhoodEvaluator.stateRoot guess)

/-- Direct latest-verdict-block query for one explicit guessed graph. -/
def profileVerdict (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    Workspace.Profile (EvaluationValue tm blockLength) :=
  NeighborhoodEvaluator.profileEvaluate
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    guess (failureValue tm blockLength)
    (sourceValue tm x blockLength encoding hpositive)
    (combineValue tm x blockLength encoding hpositive)
    horizon (NeighborhoodEvaluator.verdictRoot guess blockLength)

/-- Sequential direct state/verdict queries with one reusable catalytic bank. -/
def profileDecision (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    Workspace.Profile
      (EvaluationValue tm blockLength × EvaluationValue tm blockLength) :=
  NeighborhoodEvaluator.profileDecision
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    guess blockLength (failureValue tm blockLength)
    (sourceValue tm x blockLength encoding hpositive)
    (combineValue tm x blockLength encoding hpositive)

/-- Decode one grouped searched-field value to a compact machine value. -/
def decodeValue (tm : TM workTapeCount) (blockLength : ℕ)
    (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (value : EvaluationValue tm blockLength) :
    ComputationGraph.CompactContent.Content blockLength tm.Q :=
  decodeBits encoding tm.qstart hpositive
    (PrimeGrouped.Logarithmic.Decoding.decodeValue
      (payloadWidth tm blockLength) (graphFanIn workTapeCount) value)

/-- Decode the two direct query results to the requested horizon snapshot. -/
def decodedDecisionSnapshot
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    DecisionRecovery.Snapshot tm.Q :=
  let result :=
    (profileDecision tm x blockLength encoding hpositive
      horizon guess).result
  { state :=
      (decodeValue tm blockLength encoding hpositive result.1).state
    verdict :=
      (decodeValue tm blockLength encoding hpositive result.2).cells
        (DecisionRecovery.verdictOffset blockLength hpositive) }

/-- Option-valued decoded direct-node callback used by local consistency.

The source and combine callbacks are independent of the guess; the direct
traversal itself uses the guess only to regenerate recursive predecessors. -/
def nodeCallback
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    Guess.EvaluatedProvider.NodeContentCallback
      workTapeCount tm blockLength horizon :=
  Guess.EvaluatedProvider.directCallback
    (PrimeGrouped.Logarithmic.units
      (payloadWidth tm blockLength) (graphFanIn workTapeCount))
    (failureValue tm blockLength)
    (fun _ => sourceValue tm x blockLength encoding hpositive)
    (fun _ => combineValue tm x blockLength encoding hpositive)
    (fun value =>
      some (decodeValue tm blockLength encoding hpositive value))

/-- Concrete direct evaluator and decoded decision snapshot for one
block/horizon trial.

This engine is the typed correctness reference. The fully natural streamed
implementation appears as `Residue.certifiedEngine` below. -/
def certifiedEngine
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    CertifiedTrial.Engine tm blockLength horizon where
  node :=
    nodeCallback tm x blockLength encoding hpositive horizon
  snapshot := fun guess =>
    some (decodedDecisionSnapshot tm x blockLength encoding hpositive
      horizon guess)

/-- Read the canonical natural residues of one typed searched-field value. -/
def toResidues (value : EvaluationValue tm blockLength) :
    ResidueValue tm blockLength :=
  fun chunk => (value chunk).val

/-- Cast natural representatives into the typed searched prime field. -/
def ofResidues (value : ResidueValue tm blockLength) :
    EvaluationValue tm blockLength :=
  fun chunk => (value chunk : EvaluationField tm blockLength)

namespace Residue

/-- Searched prime modulus for generic payload width and fan-in parameters. -/
def fieldModulus (payloadWidth fanIn : ℕ) : ℕ :=
  PrimeField.Search.searchModulus
    (PrimeGrouped.Logarithmic.degreeEndpoint payloadWidth fanIn)

/-- Tail-recursive modular product over a natural range. -/
def foldProduct (prime : ℕ) (term : ℕ → ℕ) :
    ℕ → ℕ → ℕ
  | 0, accumulator =>
      accumulator
  | count + 1, accumulator =>
      foldProduct prime term count
        (PrimeField.Runtime.mul prime (term count) accumulator)

/-- Product of `term 0, ..., term (count - 1)` as natural residues. -/
def productRange (prime : ℕ) (term : ℕ → ℕ)
    (count : ℕ) : ℕ :=
  foldProduct prime term count
    (PrimeField.Runtime.normalize prime 1)

/-- Tail-recursive modular sum over a natural range. -/
def foldSum (prime : ℕ) (term : ℕ → ℕ) :
    ℕ → ℕ → ℕ
  | 0, accumulator =>
      accumulator
  | count + 1, accumulator =>
      foldSum prime term count
        (PrimeField.Runtime.add prime (term count) accumulator)

/-- Sum of `term 0, ..., term (count - 1)` as natural residues. -/
def sumRange (prime : ℕ) (term : ℕ → ℕ)
    (count : ℕ) : ℕ :=
  foldSum prime term count
    (PrimeField.Runtime.normalize prime 0)

/-- Fold a finite coordinate order with runtime modular multiplication. -/
def productList (prime : ℕ) : List ℕ → ℕ
  | [] =>
      PrimeField.Runtime.normalize prime 1
  | value :: values =>
      PrimeField.Runtime.mul prime value
        (productList prime values)

/-- Runtime natural-residue value of one normalized Lagrange factor. -/
def lagrangeFactor (payloadWidth fanIn : ℕ)
    (selected other :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point : ℕ) : ℕ :=
  let prime := fieldModulus payloadWidth fanIn
  if selected = other then
    PrimeField.Runtime.normalize prime 1
  else
    PrimeField.Runtime.mul prime
      (PrimeField.Runtime.inverse prime
        (PrimeField.Runtime.sub prime
          (PrimeGrouped.Logarithmic.chunkCodeNat selected)
          (PrimeGrouped.Logarithmic.chunkCodeNat other)))
      (PrimeField.Runtime.sub prime point
        (PrimeGrouped.Logarithmic.chunkCodeNat other))

/-- Runtime natural-residue evaluation of one chunk Lagrange basis. -/
def chunkBasisValue (payloadWidth fanIn : ℕ)
    (selected :
      GroupedExtension.Chunk
        (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point : ℕ) : ℕ :=
  productRange (fieldModulus payloadWidth fanIn)
    (fun code =>
      lagrangeFactor payloadWidth fanIn selected
        (GroupedExtension.Evaluation.chunkOfCode
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
          code)
        point)
    (2 ^ PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)

/-- Runtime natural-residue tensor-product basis value. -/
def basisValue (payloadWidth fanIn : ℕ)
    (assignment :
      Fin fanIn ×
          Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
        GroupedExtension.Chunk
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (point :
      Fin fanIn ×
          Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
        ℕ) : ℕ :=
  productList (fieldModulus payloadWidth fanIn)
    ((BooleanExtension.Evaluation.coordinates finProdFinEquiv).map
      fun coordinate =>
        chunkBasisValue payloadWidth fanIn
          (assignment coordinate) (point coordinate))

/-- Natural chunk code returned by one Boolean-node assignment. -/
def packedNodeValue (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (assignment :
      Fin fanIn ×
          Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
        GroupedExtension.Chunk
          (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))
    (outputChunk :
      Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    ℕ :=
  PrimeGrouped.Logarithmic.chunkCodeNat
    (GroupedExtension.Layout.pack
      (chunkBits :=
        PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
      (combine
        (GroupedExtension.unpackChildren
          (PrimeGrouped.Logarithmic.layout payloadWidth fanIn)
          assignment))
      outputChunk)

/-- Fully natural-residue grouped evaluation of one Boolean node.

The outer assignment sum and every Lagrange product use only
`PrimeField.Runtime` operations. -/
def evaluateNode (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ) :
    Fin (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) → ℕ :=
  fun outputChunk =>
    sumRange (fieldModulus payloadWidth fanIn)
      (fun code =>
        let assignment :=
          GroupedExtension.Evaluation.chunkAssignmentOfCode
            finProdFinEquiv
            (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
            code
        PrimeField.Runtime.mul
          (fieldModulus payloadWidth fanIn)
          (packedNodeValue payloadWidth fanIn
            combine assignment outputChunk)
          (basisValue payloadWidth fanIn assignment
            (fun input => args input.1 input.2)))
      (2 ^
        ((fanIn *
            PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) *
          PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn))

end Residue

/-- Natural-residue form of the local grouped callback. -/
def combineResidues (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        ResidueValue tm blockLength) :
    ResidueValue tm blockLength :=
  Residue.evaluateNode
    (payloadWidth tm blockLength) (graphFanIn workTapeCount)
    (booleanCombine tm x blockLength encoding hpositive
      tape slot timeBlock)
    children

namespace Residue

/-- Natural-residue vector registers for the direct neighborhood traversal. -/
abbrev Registers (tm : TM workTapeCount) (blockLength : ℕ) :=
  Fin (graphFanIn workTapeCount + 1) → ResidueValue tm blockLength

/-- Canonical zero natural-residue vector. -/
def zeroValue (tm : TM workTapeCount) (blockLength : ℕ) :
    ResidueValue tm blockLength :=
  fun _ => PrimeField.Runtime.normalize (modulus tm blockLength) 0

/-- Natural-residue source value for one compact source block. -/
def sourceValue (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    ResidueValue tm blockLength :=
  toResidues
    (NeighborhoodExecutableEvaluation.sourceValue
      tm x blockLength encoding hpositive tape block)

/-- Canonical failure value for malformed or exhausted queries. -/
def failureValue (tm : TM workTapeCount) (blockLength : ℕ) :
    ResidueValue tm blockLength :=
  zeroValue tm blockLength

/-- Coordinatewise modular addition of natural-residue vectors. -/
def addValue (tm : TM workTapeCount) (blockLength : ℕ)
    (first second : ResidueValue tm blockLength) :
    ResidueValue tm blockLength :=
  fun chunk =>
    PrimeField.Runtime.add (modulus tm blockLength)
      (first chunk) (second chunk)

/-- Coordinatewise modular scaling of a natural-residue vector. -/
def scaleValue (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (value : ResidueValue tm blockLength) :
    ResidueValue tm blockLength :=
  fun chunk =>
    PrimeField.Runtime.mul (modulus tm blockLength)
      scalar (value chunk)

/-- Add a natural-residue vector to one catalytic register. -/
def addAt (tm : TM workTapeCount) (blockLength : ℕ)
    (regs : Registers tm blockLength)
    (index : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength) :
    Registers tm blockLength :=
  Function.update regs index
    (addValue tm blockLength (regs index) value)

/-- Scale one natural-residue catalytic register. -/
def scaleAt (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs : Registers tm blockLength)
    (index : Fin (graphFanIn workTapeCount + 1)) :
    Registers tm blockLength :=
  Function.update regs index
    (scaleValue tm blockLength scalar (regs index))

/-- Direct profiled natural-residue Cook--Mertz traversal.

Recursive children are regenerated from the finite guess. Nonzero field
scalars are streamed by `PrimeField.Runtime.foldNonzero`, so this definition
does not allocate a modulus-sized list. -/
def profileAccumulate
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    ℕ → NeighborhoodEvaluator.QueryNode workTapeCount horizon → ℕ →
      Fin (graphFanIn workTapeCount + 1) →
      Registers tm blockLength →
      Workspace.Profile (Registers tm blockLength)
  | _, .failure, scalar, out, regs =>
      Workspace.Profile.start
        (addAt tm blockLength regs out
          (scaleValue tm blockLength scalar
            (failureValue tm blockLength)))
  | _, .graph (.source tape block), scalar, out, regs =>
      Workspace.Profile.start
        (addAt tm blockLength regs out
          (scaleValue tm blockLength scalar
            (sourceValue tm x blockLength encoding hpositive tape block)))
  | 0, .graph (.computation _ _ _), scalar, out, regs =>
      Workspace.Profile.start
        (addAt tm blockLength regs out
          (scaleValue tm blockLength scalar
            (failureValue tm blockLength)))
  | fuel + 1, node@(.graph (.computation tape slot interval)),
      scalar, out, regs =>
      if _hinterval : interval < horizon then
        PrimeField.Runtime.foldNonzero (modulus tm blockLength)
          (fun current residue =>
            let current :=
              (List.finRange (graphFanIn workTapeCount)).foldl
                (fun current childIndex =>
                  let target := out.succAbove childIndex
                  let child :=
                    profileAccumulate tm x blockLength encoding hpositive
                      horizon guess fuel
                      (NeighborhoodEvaluator.childAt guess node childIndex)
                      (PrimeField.Runtime.normalize
                        (modulus tm blockLength) 1)
                      target
                      (scaleAt tm blockLength residue
                        current.result target)
                  Workspace.Profile.recordChild current child)
                current
            let args := fun childIndex =>
              current.result (out.succAbove childIndex)
            let current :=
              Workspace.Profile.map
                (fun currentRegs =>
                  addAt tm blockLength currentRegs out
                    (scaleValue tm blockLength
                      (PrimeField.Runtime.sub
                        (modulus tm blockLength) 0 scalar)
                      (combineResidues tm x blockLength encoding hpositive
                        tape slot interval args)))
                current
            (List.finRange (graphFanIn workTapeCount)).foldl
              (fun current childIndex =>
                let target := out.succAbove childIndex
                let child :=
                  profileAccumulate tm x blockLength encoding hpositive
                    horizon guess fuel
                    (NeighborhoodEvaluator.childAt guess node childIndex)
                    (PrimeField.Runtime.sub
                      (modulus tm blockLength) 0 1)
                    target current.result
                Workspace.Profile.map
                  (fun currentRegs =>
                    scaleAt tm blockLength
                      (PrimeField.Runtime.inverse
                        (modulus tm blockLength) residue)
                      currentRegs target)
                  (Workspace.Profile.recordChild current child))
              current)
          (Workspace.Profile.start regs)
      else
        Workspace.Profile.start
          (addAt tm blockLength regs out
            (scaleValue tm blockLength scalar
              (failureValue tm blockLength)))

/-- Evaluate one guessed query from zero natural-residue registers. -/
def profileEvaluate
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) :
    Workspace.Profile (ResidueValue tm blockLength) :=
  Workspace.Profile.map
    (fun regs => regs (Fin.last (graphFanIn workTapeCount)))
    (profileAccumulate tm x blockLength encoding hpositive horizon guess
      fuel node
      (PrimeField.Runtime.normalize (modulus tm blockLength) 1)
      (Fin.last (graphFanIn workTapeCount))
      (fun _ => zeroValue tm blockLength))

/-- Direct natural-residue query for one guessed graph node. -/
def profileNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (node : Node workTapeCount) :
    Workspace.Profile (ResidueValue tm blockLength) :=
  profileEvaluate tm x blockLength encoding hpositive horizon guess
    horizon (.graph node)

/-- Sequential natural-residue state and verdict queries. -/
def profileDecision
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    Workspace.Profile
      (ResidueValue tm blockLength × ResidueValue tm blockLength) :=
  let state :=
    profileEvaluate tm x blockLength encoding hpositive horizon guess
      horizon (NeighborhoodEvaluator.stateRoot guess)
  let verdict :=
    profileEvaluate tm x blockLength encoding hpositive horizon guess
      horizon (NeighborhoodEvaluator.verdictRoot guess blockLength)
  ⟨(state.result, verdict.result),
    max state.peakFrames verdict.peakFrames⟩

/-- Decode a natural-residue grouped value directly, without constructing a
runtime field-element list. -/
def decodeValue
    (tm : TM workTapeCount) (blockLength : ℕ)
    (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (value : ResidueValue tm blockLength) :
    NeighborhoodContent.Content blockLength tm.Q :=
  NeighborhoodExecutableEvaluation.decodeBits
    encoding tm.qstart hpositive
    ((PrimeGrouped.Logarithmic.layout
      (payloadWidth tm blockLength)
      (graphFanIn workTapeCount)).unpack fun chunk =>
        BooleanExtension.Evaluation.assignmentOfCode
          (Equiv.refl
            (Fin (PrimeGrouped.Logarithmic.chunkBits
              (payloadWidth tm blockLength)
              (graphFanIn workTapeCount))))
          (PrimeField.Runtime.normalize
            (modulus tm blockLength) (value chunk)))

/-- Decode the two streamed natural-residue queries to one decision
snapshot. -/
def decodedDecisionSnapshot
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ)
    (guess : Guess.CenterGuess workTapeCount horizon) :
    DecisionRecovery.Snapshot tm.Q :=
  let result :=
    (profileDecision tm x blockLength encoding hpositive
      horizon guess).result
  { state :=
      (decodeValue tm blockLength encoding hpositive result.1).state
    verdict :=
      (decodeValue tm blockLength encoding hpositive result.2).cells
        (DecisionRecovery.verdictOffset blockLength hpositive) }

/-- Decoded natural-residue node callback for local consistency checking. -/
def nodeCallback
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    Guess.EvaluatedProvider.NodeContentCallback
      workTapeCount tm blockLength horizon :=
  fun guess node =>
    some (decodeValue tm blockLength encoding hpositive
      (profileNode tm x blockLength encoding hpositive
        horizon guess node).result)

/-- Fully natural-residue evaluator and snapshot callbacks for one certified
trial. -/
def certifiedEngine
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength) (horizon : ℕ) :
    CertifiedTrial.Engine tm blockLength horizon where
  node :=
    nodeCallback tm x blockLength encoding hpositive horizon
  snapshot := fun guess =>
    some (decodedDecisionSnapshot
      tm x blockLength encoding hpositive horizon guess)

end Residue

/-- Typed adapter around the natural-residue local callback.

Only the callback uses natural arithmetic. The surrounding direct traversal
still uses its typed field/module API. -/
def combineValueViaResidues
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (encoding : FiniteEncoding tm blockLength)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children :
      Fin (graphFanIn workTapeCount) →
        EvaluationValue tm blockLength) :
    EvaluationValue tm blockLength :=
  ofResidues
    (combineResidues tm x blockLength encoding hpositive
      tape slot timeBlock fun child =>
        toResidues (children child))

end NeighborhoodExecutableEvaluation

end TimeSpaceSimulation

end Complexity
