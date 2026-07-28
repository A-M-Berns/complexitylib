/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderResultDecoding.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorSemantics.Defs

/-!
# Uniform packed collection of consistency-provider vectors

Each provider query leaves its answer in the distinguished catalytic-bank
row.  This module streams that row into a second packed word held in the
outer controller's `hasNext` cell.  The source bank is read without mutation;
the destination is updated at the role-major `(child, chunk)` coordinate.

The only statically unrolled dimension is `graphFanIn workTapeCount`, which
depends solely on the fixed source machine.  The grouped-coordinate loop is
driven by the runtime `chunkCount` parameter, so the command does not depend
on the candidate, block length, horizon, interval, guess, or query result.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderVectorCollection

open RAM Structured
open NeighborhoodExecutableEvaluation

/-- Physical packed-bank reader used for the distinguished query-result row. -/
def resultBankMap : Fin 12 → Fin 34 :=
  ![33, 0, 14, 1, 4, 5, 17, 9, 10, 11, 12, 18]

theorem resultBankMap_injective :
    Function.Injective resultBankMap := by
  decide

/-- Collision-free reader view of the evaluator's catalytic bank. -/
def resultBankRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters where
  index := fun slot => regs.index (resultBankMap slot)
  injective := regs.injective.comp resultBankMap_injective

/-- Workspace tail of the packed destination-bank interface.

The destination word itself is the outer `hasNext` register. -/
def collectionBankTailMap : Fin 11 → Fin 34 :=
  ![0, 14, 1, 4, 5, 17, 9, 10, 11, 18, 12]

theorem collectionBankTailMap_injective :
    Function.Injective collectionBankTailMap := by
  decide

/-- Physical address of one destination-bank interface slot. -/
def collectionBankIndex
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Fin 12 → ℕ :=
  Fin.cases controller.hasNext
    (fun slot => regs.index (collectionBankTailMap slot))

theorem collectionBankIndex_injective
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Function.Injective (collectionBankIndex controller regs) := by
  intro first second heq
  rcases Fin.eq_zero_or_eq_succ first with rfl | ⟨firstTail, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ second with rfl | ⟨secondTail, rfl⟩
    · rfl
    · exfalso
      simp only [collectionBankIndex, Fin.cases_zero,
        Fin.cases_succ] at heq
      exact regs.index_ne_controller
        (collectionBankTailMap secondTail) (5 : Fin 17) heq.symm
  · rcases Fin.eq_zero_or_eq_succ second with rfl | ⟨secondTail, rfl⟩
    · exfalso
      simp only [collectionBankIndex, Fin.cases_zero,
        Fin.cases_succ] at heq
      exact regs.index_ne_controller
        (collectionBankTailMap firstTail) (5 : Fin 17) heq
    · apply Fin.succ_inj.mpr
      apply collectionBankTailMap_injective
      apply regs.injective
      simpa only [collectionBankIndex, Fin.cases_succ] using heq

/-- Packed-bank writer whose word is the collected-provider output. -/
def collectionBankRegisters
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters where
  index := collectionBankIndex controller regs
  injective := collectionBankIndex_injective controller regs

/-- Runtime grouped-coordinate countdown. -/
abbrev chunkRemaining
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 31

/-- Dynamic source or destination packed coordinate. -/
abbrev coordinate
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 30

/-- Exact fixed write overapproximation for one result-row collection. -/
def currentResultFootprint
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (resultBankRegisters regs).footprint ∪
    (collectionBankRegisters controller regs).footprint ∪
      {coordinate regs, chunkRemaining regs}

/-- Row-major coordinate of one collected provider residue. -/
def providerCoordinate
    (chunkCount child chunk : ℕ) : ℕ :=
  child * chunkCount + chunk

/-- Total natural-index view of one logical provider-result residue row.

Only indices below the runtime grouped-coordinate count are installed by the
collection loop; the zero default keeps the packed-word specification total. -/
def providerResidue
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (chunk : ℕ) : ℕ :=
  if hchunk :
      chunk <
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount) then
    ProviderResultDecoding.resultResidues
      tm instanceData interval child ⟨chunk, hchunk⟩
  else
    0

/-- Pure packed-word effect of installing a descending prefix of one
provider row. -/
def installRowFrom
    (base chunkCount child : ℕ)
    (value : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, word => word
  | remaining + 1, word =>
      installRowFrom base chunkCount child value remaining
        (NeighborhoodProgram.replaceAt base word
          (providerCoordinate chunkCount child remaining)
          (value remaining))

/-- Pure packed-word effect of installing one complete provider row. -/
def installRow
    (base chunkCount child : ℕ)
    (value : ℕ → ℕ) (word : ℕ) : ℕ :=
  installRowFrom base chunkCount child value chunkCount word

/-- Pure packed-word effect of installing a list of provider rows. -/
def installChildren
    (base chunkCount : ℕ)
    (value : Fin childCount → ℕ → ℕ) :
    List (Fin childCount) → ℕ → ℕ
  | [], word => word
  | child :: rest, word =>
      installChildren base chunkCount value rest
        (installRow base chunkCount child.val (value child) word)

/-- Decrement the chunk cursor and prepare the distinguished source-bank
coordinate. -/
def prepareSourceOps
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    List Basic :=
  let source := resultBankRegisters regs
  [.imm source.one 1,
    .sub (chunkRemaining regs) (chunkRemaining regs) source.one,
    .imm (coordinate regs) (graphFanIn workTapeCount),
    .mul (coordinate regs) (coordinate regs) (Layout.chunkCount regs),
    .add (coordinate regs) (coordinate regs) (chunkRemaining regs),
    .imm source.indexCount 0,
    .add source.indexCount (coordinate regs) source.indexCount,
    .sub source.basePred source.base source.one]

/-- Prepare the destination coordinate while preserving the residue returned
by the source-bank reader. -/
def prepareTargetOps
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    List Basic :=
  [.imm (coordinate regs) 0,
    .add (coordinate regs) controller.verdict (coordinate regs),
    .mul (coordinate regs) (coordinate regs) (Layout.chunkCount regs),
    .add (coordinate regs) (coordinate regs) (chunkRemaining regs),
    .imm (regs.index 10) 0,
    .add (regs.index 10) (coordinate regs) (regs.index 10),
    .sub (regs.index 1) (regs.index 14) (regs.index 17)]

/-- One descending chunk iteration.

The command first reads coordinate `(Fin.last, chunk)` from the completed
query bank, then writes that residue to `(controller.verdict, chunk)` of the
collection word. -/
def collectChunkBody
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let source := resultBankRegisters regs
  let target := collectionBankRegisters controller regs
  Cmd.seqList
    [Cmd.basics (prepareSourceOps workTapeCount controller regs),
      NeighborhoodProgram.bankRead source,
      Cmd.basics (prepareTargetOps controller regs),
      NeighborhoodProgram.bankReplace target]

/-- Copy every grouped residue of the completed query result into the row
selected by the outer child cursor. -/
def collectCurrentResult
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (Cmd.seq
      (.basic (.imm (chunkRemaining regs) 0))
      (.basic
        (.add (chunkRemaining regs) (Layout.chunkCount regs)
          (chunkRemaining regs))))
    (.whileNonzero (chunkRemaining regs)
      (collectChunkBody workTapeCount controller regs))

/-- Evaluate and collect one statically selected role-major child. -/
def collectChild
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (child : Fin (graphFanIn workTapeCount)) : Cmd :=
  Cmd.seqList
    [.basic (.imm controller.verdict child.val),
      ProviderQueryEvaluation.evaluate
        tm order controller regs combine,
      collectCurrentResult workTapeCount controller regs]

/-- Statically fixed list of all role-major provider coordinates. -/
def children (workTapeCount : ℕ) :
    List (Fin (graphFanIn workTapeCount)) :=
  List.finRange (graphFanIn workTapeCount)

/-- Canonical packed word obtained from every role-major provider row. -/
def collectedWord
    (base chunkCount : ℕ)
    (value : Fin (graphFanIn workTapeCount) → ℕ → ℕ) : ℕ :=
  installChildren base chunkCount value
    (children workTapeCount) 0

/-- Evaluate every provider coordinate and collect its distinguished result
row into one packed word.

The final child cursor is the one-past-the-end fan-in value. -/
def collect
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd) : Cmd :=
  Cmd.seqList
    [.basic (.imm controller.hasNext 0),
      Cmd.seqList
        ((children workTapeCount).map
          (collectChild tm order controller regs combine)),
      .basic
        (.imm controller.verdict (graphFanIn workTapeCount))]

/-- Runtime view of one collected logical residue row. -/
def storedCollectedResidues
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (child : Fin (graphFanIn workTapeCount)) :
    ResidueValue tm instanceData.blockLength :=
  fun chunk =>
    PackedDigits.digit
      (Representation.fieldBase instanceData)
      (store controller.hasNext)
      (providerCoordinate
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount))
        child.val chunk.val)

/-- Canonically decoded content of one collected provider row. -/
def decodedCollectedResult
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (child : Fin (graphFanIn workTapeCount)) :
    NeighborhoodContent.Content instanceData.blockLength tm.Q :=
  Residue.decodeValue
    tm instanceData.blockLength instanceData.encoding
      instanceData.positive
      (storedCollectedResidues
        tm controller instanceData store child)

/-- Fixed vector decoded from the packed collection word. -/
def decodedCollectedVector
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store) :
    ProviderVectorSemantics.ProviderVector tm instanceData :=
  fun child =>
    decodedCollectedResult tm controller instanceData store child

end ProviderVectorCollection
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
