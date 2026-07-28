/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SourceValue.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SourceValue.Internal

/-!
# Concrete source-leaf values for neighborhood microcode
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace SourceValue

open RAM Structured
open TreeEval CookMertz
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- The canonical numeric cap for source-leaf transients fits exactly in the
shared fixed-register trial envelope. -/
theorem sourceTransientValueBound_bitlen_le_trialEnvelope
    (tm : TM workTapeCount) (candidate : ℕ) :
    bitlen (sourceTransientValueBound tm candidate) ≤
      NeighborhoodProgram.fixedRegisterCount *
        NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount candidate :=
  Internal.sourceTransientValueBound_bitlen_le_trialEnvelope_internal
    tm candidate

/-- The pure unbounded-coordinate specification agrees with the compact
initial-neighborhood encoding at every payload coordinate. -/
theorem sourceBits_eq_coordinateBit
    (tm : TM workTapeCount) (order : FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (index : Fin (payloadWidth tm blockLength)) :
    sourceBits tm input blockLength
        (FiniteEncoding.ofStateOrder order blockLength)
        hpositive tape block index =
      coordinateBit tm order input blockLength tape.val block index.val :=
  Internal.sourceBits_eq_coordinateBit_internal
    tm order input blockLength hpositive tape block index

/-- The big-endian natural produced by the concrete source loop is the
semantic grouped source residue. -/
theorem sourceChunkValue_eq
    (tm : TM workTapeCount) (order : FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount))) :
    sourceChunkValue tm order input blockLength tape.val block chunk.val
        (PrimeGrouped.Logarithmic.chunkBits
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)) =
      Residue.sourceValue tm input blockLength
        (FiniteEncoding.ofStateOrder order blockLength)
        hpositive tape block chunk :=
  Internal.sourceChunkValue_eq_internal
    tm order input blockLength hpositive tape block chunk

/-- Source evaluation writes only its explicit sixteen-cell workspace. -/
theorem sourceChunk_writesWithin
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (sourceChunk tm order regs) :=
  Internal.sourceChunk_writesWithin_internal tm order regs

/-- Failure-source evaluation writes only the shared residue operand. -/
theorem failureChunk_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin
      (writeFootprint regs) (failureChunk regs) :=
  Internal.failureChunk_writesWithin_internal regs

/-- Every source workspace cell belongs to the shared evaluator layout. -/
theorem writeFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint :=
  Internal.writeFootprint_subset_layout_internal regs

/-- Every source workspace cell belongs to the enclosing trial footprint. -/
theorem writeFootprint_subset_trial
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.footprint :=
  Internal.writeFootprint_subset_trial_internal regs

/-- The concrete first-order source evaluator terminates with the exact
grouped source residue and preserves the input frame, active fields, cursor,
and catalytic-bank parameters consumed by the following update. -/
theorem sourceChunk_runs
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final,
      Runs (sourceChunk tm order regs) initial final ∧
      SourceChunkPost regs input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          hpositive tape block chunk)
        initial final :=
  Internal.sourceChunk_runs_internal
    tm order regs input blockLength hpositive tape block chunk
    initial htape hblock hblockLength hradix hcursor hinputLength
    hframe

/-- Under the canonical candidate block length and scheduler block range,
every source-leaf program point stays below the explicit shared trial cap.
The extra address-capacity premise is the exact condition needed by an
arbitrary physical register allocation: the collision-safe input cache packs
all public addresses through the largest fixed destination. -/
theorem sourceChunk_invariantRuns
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (candidate blockLength : ℕ)
    (hcanonical :
      blockLength =
        NeighborhoodGraph.WorkspaceAccounting.blockLength candidate)
    (hinput : input.length ≤ candidate)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hblockBound :
      block ≤
        max
          (NeighborhoodGraph.WorkspaceAccounting.horizon candidate)
          1)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = input.length)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed
        (sourceTransientValueBound tm candidate) initial)
    (hwriteSubset : writeFootprint regs ⊆ allowed)
    (haddressCapacity :
      2 ^ SearchProgram.footprintLimit controller regs.footprint ≤
        sourceTransientValueBound tm candidate)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed
          (sourceTransientValueBound tm candidate))
        (sourceChunk tm order regs) initial final steps ∧
      SourceChunkPost regs input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          (hcanonical ▸
            NeighborhoodGraph.WorkspaceAccounting.blockLength_pos
              candidate)
          tape block chunk)
        initial final :=
  Internal.sourceChunk_fixedCap_invariantRuns_internal
    tm order regs input candidate blockLength hcanonical hinput tape
    block hblockBound chunk allowed initial htape hblock hblockLength
    hradix hcursor hinputLength hvalues hwriteSubset
    haddressCapacity hframe

/-- The canonical controller/workspace allocation discharges the address
capacity side condition automatically: its largest fixed destination is
physical register fifty, which is covered by every canonical trial cap. -/
theorem sourceChunk_invariantRuns_canonical
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (input : List Bool) (candidate blockLength : ℕ)
    (hcanonical :
      blockLength =
        NeighborhoodGraph.WorkspaceAccounting.blockLength candidate)
    (hinput : input.length ≤ candidate)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hblockBound :
      block ≤
        max
          (NeighborhoodGraph.WorkspaceAccounting.horizon candidate)
          1)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (initial : Store)
    (htape :
      initial
          (ControlDecode.nodeTape
            NeighborhoodTrial.Registers.canonical) =
        tape.val)
    (hblock :
      initial
          (ControlDecode.nodePayload0
            NeighborhoodTrial.Registers.canonical) =
        block)
    (hblockLength :
      initial
          (Layout.blockLength
            NeighborhoodTrial.Registers.canonical) =
        blockLength)
    (hradix :
      initial
          (Layout.chunkRadix
            NeighborhoodTrial.Registers.canonical) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial
          (Layout.codecScratch
            NeighborhoodTrial.Registers.canonical) =
        chunk.val)
    (hinputLength :
      initial SearchProgram.Registers.canonical.inputLength =
        input.length)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed
        (sourceTransientValueBound tm candidate) initial)
    (hwriteSubset :
      writeFootprint NeighborhoodTrial.Registers.canonical ⊆
        allowed)
    (hframe :
      SearchProgram.InputFrame
        SearchProgram.Registers.canonical
        NeighborhoodTrial.Registers.canonical.footprint
        input initial) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed
          (sourceTransientValueBound tm candidate))
        (sourceChunk tm order
          NeighborhoodTrial.Registers.canonical)
        initial final steps ∧
      SourceChunkPost NeighborhoodTrial.Registers.canonical input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          (hcanonical ▸
            NeighborhoodGraph.WorkspaceAccounting.blockLength_pos
              candidate)
          tape block chunk)
        initial final :=
  Internal.sourceChunk_fixedCap_invariantRuns_canonical_internal
    tm order input candidate blockLength hcanonical hinput tape block
    hblockBound chunk allowed initial htape hblock hblockLength
    hradix hcursor hinputLength hvalues hwriteSubset hframe

/-- Every terminating source-leaf evaluation admits one common numeric
bound, no smaller than a requested lower bound, at every source program
point.  This is a qualitative trace-level certificate; it does not by
itself upper-bound that witness by the explicit candidate envelope. -/
theorem sourceChunk_exists_invariantRuns
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (blockLength : ℕ)
    (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (lowerBound : ℕ)
    (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = input.length)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final bound steps,
      lowerBound ≤ bound ∧
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (sourceChunk tm order regs) initial final steps ∧
      SourceChunkPost regs input
        (Residue.sourceValue tm input blockLength
          (FiniteEncoding.ofStateOrder order blockLength)
          hpositive tape block chunk)
        initial final :=
  Internal.sourceChunk_invariantRuns_internal
    tm order regs input blockLength hpositive tape block chunk
    allowed lowerBound initial htape hblock hblockLength hradix
    hcursor hinputLength hframe

/-- The failure leaf terminates with the canonical zero residue while
preserving the same dispatcher-visible state as a successful source leaf. -/
theorem failureChunk_runs
    (tm : TM workTapeCount) (blockLength : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (initial : Store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final,
      Runs (failureChunk regs) initial final ∧
      SourceChunkPost regs input
        (Residue.failureValue tm blockLength chunk)
        initial final :=
  Internal.failureChunk_runs_internal
    tm blockLength chunk regs input initial hframe

/-- Failure-leaf execution likewise admits one common all-program-point
numeric bound extending any requested lower bound. -/
theorem failureChunk_invariantRuns
    (tm : TM workTapeCount) (blockLength : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ)
    (lowerBound : ℕ) (initial : Store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final bound steps,
      lowerBound ≤ bound ∧
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (failureChunk regs) initial final steps ∧
      SourceChunkPost regs input
        (Residue.failureValue tm blockLength chunk)
        initial final :=
  Internal.failureChunk_invariantRuns_internal
    tm blockLength chunk regs input allowed lowerBound initial
    hframe

/-- At any pre-established numeric envelope, the failure leaf preserves
that envelope at its source and endpoint. -/
theorem failureChunk_invariantRuns_at
    (tm : TM workTapeCount) (blockLength : ℕ)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)))
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (allowed : Finset ℕ)
    (bound : ℕ) (initial : Store)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed bound initial)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    ∃ final,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed bound)
        (failureChunk regs) initial final 1 ∧
      SourceChunkPost regs input
        (Residue.failureValue tm blockLength chunk)
        initial final :=
  Internal.failureChunk_invariantRuns_at_internal
    tm blockLength chunk regs input allowed bound initial
    hvalues hframe

end SourceValue
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
