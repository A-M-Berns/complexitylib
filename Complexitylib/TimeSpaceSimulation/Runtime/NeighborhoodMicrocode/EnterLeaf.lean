/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterLeaf.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.EnterLeaf.Internal

/-!
# Entry transitions for failure and source leaves

The concrete commands in this module stream every grouped source/failure
coordinate into the active catalytic register, restore the current frame,
and pop its continuation.  The endpoint theorems are stated directly as the
corresponding `NeighborhoodScheduler.State.next` transition.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterLeaf

open RAM Structured
open TreeEval CookMertz
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- No processed coordinates leaves the logical catalytic bank unchanged. -/
theorem addScaledPrefix_zero
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (original : Residue.Registers tm blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength) :
    addScaledPrefix tm blockLength scalar original out value 0 =
      original :=
  Internal.addScaledPrefix_zero_internal
    tm blockLength scalar original out value

/-- Updating the current coordinate advances the exact logical prefix by one. -/
theorem addScaledPrefix_succ
    (tm : TM workTapeCount) (blockLength scalar processed : ℕ)
    (original : Residue.Registers tm blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength)
    (hprocessed :
      processed <
        PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm blockLength)
          (graphFanIn workTapeCount)) :
    NeighborhoodProgram.updateResidueCoordinate
        tm blockLength
        (addScaledPrefix tm blockLength scalar original out value
          processed)
        out ⟨processed, hprocessed⟩
        (NeighborhoodProgram.ResidueBankOp.add.apply
          (modulus tm blockLength)
          (original out ⟨processed, hprocessed⟩)
          ((value ⟨processed, hprocessed⟩ * scalar) %
            modulus tm blockLength)) =
      addScaledPrefix tm blockLength scalar original out value
        (processed + 1) :=
  Internal.addScaledPrefix_succ_internal tm blockLength scalar
    processed original out value hprocessed

/-- Processing the full grouped-coordinate range is exactly the scheduler's
coordinatewise scaled addition. -/
theorem addScaledPrefix_full
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (scalar : ℕ)
    (original : Residue.Registers tm instanceData.blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm instanceData.blockLength) :
    addScaledPrefix tm instanceData.blockLength scalar original out value
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)) =
      NeighborhoodScheduler.addScaledAt
        instanceData original out scalar value :=
  Internal.addScaledPrefix_full_internal
    tm instanceData scalar original out value

/-- Failure entry writes only inside the shared packed-evaluator layout. -/
theorem failure_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint (failure regs) :=
  Internal.failure_writesWithin_internal regs

/-- Source entry writes only inside the shared packed-evaluator layout. -/
theorem source_writesWithin
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (source tm order regs) :=
  Internal.source_writesWithin_internal tm order regs

/-- A bounded represented source frame discharges the canonical candidate,
input-length, and source-block premises of the fixed-cap source-value trace.
This is the quantitative bridge used inside source entry loops after the node
fields have been decoded. -/
theorem sourceChunk_invariantRuns_of_frameBound
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (hnode : frame.node = .graph (.source tape block))
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)))
    (allowed : Finset ℕ) (initial : Store)
    (htape :
      initial (ControlDecode.nodeTape regs) = tape.val)
    (hblock :
      initial (ControlDecode.nodePayload0 regs) = block)
    (hblockLength :
      initial (Layout.blockLength regs) = instanceData.blockLength)
    (hradix :
      initial (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
    (hcursor :
      initial (Layout.codecScratch regs) = chunk.val)
    (hinputLength :
      initial controller.inputLength = instanceData.x.length)
    (hvalues :
      NeighborhoodProgram.ValuesWithin allowed
        (SourceValue.sourceTransientValueBound
          tm instanceData.candidateTime)
        initial)
    (hwriteSubset :
      SourceValue.writeFootprint regs ⊆ allowed)
    (haddressCapacity :
      2 ^ SearchProgram.footprintLimit controller regs.footprint ≤
        SourceValue.sourceTransientValueBound
          tm instanceData.candidateTime)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x initial) :
    ∃ final steps,
      InvariantRuns
        (NeighborhoodProgram.ValuesWithin allowed
          (SourceValue.sourceTransientValueBound
            tm instanceData.candidateTime))
        (SourceValue.sourceChunk tm order regs) initial final steps ∧
      SourceValue.SourceChunkPost regs instanceData.x
        (Residue.sourceValue tm instanceData.x
          instanceData.blockLength
          (FiniteEncoding.ofStateOrder order instanceData.blockLength)
          instanceData.positive tape block chunk)
        initial final :=
  Internal.sourceChunk_invariantRuns_of_frameBound_internal
    tm order regs instanceData frame tape block hnode hbound chunk
    allowed initial htape hblock hblockLength hradix hcursor
    hinputLength hvalues hwriteSubset haddressCapacity hframe

/-- The concrete failure-value provider can close any entering frame.  This
is the reusable branch for literal failures, exhausted computation fuel, and
out-of-horizon computation queries. -/
theorem failureValue_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (store : Store)
    (hphase : frame.phase = .enter)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (failure regs) store final ∧
      Representation.QueryState regs instanceData
        { stack := rest
          registers :=
            NeighborhoodScheduler.addScaledAt
              instanceData logicalBank frame.out frame.scalar
                (Residue.failureValue tm instanceData.blockLength) }
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 :=
  Internal.failureValue_runs_internal regs instanceData frame rest
    logicalBank store hphase hquery hframe hinputLength hone

/-- A represented failure leaf executes exactly one semantic scheduler step,
including scaled bank addition and parent-pop or terminal behavior. -/
theorem failure_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (store : Store)
    (hnode : frame.node = .failure)
    (hphase : frame.phase = .enter)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (failure regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 :=
  Internal.failure_runs_internal regs instanceData frame rest
    logicalBank store hnode hphase hquery hframe hinputLength hone

/-- A represented source leaf executes exactly one semantic scheduler step.
The encoding premise is the honest boundary between an arbitrary runtime
instance and the concrete finite-state ordering used by source microcode. -/
theorem source_runs
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank : Residue.Registers tm instanceData.blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ)
    (store : Store)
    (hnode : frame.node = .graph (.source tape block))
    (hphase : frame.phase = .enter)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (source tm order regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 :=
  Internal.source_runs_internal order regs instanceData frame rest
    logicalBank tape block store hnode hphase hencoding hquery hframe
    hinputLength hone

end EnterLeaf
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
