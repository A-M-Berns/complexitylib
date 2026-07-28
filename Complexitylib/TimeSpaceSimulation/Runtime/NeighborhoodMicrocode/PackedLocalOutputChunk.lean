/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalOutputChunk.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalOutputChunk.Internal

/-!
# Executable packed local output chunks

This module exposes the verified endpoint of runtime grouped-output
extraction from a represented packed local configuration. The command
decodes the active computation node, derives its guessed tape center,
dispatches the requested lower, center, or upper block, and folds the
selected runtime-width Boolean chunk in big-endian order.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalOutputChunk

open RAM Structured
open NeighborhoodGraph

/-- Grouped packed output extraction writes only the packed-step scratch
footprint. -/
theorem build_writesWithin
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (PackedLocalStep.footprint regs)
      (build tm controller regs) :=
  Internal.build_writesWithin_internal tm controller regs

/-- The executable builder returns the exact pure grouped output chunk while
preserving the packed word, live combine context, catalytic bank, and stable
ABI. -/
theorem build_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (horizon blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : NeighborhoodGraph.Guess.CenterGuess
      workTapeCount horizon)
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (hguess :
      guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (cursor width : ℕ)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode workTapeCount horizon
              from .graph
                (.computation targetTape targetSlot interval.val)),
        digit < 2 ^ width)
    (hnode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode (2 ^ width)
          (show
            NeighborhoodEvaluator.QueryNode workTapeCount horizon
            from .graph
              (.computation targetTape targetSlot interval.val)))
    (hradix : store (Layout.chunkRadix regs) = 2 ^ width)
    (hguessStore : store controller.guess = guessCode.val)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents tm order blockLength
        (NeighborhoodGraph.Guess.Consistency.guessedCenters
          guess interval.val)
        cfg suffix word)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hcursor : store (Layout.active regs) = cursor)
    (hheadLower :
      PackedLocalConfiguration.windowStart blockLength
          (NeighborhoodGraph.Guess.Consistency.guessedCenters
            guess interval.val targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hheadUpper :
      (tapeAt cfg targetTape).head <
        PackedLocalConfiguration.windowStart blockLength
            (NeighborhoodGraph.Guess.Consistency.guessedCenters
              guess interval.val targetTape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (build tm controller regs) store final ∧
      Post tm blockLength
        (NeighborhoodGraph.Guess.Consistency.guessedCenters
          guess interval.val targetTape)
        targetTape targetSlot word cursor width regs store final :=
  Internal.build_runs_internal tm order horizon blockLength hpositive
    guess guessCode hguess interval targetTape targetSlot cfg suffix
    word controller regs store cursor width hfits hnode hradix
    hguessStore hblock hword hrep hone hcursor hheadLower hheadUpper

end PackedLocalOutputChunk
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
