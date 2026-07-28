/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentPayloadBit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentPayloadBit.Internal

/-!
# Uniform semantic payload-bit lookup

This module exposes a runtime lookup command for one semantic payload bit of
a compile-time child. The command recovers the chunk width from the runtime
power-of-two radix, computes the exact low-order assignment-code index, and
delegates the binary lookup to `AssignmentBit.read`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentPayloadBit

open RAM Structured
open TreeEval CookMertz
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Chunk-width recovery stays inside its advertised scratch footprint. -/
theorem recoverChunkBits_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (recoveryFootprint regs) (recoverChunkBits regs) :=
  Internal.recoverChunkBits_writesWithin_internal regs

/-- Recovering the exponent of the runtime power-of-two chunk radix returns
the exact chunk width, normalizes its division stack, and preserves every
address outside the advertised recovery footprint. -/
theorem recoverChunkBits_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (chunkBits : ℕ)
    (hradix :
      store (Layout.chunkRadix regs) = 2 ^ chunkBits) :
    ∃ final,
      Runs (recoverChunkBits regs) store final ∧
      final (recoveredChunkBits regs) = chunkBits ∧
      final (exponentStackRegisters regs).word = 1 ∧
      final (exponentStackRegisters regs).test = 0 ∧
      final (exponentStackRegisters regs).base = 2 ∧
      final (exponentStackRegisters regs).basePred = 1 ∧
      final (exponentStackRegisters regs).one = 1 ∧
      ∀ address, address ∉ recoveryFootprint regs →
        final address = store address :=
  Internal.recoverChunkBits_runs_internal regs store chunkBits hradix

/-- Low-order index preparation stays inside the complete lookup footprint.
-/
theorem prepareIndex_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      (writeFootprint regs)
      (prepareIndex workTapeCount regs child) :=
  Internal.prepareIndex_writesWithin_internal
    workTapeCount regs child

/-- The complete semantic lookup footprint is combine scratch. -/
theorem writeFootprint_subset_combineScratch
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆
      CombineValue.combineScratchFootprint regs :=
  Internal.writeFootprint_subset_combineScratch_internal regs

/-- The active assignment code lies outside the semantic lookup
footprint. -/
theorem remaining_not_mem_writeFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).remaining ∉
      writeFootprint regs :=
  Internal.remaining_not_mem_writeFootprint_internal regs

/-- The outer fold accumulator lies outside the semantic lookup
footprint. -/
theorem accumulator_not_mem_writeFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).accumulator ∉
      writeFootprint regs :=
  Internal.accumulator_not_mem_writeFootprint_internal regs

/-- The immutable assignment count lies outside the semantic lookup
footprint. -/
theorem count_not_mem_writeFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    (CombineValue.rangeRegisters regs).count ∉
      writeFootprint regs :=
  Internal.count_not_mem_writeFootprint_internal regs

/-- The packed catalytic bank lies outside the semantic lookup
footprint. -/
theorem catalyticBank_not_mem_writeFootprint
    (regs : NeighborhoodTrial.Registers controller) :
    regs.layout.bank ∉ writeFootprint regs :=
  Internal.catalyticBank_not_mem_writeFootprint_internal regs

/-- Semantic payload-bit lookup stays inside its exact advertised
footprint. -/
theorem read_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      (writeFootprint regs)
      (read workTapeCount regs child) :=
  Internal.read_writesWithin_internal workTapeCount regs child

/-- Semantic payload-bit lookup stays inside combine scratch. -/
theorem read_combineScratch_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      (CombineValue.combineScratchFootprint regs)
      (read workTapeCount regs child) :=
  Internal.read_combineScratch_writesWithin_internal
    workTapeCount regs child

/-- Semantic payload-bit lookup stays inside the shared evaluator layout. -/
theorem read_layout_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) :
    Footprint.CmdWritesWithin
      regs.layout.footprint
      (read workTapeCount regs child) :=
  Internal.read_layout_writesWithin_internal
    workTapeCount regs child

/-- The runtime arithmetic formula is exactly the semantic low-order
assignment-bit coordinate. -/
theorem assignmentIndex_eq_lowOrderBitIndex
    (workTapeCount payloadWidth : ℕ)
    (child : Fin (graphFanIn workTapeCount))
    (position : Fin payloadWidth) :
    assignmentIndex workTapeCount
        (PrimeGrouped.Logarithmic.chunkCount
          payloadWidth (graphFanIn workTapeCount))
        (PrimeGrouped.Logarithmic.chunkBits
          payloadWidth (graphFanIn workTapeCount))
        child position.val =
      AssignmentCodeSemantics.lowOrderBitIndex
        payloadWidth (graphFanIn workTapeCount)
        child position :=
  Internal.assignmentIndex_eq_lowOrderBitIndex_internal
    workTapeCount payloadWidth child position

/-- The uniform command returns the requested semantic child bit and
preserves the outer fold, evaluator frame, bank, and ABI. -/
theorem read_runs
    (workTapeCount payloadWidth : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount))
    (position : Fin payloadWidth)
    (store : Store) (code : ℕ)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        PrimeGrouped.Logarithmic.chunkCount
          payloadWidth (graphFanIn workTapeCount))
    (hradix :
      store (Layout.chunkRadix regs) =
        2 ^
          PrimeGrouped.Logarithmic.chunkBits
            payloadWidth (graphFanIn workTapeCount))
    (hcode :
      store (CombineValue.rangeRegisters regs).remaining = code)
    (hposition :
      store (payloadPosition regs) = position.val) :
    ∃ final,
      Runs (read workTapeCount regs child) store final ∧
      Post workTapeCount payloadWidth code regs child position
        store final :=
  Internal.read_runs_internal workTapeCount payloadWidth regs
    child position store code hchunkCount hradix hcode hposition

end AssignmentPayloadBit
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
