/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalHeadScan.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalHeadScan.Internal

/-!
# Fixed-register packed local-head scan

This surface exposes a compile-time named-tape scan over the
`3 * blockLength` cell digits in a packed local configuration. The scan
returns the exact local head offset and alphabet code while preserving the
packed word, its continuation suffix, live combine fields, and the stable
computation ABI.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalHeadScan

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The packed local-head scan writes only its fixed direct-register
footprint. -/
theorem scan_writesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (scan tm tape regs) :=
  Internal.scan_writesWithin_internal tm tape regs

/-- Compiling the packed local-head scan preserves its fixed source write
footprint. -/
theorem scan_compiledWritesWithin
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (scan tm tape regs).compile (footprint regs) :=
  Internal.scan_compiledWritesWithin_internal tm tape regs

/-- Every mutable scan register lies in the range term kernel's advertised
combine-scratch footprint. -/
theorem footprint_subset_combineScratch
    (regs : NeighborhoodTrial.Registers controller) :
    footprint regs ⊆ CombineValue.combineScratchFootprint regs :=
  Internal.footprint_subset_combineScratch_internal regs

/-- Any scan execution with the canonical range-one entry invariant
preserves all live combine fields and the stable computation ABI. -/
theorem scan_preservesCombine
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hone :
      initial (CombineValue.rangeRegisters regs).one = 1)
    (hrun : Runs (scan tm tape regs) initial final) :
    PreservesCombine regs initial final :=
  Internal.scan_preservesCombine_internal tm tape regs hone hrun

/-- On any mutable packed word satisfying the semantic representation
predicate, the scan returns the exact local head offset and alphabet code.
This form remains applicable after represented in-prefix digit updates. -/
theorem scan_runs_represents
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword : store (bankRegisters regs).word = word)
    (hrep :
      PackedLocalRepresentation.Represents
        tm order blockLength centers cfg suffix word)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (scan tm tape regs) store final ∧
      Post tm blockLength centers cfg tape
        word regs store final ∧
      PreservesCombine regs store final :=
  Internal.scan_runs_represents_internal
    tm order blockLength hpositive centers cfg tape suffix word
      regs store hblock hword hrep hrangeOne hlower hupper

/-- On an encoded local configuration whose named head lies in its
three-block window, the scan terminates at the exact local head offset and
returns the exact alphabet code under that head. The packed word and every
address outside the fixed footprint are preserved. -/
theorem scan_runs
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hblock : store (Layout.blockLength regs) = blockLength)
    (hword :
      store (bankRegisters regs).word =
        PackedLocalConfiguration.encodeAbove
          tm order blockLength centers cfg suffix)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    ∃ final,
      Runs (scan tm tape regs) store final ∧
      Post tm blockLength centers cfg tape
        (PackedLocalConfiguration.encodeAbove
          tm order blockLength centers cfg suffix)
        regs store final ∧
      PreservesCombine regs store final :=
  Internal.scan_runs_internal tm order blockLength hpositive centers
    cfg tape suffix regs store hblock hword hrangeOne hlower hupper

end PackedLocalHeadScan
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
