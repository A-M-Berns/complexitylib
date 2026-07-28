/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Internal

/-!
# Fixed write footprints for structured RAM programs

The structured compiler introduces only control-flow instructions, so a
source command whose direct writes lie in one finite set compiles to a
dense-overlay program with exactly the same write footprint.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace Footprint

open RegisterStore DenseOverlay FixedRegisters
open FixedRegisters.Footprint

/-- A structured execution leaves every address outside its fixed write
footprint unchanged. -/
theorem exec_eq_outside
    {allowed : Finset ℕ} {cmd : Cmd} {initial final : Store}
    {steps cost space : ℕ}
    (hwrites : CmdWritesWithin allowed cmd)
    (hexec : Exec cmd initial final steps cost space)
    {address : ℕ} (haddress : address ∉ allowed) :
    final address = initial address :=
  Internal.exec_eq_outside_internal hwrites hexec haddress

/-- The resource-erased structured semantics preserves every address outside
the command's fixed write footprint. -/
theorem runs_eq_outside
    {allowed : Finset ℕ} {cmd : Cmd} {initial final : Store}
    (hwrites : CmdWritesWithin allowed cmd)
    (hrun : Runs cmd initial final)
    {address : ℕ} (haddress : address ∉ allowed) :
    final address = initial address :=
  Internal.runs_eq_outside_internal hwrites hrun haddress

/-- Compilation preserves the source command's fixed write footprint. -/
theorem programWritesWithin_compile
    {allowed : Finset ℕ} {cmd : Cmd}
    (hwrites : CmdWritesWithin allowed cmd) :
    ProgramWritesWithin cmd.compile allowed :=
  Internal.programWritesWithin_compile_internal hwrites

/-- A structured command with a fixed direct-write footprint and uniformly
bounded mutable values has the concrete dense-overlay trace bound required by
the RAM-to-Turing-machine simulator. The compiler's control-flow theorem
supplies the program-counter bound automatically. -/
theorem traceBound_compile
    {allowed : Finset ℕ} {cmd : Cmd} {input : List Bool}
    {fuel valueBits : ℕ}
    (hwrites : CmdWritesWithin allowed cmd)
    (hzero : 0 ∈ allowed)
    (hcode : bitlen cmd.codeSize ≤ valueBits + 1)
    (hcount : bitlen allowed.card ≤ valueBits + 1)
    (haddresses : ∀ address ∈ allowed,
      bitlen address ≤ valueBits + 1)
    (hvalues : ∀ k, k ≤ fuel → ∀ address ∈ allowed,
      bitlen ((RAM.run cmd.compile k (RAM.initCfg input)).regs address) ≤
        valueBits) :
    FixedRegisters.TraceBound cmd.compile input fuel allowed.card
      (valueBits + 1) :=
  Internal.traceBound_compile_internal hwrites hzero hcode hcount
    haddresses hvalues

end Footprint

end Structured

end RAM

end Complexity
