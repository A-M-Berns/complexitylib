/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram.Defs

/-!
# Collision-safe public-input lookup

The outer search controller packs every public RAM input cell that may later
be shadowed by a fixed mutable register. This module defines a first-order
lookup routine that reads those low cells from the packed cache and uses an
ordinary indirect load only for the untouched suffix.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace InputLookup

open RAM Structured
open NeighborhoodProgram

/-- A radix-two word contains the public RAM cells `R₁, …, R_limit` in
high-to-low order. Thus physical address `address` is digit
`limit - address`. -/
def CachedPrefixRepresents
    (input : List Bool) (limit word : ℕ) : Prop :=
  ∀ address, 0 < address → address ≤ limit →
    PackedDigits.digit 2 word (limit - address) =
      RAM.initRegs input address

/-- Pure packed-prefix specification, independent of the controller's
straight-line implementation. Addresses are appended in increasing order, so
the highest cached address becomes digit zero. -/
def packedPrefix (input : List Bool) (limit : ℕ) : ℕ :=
  (List.range limit).foldl
    (fun word offset =>
      PackedDigits.push 2 (RAM.initRegs input (offset + 1)) word)
    0

/-- The packed-bank register used as the dynamic input address. It is
preserved by `NeighborhoodProgram.bankRead`. -/
abbrev address (regs : BankRegisters) : ℕ :=
  regs.replacement

/-- Collision-safe lookup of one positive public RAM address.

The test `limit + 1 - address` is nonzero exactly on the cached prefix. In
that branch the routine streams to digit `limit - address`; otherwise the
address exceeds every mutable destination and an ordinary indirect load is
sound. -/
def command (regs : BankRegisters) (limit : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm regs.result (limit + 1)))
    (Cmd.seq
      (.basic (.sub regs.test regs.result (address regs)))
      (.ifZero regs.test
        (.basic (.load regs.result (address regs)))
        (Cmd.seq
          (.basic (.imm regs.indexCount limit))
          (Cmd.seq
            (.basic
              (.sub regs.indexCount regs.indexCount (address regs)))
            (Cmd.seq
              (.basic (.imm regs.base 2))
              (Cmd.seq
                (.basic (.imm regs.basePred 1))
                (bankRead regs)))))))

/-- Exact observable endpoint of a collision-safe lookup. -/
structure Post
    (regs : BankRegisters) (input : List Bool)
    (address : ℕ) (initial final : Store) : Prop where
  /-- The selected public cell is returned. -/
  result_eq :
    final regs.result = RAM.initRegs input address
  /-- The dynamic address is preserved. -/
  address_eq :
    final regs.replacement = address
  /-- The packed prefix cache is restored exactly. -/
  word_eq :
    final regs.word = initial regs.word
  /-- The caller's constant-one register is preserved. -/
  one_eq :
    final regs.one = initial regs.one

end InputLookup

end Runtime

end TimeSpaceSimulation

end Complexity
