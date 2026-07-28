/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.InputLookup.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.InputLookup.Internal

/-!
# Collision-safe public-input lookup

This module exposes a fixed-register accessor for the public RAM input. Low
addresses are decoded from the controller's packed prefix cache; addresses
beyond every mutable destination use the ordinary immutable-input fallback.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace InputLookup

open RAM Structured
open NeighborhoodProgram

/-- Every positive public-input register contains a Boolean value. -/
theorem initRegs_lt_two_of_pos
    (input : List Bool) {address : ℕ}
    (hpositive : 0 < address) :
    RAM.initRegs input address < 2 :=
  Internal.initRegs_lt_two_of_pos_internal input hpositive

/-- The pure packed-prefix specification contains every shadowable public
input cell at its advertised digit. -/
theorem packedPrefix_represents
    (input : List Bool) (limit : ℕ) :
    CachedPrefixRepresents input limit
      (packedPrefix input limit) :=
  Internal.packedPrefix_represents_internal input limit

/-- Packing `limit` Boolean public-input cells occupies at most `limit`
binary digits. -/
theorem packedPrefix_lt_pow
    (input : List Bool) (limit : ℕ) :
    packedPrefix input limit < 2 ^ limit :=
  Internal.packedPrefix_lt_pow_internal input limit

/-- The controller's operational cache agrees with the pure packed-prefix
specification at every positive footprint limit. -/
theorem prefixCacheValue_eq_packedPrefix
    (regs : SearchProgram.Registers) (input : List Bool)
    (limit : ℕ) (hpositive : 0 < limit) :
    SearchProgram.prefixCacheValue regs input limit =
      packedPrefix input limit :=
  Internal.prefixCacheValue_eq_packedPrefix_internal
    regs input limit hpositive

/-- The cache produced by the uniform controller prelude contains every
shadowable public-input cell at the digit used by `command`. -/
theorem prefixCacheValue_represents
    (regs : SearchProgram.Registers) (input : List Bool)
    (limit : ℕ) (hpositive : 0 < limit) :
    CachedPrefixRepresents input limit
      (SearchProgram.prefixCacheValue regs input limit) :=
  Internal.prefixCacheValue_represents_internal
    regs input limit hpositive

/-- Prefix preprocessing changes only the dedicated cache register. -/
theorem prefixCacheOps_eq_outside
    (regs : SearchProgram.Registers) (input : List Bool)
    (limit : ℕ) {address : ℕ}
    (haddress : address ≠ regs.prefixCache) :
    Basic.execList
        (SearchProgram.cacheInputPrefixOps regs limit)
        (RAM.initRegs input) address =
      RAM.initRegs input address :=
  Internal.prefixCacheOps_eq_outside_internal
    regs input limit haddress

/-- Extending a positive cached prefix appends exactly one doubling/bit-add
instruction pair. -/
theorem cacheInputPrefixOps_succ
    (regs : SearchProgram.Registers) (limit : ℕ)
    (hpositive : 0 < limit) :
    SearchProgram.cacheInputPrefixOps regs (limit + 1) =
      SearchProgram.cacheInputPrefixOps regs limit ++
        [.add regs.prefixCache regs.prefixCache regs.prefixCache,
          .add regs.prefixCache regs.prefixCache (limit + 1)] :=
  Internal.cacheInputPrefixOps_succ_internal
    regs limit hpositive

/-- Every direct write of the collision-safe lookup lies in its twelve fixed
registers. In particular, the routine performs no indirect store. -/
theorem sourceWritesWithin
    (regs : BankRegisters) (limit : ℕ) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (command regs limit) :=
  Internal.sourceWritesWithin_internal regs limit

/-- Structured compilation preserves the lookup's fixed write footprint. -/
theorem compiledWritesWithin
    (regs : BankRegisters) (limit : ℕ) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (command regs limit).compile regs.footprint :=
  RAM.Structured.Footprint.programWritesWithin_compile
    (sourceWritesWithin regs limit)

/-- The accessor returns the requested positive public input cell, restores
the packed cache, and preserves its dynamic address and constant one. -/
theorem runs
    (regs : BankRegisters) (input : List Bool)
    (limit address word : ℕ) (store : Store)
    (hpositive : 0 < address)
    (hregisters : ∀ slot, regs.index slot ≤ limit)
    (hprefix : CachedPrefixRepresents input limit word)
    (hsuffix : ∀ queried, limit < queried →
      store queried = RAM.initRegs input queried)
    (hword : store regs.word = word)
    (haddress : store (InputLookup.address regs) = address)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (command regs limit) store final ∧
      Post regs input address store final :=
  Internal.runs_internal regs input limit address word store
    hpositive hregisters hprefix hsuffix hword haddress hone

end InputLookup

end Runtime

end TimeSpaceSimulation

end Complexity
