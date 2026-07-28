/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Defs

/-!
# Fixed-register dense-overlay bounds

This definitions layer records the representation invariant used by
fixed-register RAM programs. Such a program may read the immutable public
input indirectly, but it materializes only a fixed number of mutable
registers. A snapshot bound records the two header widths, the entry-count
budget, and a uniform address/tag width.

The invariant concerns the actual tagged dense overlay. In particular, an
explicit write of zero still occupies one entry and is charged honestly.
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace DenseOverlay

namespace FixedRegisters

/-- Tape-cell budget obtained from a fixed entry count and uniform word width. -/
def codeBudget (entryBudget wordBits : ℕ) : ℕ :=
  (entryBudget + 1) * (4 * wordBits + 2)

/-- A dense snapshot uses at most `entryBudget` uniformly `wordBits`-wide
mutable entries, including its two serialized headers. -/
structure SnapshotBound (snapshot : Snapshot)
    (entryBudget wordBits : ℕ) : Prop where
  /-- The program counter fits the common word width. -/
  pcWidth : bitlen snapshot.pc ≤ wordBits
  /-- At most the advertised number of mutable registers is materialized. -/
  entryCount : snapshot.overlay.length ≤ entryBudget
  /-- The entry-count header also fits the common word width. -/
  entryBudgetWidth : bitlen entryBudget ≤ wordBits
  /-- Every materialized address and positive value tag fits the width. -/
  entries : ∀ entry ∈ snapshot.overlay,
    bitlen entry.1 ≤ wordBits ∧ bitlen entry.2 ≤ wordBits

/-- Every prefix of a dense run satisfies one fixed-register snapshot bound. -/
def TraceBound (program : Program) (input : List Bool)
    (fuel entryBudget wordBits : ℕ) : Prop :=
  ∀ k, k ≤ fuel →
    SnapshotBound
      ((Snapshot.initial input).run program input k)
      entryBudget wordBits

end FixedRegisters

end DenseOverlay

end RegisterStore

end RAM

end Complexity
