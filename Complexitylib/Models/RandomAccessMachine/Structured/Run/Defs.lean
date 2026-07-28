/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Defs

/-!
# Qualitative execution of structured RAM commands

`Exec` deliberately records exact transition count, logarithmic cost, and
peak source-store space. Program-correctness proofs that do not yet need
those numbers can use `Runs`, which existentially hides all three while
retaining the same independently defined structured semantics.
-/

namespace Complexity

namespace RAM

namespace Structured

/-- A structured command has some finite execution from `initial` to `final`. -/
def Runs (cmd : Cmd) (initial final : Store) : Prop :=
  ∃ steps cost space, Exec cmd initial final steps cost space

end Structured

end RAM

end Complexity
