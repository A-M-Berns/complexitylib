/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInitDefs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInitProof

/-!
# Dense-overlay public-input initialization

The optimized initializer retains the public bits on the immutable input tape,
materializes only the positive-tagged length register, installs the reusable
program ABI, and rewinds the input for dense fallback reads.
-/

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Complete dense public-input initialization reaches the exact one-entry
snapshot image with the immutable input bank parked at cell one. -/
theorem denseProgramInitTM_hoareTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (denseProgramInitTM tapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork tapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = TM.resetBinaryBlank)
      (denseProgramInitTime tapes input) :=
  denseProgramInitTM_hoareTime_internal tapes input

/-- Dense initialization also satisfies an honest all-prefix auxiliary-space
bound linear in the binary width of the public-input length. -/
theorem denseProgramInitTM_hoareTimeSpace {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (denseProgramInitTM tapes).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork tapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = TM.resetBinaryBlank)
      (denseProgramInitTime tapes input) input.length
      (denseProgramInitSpace input.length) :=
  denseProgramInitTM_hoareTimeSpace_internal tapes input

/-- A serialized all-prefix trace budget covers dense initialization space up
to one fixed factor. -/
theorem denseProgramInitSpace_le_of_traceFits
    {program : Program} {input : List Bool} {fuel bound : ℕ}
    (hfits : DenseOverlay.TraceFits program input fuel bound) :
    denseProgramInitSpace input.length ≤ 32 * bound :=
  denseProgramInitSpace_le_of_traceFits_internal hfits

end Machine
end RegisterStore
end RAM
end Complexity
