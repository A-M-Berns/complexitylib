/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseSpaceDefs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseSpaceProof

/-!
# Fixed-register space bounds for the dense RAM simulator

The standard controller uses twenty work tapes. A uniform fixed-register bound
on every dense RAM prefix gives one fuel-independent space budget for the
initializer, reusable instruction loop, and final verdict phase.
-/

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- A fixed-register trace bound upgrades the exact standard loop simulation
to an all-prefix time-and-space contract. -/
theorem denseProgramLoopTM_hoareTimeSpace_traceBound
    (program : Program) (input : List Bool) (fuel entryBudget wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel entryBudget wordBits) :
    (denseProgramLoopTM standardControlInstructionTapes program).HoareTimeSpace
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = denseProgramSnapshotWork standardControlInstructionTapes
          (DenseOverlay.Snapshot.initial input) ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        let final :=
          (DenseOverlay.Snapshot.initial input).run program input fuel
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady standardControlInstructionTapes
          final.overlay final.pc work ∧
        out = instructionHaltOutput (final.curInstr program))
      (denseProgramLoopTime standardControlInstructionTapes program input
        (fuel + 1) (DenseOverlay.Snapshot.initial input))
      input.length
      (denseFixedIterationSpace program input.length entryBudget wordBits) :=
  denseProgramLoopTM_hoareTimeSpace_traceBound_internal
    program input fuel entryBudget wordBits hhalted hbound

/-- A bounded halted dense snapshot gives an all-prefix contract for the final
lookup-and-verdict phase. -/
theorem denseProgramOutputTM_hoareTimeSpace_snapshotBound
    (input : List Bool) (snapshot : DenseOverlay.Snapshot)
    (entryBudget wordBits : ℕ)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hbound : DenseOverlay.FixedRegisters.SnapshotBound snapshot
      entryBudget wordBits) :
    (denseProgramOutputTM standardControlInstructionTapes).HoareTimeSpace
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady standardControlInstructionTapes
          snapshot.overlay snapshot.pc work ∧
        out = instructionHaltOutput .halt)
      (fun inp _work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        out = registerVerdictOutput
          (DenseOverlay.read input snapshot.overlay 0))
      (denseProgramOutputTime standardControlInstructionTapes input
        snapshot.overlay)
      input.length
      (denseFixedOutputSpace input.length entryBudget wordBits) :=
  denseProgramOutputTM_hoareTimeSpace_snapshotBound_internal
    input snapshot entryBudget wordBits hvalid hbound

/-- The complete standard dense simulator has an exact endpoint/time contract
and a fuel-independent all-prefix auxiliary-space bound. -/
theorem denseProgramDecisionTM_hoareTimeSpace_traceBound
    (program : Program) (input : List Bool) (fuel entryBudget wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel entryBudget wordBits) :
    (denseProgramDecisionTM standardControlInstructionTapes program
      ).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out =>
        let final :=
          (DenseOverlay.Snapshot.initial input).run program input fuel
        out = registerVerdictOutput
          (DenseOverlay.read input final.overlay 0))
      (denseProgramDecisionTime standardControlInstructionTapes program
        input fuel)
      input.length
      (denseProgramDecisionSpace program input.length entryBudget wordBits) :=
  denseProgramDecisionTM_hoareTimeSpace_traceBound_internal
    program input fuel entryBudget wordBits hhalted hbound

/-- Every reachable configuration of the complete fixed simulator keeps the
two-way verdict head inside the same decision-space budget. -/
theorem denseProgramDecisionTM_output_head_le_traceBound
    (program : Program) (input : List Bool) (fuel entryBudget wordBits : ℕ)
    (hhalted :
      ((DenseOverlay.Snapshot.initial input).run program input fuel).Halted
        program)
    (hbound : DenseOverlay.FixedRegisters.TraceBound
      program input fuel entryBudget wordBits) :
    ∀ cfg,
      (denseProgramDecisionTM standardControlInstructionTapes program
        ).reaches
        ((denseProgramDecisionTM standardControlInstructionTapes program
          ).initCfg input) cfg →
      cfg.output.head ≤
        denseProgramDecisionSpace program input.length entryBudget wordBits :=
  denseProgramDecisionTM_output_head_le_traceBound_internal
    program input fuel entryBudget wordBits hhalted hbound

/-- A fixed twenty-work-tape TM decides every language decided by a fixed RAM
run whose dense prefixes satisfy one length-uniform register bound. -/
theorem denseProgramDecisionTM_decidesInSpace_traceBound
    (program : Program) (L : Language)
    (fuel : List Bool → ℕ) (entryBudget wordBits : ℕ → ℕ)
    (hhalted : ∀ input, RAM.Halted program
      (RAM.run program (fuel input) (RAM.initCfg input)))
    (hbound : ∀ input,
      DenseOverlay.FixedRegisters.TraceBound program input (fuel input)
        (entryBudget input.length) (wordBits input.length))
    (hyes : ∀ input, input ∈ L →
      (RAM.run program (fuel input) (RAM.initCfg input)).verdict = 1)
    (hno : ∀ input, input ∉ L →
      (RAM.run program (fuel input) (RAM.initCfg input)).verdict = 0) :
    (denseProgramDecisionTM standardControlInstructionTapes program
      ).DecidesInSpace L
      (fun inputLength =>
        denseProgramDecisionSpace program inputLength
          (entryBudget inputLength) (wordBits inputLength)) :=
  denseProgramDecisionTM_decidesInSpace_traceBound_internal
    program L fuel entryBudget wordBits hhalted hbound hyes hno

end Machine
end RegisterStore
end RAM
end Complexity
