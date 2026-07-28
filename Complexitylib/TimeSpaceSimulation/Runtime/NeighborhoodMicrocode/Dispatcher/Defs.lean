/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.Arithmetic
import Complexitylib.Models.RandomAccessMachine.Structured.Switch
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameTransfer
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps

/-!
# Concrete control fragments for neighborhood-scheduler dispatch

This definitions layer contains the uniform first-order fragments shared by
the five scheduler phases.  In particular, phase values are rebuilt from the
decoded numeric fields by RAM arithmetic, and cleanup scaling computes its
field inverse with the verified modular-power routine before streaming the
selected catalytic register.

No semantic node callback occurs in these commands.  Node decoding, child
construction, and value generation are separate concrete microcode layers.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Dispatcher

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The five branch bodies in scheduler-tag order. -/
def phaseBranches
    (enter prepare combine cleanupCall cleanupScale : Cmd) :
    Fin 5 → Cmd :=
  ![enter, prepare, combine, cleanupCall, cleanupScale]

/-- Uniform five-way dispatch on the decoded scheduler-phase tag.

The verified numeric switch decrements the tag cell to zero before entering
the selected branch.  It reads the controller's persistent constant-one cell,
which is disjoint from the evaluator workspace. -/
def dispatchPhase
    (regs : NeighborhoodTrial.Registers controller)
    (enter prepare combine cleanupCall cleanupScale : Cmd) : Cmd :=
  RAM.Structured.Switch.select 5
    (ControlDecode.tag regs) controller.one
    (phaseBranches enter prepare combine cleanupCall cleanupScale)

/-- Decode the active phase and immediately dispatch its runtime tag. -/
def decodeAndDispatch
    (regs : NeighborhoodTrial.Registers controller)
    (enter prepare combine cleanupCall cleanupScale : Cmd) : Cmd :=
  Cmd.seq (ControlDecode.decodePhase regs)
    (dispatchPhase regs enter prepare combine cleanupCall cleanupScale)

/-- The three node-entry branch bodies in decoder-tag order. -/
def nodeBranches
    (failure source computation : Cmd) :
    Fin 3 → Cmd :=
  ![failure, source, computation]

/-- Uniform three-way dispatch on the decoded query-node tag. -/
def dispatchNode
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd) : Cmd :=
  RAM.Structured.Switch.select 3
    (ControlDecode.tag regs) controller.one
    (nodeBranches failure source computation)

/-- Decode the active query node and immediately dispatch its runtime tag. -/
def decodeAndDispatchNode
    (regs : NeighborhoodTrial.Registers controller)
    (failure source computation : Cmd) : Cmd :=
  Cmd.seq (ControlDecode.decodeNode regs)
    (dispatchNode regs failure source computation)

/-- First decoded phase payload: the current residue. -/
abbrev decodedResidue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 9

/-- Second decoded phase payload: the remaining residue count. -/
abbrev decodedResiduesLeft
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 10

/-- Third decoded phase payload: the active child cursor. -/
abbrev decodedChild
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 11

/-- Fourth decoded phase payload: the next child cursor. -/
abbrev decodedNextChild
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 12

/-- Pure mixed-radix value represented by the seven phase digits.

`digitBase` is the one-chunk radix and `scalarBase = digitBase ^ 2` is the
two-digit scalar radix. -/
def phaseValue
    (digitBase scalarBase tag residue residuesLeft child nextChild : ℕ) :
    ℕ :=
  tag +
    digitBase *
      (residue +
        scalarBase *
          (residuesLeft +
            scalarBase * (child + digitBase * nextChild)))

/-- Straight-line instructions rebuilding one phase code from four source
registers and a fixed phase tag. -/
def encodePhaseOps
    (regs : NeighborhoodTrial.Registers controller)
    (tag residue residuesLeft child nextChild : ℕ) : List Basic :=
  [.imm (Layout.phaseCode regs) 0,
    .add (Layout.phaseCode regs) nextChild (Layout.phaseCode regs),
    .mul (Layout.phaseCode regs)
      (Layout.chunkRadix regs) (Layout.phaseCode regs),
    .add (Layout.phaseCode regs) child (Layout.phaseCode regs),
    .mul (Layout.phaseCode regs)
      (Layout.bankRadix regs) (Layout.phaseCode regs),
    .add (Layout.phaseCode regs)
      residuesLeft (Layout.phaseCode regs),
    .mul (Layout.phaseCode regs)
      (Layout.bankRadix regs) (Layout.phaseCode regs),
    .add (Layout.phaseCode regs) residue (Layout.phaseCode regs),
    .mul (Layout.phaseCode regs)
      (Layout.chunkRadix regs) (Layout.phaseCode regs),
    .imm (Layout.codecDigit regs) tag,
    .add (Layout.phaseCode regs)
      (Layout.codecDigit regs) (Layout.phaseCode regs),
    .imm (Layout.codecDigit regs) 0]

/-- Rebuild one encoded phase from numeric fields already held in registers. -/
def encodePhase
    (regs : NeighborhoodTrial.Registers controller)
    (tag residue residuesLeft child nextChild : ℕ) : Cmd :=
  Cmd.basics
    (encodePhaseOps regs tag residue residuesLeft child nextChild)

/-- Observable result of rebuilding a phase from the decoder ABI. -/
structure EncodePhasePost
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) (initial final : Store) : Prop where
  /-- The phase cell contains the exact mixed-radix value. -/
  phaseCode_eq :
    final (Layout.phaseCode regs) =
      phaseValue
        (initial (Layout.chunkRadix regs))
        (initial (Layout.bankRadix regs)) tag
        (initial (decodedResidue regs))
        (initial (decodedResiduesLeft regs))
        (initial (decodedChild regs))
        (initial (decodedNextChild regs))
  /-- Only the phase destination and two codec scratch cells may change. -/
  eq_of_ne :
    ∀ address,
      address ≠ Layout.phaseCode regs →
      address ≠
        (Layout.frameCodecRegisters regs).quotient →
      address ≠ Layout.codecDigit regs →
      final address = initial address

/-- Encode a cleanup-call phase from the fields produced by phase decoding.
The high next-child digit is canonically zero. -/
def encodeCleanupCallPhase
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic (.imm (Layout.codecDigit regs) 0))
    (encodePhase regs 3
      (decodedResidue regs)
      (decodedResiduesLeft regs)
      (decodedNextChild regs)
      (Layout.codecDigit regs))

/-- Observable result of committing a cleanup-call phase.  Every cell other
than the encoded phase and the codec scratch digit is preserved. -/
structure EncodeCleanupPost
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Exact mixed-radix successor phase. -/
  phaseCode_eq :
    final (Layout.phaseCode regs) =
      phaseValue
        (initial (Layout.chunkRadix regs))
        (initial (Layout.bankRadix regs)) 3
        (initial (decodedResidue regs))
        (initial (decodedResiduesLeft regs))
        (initial (decodedNextChild regs)) 0
  /-- No other logical cell is changed by phase encoding. -/
  eq_of_ne :
    ∀ address,
      address ≠ Layout.phaseCode regs →
      address ≠ Layout.codecDigit regs →
      final address = initial address

/-- Seven-register view used to compute the inverse of the decoded residue.
All cells belong to the existing shared evaluator allocation. -/
def cleanupInverseMap : Fin 7 → Fin 34 :=
  ![19, 24, 16, 5, 9, 20, 17]

theorem cleanupInverseMap_injective :
    Function.Injective cleanupInverseMap := by
  decide

/-- Modular-power registers for cleanup scaling.  The accumulator is the
residue operand cell, while the base is the decoded residue. -/
def cleanupInverseRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.Structured.RuntimeArithmetic.PowRegisters where
  index := fun slot => regs.index (cleanupInverseMap slot)
  injective := regs.injective.comp cleanupInverseMap_injective

/-- Direct-register copy in the source RAM instruction set. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Save the parent scalar and output coordinate across streamed bank
scaling.  The two codec cells are outside the bank-scaling register view. -/
def saveActiveFields
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (copy (Layout.codecScratch regs) (Layout.scalar regs))
    (copy (Layout.frameCode regs) (Layout.out regs))

/-- Observable result of saving the two active parent fields. -/
structure SaveActivePost
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The scalar is saved in the spare codec cell. -/
  savedScalar_eq :
    final (Layout.codecScratch regs) =
      initial (Layout.scalar regs)
  /-- The output coordinate is saved in the transient frame-code cell. -/
  savedOut_eq :
    final (Layout.frameCode regs) =
      initial (Layout.out regs)
  /-- All cells other than the two save destinations are preserved. -/
  eq_of_ne :
    ∀ address,
      address ≠ Layout.codecScratch regs →
      address ≠ Layout.frameCode regs →
      final address = initial address

/-- Restore the parent scalar and output coordinate after streamed bank
scaling. -/
def restoreActiveFields
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (copy (Layout.scalar regs) (Layout.codecScratch regs))
    (copy (Layout.out regs) (Layout.frameCode regs))

/-- Observable result of restoring the two active parent fields. -/
structure RestoreActivePost
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The active scalar is restored from its saved cell. -/
  scalar_eq :
    final (Layout.scalar regs) =
      initial (Layout.codecScratch regs)
  /-- The active output coordinate is restored from its saved cell. -/
  out_eq :
    final (Layout.out regs) =
      initial (Layout.frameCode regs)
  /-- All cells other than the two active destinations are preserved. -/
  eq_of_ne :
    ∀ address,
      address ≠ Layout.scalar regs →
      address ≠ Layout.out regs →
      final address = initial address

/-- Replace the active output coordinate by `out.succAbove child`.

For natural representatives, `out - child` is nonzero exactly when
`child < out`; in that case the embedding is `child`, and otherwise it is
`child + 1`. -/
def selectChildTarget
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inverse := cleanupInverseRegisters regs
  Cmd.seq
    (.basic
      (.sub inverse.test
        (Layout.out regs) (decodedChild regs)))
    (.ifZero inverse.test
      (Cmd.seq
        (copy (Layout.out regs) (decodedChild regs))
        (.basic
          (.add (Layout.out regs)
            (Layout.out regs) inverse.one)))
      (copy (Layout.out regs) (decodedChild regs)))

/-- Observable result of embedding the decoded child coordinate around the
parent output coordinate. -/
structure ChildTargetPost
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The selected target is the natural representative of
  `out.succAbove child`. -/
  out_eq :
    final (Layout.out regs) =
      if initial (decodedChild regs) < initial (Layout.out regs) then
        initial (decodedChild regs)
      else
        initial (decodedChild regs) + 1
  /-- Only the output destination and comparison scratch may change. -/
  eq_of_ne :
    ∀ address,
      address ≠ Layout.out regs →
      address ≠ (cleanupInverseRegisters regs).test →
      final address = initial address

/-- Concrete cleanup-scale phase fragment.

The command first commits the successor cleanup-call phase, saves the parent
fields, computes the current residue's field inverse, temporarily installs
that inverse and the selected child target as the active scaling operands,
streams the complete catalytic register, and restores the parent fields.
-/
def cleanupScale
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inverse := cleanupInverseRegisters regs
  Cmd.seqList
    [encodeCleanupCallPhase regs,
      saveActiveFields regs,
      Runtime.inverseMod inverse,
      copy (Layout.scalar regs) inverse.accumulator,
      selectChildTarget regs,
      ResidueBankOps.scaleActiveRegister regs,
      restoreActiveFields regs]

/-- Physical ABI cells that cleanup scaling must preserve exactly:
block length, horizon, grouped-chunk count, codec radix, frame radix, bank
digit count, active fuel, node code, activity flag, and packed stack word. -/
def cleanupRetainedMap : Fin 10 → Fin 34 :=
  ![2, 3, 7, 8, 13, 15, 22, 23, 28, 32]

/-- Exact semantic and representation result of cleanup scaling. -/
structure CleanupScalePost
    (tm : TM workTapeCount)
    (blockLength scalar residue residuesLeft nextChild
      digitBase bankBase finalWord : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (out :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount))
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The parent resumes at the next cleanup-call cursor. -/
  phaseCode_eq :
    final (Layout.phaseCode regs) =
      FrameCodec.encodePhase digitBase
        (.cleanupCall residue residuesLeft nextChild :
          NeighborhoodScheduler.Phase workTapeCount)
  /-- The parent scalar is restored after temporary inverse installation. -/
  scalar_eq : final (Layout.scalar regs) = scalar
  /-- The parent output coordinate is restored after target selection. -/
  out_eq : final (Layout.out regs) = out.val
  /-- The final packed catalytic word. -/
  word_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.word =
      finalWord
  /-- The final word remains inside its advertised fixed digit width. -/
  word_lt :
    finalWord <
      bankBase ^
        ((NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
  /-- The selected child register is scaled by the current residue inverse. -/
  represents :
    NeighborhoodProgram.RepresentsResidueBank
      tm blockLength bankBase finalWord
      (NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm blockLength
        (TreeEval.CookMertz.PrimeField.Runtime.inverse
          (NeighborhoodExecutableEvaluation.modulus
            tm blockLength) residue)
        original (out.succAbove child))
  /-- Packed-bank radix is preserved. -/
  base_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.base =
      bankBase
  /-- Cached packed-bank radix predecessor is canonical. -/
  basePred_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.basePred =
      bankBase - 1
  /-- Packed-bank loop constant is canonical. -/
  one_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.one =
      1
  /-- The field modulus is preserved. -/
  modulus_eq :
    final (Layout.residueScaleRegisters regs).bank.modulus =
      NeighborhoodExecutableEvaluation.modulus tm blockLength
  /-- The cached modulus predecessor is canonical. -/
  modulusPred_eq :
    final (Layout.residueScaleRegisters regs).bank.modulusPred =
      NeighborhoodExecutableEvaluation.modulus tm blockLength - 1
  /-- Every retained parent, parameter, and continuation ABI cell survives
  the fragment exactly. -/
  retained_eq :
    ∀ slot,
      final (regs.index (cleanupRetainedMap slot)) =
        initial (regs.index (cleanupRetainedMap slot))

end Dispatcher
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
