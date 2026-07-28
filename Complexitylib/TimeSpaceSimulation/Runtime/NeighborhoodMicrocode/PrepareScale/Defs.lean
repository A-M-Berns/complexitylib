/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Defs

/-!
# Prepare-fold catalytic-bank scaling

Before descending to one prepare child, the evaluator multiplies the child's
catalytic target register by the decoded residue.  This fragment saves the
parent scalar and output coordinate, installs the decoded residue and
`succAbove` child target, streams the verified packed-bank scaler, and
restores the active parent ABI.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareScale

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Exact direct-write footprint of prepare-fold scaling. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (Layout.residueScaleRegisters regs).footprint ∪
    {Layout.codecScratch regs, Layout.frameCode regs,
      Layout.scalar regs, Layout.out regs}

/-- Scale the selected prepare-child register by the decoded residue while
preserving the parent scalar and output coordinate. -/
def scaleChildTarget
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [Dispatcher.saveActiveFields regs,
      Dispatcher.copy
        (Layout.scalar regs) (Dispatcher.decodedResidue regs),
      Dispatcher.selectChildTarget regs,
      ResidueBankOps.scaleActiveRegister regs,
      Dispatcher.restoreActiveFields regs]

/-- Exact observable and logical result of prepare-fold scaling. -/
structure ScalePost
    (tm : TM workTapeCount)
    (blockLength parentScalar residue base finalWord : ℕ)
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
  /-- The active parent scalar is restored. -/
  scalar_eq : final (Layout.scalar regs) = parentScalar
  /-- The active parent output coordinate is restored. -/
  out_eq : final (Layout.out regs) = out.val
  /-- The final packed catalytic word. -/
  word_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.word =
      finalWord
  /-- The packed word represents scaling exactly the selected child target. -/
  represents :
    NeighborhoodProgram.RepresentsResidueBank
      tm blockLength base finalWord
      (NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm blockLength residue original (out.succAbove child))
  /-- The scaled packed word remains within the canonical bank capacity. -/
  word_lt :
    finalWord <
      base ^
        ((NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
  /-- The packed-bank radix is preserved. -/
  base_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.base =
      base
  /-- The cached radix predecessor is canonical. -/
  basePred_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.basePred =
      base - 1
  /-- The packed-bank constant is canonical. -/
  one_eq :
    final
        (Layout.residueScaleRegisters regs).bank.bank.one =
      1
  /-- The field modulus is preserved. -/
  modulus_eq :
    final (Layout.residueScaleRegisters regs).bank.modulus =
      NeighborhoodExecutableEvaluation.modulus tm blockLength
  /-- The cached field-modulus predecessor is canonical. -/
  modulusPred_eq :
    final (Layout.residueScaleRegisters regs).bank.modulusPred =
      NeighborhoodExecutableEvaluation.modulus tm blockLength - 1
  /-- Every address outside the exact fragment footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ writeFootprint regs →
      final address = initial address

end PrepareScale
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
