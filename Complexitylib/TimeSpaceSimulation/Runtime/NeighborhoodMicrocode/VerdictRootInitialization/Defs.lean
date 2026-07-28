/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryReinitialization.Defs

/-!
# Uniform initialization of the verdict-consistency root

The latest-output-block root requires the greatest earlier valid guessed
neighborhood containing the verdict block. Unlike the ordinary child scan,
this search must skip invalid later movement prefixes. The command below does
so directly while reading only the retained runtime horizon, block length, and
packed guess word.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace VerdictRootInitialization

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Greatest containing valid candidate in the descending prefix
`0, ..., count - 1`. Invalid candidates are skipped. -/
def exactPriorSearchValue
    (workTapeCount word tape requested : ℕ) : ℕ →
      Option (ℕ × ℕ)
  | 0 => none
  | count + 1 =>
      match
        ChildNode.derivedCenterValue
          workTapeCount word tape count with
      | none =>
          exactPriorSearchValue
            workTapeCount word tape requested count
      | some center =>
          if NeighborhoodGraph.NeighborhoodContains center requested then
            some (count, center)
          else
            exactPriorSearchValue
              workTapeCount word tape requested count

/-- One descending exact-prior candidate test. An invalid center leaves the
countdown live so the loop continues with the preceding candidate. -/
def exactPriorSearchBody
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic
      (.sub (ChildNode.priorCountdown regs)
        (ChildNode.priorCountdown regs)
        (ChildNode.movementDivision regs).one),
      ControlDecode.copy
        (ControlDecode.nodePayload1 regs)
        (ChildNode.priorCountdown regs),
      ChildNode.deriveCenter workTapeCount controller regs,
      .ifZero (ChildNode.centerValid regs)
        .skip
        (ChildNode.recordPriorIfContains regs)]

/-- Exact backwards scan that skips invalid guessed centers. -/
def scanExactPrior
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (Cmd.basics
      [.imm (ChildNode.movementDivision regs).one 1,
        .imm (ChildNode.priorFound regs) 0,
        .imm (ChildNode.priorInterval regs) 0,
        .imm (ChildNode.priorCenter regs) 0])
    (Cmd.seq
      (ControlDecode.copy
        (ChildNode.priorCountdown regs)
        (ControlDecode.nodePayload1 regs))
      (.whileNonzero (ChildNode.priorCountdown regs)
        (exactPriorSearchBody workTapeCount controller regs)))

/-- Observable result of the invalid-skipping greatest-prior scan. -/
structure ScanExactPriorPost
    (workTapeCount word tape requested interval : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Found flag for the exact option-valued result. -/
  found_eq :
    final (ChildNode.priorFound regs) =
      ChildNode.priorFoundValue
        (some
          (exactPriorSearchValue
            workTapeCount word tape requested interval))
  /-- Greatest matching interval, or zero when absent. -/
  interval_eq :
    final (ChildNode.priorInterval regs) =
      ChildNode.priorIntervalValue
        (some
          (exactPriorSearchValue
            workTapeCount word tape requested interval))
  /-- Center at the greatest match, or zero when absent. -/
  center_eq :
    final (ChildNode.priorCenter regs) =
      ChildNode.priorCenterValue
        (some
          (exactPriorSearchValue
            workTapeCount word tape requested interval))
  /-- The descending candidate countdown is exhausted. -/
  countdown_eq : final (ChildNode.priorCountdown regs) = 0
  /-- Arithmetic constant one is retained for node assembly. -/
  one_eq : final (ChildNode.movementDivision regs).one = 1
  /-- Selected tape is retained. -/
  tape_eq : final (ControlDecode.nodeTape regs) = tape
  /-- Requested block is retained. -/
  requested_eq : final (ChildNode.requestedBlock regs) = requested
  /-- The outer movement word is read-only. -/
  guess_eq : final controller.guess = word
  /-- Every address outside the predecessor scratch is preserved. -/
  eq_outside :
    ∀ address, address ∉ ChildNode.priorFootprint regs →
      final address = initial address

/-- The catalytic output coordinate reserved for the verdict value. -/
def verdictOut
    (workTapeCount : ℕ) :
    Fin (graphFanIn workTapeCount + 1) :=
  ⟨0, by omega⟩

/-- Initialize the requested verdict block, output tape, and search horizon
from runtime registers. Positivity of the represented block length proves
that `blockIndex blockLength 1` is one exactly at block length one. -/
def initializeVerdictFields
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic
      (.imm (ControlDecode.nodeTape regs)
        (TapeIndex.output workTapeCount).val),
      .basic (.imm (ChildNode.requestedBlock regs) 0),
      .basic
        (.sub (ChildNode.movementDivision regs).test
          (Layout.blockLength regs) controller.one),
      .ifZero (ChildNode.movementDivision regs).test
        (.basic (.imm (ChildNode.requestedBlock regs) 1))
        .skip,
      ControlDecode.copy
        (ControlDecode.nodePayload1 regs)
        (Layout.horizon regs)]

/-- Convert the exact scan result to the existing source/computation node
assembler. The validity flag is forced to one because invalid candidates
were skipped rather than returned. -/
def installExactPrior
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic (.imm (ChildNode.centerValid regs) 1))
    (ChildNode.installPrior regs)

/-- Build the packed verdict-consistency root from runtime data only. -/
def buildVerdictRoot
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [initializeVerdictFields workTapeCount controller regs,
      scanExactPrior workTapeCount controller regs,
      installExactPrior regs]

/-- Build the verdict root and replace the current query while preserving its
catalytic bank. -/
def reinitializeVerdictQuery
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (buildVerdictRoot workTapeCount controller regs)
    (QueryReinitialization.reinitializeQuery
      workTapeCount regs (verdictOut workTapeCount))

end VerdictRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
