/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode

/-!
# Fixed-register child-node regeneration

Recursive neighborhood children are not stored in scheduler frames.  They
must be regenerated from the packed ternary movement guess whenever the
depth-first scheduler descends to a child.

The pipeline decodes the role-major child cursor, reconstructs guessed tape
centers from arbitrary little-endian ternary movement digits, scans for the
greatest containing prior neighborhood, and packs the resulting failure,
source, or computation node.  No indirect load or store occurs.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ChildNode

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Six time-multiplexed workspace cells used by ternary digit lookup.

The first five form a `ControlDecode.DivisionRegisters` view; the final cell
is the destructive digit-index countdown. -/
def movementMap : Fin 6 → Fin 34 :=
  ![0, 4, 5, 17, 18, 19]

theorem movementMap_injective :
    Function.Injective movementMap := by
  decide

/-- Concrete quotient/remainder view used to divide the movement word by
three. -/
def movementDivision
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.DivisionRegisters where
  index := fun slot =>
    regs.index (movementMap ⟨slot.val, by omega⟩)
  injective := regs.injective.comp fun first second heq => by
    apply Fin.ext
    have hmap := movementMap_injective heq
    exact congrArg (fun slot : Fin 6 => slot.val) hmap

/-- Destructive requested movement-digit index. -/
abbrev movementIndex
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (movementMap 5)

/-- Exact finite write footprint of ternary digit lookup. -/
def movementFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  Finset.univ.image fun slot => regs.index (movementMap slot)

/-- Suffix remaining after dropping `count` little-endian ternary digits. -/
def ternarySuffix : ℕ → ℕ → ℕ
  | word, 0 => word
  | word, count + 1 => ternarySuffix (word / 3) count

/-- Pure ternary digit selected by the concrete streaming routine. -/
def movementDigitValue (word index : ℕ) : ℕ :=
  ternarySuffix word index % 3

/-- Initialize the local divisor and copy the read-only guess word. -/
def initializeMovement
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let division := movementDivision regs
  Cmd.basics
    [.imm division.divisor 3,
      .imm division.value 0,
      .add division.value controller.guess division.value]

/-- Drop one ternary digit and decrement the requested-index countdown. -/
def dropMovementDigit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let division := movementDivision regs
  Cmd.seqList
    [ControlDecode.divRem division,
      ControlDecode.copy division.value division.quotient,
      .basic
        (.sub (movementIndex regs)
          (movementIndex regs) division.one)]

/-- Drop exactly the requested number of low ternary digits. -/
def seekMovementDigit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .whileNonzero (movementIndex regs) (dropMovementDigit regs)

/-- Read one arbitrary movement trit from the outer controller's packed
guess word.

On entry `movementIndex` contains the desired little-endian digit index.
On exit `movementDivision.value` contains that ternary digit and the index
countdown is zero. -/
def movementDigit
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [initializeMovement controller regs,
      seekMovementDigit regs,
      ControlDecode.divRem (movementDivision regs)]

/-- Exact observable result of one ternary movement-digit lookup. -/
structure MovementDigitPost
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (word index : ℕ) (initial final : Store) : Prop where
  /-- Selected little-endian ternary digit. -/
  value_eq :
    final (movementDivision regs).value =
      movementDigitValue word index
  /-- The destructive index countdown is exhausted. -/
  index_eq : final (movementIndex regs) = 0
  /-- The fixed divisor is retained. -/
  divisor_eq : final (movementDivision regs).divisor = 3
  /-- The division-loop constant is canonical. -/
  one_eq : final (movementDivision regs).one = 1
  /-- The final quotient/remainder loop test is cleared. -/
  test_eq : final (movementDivision regs).test = 0
  /-- The outer movement counter is read-only. -/
  guess_eq : final controller.guess = word
  /-- Every address outside the six-cell lookup footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ movementFootprint regs →
      final address = initial address

/-- Child cursor retained across parent-frame pushing and node decoding. -/
abbrev savedChildIndex
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  Layout.codecScratch regs

/-- Decode the role-major predecessor cursor into its named-tape remainder
and predecessor-kind quotient.

The fixed divisor is `workTapeCount + 2`, exactly the number of named tapes.
The saved child cursor itself is read-only. -/
def decodeChildIndex
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let division := movementDivision regs
  Cmd.seqList
    [.basic (.imm division.divisor (workTapeCount + 2)),
      ControlDecode.copy division.value (savedChildIndex regs),
      ControlDecode.divRem division]

/-- Exact observable result of predecessor-cursor decoding. -/
structure ChildIndexPost
    (workTapeCount child : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Named-tape coordinate is the cursor remainder. -/
  tape_eq :
    final (movementDivision regs).value =
      child % (workTapeCount + 2)
  /-- Predecessor kind is the role-major cursor quotient. -/
  kind_eq :
    final (movementDivision regs).quotient =
      child / (workTapeCount + 2)
  /-- The saved cursor is preserved for later dispatch. -/
  child_eq : final (savedChildIndex regs) = child
  /-- The fixed named-tape divisor is retained. -/
  divisor_eq :
    final (movementDivision regs).divisor = workTapeCount + 2
  /-- The division-loop constant is canonical for kind dispatch. -/
  one_eq : final (movementDivision regs).one = 1
  /-- Every address outside the six-cell arithmetic footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ movementFootprint regs →
      final address = initial address

/-- Pure little-endian four-field node value used by the RAM encoder. -/
def nodeFieldValue
    (base tag tape payload0 payload1 : ℕ) : ℕ :=
  tag + base * (tape + base * (payload0 + base * payload1))

/-- Straight-line operations rebuilding a child node from the three shared
decoded payload cells and a fixed node tag. -/
def encodeNodeFieldsOps
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) : List Basic :=
  [.imm (Layout.nodeCode regs) 0,
    .add (Layout.nodeCode regs)
      (ControlDecode.nodePayload1 regs) (Layout.nodeCode regs),
    .mul (Layout.nodeCode regs)
      (Layout.chunkRadix regs) (Layout.nodeCode regs),
    .add (Layout.nodeCode regs)
      (ControlDecode.nodePayload0 regs) (Layout.nodeCode regs),
    .mul (Layout.nodeCode regs)
      (Layout.chunkRadix regs) (Layout.nodeCode regs),
    .add (Layout.nodeCode regs)
      (ControlDecode.nodeTape regs) (Layout.nodeCode regs),
    .mul (Layout.nodeCode regs)
      (Layout.chunkRadix regs) (Layout.nodeCode regs),
    .imm (Layout.codecDigit regs) tag,
    .add (Layout.nodeCode regs)
      (Layout.codecDigit regs) (Layout.nodeCode regs),
    .imm (Layout.codecDigit regs) 0]

/-- Rebuild the active packed child-node code from shared numeric fields. -/
def encodeNodeFields
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) : Cmd :=
  Cmd.basics (encodeNodeFieldsOps regs tag)

/-- Exact two-cell footprint of child-node field encoding. -/
def nodeEncodingFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {Layout.nodeCode regs, Layout.codecDigit regs}

/-- Observable result of child-node field encoding. -/
structure EncodeNodeFieldsPost
    (regs : NeighborhoodTrial.Registers controller)
    (tag : ℕ) (initial final : Store) : Prop where
  /-- The packed node is the exact four-field radix numeral. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) =
      nodeFieldValue
        (initial (Layout.chunkRadix regs)) tag
        (initial (ControlDecode.nodeTape regs))
        (initial (ControlDecode.nodePayload0 regs))
        (initial (ControlDecode.nodePayload1 regs))
  /-- The transient immediate cell is cleared. -/
  codecDigit_eq : final (Layout.codecDigit regs) = 0
  /-- Every other address is preserved. -/
  eq_outside :
    ∀ address, address ∉ nodeEncodingFootprint regs →
      final address = initial address

/-- Five outer-loop cells used while reconstructing one guessed center.

They are disjoint from the six-cell ternary lookup allocation. -/
def centerMap : Fin 5 → Fin 34 :=
  ![6, 10, 12, 20, 21]

theorem centerMap_injective :
    Function.Injective centerMap := by
  decide

/-- Fixed distance between consecutive movement digits for one named tape. -/
abbrev centerStride
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 0)

/-- Current reconstructed center block. -/
abbrev centerValue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 1)

/-- One exactly while the scanned movement prefix remains valid. -/
abbrev centerValid
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 2)

/-- Number of movement boundaries still to scan. -/
abbrev centerRemaining
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 3)

/-- Packed-guess digit index for the next boundary of the selected tape. -/
abbrev centerNextIndex
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (centerMap 4)

/-- Exact write footprint of one center-prefix reconstruction. -/
def centerFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  movementFootprint regs ∪
    Finset.univ.image fun slot => regs.index (centerMap slot)

/-- Apply one decoded movement digit to a natural center, rejecting only a
left move from block zero. -/
def applyMovementDigit (digit center : ℕ) : Option ℕ :=
  if digit = 0 then
    if center = 0 then none else some (center - 1)
  else if digit = 1 then
    some center
  else
    some (center + 1)

/-- Pure forward scan corresponding exactly to the center RAM loop. -/
def scanCenter (word stride : ℕ) :
    ℕ → ℕ → ℕ → Option ℕ
  | 0, _, center => some center
  | remaining + 1, index, center =>
      match applyMovementDigit
          (movementDigitValue word index) center with
      | none => none
      | some next =>
          scanCenter word stride remaining (index + stride) next

/-- Center reconstructed from canonical initial center zero for one numeric
tape and interval. -/
def derivedCenterValue
    (workTapeCount word tape interval : ℕ) : Option ℕ :=
  scanCenter word (workTapeCount + 2) interval tape 0

/-- Numeric validity flag for an optional reconstructed center. -/
def centerValidValue : Option ℕ → ℕ
  | none => 0
  | some _ => 1

/-- Numeric center output, with zero in the invalid-prefix case. -/
def centerOutputValue : Option ℕ → ℕ
  | none => 0
  | some center => center

/-- Remaining-boundary output of one movement application. -/
def centerRemainingValue (remaining : ℕ) : Option ℕ → ℕ
  | none => 0
  | some _ => remaining - 1

/-- Next movement-digit index after one movement application. -/
def centerNextIndexValue (index stride : ℕ) : Option ℕ → ℕ
  | none => index
  | some _ => index + stride

/-- Advance the selected tape's digit index and exhaust one boundary. -/
def advanceCenter
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.add (centerNextIndex regs)
        (centerNextIndex regs) (centerStride regs),
      .sub (centerRemaining regs)
        (centerRemaining regs) (movementDivision regs).one]

/-- Terminate a scan after an invalid left move from block zero. -/
def invalidateCenter
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (centerValid regs) 0,
      .imm (centerRemaining regs) 0]

/-- Apply a decoded left movement. -/
def applyLeftMovement
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .ifZero (centerValue regs)
    (invalidateCenter regs)
    (Cmd.seq
      (.basic
        (.sub (centerValue regs)
          (centerValue regs) (movementDivision regs).one))
      (advanceCenter regs))

/-- Apply a decoded stay or right movement. -/
def applyNonleftMovement
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let division := movementDivision regs
  Cmd.seq
    (.basic (.sub division.test division.value division.one))
    (.ifZero division.test
      (advanceCenter regs)
      (Cmd.seq
        (.basic
          (.add (centerValue regs)
            (centerValue regs) division.one))
        (advanceCenter regs)))

/-- Apply the selected ternary digit to the current center. -/
def applySelectedMovement
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .ifZero (movementDivision regs).value
    (applyLeftMovement regs)
    (applyNonleftMovement regs)

/-- One center-prefix loop iteration. -/
def centerStep
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.copy
      (movementIndex regs) (centerNextIndex regs),
      movementDigit controller regs,
      applySelectedMovement regs]

/-- Initialize one canonical center-prefix scan from the shared decoded
node tape and interval fields. -/
def initializeCenter
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (movementDivision regs).one 1),
      .basic (.imm (centerValue regs) 0),
      .basic (.imm (centerValid regs) 1),
      ControlDecode.copy
        (centerRemaining regs) (ControlDecode.nodePayload1 regs),
      ControlDecode.copy
        (centerNextIndex regs) (ControlDecode.nodeTape regs),
      .basic (.imm (centerStride regs) (workTapeCount + 2))]

/-- Reconstruct the guessed center of the shared decoded tape at the shared
decoded interval. -/
def deriveCenter
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (initializeCenter workTapeCount regs)
    (.whileNonzero (centerRemaining regs)
      (centerStep controller regs))

/-- Exact observable result of one center-prefix reconstruction. -/
structure DeriveCenterPost
    (workTapeCount word tape interval : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The validity flag is the exact option discriminator. -/
  valid_eq :
    final (centerValid regs) =
      centerValidValue
        (derivedCenterValue workTapeCount word tape interval)
  /-- The numeric center is exact, with canonical zero on failure. -/
  center_eq :
    final (centerValue regs) =
      centerOutputValue
        (derivedCenterValue workTapeCount word tape interval)
  /-- The boundary countdown is exhausted on both success and failure. -/
  remaining_eq : final (centerRemaining regs) = 0
  /-- The arithmetic constant is canonical for subsequent local tests. -/
  one_eq : final (movementDivision regs).one = 1
  /-- The read-only movement guess is preserved. -/
  guess_eq : final controller.guess = word
  /-- The shared decoded tape remains available. -/
  tape_eq : final (ControlDecode.nodeTape regs) = tape
  /-- The shared decoded interval remains available. -/
  interval_eq :
    final (ControlDecode.nodePayload1 regs) = interval
  /-- Every address outside the eleven-cell center footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ centerFootprint regs →
      final address = initial address

/-- Five persistent cells for the backward greatest-predecessor scan. -/
def priorMap : Fin 5 → Fin 34 :=
  ![25, 26, 27, 28, 29]

theorem priorMap_injective :
    Function.Injective priorMap := by
  decide

/-- Requested tape block whose latest earlier neighborhood is sought. -/
abbrev requestedBlock
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (priorMap 0)

/-- Descending candidate interval, also serving as the loop test. -/
abbrev priorCountdown
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (priorMap 1)

/-- One exactly when a containing earlier interval has been found. -/
abbrev priorFound
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (priorMap 2)

/-- Greatest containing earlier interval found by the backward scan. -/
abbrev priorInterval
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (priorMap 3)

/-- Guessed center at the greatest containing earlier interval. -/
abbrev priorCenter
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index (priorMap 4)

/-- Exact fixed footprint of the greatest-prior scan. -/
def priorFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  centerFootprint regs ∪
    {ControlDecode.nodePayload1 regs} ∪
    Finset.univ.image fun slot => regs.index (priorMap slot)

/-- Three-valued pure result of a greatest-prior search.

Outer `none` means an invalid movement prefix.  `some none` means every
prefix was valid but no earlier neighborhood contained the requested block.
`some (some (interval, center))` records the greatest match. -/
def priorSearchValue
    (workTapeCount word tape requested : ℕ) : ℕ →
      Option (Option (ℕ × ℕ))
  | 0 => some none
  | count + 1 =>
      match derivedCenterValue workTapeCount word tape count with
      | none => none
      | some center =>
          if NeighborhoodGraph.NeighborhoodContains center requested then
            some (some (count, center))
          else
            priorSearchValue workTapeCount word tape requested count

/-- Numeric validity flag of a greatest-prior search. -/
def priorValidValue : Option (Option (ℕ × ℕ)) → ℕ
  | none => 0
  | some _ => 1

/-- Numeric found flag of a greatest-prior search. -/
def priorFoundValue : Option (Option (ℕ × ℕ)) → ℕ
  | some (some _) => 1
  | _ => 0

/-- Greatest matching interval, or canonical zero when absent/invalid. -/
def priorIntervalValue : Option (Option (ℕ × ℕ)) → ℕ
  | some (some result) => result.1
  | _ => 0

/-- Center at the greatest match, or canonical zero when absent/invalid. -/
def priorCenterValue : Option (Option (ℕ × ℕ)) → ℕ
  | some (some result) => result.2
  | _ => 0

/-- Record the current candidate as the greatest containing predecessor and
force the descending loop to stop. -/
def recordPrior
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics
    [.imm (priorFound regs) 1,
      .imm (priorInterval regs) 0,
      .add (priorInterval regs)
        (ControlDecode.nodePayload1 regs) (priorInterval regs),
      .imm (priorCenter regs) 0,
      .add (priorCenter regs)
        (centerValue regs) (priorCenter regs),
      .imm (priorCountdown regs) 0]

/-- Test whether the requested block lies in the current three-block
neighborhood, recording the candidate exactly when it does.

For naturals, membership is equivalent to the two inequalities
`requested ≤ center + 1` and `center ≤ requested + 1`.  The command tests
those inequalities by adding two before truncated subtraction. -/
def recordPriorIfContains
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let division := movementDivision regs
  Cmd.seq
    (Cmd.basics
      [.imm division.value 0,
        .add division.value (centerValue regs) division.value,
        .add division.value division.value division.one,
        .add division.value division.value division.one,
        .sub division.test division.value (requestedBlock regs)])
    (.ifZero division.test .skip
      (Cmd.seq
        (Cmd.basics
          [.imm division.value 0,
            .add division.value
              (requestedBlock regs) division.value,
            .add division.value division.value division.one,
            .add division.value division.value division.one,
            .sub division.test division.value (centerValue regs)])
        (.ifZero division.test .skip (recordPrior regs))))

/-- Observable state after testing whether one valid center contains the
requested block. -/
structure RecordPriorIfContainsPost
    (regs : NeighborhoodTrial.Registers controller)
    (center requested candidate countdown word tape : ℕ)
    (final : Store) : Prop where
  /-- The found flag records exactly a containing candidate. -/
  found_eq :
    final (priorFound regs) =
      if NeighborhoodGraph.NeighborhoodContains center requested then
        1
      else
        0
  /-- A containing candidate becomes the retained interval. -/
  interval_eq :
    final (priorInterval regs) =
      if NeighborhoodGraph.NeighborhoodContains center requested then
        candidate
      else
        0
  /-- A containing candidate retains its reconstructed center. -/
  priorCenter_eq :
    final (priorCenter regs) =
      if NeighborhoodGraph.NeighborhoodContains center requested then
        center
      else
        0
  /-- Finding a candidate stops the descending search. -/
  countdown_eq :
    final (priorCountdown regs) =
      if NeighborhoodGraph.NeighborhoodContains center requested then
        0
      else
        countdown
  /-- The valid-center flag is retained. -/
  valid_eq : final (centerValid regs) = 1
  /-- The arithmetic constant one is retained. -/
  one_eq : final (movementDivision regs).one = 1
  /-- The tested candidate interval is retained. -/
  candidate_eq :
    final (ControlDecode.nodePayload1 regs) = candidate
  /-- The selected named tape is retained. -/
  tape_eq : final (ControlDecode.nodeTape regs) = tape
  /-- The requested block is retained. -/
  requested_eq : final (requestedBlock regs) = requested
  /-- The packed movement guess is read-only. -/
  guess_eq : final controller.guess = word

/-- One descending greatest-prior candidate test. -/
def priorSearchBody
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic
      (.sub (priorCountdown regs)
        (priorCountdown regs) (movementDivision regs).one),
      ControlDecode.copy
        (ControlDecode.nodePayload1 regs) (priorCountdown regs),
      deriveCenter workTapeCount controller regs,
      .ifZero (centerValid regs)
        (.basic (.imm (priorCountdown regs) 0))
        (recordPriorIfContains regs)]

/-- Search backward for the greatest earlier guessed neighborhood containing
the requested block. -/
def scanPrior
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (Cmd.basics
      [.imm (movementDivision regs).one 1,
        .imm (centerValid regs) 1,
        .imm (priorFound regs) 0,
        .imm (priorInterval regs) 0,
        .imm (priorCenter regs) 0])
    (Cmd.seq
      (ControlDecode.copy
        (priorCountdown regs) (ControlDecode.nodePayload1 regs))
      (.whileNonzero (priorCountdown regs)
        (priorSearchBody workTapeCount controller regs)))

/-- Exact observable result of the backward greatest-prior scan. -/
structure ScanPriorPost
    (workTapeCount word tape requested interval : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Prefix validity agrees with the pure backward search. -/
  valid_eq :
    final (centerValid regs) =
      priorValidValue
        (priorSearchValue
          workTapeCount word tape requested interval)
  /-- Found flag agrees with the pure backward search. -/
  found_eq :
    final (priorFound regs) =
      priorFoundValue
        (priorSearchValue
          workTapeCount word tape requested interval)
  /-- Greatest interval output agrees with the pure backward search. -/
  interval_eq :
    final (priorInterval regs) =
      priorIntervalValue
        (priorSearchValue
          workTapeCount word tape requested interval)
  /-- Matching center output agrees with the pure backward search. -/
  center_eq :
    final (priorCenter regs) =
      priorCenterValue
        (priorSearchValue
          workTapeCount word tape requested interval)
  /-- Descending candidate countdown is exhausted. -/
  countdown_eq : final (priorCountdown regs) = 0
  /-- The arithmetic constant is canonical for final node assembly. -/
  one_eq : final (movementDivision regs).one = 1
  /-- Selected tape is preserved. -/
  tape_eq : final (ControlDecode.nodeTape regs) = tape
  /-- Requested block is preserved. -/
  requested_eq : final (requestedBlock regs) = requested
  /-- The read-only movement word is preserved. -/
  guess_eq : final controller.guess = word
  /-- Every address outside the fixed predecessor footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ priorFootprint regs →
      final address = initial address

/-- Query regenerated by the chronological branch from an option-valued
current center. -/
def chronologicalQueryValue
    (tape : TapeIndex workTapeCount) (interval : ℕ) :
    Option ℕ → NeighborhoodEvaluator.QueryNode workTapeCount horizon
  | none => .failure
  | some center =>
      match interval with
      | 0 =>
          .graph (.source tape center)
      | previous + 1 =>
          .graph
            (.computation tape .center previous)

/-- Query selected by the three-valued greatest-prior result of a content
predecessor branch. -/
def priorQueryValue
    (tape : TapeIndex workTapeCount) (requested : ℕ) :
    Option (Option (ℕ × ℕ)) →
      NeighborhoodEvaluator.QueryNode workTapeCount horizon
  | none => .failure
  | some none => .graph (.source tape requested)
  | some (some (interval, center)) =>
      .graph
        (.computation tape
          (NeighborhoodGraph.matchingSlot center requested) interval)

/-- Clear all four numeric node fields and install the failure tag. -/
def installFailure
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (Cmd.basics
      [.imm (ControlDecode.nodeTape regs) 0,
        .imm (ControlDecode.nodePayload0 regs) 0,
        .imm (ControlDecode.nodePayload1 regs) 0])
    (encodeNodeFields regs 0)

/-- Assemble the chronological predecessor from a reconstructed current
center and the shared decoded interval. -/
def installChronological
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .ifZero (centerValid regs)
    (installFailure regs)
    (.ifZero (ControlDecode.nodePayload1 regs)
      (encodeNodeFields regs 1)
      (Cmd.seq
        (Cmd.basics
          [.sub (ControlDecode.nodePayload1 regs)
              (ControlDecode.nodePayload1 regs)
              (movementDivision regs).one,
            .imm (ControlDecode.nodePayload0 regs) 1])
        (encodeNodeFields regs 2)))

/-- Assemble the no-prior-match content branch as an initial source node. -/
def installPriorSource
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.copy
      (ControlDecode.nodePayload0 regs) (requestedBlock regs),
      .basic (.imm (ControlDecode.nodePayload1 regs) 0),
      encodeNodeFields regs 1]

/-- Assemble a matching prior computation node.

The two equality tests implement `matchingSlot` in lower-first order.  If
neither the lower nor center block matches, the upper slot is selected,
exactly as in the total pure definition. -/
def installPriorComputation
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let division := movementDivision regs
  Cmd.seqList
    [ControlDecode.copy
      (ControlDecode.nodePayload1 regs) (priorInterval regs),
      .basic (.imm (ControlDecode.nodePayload0 regs) 0),
      .basic
        (.sub division.value
          (priorCenter regs) division.one),
      .basic
        (.sub division.test
          (requestedBlock regs) division.value),
      .ifZero division.test
        (encodeNodeFields regs 2)
        (Cmd.seqList
          [.basic (.imm (ControlDecode.nodePayload0 regs) 1),
            .basic
              (.sub division.test
                (requestedBlock regs) (priorCenter regs)),
            .ifZero division.test
              (encodeNodeFields regs 2)
              (Cmd.seq
                (.basic
                  (.imm (ControlDecode.nodePayload0 regs) 2))
                (encodeNodeFields regs 2))])]

/-- Assemble the three-valued content-predecessor result produced by the
backward scan. -/
def installPrior
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .ifZero (centerValid regs)
    (installFailure regs)
    (.ifZero (priorFound regs)
      (installPriorSource regs)
      (installPriorComputation regs))

/-- Run the exact backward scan and immediately assemble its content child. -/
def scanAndInstallPrior
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (scanPrior workTapeCount controller regs)
    (installPrior regs)

/-- Copy the reconstructed center into the requested-block cell and adjust
it for one content predecessor slot. -/
def installRequestedBlock
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodGraph.Slot → Cmd
  | .lower =>
      Cmd.seq
        (ControlDecode.copy
          (requestedBlock regs) (centerValue regs))
        (.basic
          (.sub (requestedBlock regs)
            (requestedBlock regs) (movementDivision regs).one))
  | .center =>
      ControlDecode.copy
        (requestedBlock regs) (centerValue regs)
  | .upper =>
      Cmd.seq
        (ControlDecode.copy
          (requestedBlock regs) (centerValue regs))
        (.basic
          (.add (requestedBlock regs)
            (requestedBlock regs) (movementDivision regs).one))

/-- Reconstruct a current center, form one requested content block, and
install its greatest-prior predecessor. -/
def installContentChild
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (slot : NeighborhoodGraph.Slot) : Cmd :=
  Cmd.seq
    (deriveCenter workTapeCount controller regs)
    (.ifZero (centerValid regs)
      (installFailure regs)
      (Cmd.seq
        (installRequestedBlock regs slot)
        (scanAndInstallPrior workTapeCount controller regs)))

/-- Reconstruct the current center and install its chronological
predecessor. -/
def installChronologicalChild
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (deriveCenter workTapeCount controller regs)
    (installChronological regs)

/-- Dispatch a decoded predecessor-kind quotient.

The quotient is in `{0,1,2,3}` for an in-range child cursor.  Two destructive
decrements select lower content, center content, upper content, or
chronological predecessor in that order. -/
def dispatchDecodedChild
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let division := movementDivision regs
  .ifZero division.quotient
    (installContentChild workTapeCount controller regs .lower)
    (Cmd.seq
      (.basic
        (.sub division.quotient
          division.quotient division.one))
      (.ifZero division.quotient
        (installContentChild
          workTapeCount controller regs .center)
        (Cmd.seq
          (.basic
            (.sub division.quotient
              division.quotient division.one))
          (.ifZero division.quotient
            (installContentChild
              workTapeCount controller regs .upper)
            (installChronologicalChild
              workTapeCount controller regs)))))

/-- Decode a saved role-major child cursor and regenerate the corresponding
recursive query node. -/
def regenerateChild
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [decodeChildIndex workTapeCount regs,
      ControlDecode.copy
        (ControlDecode.nodeTape regs)
        (movementDivision regs).value,
      dispatchDecodedChild workTapeCount controller regs]

/-- Fixed write footprint of chronological child-node installation. -/
def chronologicalFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  priorFootprint regs ∪
    {ControlDecode.nodeTape regs} ∪
    nodeEncodingFootprint regs

/-- Exact observable result of chronological child-node installation. -/
structure InstallChronologicalPost
    (tape : TapeIndex workTapeCount) (interval : ℕ)
    (result : Option ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Packed node code is exactly the semantic chronological query. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) =
      FrameCodec.encodeNode
        (initial (Layout.chunkRadix regs))
        (chronologicalQueryValue
          (horizon := horizon) tape interval result)
  /-- The transient encoder digit is cleared. -/
  codecDigit_eq : final (Layout.codecDigit regs) = 0
  /-- Every address outside the fixed assembly footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ chronologicalFootprint regs →
      final address = initial address

/-- Fixed write footprint of content-predecessor installation. -/
def priorAssemblyFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  priorFootprint regs ∪
    {ControlDecode.nodeTape regs} ∪
    nodeEncodingFootprint regs

/-- Exact observable result of content-predecessor installation. -/
structure InstallPriorPost
    (tape : TapeIndex workTapeCount) (requested : ℕ)
    (result : Option (Option (ℕ × ℕ)))
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Packed node code is exactly the semantic content query. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) =
      FrameCodec.encodeNode
        (initial (Layout.chunkRadix regs))
        (priorQueryValue
          (horizon := horizon) tape requested result)
  /-- The transient encoder digit is cleared. -/
  codecDigit_eq : final (Layout.codecDigit regs) = 0
  /-- Every address outside the fixed assembly footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ priorAssemblyFootprint regs →
      final address = initial address

end ChildNode
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
