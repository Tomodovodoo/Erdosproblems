import ErdosProblems1066.PachToth.PeriodClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.FlexibleTransitionClosureW11
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11

set_option autoImplicit false

/-!
# W11 integrated period matrix

This module gathers the checked W11 period-equation, separation,
cross-block inequality, lower-bound, transition, and arbitrary target routes
that are available in the current tree.

All conclusions below remain conditional on an explicit data package.  Period
words, equation witnesses, separation witnesses, lower bounds, and route
certificates stay as visible fields of the package being consumed.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodIntegratedW11

noncomputable section

universe u

abbrev Candidate := PeriodClosureW11.Candidate

abbrev CheckedWordEquationPackage :=
  PeriodEquationSearchW11.CheckedWordEquationPackage

abbrev CheckedWordEquationFamily :=
  PeriodEquationSearchW11.CheckedWordEquationFamily

abbrev GeneratedFamilyRemainingFields :=
  PeriodClosureW11.GeneratedFamilyRemainingFields

abbrev CrossBlockLedgerClosureFields :=
  PeriodClosureW11.CrossBlockLedgerClosureFields

abbrev ExplicitLowerBoundClosureFields :=
  PeriodClosureW11.ExplicitLowerBoundClosureFields

abbrev ExactCandidatePeriodFields :=
  PeriodClosureW11.ExactCandidatePeriodFields

abbrev PeriodNonRigidRouteFields :=
  PeriodClosureW11.W11NonRigidRouteFields

abbrev TransitionRouteFields :=
  FlexibleTransitionClosureW11.TransitionRouteFields

abbrev TransitionRemainingFields :=
  FlexibleTransitionClosureW11.TransitionRemainingFields

abbrev SameOppositeCandidate :=
  FlexibleTransitionClosureW11.SameOppositeCandidate

abbrev InequalityPeriodFamily :=
  CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily

abbrev RawCrossBlockInequalityLedger :=
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger

abbrev CrossBlockClosureLedger :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger

abbrev ExactTargetAssumptions :=
  ArbitraryNTargetClosureW11.ExactTargetAssumptions

abbrev EventualSmallCaseAssumptions :=
  ArbitraryNTargetClosureW11.EventualSmallCaseAssumptions

abbrev ArbitraryNTargetFacade :=
  ArbitraryNTargetClosureW11.ArbitraryNTargetFacade

/-! ## Shared facades -/

/-- Eventual target obtained from a conditional arbitrary target. -/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

/-- Exact, eventual, fixed-`n`, arbitrary, and facade projections from one
explicit package shape. -/
structure TargetFacadeRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

/-- Eventual, fixed-`n`, arbitrary, and facade projections for threshold
packages that do not carry an exact block-family target. -/
structure EventualFacadeRow (alpha : Sort u) where
  vertexThreshold : alpha -> Nat
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

/-- A fixed exact-block projection for one checked period word. -/
structure FixedBlockTargetRow (alpha : Sort u) where
  vertexCount : alpha -> Nat
  fixedBlockTarget :
    forall a : alpha,
      PachToth.targetUpperConstructionFiveSixteenAt (vertexCount a)

/-- A positive block-family projection. -/
structure ExactBlockFamilyRow (alpha : Sort u) where
  exactBlockTarget :
    alpha -> forall k : Nat, 0 < k ->
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

def targetFacadeOfExactFixedArbitrary
    {alpha : Sort u}
    (fixedTarget :
      alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary)
    (a : alpha) :
    ArbitraryNTargetFacade where
  fixedTarget := fixedTarget a
  arbitraryTarget := arbitraryTarget a

def rowOfExactFixedEventualArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (fixedTarget :
      alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n)
    (eventualTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenEventually)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    TargetFacadeRow alpha where
  exactTarget := exactTarget
  eventualTarget := eventualTarget
  fixedTarget := fixedTarget
  arbitraryTarget := arbitraryTarget
  targetFacade :=
    targetFacadeOfExactFixedArbitrary fixedTarget arbitraryTarget

def rowOfExactFixedArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (fixedTarget :
      alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    TargetFacadeRow alpha :=
  rowOfExactFixedEventualArbitrary
    exactTarget
    fixedTarget
    (fun a => eventualTargetOfArbitrary (arbitraryTarget a))
    arbitraryTarget

def rowOfExactArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    TargetFacadeRow alpha :=
  rowOfExactFixedArbitrary
    exactTarget
    (fun a n =>
      (ArbitraryNTargetClosureW11.targetFacadeOfExactTargetAndArbitrary
        (exactTarget a) (arbitraryTarget a)).fixedTarget n)
    arbitraryTarget

def rowOfPeriodProjection
    {alpha : Type}
    (R : PeriodClosureW11.TargetProjectionRow alpha) :
    TargetFacadeRow alpha :=
  rowOfExactFixedEventualArbitrary
    R.exactTarget
    (fun a n =>
      (ArbitraryNTargetClosureW11.targetFacadeOfExactTargetAndArbitrary
        (R.exactTarget a) (R.arbitraryTarget a)).fixedTarget n)
    R.eventualTarget
    R.arbitraryTarget

def rowOfTransitionProjection
    {alpha : Sort u}
    (R : FlexibleTransitionClosureW11.StrongTargetRow alpha) :
    TargetFacadeRow alpha :=
  rowOfExactFixedEventualArbitrary
    R.exactTarget R.fixedTarget R.eventualTarget R.arbitraryTarget

def rowOfArbitraryExactProjection
    {alpha : Sort u}
    (R : ArbitraryNTargetClosureW11.ExactTargetClosureRow alpha) :
    TargetFacadeRow alpha :=
  rowOfExactFixedArbitrary R.exactTarget R.fixedTarget R.arbitraryTarget

def rowOfArbitraryEventualProjection
    {alpha : Sort u}
    (R : ArbitraryNTargetClosureW11.EventualSmallCaseClosureRow alpha) :
    EventualFacadeRow alpha where
  vertexThreshold := R.vertexThreshold
  eventualTarget := fun a =>
    Exists.intro (R.vertexThreshold a) (R.largeTarget a)
  fixedTarget := R.fixedTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

/-! ## Checked finite period words -/

/-- One checked finite period word together with the separation witness needed
to close its exact block target. -/
structure CheckedWordSeparationFields (T : Candidate) where
  checkedWord : CheckedWordEquationPackage T
  separated :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      T.toFigure2TransitionObligations
      checkedWord.positive_length
      BaseTransitionRealization.exactBase
      checkedWord.orientation

namespace CheckedWordSeparationFields

theorem targetUpperConstructionFiveSixteenAt
    {T : Candidate}
    (D : CheckedWordSeparationFields T) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * D.checkedWord.length) :=
  D.checkedWord.targetUpperConstructionFiveSixteenAt_exactBlock
    D.separated

end CheckedWordSeparationFields

def checkedWordSeparationRow
    (T : Candidate) :
    FixedBlockTargetRow (CheckedWordSeparationFields T) where
  vertexCount := fun D => 16 * D.checkedWord.length
  fixedBlockTarget := fun D =>
    D.targetUpperConstructionFiveSixteenAt

def explicitLowerBoundExactBlockRow
    (T : Candidate) :
    ExactBlockFamilyRow (ExplicitLowerBoundClosureFields T) where
  exactBlockTarget := fun D k hk =>
    D.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-! ## Period and inequality package rows -/

def separatedFamilyFieldsRow
    (T : Candidate) :
    TargetFacadeRow (GeneratedFamilyRemainingFields T) :=
  rowOfPeriodProjection (PeriodClosureW11.matrix.separatedFamilies T)

def crossBlockLedgerFieldsRow
    (T : Candidate) :
    TargetFacadeRow (CrossBlockLedgerClosureFields T) :=
  rowOfPeriodProjection (PeriodClosureW11.matrix.crossBlockLedgerClosures T)

def explicitLowerBoundFieldsRow
    (T : Candidate) :
    TargetFacadeRow (ExplicitLowerBoundClosureFields T) :=
  rowOfPeriodProjection (PeriodClosureW11.matrix.explicitLowerBoundClosures T)

def exactCandidatePeriodFieldsRow
    (T : Candidate) :
    TargetFacadeRow (ExactCandidatePeriodFields T) :=
  rowOfPeriodProjection (PeriodClosureW11.matrix.exactCandidatePeriods T)

def periodNonRigidRouteFieldsRow :
    TargetFacadeRow PeriodNonRigidRouteFields :=
  rowOfPeriodProjection PeriodClosureW11.matrix.nonRigidRoutes

def transitionRouteFieldsRow :
    TargetFacadeRow TransitionRouteFields :=
  rowOfTransitionProjection
    FlexibleTransitionClosureW11.matrix.transitionRouteTargets

def transitionRemainingFieldsRow
    (T : SameOppositeCandidate) :
    TargetFacadeRow (TransitionRemainingFields T) :=
  rowOfTransitionProjection
    (FlexibleTransitionClosureW11.matrix.transitionRemainingTargets T)

def toCrossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F where
  inequalityLedger := L

def crossBlockCheckedRemainderRow
    (F : InequalityPeriodFamily) :
    ArbitraryNBridgeW10.CheckedRemainderRouteRow
      (CrossBlockClosureLedger F) :=
  (CrossBlockInequalityClosureW11.conditionalTargetRouteLedger F)
    |>.crossBlockClosure

def crossBlockClosureLedgerRow
    (F : InequalityPeriodFamily) :
    TargetFacadeRow (CrossBlockClosureLedger F) :=
  rowOfExactFixedArbitrary
    (crossBlockCheckedRemainderRow F).exactTarget
    (crossBlockCheckedRemainderRow F).fixedTarget
    (crossBlockCheckedRemainderRow F).arbitraryTarget

def rawCrossBlockInequalityLedgerRow
    (F : InequalityPeriodFamily) :
    TargetFacadeRow (RawCrossBlockInequalityLedger F) :=
  rowOfExactFixedArbitrary
    (fun L =>
      (crossBlockClosureLedgerRow F).exactTarget
        (toCrossBlockClosureLedger L))
    (fun L n =>
      (crossBlockClosureLedgerRow F).fixedTarget
        (toCrossBlockClosureLedger L) n)
    (fun L =>
      (crossBlockClosureLedgerRow F).arbitraryTarget
        (toCrossBlockClosureLedger L))

def exactTargetAssumptionsRow :
    TargetFacadeRow ExactTargetAssumptions :=
  rowOfArbitraryExactProjection
    ArbitraryNTargetClosureW11.matrix.exactAssumptions

def eventualSmallCaseAssumptionsRow :
    EventualFacadeRow EventualSmallCaseAssumptions :=
  rowOfArbitraryEventualProjection
    ArbitraryNTargetClosureW11.matrix.eventualSmallCaseAssumptions

/-! ## Source ledger and integrated matrix -/

/-- Explicit source package shapes consumed by this period integration layer.
-/
structure SourcePackageLedger where
  checkedWordSeparationFields : Candidate -> Sort 1
  checkedWordEquationPackages : Candidate -> Sort 1
  checkedWordEquationFamilies : Candidate -> Sort 1
  separatedFamilyFields : Candidate -> Sort 1
  crossBlockLedgerFields : Candidate -> Sort 1
  explicitLowerBoundFields : Candidate -> Sort 1
  exactCandidatePeriodFields : Candidate -> Sort 1
  periodNonRigidRouteFields : Sort 1
  transitionRouteFields : Sort 1
  transitionRemainingFields : SameOppositeCandidate -> Sort 1
  rawCrossBlockInequalityLedgers : InequalityPeriodFamily -> Sort 1
  crossBlockClosureLedgers : InequalityPeriodFamily -> Sort 1
  exactTargetAssumptions : Prop
  eventualSmallCaseAssumptions : Type

def sourcePackageLedger : SourcePackageLedger where
  checkedWordSeparationFields := CheckedWordSeparationFields
  checkedWordEquationPackages := CheckedWordEquationPackage
  checkedWordEquationFamilies := CheckedWordEquationFamily
  separatedFamilyFields := GeneratedFamilyRemainingFields
  crossBlockLedgerFields := CrossBlockLedgerClosureFields
  explicitLowerBoundFields := ExplicitLowerBoundClosureFields
  exactCandidatePeriodFields := ExactCandidatePeriodFields
  periodNonRigidRouteFields := PeriodNonRigidRouteFields
  transitionRouteFields := TransitionRouteFields
  transitionRemainingFields := TransitionRemainingFields
  rawCrossBlockInequalityLedgers := RawCrossBlockInequalityLedger
  crossBlockClosureLedgers := CrossBlockClosureLedger
  exactTargetAssumptions := ExactTargetAssumptions
  eventualSmallCaseAssumptions := EventualSmallCaseAssumptions

/-- Integrated W11 period routing matrix. -/
structure Matrix where
  sources : SourcePackageLedger
  periodEquationSearch : PeriodEquationSearchW11.Matrix
  periodClosure : PeriodClosureW11.Matrix
  crossBlockRoutes :
    forall F : InequalityPeriodFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  transitionClosure : FlexibleTransitionClosureW11.Matrix
  arbitraryTargetClosure : ArbitraryNTargetClosureW11.Matrix
  checkedWordSeparation :
    forall T : Candidate,
      FixedBlockTargetRow (CheckedWordSeparationFields T)
  explicitLowerBoundExactBlocks :
    forall T : Candidate,
      ExactBlockFamilyRow (ExplicitLowerBoundClosureFields T)
  separatedFamilies :
    forall T : Candidate,
      TargetFacadeRow (GeneratedFamilyRemainingFields T)
  crossBlockLedgerFields :
    forall T : Candidate,
      TargetFacadeRow (CrossBlockLedgerClosureFields T)
  explicitLowerBoundFields :
    forall T : Candidate,
      TargetFacadeRow (ExplicitLowerBoundClosureFields T)
  exactCandidatePeriodFields :
    forall T : Candidate,
      TargetFacadeRow (ExactCandidatePeriodFields T)
  periodNonRigidRouteFields :
    TargetFacadeRow PeriodNonRigidRouteFields
  transitionRouteFields :
    TargetFacadeRow TransitionRouteFields
  transitionRemainingFields :
    forall T : SameOppositeCandidate,
      TargetFacadeRow (TransitionRemainingFields T)
  rawCrossBlockInequalityLedgers :
    forall F : InequalityPeriodFamily,
      TargetFacadeRow (RawCrossBlockInequalityLedger F)
  crossBlockClosureLedgers :
    forall F : InequalityPeriodFamily,
      TargetFacadeRow (CrossBlockClosureLedger F)
  exactTargetAssumptions :
    TargetFacadeRow ExactTargetAssumptions
  eventualSmallCaseAssumptions :
    EventualFacadeRow EventualSmallCaseAssumptions

def matrix : Matrix where
  sources := sourcePackageLedger
  periodEquationSearch := PeriodEquationSearchW11.matrix
  periodClosure := PeriodClosureW11.matrix
  crossBlockRoutes :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  transitionClosure := FlexibleTransitionClosureW11.matrix
  arbitraryTargetClosure := ArbitraryNTargetClosureW11.matrix
  checkedWordSeparation := checkedWordSeparationRow
  explicitLowerBoundExactBlocks := explicitLowerBoundExactBlockRow
  separatedFamilies := separatedFamilyFieldsRow
  crossBlockLedgerFields := crossBlockLedgerFieldsRow
  explicitLowerBoundFields := explicitLowerBoundFieldsRow
  exactCandidatePeriodFields := exactCandidatePeriodFieldsRow
  periodNonRigidRouteFields := periodNonRigidRouteFieldsRow
  transitionRouteFields := transitionRouteFieldsRow
  transitionRemainingFields := transitionRemainingFieldsRow
  rawCrossBlockInequalityLedgers := rawCrossBlockInequalityLedgerRow
  crossBlockClosureLedgers := crossBlockClosureLedgerRow
  exactTargetAssumptions := exactTargetAssumptionsRow
  eventualSmallCaseAssumptions := eventualSmallCaseAssumptionsRow

/-! ## Public projections -/

theorem targetUpperConstructionFiveSixteenAt_of_checkedWordSeparation
    {T : Candidate}
    (D : CheckedWordSeparationFields T) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * D.checkedWord.length) :=
  (matrix.checkedWordSeparation T).fixedBlockTarget D

theorem targetUpperConstructionFiveSixteen_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.separatedFamilies T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.separatedFamilies T).eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.separatedFamilies T).fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.separatedFamilies T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockLedgerFields T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLedgerFields T).eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.crossBlockLedgerFields T).fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLedgerFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.explicitLowerBoundExactBlocks T).exactBlockTarget D k hk

theorem targetUpperConstructionFiveSixteen_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.explicitLowerBoundFields T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.explicitLowerBoundFields T).eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.explicitLowerBoundFields T).fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.explicitLowerBoundFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.exactCandidatePeriodFields T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.exactCandidatePeriodFields T).eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.exactCandidatePeriodFields T).fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.exactCandidatePeriodFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.periodNonRigidRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.periodNonRigidRouteFields.eventualTarget R

theorem targetUpperConstructionFiveSixteenAt_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.periodNonRigidRouteFields.fixedTarget R n

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.periodNonRigidRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.transitionRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.transitionRouteFields.eventualTarget R

theorem targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
    (R : TransitionRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.transitionRouteFields.fixedTarget R n

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.rawCrossBlockInequalityLedgers F).exactTarget L

theorem targetUpperConstructionFiveSixteenEventually_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.rawCrossBlockInequalityLedgers F).eventualTarget L

theorem targetUpperConstructionFiveSixteenAt_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.rawCrossBlockInequalityLedgers F).fixedTarget L n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.rawCrossBlockInequalityLedgers F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockClosureLedgers F).exactTarget L

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockClosureLedgers F).eventualTarget L

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.crossBlockClosureLedgers F).fixedTarget L n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockClosureLedgers F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_exactTargetAssumptions
    (A : ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.exactTargetAssumptions.exactTarget A

theorem targetUpperConstructionFiveSixteenAt_of_exactTargetAssumptions
    (A : ExactTargetAssumptions) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.exactTargetAssumptions.fixedTarget A n

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTargetAssumptions
    (A : ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactTargetAssumptions.arbitraryTarget A

theorem
    targetUpperConstructionFiveSixteenEventually_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.eventualSmallCaseAssumptions.eventualTarget A

theorem targetUpperConstructionFiveSixteenAt_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.eventualSmallCaseAssumptions.fixedTarget A n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualSmallCaseAssumptions.arbitraryTarget A

end

end PeriodIntegratedW11
end PachToth
end ErdosProblems1066
