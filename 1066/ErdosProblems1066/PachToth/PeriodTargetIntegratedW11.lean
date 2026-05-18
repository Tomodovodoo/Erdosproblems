import ErdosProblems1066.PachToth.PeriodIntegratedW11
import ErdosProblems1066.PachToth.PeriodClosureW11
import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 period target integration

This module is a target-facing aggregate over the W11 period route layers.
It keeps the word, separation, lower-bound, and exact-candidate packages as
explicit inputs, then records only conditional projections from those packages
to the Pach--Toth target forms.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodTargetIntegratedW11

noncomputable section

universe u

abbrev Candidate := PeriodIntegratedW11.Candidate

abbrev CheckedWordEquationPackage :=
  PeriodIntegratedW11.CheckedWordEquationPackage

abbrev CheckedWordEquationFamily :=
  PeriodIntegratedW11.CheckedWordEquationFamily

abbrev CheckedWordSeparationFields
    (T : Candidate) :=
  PeriodIntegratedW11.CheckedWordSeparationFields T

abbrev GeneratedFamilyRemainingFields
    (T : Candidate) :=
  PeriodIntegratedW11.GeneratedFamilyRemainingFields T

abbrev CrossBlockLedgerClosureFields
    (T : Candidate) :=
  PeriodIntegratedW11.CrossBlockLedgerClosureFields T

abbrev ExplicitLowerBoundClosureFields
    (T : Candidate) :=
  PeriodIntegratedW11.ExplicitLowerBoundClosureFields T

abbrev ExactCandidatePeriodFields
    (T : Candidate) :=
  PeriodIntegratedW11.ExactCandidatePeriodFields T

abbrev PeriodNonRigidRouteFields :=
  PeriodIntegratedW11.PeriodNonRigidRouteFields

abbrev SameOppositeCandidate :=
  PeriodIntegratedW11.SameOppositeCandidate

abbrev TransitionRemainingFields
    (T : SameOppositeCandidate) :=
  PeriodIntegratedW11.TransitionRemainingFields T

abbrev TransitionRouteFields :=
  PeriodIntegratedW11.TransitionRouteFields

abbrev InequalityPeriodFamily :=
  PeriodIntegratedW11.InequalityPeriodFamily

abbrev RawCrossBlockInequalityLedger
    (F : InequalityPeriodFamily) :=
  PeriodIntegratedW11.RawCrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : InequalityPeriodFamily) :=
  PeriodIntegratedW11.CrossBlockClosureLedger F

abbrev ExactTargetAssumptions :=
  PeriodIntegratedW11.ExactTargetAssumptions

abbrev EventualSmallCaseAssumptions :=
  PeriodIntegratedW11.EventualSmallCaseAssumptions

abbrev ArbitraryNTargetFacade :=
  PeriodIntegratedW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNIntegratedW11.ThresholdTargetFacade

abbrev CrossBlockIntegratedFamily :=
  CrossBlockIntegratedW11.PeriodSearchFamily

abbrev CrossBlockIntegratedInequalityLedger
    (F : CrossBlockIntegratedFamily) :=
  CrossBlockIntegratedW11.CrossBlockInequalityLedger F

abbrev CrossBlockIntegratedClosureLedger
    (F : CrossBlockIntegratedFamily) :=
  CrossBlockIntegratedW11.CrossBlockClosureLedger F

/-! ## Shared target routes -/

/-- A conditional route from an explicit package to all standard target
facades used by the period layer. -/
structure TargetRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

namespace TargetRoute

/-- Promote an arbitrary-`n` target to an eventual target with threshold zero.
-/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

/-- Reuse a period-integrated facade row as a target-facing route. -/
def ofPeriodFacadeRow
    {alpha : Sort u}
    (R : PeriodIntegratedW11.TargetFacadeRow alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

/-- Reuse a cross-block checked target row as a target-facing route. -/
def ofCrossBlockCheckedTargetRow
    {alpha : Sort u}
    (R : CrossBlockIntegratedW11.CheckedTargetRow alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget
  targetFacade := fun a =>
    { fixedTarget := R.fixedTarget a
      arbitraryTarget := R.arbitraryTarget a }

end TargetRoute

/-- A row that has exact, eventual, and arbitrary conclusions but no exposed
all-`n` facade.  This is used for the source-facing transition aggregate. -/
structure ConditionalTargetRoute (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

def conditionalRouteOfTransitionRow
    {alpha : Type}
    (R : TransitionIntegratedW11.ConditionalTargetRow alpha) :
    ConditionalTargetRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-! ## Explicit period row shapes -/

/-- One checked period word together with the separation witness needed for
the exact block target at its displayed length. -/
structure CheckedWordTargetRoute (T : Candidate) where
  length : CheckedWordSeparationFields T -> Nat
  positiveLength :
    forall D : CheckedWordSeparationFields T, 0 < length D
  word :
    forall D : CheckedWordSeparationFields T,
      OrientationWord.Word (length D)
  orientation :
    forall D : CheckedWordSeparationFields T,
      Fin (length D) -> PeriodEquationSearchW11.Orientation
  separated :
    forall D : CheckedWordSeparationFields T,
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        (positiveLength D)
        BaseTransitionRealization.exactBase
        (orientation D)
  exactBlockTarget :
    forall D : CheckedWordSeparationFields T,
      PachToth.targetUpperConstructionFiveSixteenAt (16 * length D)

/-- A period family whose checked words are separated for every positive block
count, together with the resulting target route. -/
structure SeparatedFamilyTargetRoute
    (T : Candidate) (alpha : Sort u) : Sort (max 1 u) where
  period : alpha -> CheckedWordEquationFamily T
  word :
    forall _a : alpha, forall k : Nat, 0 < k -> OrientationWord.Word k
  separated :
    forall a : alpha, forall k : Nat, forall hk : 0 < k,
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word a k hk).toFin)
  exactBlockTarget :
    alpha -> forall k : Nat, forall _hk : 0 < k,
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  route : TargetRoute alpha

/-- A period family closed by explicit lower bounds. -/
structure LowerBoundTargetRoute
    (T : Candidate) (alpha : Sort u) : Sort (max 1 u) where
  period : alpha -> CheckedWordEquationFamily T
  lower :
    alpha -> forall (k : Nat), 0 < k ->
      Fin k -> FiniteGraph.LocalVertex ->
      Fin k -> FiniteGraph.LocalVertex -> Real
  lowerGeOne :
    forall a : alpha, forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : FiniteGraph.LocalVertex)
      (j : Fin k) (v : FiniteGraph.LocalVertex),
        Ne i j -> 1 <= lower a k hk i u j v
  exactBlockTarget :
    alpha -> forall k : Nat, forall _hk : 0 < k,
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  route : TargetRoute alpha

/-- Exact-candidate data keeps the checked period family visible beside its
conditional target route. -/
structure ExactCandidateTargetRoute
    (T : Candidate) (alpha : Sort u) : Sort (max 1 u) where
  period : alpha -> CheckedWordEquationFamily T
  route : TargetRoute alpha

/-- A threshold row for eventual plus finite-small-case data. -/
structure EventualTargetRoute (alpha : Sort u) : Sort (max 1 u) where
  vertexThreshold : alpha -> Nat
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  largeTarget :
    forall a : alpha, forall n : Nat, vertexThreshold a <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

/-! ## Row builders -/

def checkedWordTargetRoute
    (T : Candidate) :
    CheckedWordTargetRoute T where
  length := fun D => D.checkedWord.length
  positiveLength := fun D => D.checkedWord.positive_length
  word := fun D => D.checkedWord.word
  orientation := fun D => D.checkedWord.orientation
  separated := fun D => D.separated
  exactBlockTarget := fun D =>
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenAt_of_checkedWordSeparation
      D

def separatedFamilyTargetRoute
    (T : Candidate) :
    SeparatedFamilyTargetRoute T (GeneratedFamilyRemainingFields T) where
  period := fun D => D.period
  word := fun D k hk => D.period.word k hk
  separated := fun D k hk => D.separated k hk
  exactBlockTarget := fun D k hk =>
    (D.period.package k hk).targetUpperConstructionFiveSixteenAt_exactBlock
      (D.separated k hk)
  route :=
    TargetRoute.ofPeriodFacadeRow
      (PeriodIntegratedW11.matrix.separatedFamilies T)

def crossBlockLedgerFieldsTargetRoute
    (T : Candidate) :
    SeparatedFamilyTargetRoute T (CrossBlockLedgerClosureFields T) where
  period := fun D => D.period
  word := fun D k hk => D.period.word k hk
  separated := fun D k hk => D.separated k hk
  exactBlockTarget := fun D k hk =>
    (D.period.package k hk).targetUpperConstructionFiveSixteenAt_exactBlock
      (D.separated k hk)
  route :=
    TargetRoute.ofPeriodFacadeRow
      (PeriodIntegratedW11.matrix.crossBlockLedgerFields T)

def explicitLowerBoundTargetRoute
    (T : Candidate) :
    LowerBoundTargetRoute T (ExplicitLowerBoundClosureFields T) where
  period := fun D => D.period
  lower := fun D => D.lower
  lowerGeOne := fun D => D.lower_ge_one
  exactBlockTarget := fun D k hk =>
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundFields
      D k hk
  route :=
    TargetRoute.ofPeriodFacadeRow
      (PeriodIntegratedW11.matrix.explicitLowerBoundFields T)

def exactCandidateTargetRoute
    (T : Candidate) :
    ExactCandidateTargetRoute T (ExactCandidatePeriodFields T) where
  period := fun D => D.period
  route :=
    TargetRoute.ofPeriodFacadeRow
      (PeriodIntegratedW11.matrix.exactCandidatePeriodFields T)

def periodNonRigidTargetRoute :
    TargetRoute PeriodNonRigidRouteFields :=
  TargetRoute.ofPeriodFacadeRow
    PeriodIntegratedW11.matrix.periodNonRigidRouteFields

def transitionRemainingTargetRoute
    (T : SameOppositeCandidate) :
    TargetRoute (TransitionRemainingFields T) :=
  TargetRoute.ofPeriodFacadeRow
    (PeriodIntegratedW11.matrix.transitionRemainingFields T)

def transitionRouteTargetRoute :
    TargetRoute TransitionRouteFields :=
  TargetRoute.ofPeriodFacadeRow
    PeriodIntegratedW11.matrix.transitionRouteFields

def rawCrossBlockInequalityLedgerTargetRoute
    (F : InequalityPeriodFamily) :
    TargetRoute (RawCrossBlockInequalityLedger F) :=
  TargetRoute.ofPeriodFacadeRow
    (PeriodIntegratedW11.matrix.rawCrossBlockInequalityLedgers F)

def crossBlockClosureLedgerTargetRoute
    (F : InequalityPeriodFamily) :
    TargetRoute (CrossBlockClosureLedger F) :=
  TargetRoute.ofPeriodFacadeRow
    (PeriodIntegratedW11.matrix.crossBlockClosureLedgers F)

def exactTargetAssumptionsRoute :
    TargetRoute ExactTargetAssumptions :=
  TargetRoute.ofPeriodFacadeRow
    PeriodIntegratedW11.matrix.exactTargetAssumptions

def eventualSmallCaseAssumptionsRoute :
    EventualTargetRoute EventualSmallCaseAssumptions where
  vertexThreshold := PeriodIntegratedW11.matrix.eventualSmallCaseAssumptions.vertexThreshold
  fixedTarget := PeriodIntegratedW11.matrix.eventualSmallCaseAssumptions.fixedTarget
  largeTarget := fun A n hn =>
    (ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions).largeTarget
      A n hn
  arbitraryTarget :=
    PeriodIntegratedW11.matrix.eventualSmallCaseAssumptions.arbitraryTarget
  targetFacade := PeriodIntegratedW11.matrix.eventualSmallCaseAssumptions.targetFacade

/-! ## Cross-block and transition aggregate routes -/

/-- Cross-block integrated ledger rows expose separation, exact block targets,
and checked target routes. -/
structure CrossBlockIntegratedLedgerRoute
    (F : CrossBlockIntegratedFamily) (alpha : Sort u) :
    Sort (max 1 u) where
  separated :
    alpha -> forall k : Nat, forall hk : 0 < k,
      CrossBlockIntegratedW11.GeneratedGlobalSeparationAt F k hk
  exactBlockTarget :
    alpha -> forall k : Nat, forall _hk : 0 < k,
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  route : TargetRoute alpha

def crossBlockIntegratedInequalityLedgerRoute
    (F : CrossBlockIntegratedFamily) :
    CrossBlockIntegratedLedgerRoute F
      (CrossBlockIntegratedInequalityLedger F) where
  separated := (CrossBlockIntegratedW11.matrix.inequalityLedgers F).separated
  exactBlockTarget :=
    (CrossBlockIntegratedW11.matrix.inequalityLedgers F).exactBlockTarget
  route :=
    TargetRoute.ofCrossBlockCheckedTargetRow
      (CrossBlockIntegratedW11.matrix.inequalityLedgers F).checkedTargets

def crossBlockIntegratedClosureLedgerRoute
    (F : CrossBlockIntegratedFamily) :
    CrossBlockIntegratedLedgerRoute F
      (CrossBlockIntegratedClosureLedger F) where
  separated := (CrossBlockIntegratedW11.matrix.closureLedgers F).separated
  exactBlockTarget :=
    (CrossBlockIntegratedW11.matrix.closureLedgers F).exactBlockTarget
  route :=
    TargetRoute.ofCrossBlockCheckedTargetRow
      (CrossBlockIntegratedW11.matrix.closureLedgers F).checkedTargets

/-! ## Explicit input ledger -/

/-- Source package shapes consumed by the period target aggregate. -/
structure ExplicitPeriodTargetInputs where
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
  crossBlockIntegratedInequalityLedgers :
    CrossBlockIntegratedFamily -> Type
  crossBlockIntegratedClosureLedgers :
    CrossBlockIntegratedFamily -> Type

def explicitPeriodTargetInputs : ExplicitPeriodTargetInputs where
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
  crossBlockIntegratedInequalityLedgers :=
    CrossBlockIntegratedInequalityLedger
  crossBlockIntegratedClosureLedgers :=
    CrossBlockIntegratedClosureLedger

/-! ## Imported checked ledgers -/

/-- Checked W11 matrices used by this target-facing aggregate. -/
structure ImportedPeriodTargetLedgers where
  periodIntegrated : PeriodIntegratedW11.Matrix
  periodClosure : PeriodClosureW11.Matrix
  transitionIntegrated : TransitionIntegratedW11.Matrix
  arbitraryNIntegrated : ArbitraryNIntegratedW11.Matrix
  crossBlockIntegrated : CrossBlockIntegratedW11.Matrix
  pachTothIntegrated : PachTothW11IntegratedMatrix.Matrix

def importedPeriodTargetLedgers : ImportedPeriodTargetLedgers where
  periodIntegrated := PeriodIntegratedW11.matrix
  periodClosure := PeriodClosureW11.matrix
  transitionIntegrated := TransitionIntegratedW11.matrix
  arbitraryNIntegrated := ArbitraryNIntegratedW11.matrix
  crossBlockIntegrated := CrossBlockIntegratedW11.matrix
  pachTothIntegrated := PachTothW11IntegratedMatrix.matrix

/-! ## Target row groups and matrix -/

/-- Target-facing rows for period-specific source packages. -/
structure PeriodTargetRows where
  checkedWordSeparation :
    forall T : Candidate, CheckedWordTargetRoute T
  separatedFamilies :
    forall T : Candidate,
      SeparatedFamilyTargetRoute T (GeneratedFamilyRemainingFields T)
  crossBlockLedgerFields :
    forall T : Candidate,
      SeparatedFamilyTargetRoute T (CrossBlockLedgerClosureFields T)
  explicitLowerBoundFields :
    forall T : Candidate,
      LowerBoundTargetRoute T (ExplicitLowerBoundClosureFields T)
  exactCandidatePeriodFields :
    forall T : Candidate,
      ExactCandidateTargetRoute T (ExactCandidatePeriodFields T)
  periodNonRigidRouteFields :
    TargetRoute PeriodNonRigidRouteFields

def periodTargetRows : PeriodTargetRows where
  checkedWordSeparation := checkedWordTargetRoute
  separatedFamilies := separatedFamilyTargetRoute
  crossBlockLedgerFields := crossBlockLedgerFieldsTargetRoute
  explicitLowerBoundFields := explicitLowerBoundTargetRoute
  exactCandidatePeriodFields := exactCandidateTargetRoute
  periodNonRigidRouteFields := periodNonRigidTargetRoute

/-- Adjacent W11 routes imported into the period target aggregate. -/
structure AdjacentTargetRows where
  transitionIntegratedRoute :
    ConditionalTargetRoute TransitionIntegratedW11.TransitionRouteFields
  transitionRouteFields : TargetRoute TransitionRouteFields
  transitionRemainingFields :
    forall T : SameOppositeCandidate,
      TargetRoute (TransitionRemainingFields T)
  rawCrossBlockInequalityLedgers :
    forall F : InequalityPeriodFamily,
      TargetRoute (RawCrossBlockInequalityLedger F)
  crossBlockClosureLedgers :
    forall F : InequalityPeriodFamily,
      TargetRoute (CrossBlockClosureLedger F)
  exactTargetAssumptions : TargetRoute ExactTargetAssumptions
  eventualSmallCaseAssumptions :
    EventualTargetRoute EventualSmallCaseAssumptions
  crossBlockIntegratedInequalityLedgers :
    forall F : CrossBlockIntegratedFamily,
      CrossBlockIntegratedLedgerRoute F
        (CrossBlockIntegratedInequalityLedger F)
  crossBlockIntegratedClosureLedgers :
    forall F : CrossBlockIntegratedFamily,
      CrossBlockIntegratedLedgerRoute F
        (CrossBlockIntegratedClosureLedger F)

def adjacentTargetRows : AdjacentTargetRows where
  transitionIntegratedRoute :=
    conditionalRouteOfTransitionRow
      TransitionIntegratedW11.matrix.transitionRouteFields
  transitionRouteFields := transitionRouteTargetRoute
  transitionRemainingFields := transitionRemainingTargetRoute
  rawCrossBlockInequalityLedgers := rawCrossBlockInequalityLedgerTargetRoute
  crossBlockClosureLedgers := crossBlockClosureLedgerTargetRoute
  exactTargetAssumptions := exactTargetAssumptionsRoute
  eventualSmallCaseAssumptions := eventualSmallCaseAssumptionsRoute
  crossBlockIntegratedInequalityLedgers :=
    crossBlockIntegratedInequalityLedgerRoute
  crossBlockIntegratedClosureLedgers :=
    crossBlockIntegratedClosureLedgerRoute

/-- Target-facing W11 period integration matrix.

The matrix stores route functions only.  Each public target projection below
remains conditional on one of the explicit input packages in `requiredInputs`.
-/
structure Matrix where
  requiredInputs : ExplicitPeriodTargetInputs
  importedLedgers : ImportedPeriodTargetLedgers
  periodRows : PeriodTargetRows
  adjacentRows : AdjacentTargetRows

/-- The checked target-facing W11 period integration matrix. -/
def matrix : Matrix where
  requiredInputs := explicitPeriodTargetInputs
  importedLedgers := importedPeriodTargetLedgers
  periodRows := periodTargetRows
  adjacentRows := adjacentTargetRows

/-! ## Public period projections -/

theorem targetUpperConstructionFiveSixteenAt_of_checkedWordSeparation
    {T : Candidate}
    (D : CheckedWordSeparationFields T) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * D.checkedWord.length) :=
  (matrix.periodRows.checkedWordSeparation T).exactBlockTarget D

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.periodRows.separatedFamilies T).exactBlockTarget D k hk

theorem targetUpperConstructionFiveSixteen_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodRows.separatedFamilies T).route.exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.periodRows.separatedFamilies T).route.eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.periodRows.separatedFamilies T).route.fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodRows.separatedFamilies T).route.arbitraryTarget D

def targetFacade_of_separatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    ArbitraryNTargetFacade :=
  (matrix.periodRows.separatedFamilies T).route.targetFacade D

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.periodRows.crossBlockLedgerFields T).exactBlockTarget D k hk

theorem targetUpperConstructionFiveSixteen_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodRows.crossBlockLedgerFields T).route.exactTarget D

theorem
    targetUpperConstructionFiveSixteenEventually_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.periodRows.crossBlockLedgerFields T).route.eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.periodRows.crossBlockLedgerFields T).route.fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodRows.crossBlockLedgerFields T).route.arbitraryTarget D

def targetFacade_of_crossBlockLedgerFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    ArbitraryNTargetFacade :=
  (matrix.periodRows.crossBlockLedgerFields T).route.targetFacade D

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.periodRows.explicitLowerBoundFields T).exactBlockTarget D k hk

theorem targetUpperConstructionFiveSixteen_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodRows.explicitLowerBoundFields T).route.exactTarget D

theorem
    targetUpperConstructionFiveSixteenEventually_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.periodRows.explicitLowerBoundFields T).route.eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.periodRows.explicitLowerBoundFields T).route.fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodRows.explicitLowerBoundFields T).route.arbitraryTarget D

def targetFacade_of_explicitLowerBoundFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    ArbitraryNTargetFacade :=
  (matrix.periodRows.explicitLowerBoundFields T).route.targetFacade D

theorem targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodRows.exactCandidatePeriodFields T).route.exactTarget D

theorem
    targetUpperConstructionFiveSixteenEventually_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.periodRows.exactCandidatePeriodFields T).route.eventualTarget D

theorem targetUpperConstructionFiveSixteenAt_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.periodRows.exactCandidatePeriodFields T).route.fixedTarget D n

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodRows.exactCandidatePeriodFields T).route.arbitraryTarget D

def targetFacade_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    ArbitraryNTargetFacade :=
  (matrix.periodRows.exactCandidatePeriodFields T).route.targetFacade D

/-! ## Public adjacent projections -/

theorem targetUpperConstructionFiveSixteen_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.periodRows.periodNonRigidRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.periodRows.periodNonRigidRouteFields.eventualTarget R

theorem targetUpperConstructionFiveSixteenAt_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.periodRows.periodNonRigidRouteFields.fixedTarget R n

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.periodRows.periodNonRigidRouteFields.arbitraryTarget R

def targetFacade_of_periodNonRigidRouteFields
    (R : PeriodNonRigidRouteFields) :
    ArbitraryNTargetFacade :=
  matrix.periodRows.periodNonRigidRouteFields.targetFacade R

theorem targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.adjacentRows.transitionRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.adjacentRows.transitionRouteFields.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.adjacentRows.transitionRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
    (R : TransitionRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.adjacentRows.transitionRouteFields.fixedTarget R n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.adjacentRows.crossBlockClosureLedgers F).arbitraryTarget C

def targetFacade_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.adjacentRows.crossBlockClosureLedgers F).targetFacade C

theorem targetUpperConstructionFiveSixteenAt_of_exactTargetAssumptions
    (A : ExactTargetAssumptions) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.adjacentRows.exactTargetAssumptions.fixedTarget A n

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTargetAssumptions
    (A : ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.adjacentRows.exactTargetAssumptions.arbitraryTarget A

def targetFacade_of_exactTargetAssumptions
    (A : ExactTargetAssumptions) :
    ArbitraryNTargetFacade :=
  matrix.adjacentRows.exactTargetAssumptions.targetFacade A

theorem
    targetUpperConstructionFiveSixteenEventually_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  PeriodIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_eventualSmallCaseAssumptions
    A

theorem targetUpperConstructionFiveSixteenAt_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.adjacentRows.eventualSmallCaseAssumptions.fixedTarget A n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.adjacentRows.eventualSmallCaseAssumptions.arbitraryTarget A

def targetFacade_of_eventualSmallCaseAssumptions
    (A : EventualSmallCaseAssumptions) :
    ArbitraryNTargetFacade :=
  matrix.adjacentRows.eventualSmallCaseAssumptions.targetFacade A

/-! ## Public cross-block integrated projections -/

theorem separated_of_crossBlockIntegratedInequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockIntegratedW11.GeneratedGlobalSeparationAt F k hk :=
  (matrix.adjacentRows.crossBlockIntegratedInequalityLedgers F).separated
    L k hk

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockIntegratedInequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.adjacentRows.crossBlockIntegratedInequalityLedgers F).exactBlockTarget
    L k hk

theorem targetUpperConstructionFiveSixteen_of_crossBlockIntegratedInequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.adjacentRows.crossBlockIntegratedInequalityLedgers F).route.exactTarget
    L

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockIntegratedInequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.adjacentRows.crossBlockIntegratedInequalityLedgers F).route.fixedTarget
    L n

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_crossBlockIntegratedInequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.adjacentRows.crossBlockIntegratedInequalityLedgers F).route.arbitraryTarget
    L

def targetFacade_of_crossBlockIntegratedInequalityLedger
    {F : CrossBlockIntegratedFamily}
    (L : CrossBlockIntegratedInequalityLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.adjacentRows.crossBlockIntegratedInequalityLedgers F).route.targetFacade
    L

end

end PeriodTargetIntegratedW11
end PachToth
end ErdosProblems1066
