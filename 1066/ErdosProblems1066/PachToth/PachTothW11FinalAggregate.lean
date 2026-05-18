import ErdosProblems1066.PachToth.PachTothW11FinalConsistency
import ErdosProblems1066.PachToth.ArbitraryNFinalIntegratedW11
import ErdosProblems1066.PachToth.GeneratedFinalIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.PeriodTargetIntegratedW11
import ErdosProblems1066.PachToth.SmallLengthFinalIntegratedW11

set_option autoImplicit false

/-!
# W11 Pach--Toth final aggregate ledger

This file is the terminal aggregate ledger for the checked W11 Pach--Toth
conditional route files present in this checkout.  It records the imported
final matrices, exposes the remaining numeric, period, cross-block, and
large-chain input shapes, and provides only package-indexed target projections.

No target theorem below removes the displayed input package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW11FinalAggregate

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! ## Availability ledger -/

/-- Whether an optional final aggregate exists as a checked Lean module in
this checkout. -/
inductive LedgerAvailability where
  | present
  | absent

/-- Final aggregate modules requested by the W11 task, including the missing
period-final module as an explicit status bit. -/
structure FinalLedgerAvailability where
  finalConsistency : LedgerAvailability
  arbitraryNFinal : LedgerAvailability
  generatedFinal : LedgerAvailability
  crossBlockFinal : LedgerAvailability
  transitionFinal : LedgerAvailability
  periodFinal : LedgerAvailability
  periodTarget : LedgerAvailability
  smallLengthFinal : LedgerAvailability

/-- Availability of the W11 final ledgers in this checkout. -/
def finalLedgerAvailability : FinalLedgerAvailability where
  finalConsistency := LedgerAvailability.present
  arbitraryNFinal := LedgerAvailability.present
  generatedFinal := LedgerAvailability.present
  crossBlockFinal := LedgerAvailability.present
  transitionFinal := LedgerAvailability.present
  periodFinal := LedgerAvailability.absent
  periodTarget := LedgerAvailability.present
  smallLengthFinal := LedgerAvailability.present

theorem periodFinalIntegratedW11_absent :
    finalLedgerAvailability.periodFinal = LedgerAvailability.absent :=
  rfl

/-! ## Imported checked ledgers -/

/-- All checked W11 Pach--Toth matrices imported by this aggregate. -/
structure ImportedCheckedLedgers where
  finalConsistency : PachTothW11FinalConsistency.Matrix
  integrated : PachTothW11IntegratedMatrix.Matrix
  arbitraryNFinal : ArbitraryNFinalIntegratedW11.Matrix
  generatedFinal : GeneratedFinalIntegratedW11.Matrix
  crossBlockFinal : CrossBlockFinalIntegratedW11.Matrix
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  periodIntegrated : PeriodIntegratedW11.Matrix
  periodTarget : PeriodTargetIntegratedW11.Matrix
  smallLengthFinal : SmallLengthFinalIntegratedW11.Matrix

/-- Imported checked W11 Pach--Toth ledgers. -/
def importedCheckedLedgers : ImportedCheckedLedgers where
  finalConsistency := PachTothW11FinalConsistency.matrix
  integrated := PachTothW11IntegratedMatrix.matrix
  arbitraryNFinal := ArbitraryNFinalIntegratedW11.matrix
  generatedFinal := GeneratedFinalIntegratedW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  transitionFinal := TransitionFinalIntegratedW11.matrix
  periodIntegrated := PeriodIntegratedW11.matrix
  periodTarget := PeriodTargetIntegratedW11.matrix
  smallLengthFinal := SmallLengthFinalIntegratedW11.matrix

/-! ## Explicit missing data ledgers -/

/-- Exact small numeric targets and threshold values that remain supplied data. -/
structure ExplicitSmallNumericData where
  blockThreshold : Nat
  vertexThreshold : Nat
  exactFields : Type
  lengthOneTarget : Prop
  lengthTwoTarget : Prop
  lengthThreeTarget : Prop
  lengthFourTarget : Prop
  lengthFiveTarget : Prop
  smallTarget : Prop
  largeTargetFromThreshold : Prop
  eventualLargeFields : Type
  eventualFiniteCertificateFields : Type

/-- Displayed small numeric package shapes. -/
def explicitSmallNumericData : ExplicitSmallNumericData where
  blockThreshold := SmallLengthFinalIntegratedW11.blockThreshold
  vertexThreshold := SmallLengthFinalIntegratedW11.vertexThreshold
  exactFields := SmallLengthFinalIntegratedW11.ExactTargetFields
  lengthOneTarget := FixedTarget (16 * 1)
  lengthTwoTarget := FixedTarget (16 * 2)
  lengthThreeTarget := FixedTarget (16 * 3)
  lengthFourTarget := FixedTarget (16 * 4)
  lengthFiveTarget := FixedTarget (16 * 5)
  smallTarget :=
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo
      SmallLengthFinalIntegratedW11.vertexThreshold
  largeTargetFromThreshold :=
    forall n : Nat, SmallLengthFinalIntegratedW11.vertexThreshold <= n ->
      FixedTarget n
  eventualLargeFields := SmallLengthFinalIntegratedW11.EventualLargeTargetFields
  eventualFiniteCertificateFields :=
    SmallLengthFinalIntegratedW11.EventualFiniteCertificateFields

/-- Large-chain and generated-chain data that still has to be supplied. -/
structure ExplicitLargeChainData where
  exactClosedChainPackage : Type
  exactGeneratedClosedChainPackage : Type
  eventualClosedChainPackage : Type
  eventualGeneratedClosedChainPackage : Type
  smallLengthClosedChainFields : Type
  smallLengthGeneratedClosedChainFields : Type
  largeClosedChainsFromThreshold : Type
  largeGeneratedDataFromThreshold : Type
  finiteCertificateObligationsFromThreshold : Type

/-- Displayed large-chain package shapes. -/
def explicitLargeChainData : ExplicitLargeChainData where
  exactClosedChainPackage := ArbitraryNFinalIntegratedW11.ExactClosedChainPackage
  exactGeneratedClosedChainPackage :=
    ArbitraryNFinalIntegratedW11.ExactGeneratedClosedChainPackage
  eventualClosedChainPackage :=
    ArbitraryNFinalIntegratedW11.EventualClosedChainPackage
  eventualGeneratedClosedChainPackage :=
    ArbitraryNFinalIntegratedW11.EventualGeneratedClosedChainPackage
  smallLengthClosedChainFields :=
    SmallLengthFinalIntegratedW11.EventualClosedChainFields
  smallLengthGeneratedClosedChainFields :=
    SmallLengthFinalIntegratedW11.EventualGeneratedClosedChainFields
  largeClosedChainsFromThreshold :=
    forall k : Nat, SmallLengthFinalIntegratedW11.blockThreshold <= k ->
      0 < k -> SplitSoundness.ExactChainUpper k
  largeGeneratedDataFromThreshold :=
    forall k : Nat, SmallLengthFinalIntegratedW11.blockThreshold <= k ->
      forall hk : 0 < k,
        SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  finiteCertificateObligationsFromThreshold :=
    EventualRoleHingeClosure.EventualFiniteCertificateObligations
      SmallLengthFinalIntegratedW11.blockThreshold

/-- Period package shapes, including the absent final-period aggregate. -/
structure ExplicitPeriodData where
  finalLedgerStatus : LedgerAvailability
  integratedSources : PeriodIntegratedW11.SourcePackageLedger
  targetInputs : PeriodTargetIntegratedW11.ExplicitPeriodTargetInputs
  checkedWordSeparationFields :
    PeriodIntegratedW11.Candidate -> Sort 1
  checkedWordEquationPackages :
    PeriodIntegratedW11.Candidate -> Sort 1
  checkedWordEquationFamilies :
    PeriodIntegratedW11.Candidate -> Sort 1
  separatedFamilyFields :
    PeriodIntegratedW11.Candidate -> Sort 1
  crossBlockLedgerFields :
    PeriodIntegratedW11.Candidate -> Sort 1
  explicitLowerBoundFields :
    PeriodIntegratedW11.Candidate -> Sort 1
  exactCandidatePeriodFields :
    PeriodIntegratedW11.Candidate -> Sort 1
  periodNonRigidRouteFields : Sort 1
  transitionRouteFields : Sort 1
  transitionRemainingFields :
    PeriodIntegratedW11.SameOppositeCandidate -> Sort 1
  rawCrossBlockInequalityLedgers :
    PeriodIntegratedW11.InequalityPeriodFamily -> Sort 1
  crossBlockClosureLedgers :
    PeriodIntegratedW11.InequalityPeriodFamily -> Sort 1
  exactTargetAssumptions : Prop
  eventualSmallCaseAssumptions : Type

/-- Displayed period package shapes. -/
def explicitPeriodData : ExplicitPeriodData where
  finalLedgerStatus := finalLedgerAvailability.periodFinal
  integratedSources := PeriodIntegratedW11.sourcePackageLedger
  targetInputs := PeriodTargetIntegratedW11.explicitPeriodTargetInputs
  checkedWordSeparationFields :=
    PeriodTargetIntegratedW11.CheckedWordSeparationFields
  checkedWordEquationPackages :=
    PeriodTargetIntegratedW11.CheckedWordEquationPackage
  checkedWordEquationFamilies :=
    PeriodTargetIntegratedW11.CheckedWordEquationFamily
  separatedFamilyFields :=
    PeriodTargetIntegratedW11.GeneratedFamilyRemainingFields
  crossBlockLedgerFields :=
    PeriodTargetIntegratedW11.CrossBlockLedgerClosureFields
  explicitLowerBoundFields :=
    PeriodTargetIntegratedW11.ExplicitLowerBoundClosureFields
  exactCandidatePeriodFields :=
    PeriodTargetIntegratedW11.ExactCandidatePeriodFields
  periodNonRigidRouteFields :=
    PeriodTargetIntegratedW11.PeriodNonRigidRouteFields
  transitionRouteFields := PeriodTargetIntegratedW11.TransitionRouteFields
  transitionRemainingFields :=
    PeriodTargetIntegratedW11.TransitionRemainingFields
  rawCrossBlockInequalityLedgers :=
    PeriodTargetIntegratedW11.RawCrossBlockInequalityLedger
  crossBlockClosureLedgers :=
    PeriodTargetIntegratedW11.CrossBlockClosureLedger
  exactTargetAssumptions := PeriodTargetIntegratedW11.ExactTargetAssumptions
  eventualSmallCaseAssumptions :=
    PeriodTargetIntegratedW11.EventualSmallCaseAssumptions

/-- Cross-block numeric, polynomial, value, and ledger input shapes. -/
structure ExplicitCrossBlockData where
  fields : CrossBlockFinalIntegratedW11.ExplicitCrossBlockFields
  polynomialRows :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Prop
  polynomialRowFamilies :
    CrossBlockFinalIntegratedW11.PeriodSearchFamily -> Prop
  generatedPointTables :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Prop
  packedInequalities :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Prop
  positionPolynomialCertificates :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Prop
  valueRows :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Type
  valueRowFamilies :
    CrossBlockFinalIntegratedW11.PeriodSearchFamily -> Type
  valueMatrices :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Type
  valueMatrixFamilies :
    CrossBlockFinalIntegratedW11.PeriodSearchFamily -> Type
  lowerTables :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Prop
  lowerTableFamilies :
    CrossBlockFinalIntegratedW11.PeriodSearchFamily -> Prop
  positionValueCertificates :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Type
  sqDistanceTables :
    forall _F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      forall k : Nat, 0 < k -> Prop
  inequalityLedgers :
    CrossBlockFinalIntegratedW11.PeriodSearchFamily -> Type
  closureLedgers :
    CrossBlockFinalIntegratedW11.PeriodSearchFamily -> Type

/-- Displayed cross-block package shapes. -/
def explicitCrossBlockData : ExplicitCrossBlockData where
  fields := CrossBlockFinalIntegratedW11.explicitCrossBlockFields
  polynomialRows := CrossBlockFinalIntegratedW11.PolynomialRows
  polynomialRowFamilies := CrossBlockFinalIntegratedW11.PolynomialRowFamilies
  generatedPointTables := CrossBlockFinalIntegratedW11.GeneratedPointTable
  packedInequalities := CrossBlockFinalIntegratedW11.PackedInequalities
  positionPolynomialCertificates :=
    CrossBlockFinalIntegratedW11.PositionPolynomialCertificate
  valueRows := CrossBlockFinalIntegratedW11.ValueRows
  valueRowFamilies := CrossBlockFinalIntegratedW11.ValueRowFamilies
  valueMatrices := CrossBlockFinalIntegratedW11.NonConnectorValueMatrix
  valueMatrixFamilies :=
    CrossBlockFinalIntegratedW11.NonConnectorValueMatrixFamily
  lowerTables := CrossBlockFinalIntegratedW11.NonConnectorLowerTable
  lowerTableFamilies :=
    CrossBlockFinalIntegratedW11.NonConnectorLowerTableFamily
  positionValueCertificates :=
    CrossBlockFinalIntegratedW11.PositionValueCertificate
  sqDistanceTables := CrossBlockFinalIntegratedW11.SqDistanceTable
  inequalityLedgers := CrossBlockFinalIntegratedW11.CrossBlockInequalityLedger
  closureLedgers := CrossBlockFinalIntegratedW11.CrossBlockClosureLedger

/-- Generated-point source data shapes used by the final generated aggregate. -/
structure ExplicitGeneratedPointData where
  fields : GeneratedFinalIntegratedW11.GeneratedPointFieldLedger
  targetInputs : GeneratedTargetIntegratedW11.RequiredGeneratedPointInputs
  normalizedPolynomial :
    GeneratedFinalIntegratedW11.GeneratedPointFamily -> Prop
  normalizedValue :
    GeneratedFinalIntegratedW11.GeneratedPointFamily -> Type
  lowerBound :
    GeneratedFinalIntegratedW11.GeneratedPointFamily -> Type
  crossBlockInequality :
    GeneratedFinalIntegratedW11.CrossBlockFamily -> Type
  crossBlockClosure :
    GeneratedFinalIntegratedW11.CrossBlockFamily -> Type
  flexibleCandidateAssembly : Type
  candidateValueMatrices : Type
  finalConditionalFamilies : Type

/-- Displayed generated-point package shapes. -/
def explicitGeneratedPointData : ExplicitGeneratedPointData where
  fields := GeneratedFinalIntegratedW11.generatedPointFieldLedger
  targetInputs := GeneratedTargetIntegratedW11.requiredGeneratedPointInputs
  normalizedPolynomial :=
    GeneratedFinalIntegratedW11.GeneratedPointNormalizedPolynomialFields
  normalizedValue :=
    GeneratedFinalIntegratedW11.GeneratedPointNormalizedValueFields
  lowerBound := GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields
  crossBlockInequality :=
    GeneratedFinalIntegratedW11.CrossBlockInequalityLedger
  crossBlockClosure := GeneratedFinalIntegratedW11.CrossBlockClosureLedger
  flexibleCandidateAssembly :=
    GeneratedFinalIntegratedW11.FlexibleCandidateAssemblyFields
  candidateValueMatrices := GeneratedFinalIntegratedW11.CandidateValueMatrixFamily
  finalConditionalFamilies := GeneratedFinalIntegratedW11.FinalConditionalFamily

/-- All explicit data still required by the checked routes. -/
structure ExplicitOpenData where
  smallNumeric : ExplicitSmallNumericData
  largeChain : ExplicitLargeChainData
  period : ExplicitPeriodData
  crossBlock : ExplicitCrossBlockData
  generatedPoint : ExplicitGeneratedPointData
  arbitraryNPackages : ArbitraryNIntegratedW11.PackageLedger
  consistencyInputs : PachTothW11FinalConsistency.OpenInputLedgers

/-- Combined open-data ledger. -/
def explicitOpenData : ExplicitOpenData where
  smallNumeric := explicitSmallNumericData
  largeChain := explicitLargeChainData
  period := explicitPeriodData
  crossBlock := explicitCrossBlockData
  generatedPoint := explicitGeneratedPointData
  arbitraryNPackages := ArbitraryNIntegratedW11.packageLedger
  consistencyInputs := PachTothW11FinalConsistency.openInputLedgers

/-! ## Final aggregate matrix -/

/-- Final W11 Pach--Toth aggregate matrix.

The matrix stores checked route ledgers and the explicit data still needed by
those routes.  It does not store inhabitants of the open-data packages. -/
structure Matrix where
  availability : FinalLedgerAvailability
  checked : ImportedCheckedLedgers
  openData : ExplicitOpenData
  blockers : PachTothW11FinalConsistency.FinalBlockerLedger

/-- The final checked W11 Pach--Toth aggregate ledger. -/
def matrix : Matrix where
  availability := finalLedgerAvailability
  checked := importedCheckedLedgers
  openData := explicitOpenData
  blockers := PachTothW11FinalConsistency.finalBlockerLedger

/-! ## Conditional route projections -/

theorem arbitraryTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
    package

theorem arbitraryTarget_of_transitionCandidatePackage
    (package : TransitionFinalIntegratedW11.CandidatePackage) :
    ArbitraryTarget :=
  TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_candidatePackage
    package

theorem arbitraryTarget_of_transitionPeriodPackage
    (package : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
    package

theorem fixedTarget_of_transitionPeriodBlockPackage
    (package : TransitionFinalIntegratedW11.PeriodBlockPackage) :
    FixedTarget
      (16 * TransitionFinalIntegratedW11.PeriodBlockPackage.blockIndex package) :=
  TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodBlockPackage
    package

theorem arbitraryTarget_of_transitionCrossBlockPackage
    (package : TransitionFinalIntegratedW11.CrossBlockPackage) :
    ArbitraryTarget :=
  TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockPackage
    package

theorem arbitraryTarget_of_periodExactCandidateFields
    {T : PeriodTargetIntegratedW11.Candidate}
    (D : PeriodTargetIntegratedW11.ExactCandidatePeriodFields T) :
    ArbitraryTarget :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
    D

theorem fixedTarget_of_periodCheckedWordSeparation
    {T : PeriodTargetIntegratedW11.Candidate}
    (D : PeriodTargetIntegratedW11.CheckedWordSeparationFields T) :
    FixedTarget (16 * D.checkedWord.length) :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_checkedWordSeparation
    D

theorem arbitraryTarget_of_generatedPointLowerBoundFields
    {F : GeneratedFinalIntegratedW11.GeneratedPointFamily}
    (C : GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  GeneratedFinalIntegratedW11.arbitraryTarget_of_lowerBoundFields C

theorem arbitraryTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedFinalIntegratedW11.CrossBlockFamily}
    (L : GeneratedFinalIntegratedW11.CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  GeneratedFinalIntegratedW11.arbitraryTarget_of_crossBlockInequalityLedger L

theorem fixedTarget_of_crossBlockPolynomialRows
    {F : CrossBlockFinalIntegratedW11.PeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (R : CrossBlockFinalIntegratedW11.PolynomialRows F k hk) :
    FixedTarget (16 * k) :=
  CrossBlockFinalIntegratedW11.exactBlockTarget_of_polynomialRows R

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFinalIntegratedW11.PeriodSearchFamily}
    (C : CrossBlockFinalIntegratedW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  CrossBlockFinalIntegratedW11.arbitraryTarget_of_crossBlockClosureLedger C

theorem arbitraryTarget_of_exactClosedChains
    (P : ArbitraryNFinalIntegratedW11.ExactClosedChainPackage) :
    ArbitraryTarget :=
  ArbitraryNFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactClosedChains
    P

theorem arbitraryTarget_of_eventualGeneratedClosedChains
    (P : ArbitraryNFinalIntegratedW11.EventualGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  ArbitraryNFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_eventualGeneratedClosedChains
    P

theorem arbitraryTarget_of_smallLengthEventualGeneratedClosedChainFields
    (P : SmallLengthFinalIntegratedW11.EventualGeneratedClosedChainFields) :
    ArbitraryTarget :=
  SmallLengthFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_eventualGeneratedClosedChainFields
    P

theorem arbitraryTarget_of_smallLengthAggregateFiniteCertificates
    (A : SmallLengthFinalIntegratedW11.AggregateFields) :
    ArbitraryTarget :=
  SmallLengthFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_aggregate_finiteCertificates
    A

/-! ## Blocker projections -/

theorem transitionConcreteRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.transition.transitionShortcuts.routeClaim

theorem transitionCompletedFilteredRoute_blocked :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.transition.transitionShortcuts.completedFilteredRoute

theorem transitionFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.generatedTarget.fullSameRestShortcut

end

end PachTothW11FinalAggregate
end PachToth
end ErdosProblems1066
