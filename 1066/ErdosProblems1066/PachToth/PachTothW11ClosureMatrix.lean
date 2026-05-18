import ErdosProblems1066.PachToth.ArbitraryNClosureW11
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11
import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.ExactLocalObstructionMatrixW11
import ErdosProblems1066.PachToth.FlexibleAssemblyTargetW11
import ErdosProblems1066.PachToth.FlexibleCandidateAssemblyW11
import ErdosProblems1066.PachToth.FlexibleTransitionClosureW11
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.GeneratedPointCertificateW11
import ErdosProblems1066.PachToth.LengthFourFiveCaseW11
import ErdosProblems1066.PachToth.PachTothW10ClosureMatrix
import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.RoleHingePolynomialReductionW11

set_option autoImplicit false

/-!
# W11 Pach--Toth closure matrix

This file is the W11 consolidation layer for the Pach--Toth route.  No sibling
W11 Pach--Toth source files were present when this ledger was created, so the
matrix below records the W10-to-W11 inheritance explicitly.

Every target-producing entry is still conditional on a named field package.
The strongest inherited rows also keep their exact `16 * k` block projections.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW11ClosureMatrix

noncomputable section

universe u

abbrev W10Matrix :=
  PachTothW10ClosureMatrix.Matrix

abbrev W10RemainingDataLedger :=
  PachTothW10ClosureMatrix.RemainingDataLedger

abbrev TargetProjectionRow (alpha : Sort u) :=
  PachTothW10ClosureMatrix.TargetProjectionRow alpha

abbrev ExactBlockProjectionRow (alpha : Sort u) :=
  PachTothW10ClosureMatrix.ExactBlockProjectionRow alpha

abbrev SearchCandidate :=
  PachTothW10ClosureMatrix.SearchCandidate

abbrev LowerBoundPeriodSearchFamily :=
  CrossBlockLowerBoundSearchW9.RoleHingedPeriodSearchFamily

abbrev W10PolynomialPeriodSearchFamily :=
  PachTothW10ClosureMatrix.W10PolynomialPeriodSearchFamily

abbrev W10NormalizedPointPeriodSearchFamily :=
  PachTothW10ClosureMatrix.W10NormalizedPointPeriodSearchFamily

abbrev MinimalExactTargetField :=
  PachTothW10ClosureMatrix.W8MinimalExactTargetCertificate

abbrev ConcreteRemainingDataField :=
  PachTothW10ClosureMatrix.W8ConcreteRemainingData

abbrev ConcreteLowerTableField :=
  PachTothW10ClosureMatrix.W8ConcreteNonConnectorLowerTableFamily

abbrev W9ClosingFields :=
  PachTothW10ClosureMatrix.W9ClosingFields

abbrev W9PeriodSearchSqValuePackage :=
  PachTothW10ClosureMatrix.W9PeriodSearchSqValuePackage

abbrev FinalFlexibleLowerTableFamily :=
  PachTothW10ClosureMatrix.FinalFlexibleLowerTableFamily

abbrev FinalFlexibleValueMatrixFamily :=
  PachTothW10ClosureMatrix.FinalFlexibleValueMatrixFamily

abbrev ConcreteValueMatrixFamily :=
  PachTothW10ClosureMatrix.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  PachTothW10ClosureMatrix.CandidateValueMatrixFamily

abbrev W10ExactTargetPackage :=
  PachTothW10ClosureMatrix.W10ExactTargetPackage

abbrev W10PositiveExactChainPackage :=
  PachTothW10ClosureMatrix.W10PositiveExactChainPackage

abbrev W10ClosedPlacementPackage :=
  PachTothW10ClosureMatrix.W10ClosedPlacementPackage

abbrev W10CandidatePackedInequalities :=
  PachTothW10ClosureMatrix.W10CandidatePackedInequalities

abbrev FlexibleCandidateClosureData (T : SearchCandidate) :=
  PachTothW10ClosureMatrix.FlexibleCandidateClosureData T

abbrev W10FlexibleFamilyFields (T : SearchCandidate) :=
  PachTothW10ClosureMatrix.W10FlexibleFamilyFields T

abbrev W10AlgebraicFamily (T : SearchCandidate) :=
  PachTothW10ClosureMatrix.W10AlgebraicFamily T

abbrev W10ExactTargetRouteFields
    (T : SearchCandidate)
    (F : W10AlgebraicFamily T) :=
  PachTothW10ClosureMatrix.W10ExactTargetRouteFields T F

abbrev GeneratedPolynomialCertificateFamily
    (F : LowerBoundPeriodSearchFamily) :=
  PachTothW10ClosureMatrix.SearchGeneratedPolynomialCertificateFamily F

abbrev W10CrossBlockPolynomialSystem
    (F : W10PolynomialPeriodSearchFamily) :=
  PachTothW10ClosureMatrix.W10CrossBlockPolynomialSystem F

abbrev W10NormalizedPointPolynomialFamily
    (F : W10NormalizedPointPeriodSearchFamily) :=
  PachTothW10ClosureMatrix.W10NormalizedPointPolynomialFamily F

abbrev W10NormalizedPointValueFamily
    (F : W10NormalizedPointPeriodSearchFamily) :=
  PachTothW10ClosureMatrix.W10NormalizedPointValueFamily F

abbrev W11SameOppositeCandidate :=
  FlexibleTransitionSearchW11.SameOppositeCandidate

abbrev W11FilteredSameOpposite :=
  FlexibleTransitionSearchW11.FilteredSameOpposite

abbrev W11NonRigidCandidateRemainingFields
    (T : W11SameOppositeCandidate) :=
  FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields T

abbrev W11NonRigidRouteFields :=
  FlexibleTransitionSearchW11.NonRigidRouteFields

abbrev W11CompleteNonRigidFamilyFields :=
  FlexibleTransitionSearchW11.W10CompleteNonRigidFamilyFields

abbrev W11CompletedFilteredRouteFields
    (F : W11FilteredSameOpposite) :=
  FlexibleTransitionSearchW11.CompletedFilteredRouteFields F

abbrev W11ConcreteFourTargetRouteClaim :=
  FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim

abbrev W11ConcreteFourTargetCheckedRows :=
  FlexibleTransitionSearchW11.ConcreteFourTargetCheckedRows

abbrev W11CandidateAssemblyFields :=
  FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields

abbrev W11CandidateProjectionRow :=
  FlexibleCandidateAssemblyW11.CandidateProjectionRow

abbrev W11CandidateBranchSurfaceRows :=
  FlexibleCandidateAssemblyW11.BranchSurfaceRows

abbrev W11CandidateBlockedRoutes :=
  FlexibleCandidateAssemblyW11.BlockedRoutes

abbrev W11CrossBlockPeriodSearchFamily :=
  CrossBlockInequalityLedgerW11.RoleHingedPeriodSearchFamily

abbrev W11CrossBlockInequalityLedger
    (F : W11CrossBlockPeriodSearchFamily) :=
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger F

abbrev W11GeneratedPointPeriodSearchFamily :=
  GeneratedPointCertificateW11.RoleHingedPeriodSearchFamily

abbrev W11NormalizedPolynomialFields
    (F : W11GeneratedPointPeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedPolynomialFields F

abbrev W11NormalizedValueFields
    (F : W11GeneratedPointPeriodSearchFamily) :=
  GeneratedPointCertificateW11.NormalizedValueFields F

abbrev W11LowerBoundFields
    (F : W11GeneratedPointPeriodSearchFamily) :=
  GeneratedPointCertificateW11.LowerBoundFields F

abbrev W11ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.ArbitraryNTargetFacade

abbrev W11ThresholdTargetFacade :=
  ArbitraryNClosureW11.ThresholdTargetFacade

abbrev W11ExactClosedChainPackage :=
  ArbitraryNClosureW11.ExactClosedChainPackage

abbrev W11ExactGeneratedClosedChainPackage :=
  ArbitraryNClosureW11.ExactGeneratedClosedChainPackage

abbrev W11EventualClosedChainPackage :=
  ArbitraryNClosureW11.EventualClosedChainPackage

abbrev W11EventualGeneratedClosedChainPackage :=
  ArbitraryNClosureW11.EventualGeneratedClosedChainPackage

abbrev W11FlexibleTransitionClosureMatrix :=
  FlexibleTransitionClosureW11.Matrix

abbrev W11FlexibleTransitionStrongTargetRow :=
  FlexibleTransitionClosureW11.StrongTargetRow

abbrev W11FlexibleAssemblyTargetMatrix :=
  FlexibleAssemblyTargetW11.Matrix

abbrev W11ThresholdSmallCaseRoute :=
  FlexibleAssemblyTargetW11.ThresholdSmallCaseRoute

abbrev W11FinalConditionalFamily :=
  FlexibleAssemblyTargetW11.FinalConditionalFamily

abbrev W11RoleHingePeriodSearchFamily :=
  RoleHingePolynomialReductionW11.RoleHingedPeriodSearchFamily

abbrev W11RoleHingeCrossBlockInequalityPackage
    (F : W11RoleHingePeriodSearchFamily) :=
  RoleHingePolynomialReductionW11.CrossBlockInequalityPackage F

abbrev W11LengthFourFivePeriodSearchData :=
  LengthFourFiveCaseW11.PeriodSearchData

abbrev W11LengthFourFivePeriodLowerTables
    (F : W11LengthFourFivePeriodSearchData) :=
  LengthFourFiveCaseW11.LengthFourFivePeriodNonConnectorLowerTables F

abbrev W11LengthFourFivePeriodCandidateFamily :=
  LengthFourFiveCaseW11.PeriodCandidateFamily

abbrev W11LengthFourFiveCandidateLowerTables
    (F : W11LengthFourFivePeriodCandidateFamily) :=
  LengthFourFiveCaseW11.LengthFourFiveCandidateNonConnectorLowerTables F

abbrev W11ExactBlockTargetsBelowSix :=
  LengthFourFiveCaseW11.ExactBlockTargetsBelowSix

abbrev W11ExactLocalCandidateRows :=
  ExactLocalObstructionMatrixW11.ExactLocalCandidateRows

/-! ## Supporting separation rows -/

/-- A checked separation projection row for W11 cross-block ledger fields. -/
structure CrossBlockSeparationRow where
  separated :
    forall {F : W11CrossBlockPeriodSearchFamily},
      W11CrossBlockInequalityLedger F ->
        forall (k : Nat) (hk : 0 < k),
          CrossBlockInequalityLedgerW11.GeneratedGlobalSeparationAt F hk

def crossBlockInequalityLedgerRow : CrossBlockSeparationRow where
  separated := fun L k hk => L.separated k hk

/-- Exact block targets for the length-four and length-five W11 rows. -/
structure LengthFourFiveExactBlockRow (alpha : Sort u) where
  lengthFour : alpha -> targetUpperConstructionFiveSixteenAt (16 * 4)
  lengthFive : alpha -> targetUpperConstructionFiveSixteenAt (16 * 5)

/-! ## Inherited W10 field ledger -/

/-- W11-facing spellings of the inherited W10 field packages. -/
structure InheritedFieldLedger where
  w10Matrix : Type 1
  w10RemainingDataLedger : Type 1
  minimalExactTarget : Type
  concreteRemainingData : Type
  concreteLowerTables : Type
  w9ClosingFields : Type
  w9PeriodSearchSqValues : Type
  finalFlexibleLowerTables : Type
  finalFlexibleValueMatrices : Type
  concreteValueMatrices : Type
  candidateValueMatrices : Type
  w10ExactTargets : Prop
  w10PositiveExactChains : Type
  w10ClosedPlacements : Type
  w10PackedCrossBlockInequalities : Type
  flexibleCandidateClosures : SearchCandidate -> Type
  w10FlexibleFamilyFields : SearchCandidate -> Type
  w10ExactTargetRouteFields :
    forall T : SearchCandidate, W10AlgebraicFamily T -> Type
  generatedPolynomialCertificates :
    LowerBoundPeriodSearchFamily -> Prop
  w10CrossBlockPolynomialSystems :
    W10PolynomialPeriodSearchFamily -> Prop
  w10NormalizedPointPolynomialFamilies :
    W10NormalizedPointPeriodSearchFamily -> Prop
  w10NormalizedPointValueFamilies :
    W10NormalizedPointPeriodSearchFamily -> Type
  w11NonRigidCandidateRemainingFields :
    W11SameOppositeCandidate -> Type
  w11NonRigidRouteFields : Type
  w11CompleteNonRigidFamilyFields : Type
  w11CompletedFilteredRouteFields :
    W11FilteredSameOpposite -> Type
  w11CandidateAssemblyFields : Type
  w11CandidateBranchSurfaces : Type
  w11CandidateBlockedRoutes : Prop
  w11CrossBlockInequalityLedgers :
    W11CrossBlockPeriodSearchFamily -> Type
  w11GeneratedPointNormalizedPolynomialFields :
    W11GeneratedPointPeriodSearchFamily -> Prop
  w11GeneratedPointNormalizedValueFields :
    W11GeneratedPointPeriodSearchFamily -> Type
  w11GeneratedPointLowerBoundFields :
    W11GeneratedPointPeriodSearchFamily -> Type
  w11ArbitraryNExactClosedChains : Type
  w11ArbitraryNExactGeneratedClosedChains : Type
  w11ArbitraryNEventualClosedChains : Type
  w11ArbitraryNEventualGeneratedClosedChains : Type
  w11FlexibleTransitionClosureMatrix : Type 2
  w11FlexibleAssemblyTargetMatrix : Type
  w11FinalConditionalFamilies : Type
  w11RoleHingeCrossBlockInequalityPackages :
    W11RoleHingePeriodSearchFamily -> Prop
  w11LengthFourFivePeriodLowerTables :
    W11LengthFourFivePeriodSearchData -> Prop
  w11LengthFourFiveCandidateLowerTables :
    W11LengthFourFivePeriodCandidateFamily -> Prop
  w11ExactBlockTargetsBelowSix : Prop
  w11ExactLocalCandidateRows : Type
  w11ExactLocalCheckedRows : W11ExactLocalCandidateRows
  w11ConcreteFourTargetCheckedRows : W11ConcreteFourTargetCheckedRows
  w11ConcreteFourTargetRouteBlocker :
    W11ConcreteFourTargetRouteClaim -> False
  w11ConcreteFilteredRouteBlocker :
    W11CompletedFilteredRouteFields
        FlexibleTransitionSearchW11.concreteFourTargetCheckedRows.filtered ->
      False
  w11ConcreteSameOppositeCandidateFieldsBlocker :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)
  inheritedFullSameRestBlocker :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  inheritedConcreteT11RBlocker :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction
  inheritedFilteredCompletionBlocker :
    Not FlexibleBranchSearchSummaryW10.W10ConcreteFilteredCompletion

/-- The W11 ledger currently inherits the checked W10 field shapes. -/
def inheritedFieldLedger : InheritedFieldLedger where
  w10Matrix := W10Matrix
  w10RemainingDataLedger := W10RemainingDataLedger
  minimalExactTarget := MinimalExactTargetField
  concreteRemainingData := ConcreteRemainingDataField
  concreteLowerTables := ConcreteLowerTableField
  w9ClosingFields := W9ClosingFields
  w9PeriodSearchSqValues := W9PeriodSearchSqValuePackage
  finalFlexibleLowerTables := FinalFlexibleLowerTableFamily
  finalFlexibleValueMatrices := FinalFlexibleValueMatrixFamily
  concreteValueMatrices := ConcreteValueMatrixFamily
  candidateValueMatrices := CandidateValueMatrixFamily
  w10ExactTargets := W10ExactTargetPackage
  w10PositiveExactChains := W10PositiveExactChainPackage
  w10ClosedPlacements := W10ClosedPlacementPackage
  w10PackedCrossBlockInequalities := W10CandidatePackedInequalities
  flexibleCandidateClosures := FlexibleCandidateClosureData
  w10FlexibleFamilyFields := W10FlexibleFamilyFields
  w10ExactTargetRouteFields := W10ExactTargetRouteFields
  generatedPolynomialCertificates := GeneratedPolynomialCertificateFamily
  w10CrossBlockPolynomialSystems := W10CrossBlockPolynomialSystem
  w10NormalizedPointPolynomialFamilies :=
    W10NormalizedPointPolynomialFamily
  w10NormalizedPointValueFamilies := W10NormalizedPointValueFamily
  w11NonRigidCandidateRemainingFields :=
    W11NonRigidCandidateRemainingFields
  w11NonRigidRouteFields := W11NonRigidRouteFields
  w11CompleteNonRigidFamilyFields := W11CompleteNonRigidFamilyFields
  w11CompletedFilteredRouteFields := W11CompletedFilteredRouteFields
  w11CandidateAssemblyFields := W11CandidateAssemblyFields
  w11CandidateBranchSurfaces := W11CandidateBranchSurfaceRows
  w11CandidateBlockedRoutes := W11CandidateBlockedRoutes
  w11CrossBlockInequalityLedgers := W11CrossBlockInequalityLedger
  w11GeneratedPointNormalizedPolynomialFields :=
    W11NormalizedPolynomialFields
  w11GeneratedPointNormalizedValueFields := W11NormalizedValueFields
  w11GeneratedPointLowerBoundFields := W11LowerBoundFields
  w11ArbitraryNExactClosedChains := W11ExactClosedChainPackage
  w11ArbitraryNExactGeneratedClosedChains :=
    W11ExactGeneratedClosedChainPackage
  w11ArbitraryNEventualClosedChains := W11EventualClosedChainPackage
  w11ArbitraryNEventualGeneratedClosedChains :=
    W11EventualGeneratedClosedChainPackage
  w11FlexibleTransitionClosureMatrix := W11FlexibleTransitionClosureMatrix
  w11FlexibleAssemblyTargetMatrix := W11FlexibleAssemblyTargetMatrix
  w11FinalConditionalFamilies := W11FinalConditionalFamily
  w11RoleHingeCrossBlockInequalityPackages :=
    W11RoleHingeCrossBlockInequalityPackage
  w11LengthFourFivePeriodLowerTables :=
    W11LengthFourFivePeriodLowerTables
  w11LengthFourFiveCandidateLowerTables :=
    W11LengthFourFiveCandidateLowerTables
  w11ExactBlockTargetsBelowSix := W11ExactBlockTargetsBelowSix
  w11ExactLocalCandidateRows := W11ExactLocalCandidateRows
  w11ExactLocalCheckedRows :=
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.possibleRows
  w11ConcreteFourTargetCheckedRows :=
    FlexibleTransitionSearchW11.concreteFourTargetCheckedRows
  w11ConcreteFourTargetRouteBlocker :=
    FlexibleTransitionSearchW11.concreteFourTargetRouteClaim_blocked
  w11ConcreteFilteredRouteBlocker :=
    FlexibleTransitionSearchW11.concreteFourTargetCompletedFilteredRoute_blocked
  w11ConcreteSameOppositeCandidateFieldsBlocker :=
    FlexibleCandidateAssemblyW11.concreteSameOppositeCandidateFields_blocked
  inheritedFullSameRestBlocker :=
    PachTothW10ClosureMatrix.fullSameRestShortcut_blocked
  inheritedConcreteT11RBlocker :=
    PachTothW10ClosureMatrix.concreteT11RRow_blocked
  inheritedFilteredCompletionBlocker :=
    PachTothW10ClosureMatrix.w10ConcreteFilteredCompletion_blocked

/-! ## W11 rows inherited from W10 -/

/-- Minimal exact-target certificate row inherited from W10. -/
def minimalExactTargetRow :
    TargetProjectionRow MinimalExactTargetField :=
  PachTothW10ClosureMatrix.matrix.w8MinimalCertificate

/-- Concrete remaining-data row inherited from W10. -/
def concreteRemainingDataRow :
    TargetProjectionRow ConcreteRemainingDataField :=
  PachTothW10ClosureMatrix.matrix.w8ConcreteRemainingData

/-- Concrete lower-table row inherited from W10. -/
def concreteLowerTableRow :
    TargetProjectionRow ConcreteLowerTableField :=
  PachTothW10ClosureMatrix.matrix.w8ConcreteLowerTables

/-- W9 flattened closing-fields row inherited from W10. -/
def w9ClosingFieldsRow :
    ExactBlockProjectionRow W9ClosingFields :=
  PachTothW10ClosureMatrix.matrix.w9FlattenedClosingFields

/-- W9 period-search plus square-value row inherited from W10. -/
def w9PeriodSearchSqValuePackageRow :
    ExactBlockProjectionRow W9PeriodSearchSqValuePackage :=
  PachTothW10ClosureMatrix.matrix.w9PeriodSearchSqValues

/-- Final flexible lower-table row inherited from W10. -/
def finalFlexibleLowerTableFamilyRow :
    TargetProjectionRow FinalFlexibleLowerTableFamily :=
  PachTothW10ClosureMatrix.matrix.finalFlexibleLowerTables

/-- Final flexible value-matrix row inherited from W10. -/
def finalFlexibleValueMatrixFamilyRow :
    TargetProjectionRow FinalFlexibleValueMatrixFamily :=
  PachTothW10ClosureMatrix.matrix.finalFlexibleValueMatrices

/-- Concrete value-matrix row inherited from W10. -/
def concreteValueMatrixFamilyRow :
    ExactBlockProjectionRow ConcreteValueMatrixFamily :=
  PachTothW10ClosureMatrix.matrix.concreteValueMatrices

/-- Candidate value-matrix row inherited from W10. -/
def candidateValueMatrixFamilyRow :
    TargetProjectionRow CandidateValueMatrixFamily :=
  PachTothW10ClosureMatrix.matrix.candidateValueMatrices

/-- Flexible candidate row inherited from W10. -/
def flexibleCandidateClosureDataRow
    (T : SearchCandidate) :
    TargetProjectionRow (FlexibleCandidateClosureData T) :=
  PachTothW10ClosureMatrix.matrix.flexibleCandidateClosures T

/-- Generated-polynomial lower-bound row inherited from W10. -/
def generatedPolynomialCertificateFamilyRow
    (F : LowerBoundPeriodSearchFamily) :
    TargetProjectionRow (GeneratedPolynomialCertificateFamily F) :=
  PachTothW10ClosureMatrix.matrix.generatedPolynomialCertificates F

/-- Packed cross-block inequality row inherited from W10. -/
def w10PackedCrossBlockInequalitiesRow :
    TargetProjectionRow W10CandidatePackedInequalities :=
  PachTothW10ClosureMatrix.matrix.w10PackedCrossBlockInequalities

/-- Flexible-family field row inherited from W10. -/
def w10FlexibleFamilyFieldsRow
    (T : SearchCandidate) :
    TargetProjectionRow (W10FlexibleFamilyFields T) :=
  PachTothW10ClosureMatrix.matrix.w10FlexibleFamilyFields T

/-- Exact-target route row inherited from W10. -/
def w10ExactTargetRouteFieldsRow
    (T : SearchCandidate)
    (F : W10AlgebraicFamily T) :
    TargetProjectionRow (W10ExactTargetRouteFields T F) :=
  PachTothW10ClosureMatrix.matrix.w10ExactTargetRouteFields T F

/-- Role-hinge polynomial-system row inherited from W10. -/
def w10CrossBlockPolynomialSystemRow
    (F : W10PolynomialPeriodSearchFamily) :
    TargetProjectionRow (W10CrossBlockPolynomialSystem F) :=
  PachTothW10ClosureMatrix.matrix.w10CrossBlockPolynomialSystems F

/-! ## Checked W11 target rows -/

/-- W11 candidate remaining-fields row from the flexible transition surface.
-/
def w11NonRigidCandidateRemainingFieldsRow
    (T : W11SameOppositeCandidate) :
    TargetProjectionRow (W11NonRigidCandidateRemainingFields T) where
  exactTarget := fun R =>
    R.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun R =>
    R.targetUpperConstructionFiveSixteenArbitrary

/-- W11 non-rigid route row from the flexible transition surface. -/
def w11NonRigidRouteFieldsRow :
    TargetProjectionRow W11NonRigidRouteFields where
  exactTarget := fun R =>
    R.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun R =>
    R.targetUpperConstructionFiveSixteenArbitrary

/-- W10 complete non-rigid fields routed through the W11 flexible transition
surface. -/
def w11CompleteNonRigidFamilyFieldsRow :
    TargetProjectionRow W11CompleteNonRigidFamilyFields where
  exactTarget := fun F =>
    (FlexibleTransitionSearchW11.ofW10CompleteNonRigidFamilyFields F)
      |>.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun F =>
    (FlexibleTransitionSearchW11.ofW10CompleteNonRigidFamilyFields F)
      |>.targetUpperConstructionFiveSixteenArbitrary

/-- Completed filtered routes give the exact target, then the checked
exact-remainder bridge gives the arbitrary target. -/
def w11CompletedFilteredRouteFieldsRow
    (F : W11FilteredSameOpposite) :
    TargetProjectionRow (W11CompletedFilteredRouteFields F) where
  exactTarget := fun R =>
    R.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun R =>
    PachTothFinalDataAssembly.exactRemainderBridge_present
      R.targetUpperConstructionFiveSixteen

/-- Candidate-assembly row with exact, fixed, eventual, and arbitrary
projections. -/
def w11CandidateAssemblyFieldsRow :
    W11CandidateProjectionRow W11CandidateAssemblyFields :=
  FlexibleCandidateAssemblyW11.matrix.candidateFields

/-- W11 generated-point normalized polynomial fields route to both public
targets. -/
def w11NormalizedPolynomialFieldsRow
    (F : W11GeneratedPointPeriodSearchFamily) :
    TargetProjectionRow (W11NormalizedPolynomialFields F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- W11 generated-point normalized value fields route to both public targets.
-/
def w11NormalizedValueFieldsRow
    (F : W11GeneratedPointPeriodSearchFamily) :
    TargetProjectionRow (W11NormalizedValueFields F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- W11 raw lower-bound fields route to both public targets. -/
def w11LowerBoundFieldsRow
    (F : W11GeneratedPointPeriodSearchFamily) :
    TargetProjectionRow (W11LowerBoundFields F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- Exact closed-chain packages route to exact and arbitrary targets. -/
def w11ExactClosedChainPackageRow :
    TargetProjectionRow W11ExactClosedChainPackage where
  exactTarget := fun P =>
    P.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun P =>
    P.arbitraryTarget ArbitraryNClosureW11.checkedFiniteRemainders

/-- Exact generated closed-chain packages route through exact chains and the
split bridge. -/
def w11ExactGeneratedClosedChainPackageRow :
    TargetProjectionRow W11ExactGeneratedClosedChainPackage where
  exactTarget := fun P =>
    P.toExactClosedChainPackage.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun P =>
    P.arbitraryTarget_splitBridge

/-- Role-hinge cross-block inequality packages route to both public targets.
-/
def w11RoleHingeCrossBlockInequalityPackageRow
    (F : W11RoleHingePeriodSearchFamily) :
    TargetProjectionRow (W11RoleHingeCrossBlockInequalityPackage F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- W11 length-four/five period lower tables expose exact block targets. -/
def w11LengthFourFivePeriodLowerTablesRow
    (F : W11LengthFourFivePeriodSearchData) :
    LengthFourFiveExactBlockRow (W11LengthFourFivePeriodLowerTables F) where
  lengthFour := fun C =>
    C.toExactBlockTargets.lengthFour
  lengthFive := fun C =>
    C.toExactBlockTargets.lengthFive

/-- W11 length-four/five candidate lower tables expose exact block targets.
-/
def w11LengthFourFiveCandidateLowerTablesRow
    (F : W11LengthFourFivePeriodCandidateFamily) :
    LengthFourFiveExactBlockRow (W11LengthFourFiveCandidateLowerTables F) where
  lengthFour := fun C =>
    C.toExactBlockTargets.lengthFour
  lengthFive := fun C =>
    C.toExactBlockTargets.lengthFive

/-! ## Consolidated W11 matrix -/

/-- The W11 Pach--Toth closure matrix over the inherited W10 rows. -/
structure Matrix where
  inheritedW10 : W10Matrix
  fields : InheritedFieldLedger
  minimalExactTarget : TargetProjectionRow MinimalExactTargetField
  concreteRemainingData : TargetProjectionRow ConcreteRemainingDataField
  concreteLowerTables : TargetProjectionRow ConcreteLowerTableField
  w9ClosingFields : ExactBlockProjectionRow W9ClosingFields
  w9PeriodSearchSqValues :
    ExactBlockProjectionRow W9PeriodSearchSqValuePackage
  finalFlexibleLowerTables :
    TargetProjectionRow FinalFlexibleLowerTableFamily
  finalFlexibleValueMatrices :
    TargetProjectionRow FinalFlexibleValueMatrixFamily
  concreteValueMatrices :
    ExactBlockProjectionRow ConcreteValueMatrixFamily
  candidateValueMatrices :
    TargetProjectionRow CandidateValueMatrixFamily
  flexibleCandidateClosures :
    forall T : SearchCandidate,
      TargetProjectionRow (FlexibleCandidateClosureData T)
  generatedPolynomialCertificates :
    forall F : LowerBoundPeriodSearchFamily,
      TargetProjectionRow (GeneratedPolynomialCertificateFamily F)
  w10PackedCrossBlockInequalities :
    TargetProjectionRow W10CandidatePackedInequalities
  w10FlexibleFamilyFields :
    forall T : SearchCandidate,
      TargetProjectionRow (W10FlexibleFamilyFields T)
  w10ExactTargetRouteFields :
    forall (T : SearchCandidate) (F : W10AlgebraicFamily T),
      TargetProjectionRow (W10ExactTargetRouteFields T F)
  w10CrossBlockPolynomialSystems :
    forall F : W10PolynomialPeriodSearchFamily,
      TargetProjectionRow (W10CrossBlockPolynomialSystem F)
  w11NonRigidCandidateRemainingFields :
    forall T : W11SameOppositeCandidate,
      TargetProjectionRow (W11NonRigidCandidateRemainingFields T)
  w11NonRigidRouteFields :
    TargetProjectionRow W11NonRigidRouteFields
  w11CompleteNonRigidFamilyFields :
    TargetProjectionRow W11CompleteNonRigidFamilyFields
  w11CompletedFilteredRouteFields :
    forall F : W11FilteredSameOpposite,
      TargetProjectionRow (W11CompletedFilteredRouteFields F)
  w11CandidateAssemblyFields :
    W11CandidateProjectionRow W11CandidateAssemblyFields
  w11CrossBlockInequalityLedgers : CrossBlockSeparationRow
  w11GeneratedPointNormalizedPolynomialFields :
    forall F : W11GeneratedPointPeriodSearchFamily,
      TargetProjectionRow (W11NormalizedPolynomialFields F)
  w11GeneratedPointNormalizedValueFields :
    forall F : W11GeneratedPointPeriodSearchFamily,
      TargetProjectionRow (W11NormalizedValueFields F)
  w11GeneratedPointLowerBoundFields :
    forall F : W11GeneratedPointPeriodSearchFamily,
      TargetProjectionRow (W11LowerBoundFields F)
  w11ExactClosedChains :
    TargetProjectionRow W11ExactClosedChainPackage
  w11ExactGeneratedClosedChains :
    TargetProjectionRow W11ExactGeneratedClosedChainPackage
  w11ArbitraryNTargetClosure : ArbitraryNTargetClosureW11.Matrix
  w11CrossBlockTargetClosure :
    forall F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  w11ExactLocalClosure : ExactLocalClosureW11.Matrix
  w11FlexibleTransitionClosure : W11FlexibleTransitionClosureMatrix
  w11FlexibleAssemblyTarget : W11FlexibleAssemblyTargetMatrix
  w11RoleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  w11RoleHingeCrossBlockInequalityPackages :
    forall F : W11RoleHingePeriodSearchFamily,
      TargetProjectionRow (W11RoleHingeCrossBlockInequalityPackage F)
  w11LengthFourFivePeriodLowerTables :
    forall F : W11LengthFourFivePeriodSearchData,
      LengthFourFiveExactBlockRow (W11LengthFourFivePeriodLowerTables F)
  w11LengthFourFiveCandidateLowerTables :
    forall F : W11LengthFourFivePeriodCandidateFamily,
      LengthFourFiveExactBlockRow (W11LengthFourFiveCandidateLowerTables F)

/-- The checked W11 ledger, currently inheriting W10 projection routes. -/
def matrix : Matrix where
  inheritedW10 := PachTothW10ClosureMatrix.matrix
  fields := inheritedFieldLedger
  minimalExactTarget := minimalExactTargetRow
  concreteRemainingData := concreteRemainingDataRow
  concreteLowerTables := concreteLowerTableRow
  w9ClosingFields := w9ClosingFieldsRow
  w9PeriodSearchSqValues := w9PeriodSearchSqValuePackageRow
  finalFlexibleLowerTables := finalFlexibleLowerTableFamilyRow
  finalFlexibleValueMatrices := finalFlexibleValueMatrixFamilyRow
  concreteValueMatrices := concreteValueMatrixFamilyRow
  candidateValueMatrices := candidateValueMatrixFamilyRow
  flexibleCandidateClosures := flexibleCandidateClosureDataRow
  generatedPolynomialCertificates :=
    generatedPolynomialCertificateFamilyRow
  w10PackedCrossBlockInequalities := w10PackedCrossBlockInequalitiesRow
  w10FlexibleFamilyFields := w10FlexibleFamilyFieldsRow
  w10ExactTargetRouteFields := w10ExactTargetRouteFieldsRow
  w10CrossBlockPolynomialSystems := w10CrossBlockPolynomialSystemRow
  w11NonRigidCandidateRemainingFields :=
    w11NonRigidCandidateRemainingFieldsRow
  w11NonRigidRouteFields := w11NonRigidRouteFieldsRow
  w11CompleteNonRigidFamilyFields := w11CompleteNonRigidFamilyFieldsRow
  w11CompletedFilteredRouteFields := w11CompletedFilteredRouteFieldsRow
  w11CandidateAssemblyFields := w11CandidateAssemblyFieldsRow
  w11CrossBlockInequalityLedgers := crossBlockInequalityLedgerRow
  w11GeneratedPointNormalizedPolynomialFields :=
    w11NormalizedPolynomialFieldsRow
  w11GeneratedPointNormalizedValueFields := w11NormalizedValueFieldsRow
  w11GeneratedPointLowerBoundFields := w11LowerBoundFieldsRow
  w11ExactClosedChains := w11ExactClosedChainPackageRow
  w11ExactGeneratedClosedChains :=
    w11ExactGeneratedClosedChainPackageRow
  w11ArbitraryNTargetClosure := ArbitraryNTargetClosureW11.matrix
  w11CrossBlockTargetClosure :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  w11ExactLocalClosure := ExactLocalClosureW11.matrix
  w11FlexibleTransitionClosure := FlexibleTransitionClosureW11.matrix
  w11FlexibleAssemblyTarget := FlexibleAssemblyTargetW11.matrix
  w11RoleHingeClosure := RoleHingeClosureW11.closureMatrix
  w11RoleHingeCrossBlockInequalityPackages :=
    w11RoleHingeCrossBlockInequalityPackageRow
  w11LengthFourFivePeriodLowerTables :=
    w11LengthFourFivePeriodLowerTablesRow
  w11LengthFourFiveCandidateLowerTables :=
    w11LengthFourFiveCandidateLowerTablesRow

/-! ## Public W11 target projections -/

theorem targetUpperConstructionFiveSixteen_of_minimalExactTarget
    (C : MinimalExactTargetField) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.minimalExactTarget.exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_minimalExactTarget
    (C : MinimalExactTargetField) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.minimalExactTarget.arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_concreteRemainingData
    (D : ConcreteRemainingDataField) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concreteRemainingData.exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteRemainingData
    (D : ConcreteRemainingDataField) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteRemainingData.arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_concreteLowerTable
    (C : ConcreteLowerTableField) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concreteLowerTables.exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTable
    (C : ConcreteLowerTableField) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteLowerTables.arbitraryTarget C

theorem targetUpperConstructionFiveSixteenAt_of_w9ClosingFields
    (F : W9ClosingFields) (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.w9ClosingFields.exactBlock F k hk

theorem targetUpperConstructionFiveSixteen_of_w9ClosingFields
    (F : W9ClosingFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w9ClosingFields.exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w9ClosingFields
    (F : W9ClosingFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w9ClosingFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteenAt_of_w9PeriodSearchSqValuePackage
    (P : W9PeriodSearchSqValuePackage) (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.w9PeriodSearchSqValues.exactBlock P k hk

theorem targetUpperConstructionFiveSixteen_of_w9PeriodSearchSqValuePackage
    (P : W9PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w9PeriodSearchSqValues.exactTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_w9PeriodSearchSqValuePackage
    (P : W9PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w9PeriodSearchSqValues.arbitraryTarget P

theorem targetUpperConstructionFiveSixteen_of_finalFlexibleLowerTableFamily
    (F : FinalFlexibleLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.finalFlexibleLowerTables.exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_finalFlexibleLowerTableFamily
    (F : FinalFlexibleLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finalFlexibleLowerTables.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_finalFlexibleValueMatrixFamily
    (V : FinalFlexibleValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.finalFlexibleValueMatrices.exactTarget V

theorem targetUpperConstructionFiveSixteenArbitrary_of_finalFlexibleValueMatrixFamily
    (V : FinalFlexibleValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finalFlexibleValueMatrices.arbitraryTarget V

theorem targetUpperConstructionFiveSixteenAt_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.concreteValueMatrices.exactBlock C k hk

theorem targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concreteValueMatrices.exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteValueMatrices.arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_candidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.candidateValueMatrices.exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateValueMatrices.arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_flexibleCandidateClosureData
    {T : SearchCandidate}
    (D : FlexibleCandidateClosureData T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.flexibleCandidateClosures T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateClosureData
    {T : SearchCandidate}
    (D : FlexibleCandidateClosureData T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.flexibleCandidateClosures T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_generatedPolynomialCertificateFamily
    {F : LowerBoundPeriodSearchFamily}
    (C : GeneratedPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPolynomialCertificates F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPolynomialCertificateFamily
    {F : LowerBoundPeriodSearchFamily}
    (C : GeneratedPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generatedPolynomialCertificates F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_w10PackedCrossBlockInequalities
    (C : W10CandidatePackedInequalities) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w10PackedCrossBlockInequalities.exactTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w10PackedCrossBlockInequalities
    (C : W10CandidatePackedInequalities) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w10PackedCrossBlockInequalities.arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_w10FlexibleFamilyFields
    {T : SearchCandidate}
    (F : W10FlexibleFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w10FlexibleFamilyFields T).exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10FlexibleFamilyFields
    {T : SearchCandidate}
    (F : W10FlexibleFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w10FlexibleFamilyFields T).arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_w10ExactTargetRouteFields
    {T : SearchCandidate}
    {F : W10AlgebraicFamily T}
    (D : W10ExactTargetRouteFields T F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w10ExactTargetRouteFields T F).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10ExactTargetRouteFields
    {T : SearchCandidate}
    {F : W10AlgebraicFamily T}
    (D : W10ExactTargetRouteFields T F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w10ExactTargetRouteFields T F).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_w10CrossBlockPolynomialSystem
    {F : W10PolynomialPeriodSearchFamily}
    (C : W10CrossBlockPolynomialSystem F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w10CrossBlockPolynomialSystems F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_w10CrossBlockPolynomialSystem
    {F : W10PolynomialPeriodSearchFamily}
    (C : W10CrossBlockPolynomialSystem F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w10CrossBlockPolynomialSystems F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_w11NonRigidCandidateRemainingFields
    {T : W11SameOppositeCandidate}
    (R : W11NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w11NonRigidCandidateRemainingFields T).exactTarget R

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w11NonRigidCandidateRemainingFields
    {T : W11SameOppositeCandidate}
    (R : W11NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w11NonRigidCandidateRemainingFields T).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_w11NonRigidRouteFields
    (R : W11NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w11NonRigidRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_w11NonRigidRouteFields
    (R : W11NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w11NonRigidRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_w11CompleteNonRigidFamilyFields
    (F : W11CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w11CompleteNonRigidFamilyFields.exactTarget F

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w11CompleteNonRigidFamilyFields
    (F : W11CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w11CompleteNonRigidFamilyFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_w11CompletedFilteredRouteFields
    {F : W11FilteredSameOpposite}
    (R : W11CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w11CompletedFilteredRouteFields F).exactTarget R

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w11CompletedFilteredRouteFields
    {F : W11FilteredSameOpposite}
    (R : W11CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w11CompletedFilteredRouteFields F).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_w11CandidateAssemblyFields
    (F : W11CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w11CandidateAssemblyFields.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_w11CandidateAssemblyFields
    (F : W11CandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.w11CandidateAssemblyFields.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_w11CandidateAssemblyFields
    (F : W11CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.w11CandidateAssemblyFields.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w11CandidateAssemblyFields
    (F : W11CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w11CandidateAssemblyFields.arbitraryTarget F

theorem separated_of_w11CrossBlockInequalityLedger
    {F : W11CrossBlockPeriodSearchFamily}
    (L : W11CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockInequalityLedgerW11.GeneratedGlobalSeparationAt F hk :=
  matrix.w11CrossBlockInequalityLedgers.separated L k hk

theorem targetUpperConstructionFiveSixteen_of_w11NormalizedPolynomialFields
    {F : W11GeneratedPointPeriodSearchFamily}
    (C : W11NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w11GeneratedPointNormalizedPolynomialFields F).exactTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w11NormalizedPolynomialFields
    {F : W11GeneratedPointPeriodSearchFamily}
    (C : W11NormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w11GeneratedPointNormalizedPolynomialFields F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_w11NormalizedValueFields
    {F : W11GeneratedPointPeriodSearchFamily}
    (C : W11NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w11GeneratedPointNormalizedValueFields F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_w11NormalizedValueFields
    {F : W11GeneratedPointPeriodSearchFamily}
    (C : W11NormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w11GeneratedPointNormalizedValueFields F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_w11LowerBoundFields
    {F : W11GeneratedPointPeriodSearchFamily}
    (C : W11LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w11GeneratedPointLowerBoundFields F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_w11LowerBoundFields
    {F : W11GeneratedPointPeriodSearchFamily}
    (C : W11LowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w11GeneratedPointLowerBoundFields F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_w11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w11ExactClosedChains.exactTarget P

theorem targetUpperConstructionFiveSixteenAt_of_w11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  P.checkedTargetFacade.fixedTarget n

theorem targetUpperConstructionFiveSixteenArbitrary_of_w11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w11ExactClosedChains.arbitraryTarget P

theorem targetUpperConstructionFiveSixteen_of_w11ExactGeneratedClosedChainPackage
    (P : W11ExactGeneratedClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w11ExactGeneratedClosedChains.exactTarget P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w11ExactGeneratedClosedChainPackage
    (P : W11ExactGeneratedClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w11ExactGeneratedClosedChains.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenAt_of_w11TransitionClosureRouteFields
    (F : FlexibleTransitionClosureW11.TransitionRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.w11FlexibleTransitionClosure.transitionRouteTargets.fixedTarget F n

theorem
    targetUpperConstructionFiveSixteenEventually_of_w11TransitionClosureRouteFields
    (F : FlexibleTransitionClosureW11.TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.w11FlexibleTransitionClosure.transitionRouteTargets.eventualTarget F

theorem targetUpperConstructionFiveSixteen_of_w11FinalConditionalFamily
    (F : W11FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w11FlexibleAssemblyTarget.finalConditionalFamily.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_w11FinalConditionalFamily
    (F : W11FinalConditionalFamily) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.w11FlexibleAssemblyTarget.finalConditionalFamily.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_w11FinalConditionalFamily
    (F : W11FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.w11FlexibleAssemblyTarget.finalConditionalFamily.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w11FinalConditionalFamily
    (F : W11FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w11FlexibleAssemblyTarget.finalConditionalFamily.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_w11RoleHingeCrossBlockInequalityPackage
    {F : W11RoleHingePeriodSearchFamily}
    (C : W11RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.w11RoleHingeCrossBlockInequalityPackages F).exactTarget C

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w11RoleHingeCrossBlockInequalityPackage
    {F : W11RoleHingePeriodSearchFamily}
    (C : W11RoleHingeCrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.w11RoleHingeCrossBlockInequalityPackages F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteenAt_lengthFour_of_w11PeriodLowerTables
    {F : W11LengthFourFivePeriodSearchData}
    (C : W11LengthFourFivePeriodLowerTables F) :
    targetUpperConstructionFiveSixteenAt (16 * 4) :=
  (matrix.w11LengthFourFivePeriodLowerTables F).lengthFour C

theorem targetUpperConstructionFiveSixteenAt_lengthFive_of_w11PeriodLowerTables
    {F : W11LengthFourFivePeriodSearchData}
    (C : W11LengthFourFivePeriodLowerTables F) :
    targetUpperConstructionFiveSixteenAt (16 * 5) :=
  (matrix.w11LengthFourFivePeriodLowerTables F).lengthFive C

theorem targetUpperConstructionFiveSixteenAt_lengthFour_of_w11CandidateLowerTables
    {F : W11LengthFourFivePeriodCandidateFamily}
    (C : W11LengthFourFiveCandidateLowerTables F) :
    targetUpperConstructionFiveSixteenAt (16 * 4) :=
  (matrix.w11LengthFourFiveCandidateLowerTables F).lengthFour C

theorem targetUpperConstructionFiveSixteenAt_lengthFive_of_w11CandidateLowerTables
    {F : W11LengthFourFivePeriodCandidateFamily}
    (C : W11LengthFourFiveCandidateLowerTables F) :
    targetUpperConstructionFiveSixteenAt (16 * 5) :=
  (matrix.w11LengthFourFiveCandidateLowerTables F).lengthFive C

/-! ## Public W11 blockers inherited from W10 -/

theorem w11ConcreteFourTargetRouteClaim_blocked :
    W11ConcreteFourTargetRouteClaim -> False :=
  matrix.fields.w11ConcreteFourTargetRouteBlocker

theorem w11ConcreteFourTargetCompletedFilteredRoute_blocked :
    W11CompletedFilteredRouteFields
        FlexibleTransitionSearchW11.concreteFourTargetCheckedRows.filtered ->
      False :=
  matrix.fields.w11ConcreteFilteredRouteBlocker

theorem w11ConcreteSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.fields.w11ConcreteSameOppositeCandidateFieldsBlocker

theorem fullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.fields.inheritedFullSameRestBlocker

theorem concreteT11RRow_blocked :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction :=
  matrix.fields.inheritedConcreteT11RBlocker

theorem w10ConcreteFilteredCompletion_blocked :
    Not FlexibleBranchSearchSummaryW10.W10ConcreteFilteredCompletion :=
  matrix.fields.inheritedFilteredCompletionBlocker

end

end PachTothW11ClosureMatrix
end PachToth
end ErdosProblems1066
