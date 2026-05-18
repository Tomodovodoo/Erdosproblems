import ErdosProblems1066.PachToth.ArbitraryNBridgeW10
import ErdosProblems1066.PachToth.CrossBlockValueSearchW10
import ErdosProblems1066.PachToth.FlexibleBranchSearchSummaryW10
import ErdosProblems1066.PachToth.GeneratedPointNormalizationW10
import ErdosProblems1066.PachToth.NonRigidPeriodCandidateW10
import ErdosProblems1066.PachToth.CrossBlockLowerBoundSearchW9
import ErdosProblems1066.PachToth.PachTothFinalDataAssembly
import ErdosProblems1066.PachToth.PachTothRemainingObligationsW9
import ErdosProblems1066.PachToth.PachTothW8ClosureMatrix
import ErdosProblems1066.PachToth.PeriodFamilyCandidateSearchW9
import ErdosProblems1066.PachToth.RoleHingePolynomialSystemW10

set_option autoImplicit false

/-!
# W10 Pach--Toth closure and obligation matrix

This module is an assembly ledger, not a search result.  It records the
checked conditional rows now available for the Pach--Toth `5 / 16` route and
keeps every remaining datum as an explicit input package.

The matrix has two jobs:

* expose the exact and arbitrary target projections that follow from each
  explicit data package; and
* record the blocked concrete same-rest shortcut inherited from W9.

No unconditional target theorem is declared here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW10ClosureMatrix

noncomputable section

universe u

abbrev W8MinimalExactTargetCertificate :=
  PachTothW8ClosureMatrix.MinimalExactTargetCertificate

abbrev W8ConcreteRemainingData :=
  PachTothW8ClosureMatrix.ConcreteRemainingData

abbrev W8ConcreteNonConnectorLowerTableFamily :=
  PachTothW8ClosureMatrix.ConcreteNonConnectorLowerTableFamily

abbrev W9ClosingFields :=
  PachTothRemainingObligationsW9.FiveSixteenClosingFields

abbrev W9PeriodSearchSqValuePackage :=
  PachTothRemainingObligationsW9.PeriodSearchSqValuePackage

abbrev ConcreteValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

abbrev FinalFlexibleLowerTableFamily :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily

abbrev FinalFlexibleValueMatrixFamily :=
  PachTothFinalDataAssembly.FlexiblePeriodValueMatrixFamily

abbrev SearchCandidate :=
  PeriodFamilyCandidateSearchW9.Candidate

abbrev SearchAlgebraicEquationFamilyData
    (T : SearchCandidate) :=
  PeriodFamilyCandidateSearchW9.AlgebraicEquationFamilyData T

abbrev SearchGeneratedPolynomialCertificateFamily :=
  CrossBlockLowerBoundSearchW9.GeneratedPolynomialCertificateFamily

abbrev W10ExactTargetPackage :=
  ArbitraryNBridgeW10.ExactTargetPackage

abbrev W10PositiveExactChainPackage :=
  ArbitraryNBridgeW10.PositiveExactChainPackage

abbrev W10ClosedPlacementPackage :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

abbrev W10CandidatePackedInequalities :=
  CrossBlockValueSearchW10.CandidatePackedNonConnectorPolynomialInequalities

abbrev W10FlexibleFamilyFields
    (T : SearchCandidate) :=
  NonRigidPeriodCandidateW10.FlexibleFamilyFields T

abbrev W10AlgebraicFamily
    (T : SearchCandidate) :=
  NonRigidPeriodCandidateW10.AlgebraicFamily T

abbrev W10ExactTargetRouteFields
    (T : SearchCandidate)
    (F : W10AlgebraicFamily T) :=
  NonRigidPeriodCandidateW10.ExactTargetRouteFields T F

abbrev W10PolynomialPeriodSearchFamily :=
  RoleHingePolynomialSystemW10.RoleHingedPeriodSearchFamily

abbrev W10CrossBlockPolynomialSystem
    (F : W10PolynomialPeriodSearchFamily) :=
  RoleHingePolynomialSystemW10.CrossBlockPolynomialSystem F

abbrev W10NormalizedPointPeriodSearchFamily :=
  GeneratedPointNormalizationW10.RoleHingedPeriodSearchFamily

abbrev W10NormalizedPointPolynomialFamily :=
  GeneratedPointNormalizationW10.NormalizedGeneratedPointPositionPolynomialCertificateFamily

abbrev W10NormalizedPointValueFamily :=
  GeneratedPointNormalizationW10.NormalizedGeneratedPointPositionValueCertificateFamily

/-- A target-producing row in the W10 closure matrix. -/
structure TargetProjectionRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- A target-producing row that also exposes the exact `16 * k` block
projection directly. -/
structure ExactBlockProjectionRow (alpha : Sort u) where
  exactBlock :
    alpha -> forall (k : Nat), 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k)
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

namespace ExactBlockProjectionRow

/-- Forget the direct exact-block projection. -/
def toTargetProjectionRow
    {alpha : Sort u} (R : ExactBlockProjectionRow alpha) :
    TargetProjectionRow alpha where
  exactTarget := R.exactTarget
  arbitraryTarget := R.arbitraryTarget

end ExactBlockProjectionRow

/-! ## Candidate-period closure row -/

/-- Flexible candidate period data plus the separate generated-separation
family still required by the metric part of the route. -/
structure FlexibleCandidateClosureData (T : SearchCandidate) where
  period : SearchAlgebraicEquationFamilyData T
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (period.orientation k hk)

namespace FlexibleCandidateClosureData

/-- Repackage the explicit W10 candidate fields as a flexible generated
closure family. -/
def toGeneratedClosureFamily
    {T : SearchCandidate}
    (D : FlexibleCandidateClosureData T) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  D.period.toFlexibleGeneratedClosureFamily D.separated

/-- Exact Pach--Toth target from a flexible candidate with all period and
separation data supplied. -/
theorem targetUpperConstructionFiveSixteen
    {T : SearchCandidate}
    (D : FlexibleCandidateClosureData T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toGeneratedClosureFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target from the same explicit candidate data, routed
through the checked exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {T : SearchCandidate}
    (D : FlexibleCandidateClosureData T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachTothFinalDataAssembly.exactRemainderBridge_present
    D.targetUpperConstructionFiveSixteen

end FlexibleCandidateClosureData

/-! ## Rows inherited from W8, W9, and the final data assembly -/

/-- W8 minimal-certificate row, routed through the final checked
exact-remainder bridge. -/
def w8MinimalExactTargetCertificateRow :
    TargetProjectionRow W8MinimalExactTargetCertificate where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    PachTothFinalDataAssembly.exactRemainderBridge_present
      C.targetUpperConstructionFiveSixteen

/-- W8 concrete remaining-data row. -/
def w8ConcreteRemainingDataRow :
    TargetProjectionRow W8ConcreteRemainingData where
  exactTarget := fun D =>
    D.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun D =>
    PachTothFinalDataAssembly.exactRemainderBridge_present
      D.targetUpperConstructionFiveSixteen

/-- W8 concrete period-search plus lower-table row. -/
def w8ConcreteNonConnectorLowerTableFamilyRow :
    TargetProjectionRow W8ConcreteNonConnectorLowerTableFamily where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    PachTothFinalDataAssembly.exactRemainderBridge_present
      C.targetUpperConstructionFiveSixteen

/-- Final flexible lower-table row. -/
def finalFlexibleLowerTableFamilyRow :
    TargetProjectionRow FinalFlexibleLowerTableFamily where
  exactTarget := fun F =>
    F.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun F =>
    F.targetUpperConstructionFiveSixteenArbitrary

/-- Final flexible value-matrix row. -/
def finalFlexibleValueMatrixFamilyRow :
    TargetProjectionRow FinalFlexibleValueMatrixFamily where
  exactTarget := fun V =>
    V.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun V =>
    V.targetUpperConstructionFiveSixteenArbitrary

/-- Final concrete non-connector value-matrix row. -/
def concreteValueMatrixFamilyRow :
    ExactBlockProjectionRow ConcreteValueMatrixFamily where
  exactBlock := fun C k hk =>
    C.targetUpperConstructionFiveSixteenAt k hk
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    PachTothFinalDataAssembly.exactRemainderBridge_present
      C.targetUpperConstructionFiveSixteen

/-- Final candidate-family value-matrix row. -/
def candidateValueMatrixFamilyRow :
    TargetProjectionRow CandidateValueMatrixFamily where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- W9 flattened closing-fields row. -/
def w9ClosingFieldsRow :
    ExactBlockProjectionRow W9ClosingFields where
  exactBlock := fun F k hk =>
    F.targetUpperConstructionFiveSixteenAt_exactBlock k hk
  exactTarget := fun F =>
    F.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun F =>
    F.targetUpperConstructionFiveSixteenArbitrary

/-- W9 assembled period-search plus square-value row. -/
def w9PeriodSearchSqValuePackageRow :
    ExactBlockProjectionRow W9PeriodSearchSqValuePackage where
  exactBlock := fun P k hk =>
    P.targetUpperConstructionFiveSixteenAt_exactBlock k hk
  exactTarget := fun P =>
    P.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun P =>
    P.targetUpperConstructionFiveSixteenArbitrary

/-- Generated-polynomial lower-bound row for a supplied role-hinged period
family. -/
def generatedPolynomialCertificateFamilyRow
    (F : CrossBlockLowerBoundSearchW9.RoleHingedPeriodSearchFamily) :
    TargetProjectionRow (SearchGeneratedPolynomialCertificateFamily F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-- Flexible non-rigid candidate row. -/
def flexibleCandidateClosureDataRow
    (T : SearchCandidate) :
    TargetProjectionRow (FlexibleCandidateClosureData T) where
  exactTarget :=
    FlexibleCandidateClosureData.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    FlexibleCandidateClosureData.targetUpperConstructionFiveSixteenArbitrary

/-- W10 packed cross-block inequality row. -/
def w10CandidatePackedInequalitiesRow :
    TargetProjectionRow W10CandidatePackedInequalities where
  exactTarget := fun C =>
    C.toCandidateValueMatrixFamily.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.toCandidateValueMatrixFamily.targetUpperConstructionFiveSixteenArbitrary

/-- W10 non-rigid period-family row. -/
def w10FlexibleFamilyFieldsRow
    (T : SearchCandidate) :
    TargetProjectionRow (W10FlexibleFamilyFields T) where
  exactTarget := fun F =>
    F.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun F =>
    PachTothFinalDataAssembly.exactRemainderBridge_present
      F.targetUpperConstructionFiveSixteen

/-- W10 exact-target route row with all concrete residual fields supplied. -/
def w10ExactTargetRouteFieldsRow
    (T : SearchCandidate)
    (F : W10AlgebraicFamily T) :
    TargetProjectionRow (W10ExactTargetRouteFields T F) where
  exactTarget := fun D =>
    D.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun D =>
    D.targetUpperConstructionFiveSixteenArbitrary

/-- W10 role-hinge polynomial-system row. -/
def w10CrossBlockPolynomialSystemRow
    (F : W10PolynomialPeriodSearchFamily) :
    TargetProjectionRow (W10CrossBlockPolynomialSystem F) where
  exactTarget := fun C =>
    C.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun C =>
    C.targetUpperConstructionFiveSixteenArbitrary

/-! ## Remaining-data ledger and matrix -/

/-- The explicit data packages still needed by the checked rows. -/
structure RemainingDataLedger where
  w8MinimalCertificate : Type
  w8ConcreteRemainingData : Type
  w8ConcreteLowerTables : Type
  w9FlattenedClosingFields : Type
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
    CrossBlockLowerBoundSearchW9.RoleHingedPeriodSearchFamily -> Prop
  w10CrossBlockPolynomialSystems :
    W10PolynomialPeriodSearchFamily -> Prop
  w10NormalizedPointPolynomialFamilies :
    W10NormalizedPointPeriodSearchFamily -> Prop
  w10NormalizedPointValueFamilies :
    W10NormalizedPointPeriodSearchFamily -> Type
  w10BranchSearchBlockedRoutes : FlexibleBranchSearchSummaryW10.BlockedRoutes
  fullSameRestShortcutBlocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  concreteT11RRowBlocked :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction

/-- The W10 ledger of remaining Pach--Toth data. -/
def remainingDataLedger : RemainingDataLedger where
  w8MinimalCertificate := W8MinimalExactTargetCertificate
  w8ConcreteRemainingData := W8ConcreteRemainingData
  w8ConcreteLowerTables := W8ConcreteNonConnectorLowerTableFamily
  w9FlattenedClosingFields := W9ClosingFields
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
  generatedPolynomialCertificates :=
    SearchGeneratedPolynomialCertificateFamily
  w10CrossBlockPolynomialSystems := W10CrossBlockPolynomialSystem
  w10NormalizedPointPolynomialFamilies :=
    W10NormalizedPointPolynomialFamily
  w10NormalizedPointValueFamilies := W10NormalizedPointValueFamily
  w10BranchSearchBlockedRoutes := FlexibleBranchSearchSummaryW10.blockedRoutes
  fullSameRestShortcutBlocked :=
    PachTothRemainingObligationsW9.concreteFourTargetMap_obstructs_fullSameRest
  concreteT11RRowBlocked :=
    PachTothRemainingObligationsW9.concreteFourTarget_T11RRow_obstruction

/-- The W10 closure matrix.  Every target-producing row remains conditional
on its visible input package. -/
structure Matrix where
  ledger : RemainingDataLedger
  arbitraryNBridge : ArbitraryNBridgeW10.Matrix
  branchSearchSummary : FlexibleBranchSearchSummaryW10.Matrix
  w8MinimalCertificate :
    TargetProjectionRow W8MinimalExactTargetCertificate
  w8ConcreteRemainingData :
    TargetProjectionRow W8ConcreteRemainingData
  w8ConcreteLowerTables :
    TargetProjectionRow W8ConcreteNonConnectorLowerTableFamily
  w9FlattenedClosingFields :
    ExactBlockProjectionRow W9ClosingFields
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
    forall F : CrossBlockLowerBoundSearchW9.RoleHingedPeriodSearchFamily,
      TargetProjectionRow (SearchGeneratedPolynomialCertificateFamily F)
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

/-- The checked W10 matrix. -/
def matrix : Matrix where
  ledger := remainingDataLedger
  arbitraryNBridge := ArbitraryNBridgeW10.matrix
  branchSearchSummary := FlexibleBranchSearchSummaryW10.matrix
  w8MinimalCertificate := w8MinimalExactTargetCertificateRow
  w8ConcreteRemainingData := w8ConcreteRemainingDataRow
  w8ConcreteLowerTables := w8ConcreteNonConnectorLowerTableFamilyRow
  w9FlattenedClosingFields := w9ClosingFieldsRow
  w9PeriodSearchSqValues := w9PeriodSearchSqValuePackageRow
  finalFlexibleLowerTables := finalFlexibleLowerTableFamilyRow
  finalFlexibleValueMatrices := finalFlexibleValueMatrixFamilyRow
  concreteValueMatrices := concreteValueMatrixFamilyRow
  candidateValueMatrices := candidateValueMatrixFamilyRow
  flexibleCandidateClosures := flexibleCandidateClosureDataRow
  generatedPolynomialCertificates :=
    generatedPolynomialCertificateFamilyRow
  w10PackedCrossBlockInequalities := w10CandidatePackedInequalitiesRow
  w10FlexibleFamilyFields := w10FlexibleFamilyFieldsRow
  w10ExactTargetRouteFields := w10ExactTargetRouteFieldsRow
  w10CrossBlockPolynomialSystems := w10CrossBlockPolynomialSystemRow

/-! ## Public W10 target projections -/

theorem targetUpperConstructionFiveSixteen_of_w9ClosingFields
    (F : W9ClosingFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w9FlattenedClosingFields.exactTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_w9ClosingFields
    (F : W9ClosingFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w9FlattenedClosingFields.arbitraryTarget F

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
    {F : CrossBlockLowerBoundSearchW9.RoleHingedPeriodSearchFamily}
    (C : SearchGeneratedPolynomialCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedPolynomialCertificates F).exactTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedPolynomialCertificateFamily
    {F : CrossBlockLowerBoundSearchW9.RoleHingedPeriodSearchFamily}
    (C : SearchGeneratedPolynomialCertificateFamily F) :
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

/-- The W10 matrix still records the concrete W9 same-rest obstruction. -/
theorem fullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.ledger.fullSameRestShortcutBlocked

/-- The W10 branch-search summary still blocks the concrete filtered
completion shortcut. -/
theorem w10ConcreteFilteredCompletion_blocked :
    Not FlexibleBranchSearchSummaryW10.W10ConcreteFilteredCompletion :=
  matrix.branchSearchSummary.blocked.transitionFilteredCompletion

/-- The explicit blocked row is still the exact-base `T1_1, r` row. -/
theorem concreteT11RRow_blocked :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction :=
  matrix.ledger.concreteT11RRowBlocked

end

end PachTothW10ClosureMatrix
end PachToth
end ErdosProblems1066
