import ErdosProblems1066.PachToth.GeneratedFinalIntegratedW11
import ErdosProblems1066.PachToth.GeneratedTargetIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockTargetIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 generated/cross-block final target consistency

This module is a final target-facing consistency ledger for the checked W11
generated-point and cross-block layers present in this checkout.  It records
numeric block certificates as ledger fields and exposes only conditional
exact, eventual, and arbitrary target projections from explicit inputs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedTargetFinalW11

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev GeneratedPointFamily :=
  GeneratedFinalIntegratedW11.GeneratedPointFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointFamily) :=
  GeneratedFinalIntegratedW11.GeneratedPointNormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointFamily) :=
  GeneratedFinalIntegratedW11.GeneratedPointNormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F

abbrev GeneratedFinalConditionalFamily :=
  GeneratedFinalIntegratedW11.FinalConditionalFamily

abbrev GeneratedCrossBlockFamily :=
  GeneratedFinalIntegratedW11.CrossBlockFamily

abbrev GeneratedCrossBlockInequalityLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedFinalIntegratedW11.CrossBlockInequalityLedger F

abbrev GeneratedCrossBlockClosureLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedFinalIntegratedW11.CrossBlockClosureLedger F

abbrev CrossBlockFamily :=
  CrossBlockFinalIntegratedW11.PeriodSearchFamily

abbrev RoleHingeCrossBlockFamily :=
  CrossBlockFinalIntegratedW11.RoleHingePeriodSearchFamily

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.CrossBlockClosureLedger F

abbrev PolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PolynomialRows F k hk

abbrev PolynomialRowFamilies (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.PolynomialRowFamilies F

abbrev GeneratedPointTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.GeneratedPointTable F k hk

abbrev PackedInequalities
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PackedInequalities F k hk

abbrev PositionPolynomialCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PositionPolynomialCertificate F k hk

abbrev ValueRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.ValueRows F k hk

abbrev ValueRowFamilies (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.ValueRowFamilies F

abbrev NonConnectorValueMatrix
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.NonConnectorValueMatrix F k hk

abbrev NonConnectorValueMatrixFamily (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.NonConnectorLowerTable F k hk

abbrev NonConnectorLowerTableFamily (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.NonConnectorLowerTableFamily F

abbrev PositionValueCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PositionValueCertificate F k hk

abbrev SqDistanceTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.SqDistanceTable F k hk

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingeCrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.RoleHingeCrossBlockInequalityPackage F

/-! ## Shared projection route -/

/-- Exact, eventual, and arbitrary target projections from one explicit input. -/
structure ProjectionRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace ProjectionRoute

/-- Promote an arbitrary route to an eventual route with threshold zero. -/
theorem eventualOfArbitrary (H : ArbitraryTarget) : EventualTarget := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

def ofGeneratedFinalRoute
    {alpha : Sort u}
    (R : GeneratedFinalIntegratedW11.ConditionalTargetRoute alpha) :
    ProjectionRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofGeneratedTargetRoute
    {alpha : Sort u}
    (R : GeneratedTargetIntegratedW11.TargetRoute alpha) :
    ProjectionRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofCrossBlockFinalRoute
    {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.ConditionalPachTothRoute alpha) :
    ProjectionRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofCrossBlockFamilyRoute
    {F : CrossBlockFamily} {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.FamilyTargetRoute F alpha) :
    ProjectionRoute alpha where
  exactTarget := R.route.exactTarget
  eventualTarget := R.route.eventualTarget
  arbitraryTarget := R.route.arbitraryTarget

end ProjectionRoute

/-! ## Explicit ledgers -/

/-- Explicit input ledgers consumed by this final layer. -/
structure ExplicitInputLedgers where
  generatedTarget :
    GeneratedTargetIntegratedW11.RequiredGeneratedPointInputs
  generatedPointFields :
    GeneratedFinalIntegratedW11.GeneratedPointFieldLedger
  generatedInequalityFields :
    GeneratedFinalIntegratedW11.InequalityLedgerFieldLedger
  crossBlockTarget :
    CrossBlockTargetIntegratedW11.ExplicitCrossBlockTargetInputs
  crossBlockFinal :
    CrossBlockFinalIntegratedW11.ExplicitCrossBlockFields
  pachTothFinalConsistency :
    PachTothW11FinalConsistency.OpenInputLedgers

/-- Package-shape ledger for all imported final target layers. -/
def explicitInputLedgers : ExplicitInputLedgers where
  generatedTarget := GeneratedTargetIntegratedW11.requiredGeneratedPointInputs
  generatedPointFields := GeneratedFinalIntegratedW11.generatedPointFieldLedger
  generatedInequalityFields :=
    GeneratedFinalIntegratedW11.inequalityLedgerFieldLedger
  crossBlockTarget := CrossBlockTargetIntegratedW11.explicitCrossBlockTargetInputs
  crossBlockFinal := CrossBlockFinalIntegratedW11.explicitCrossBlockFields
  pachTothFinalConsistency := PachTothW11FinalConsistency.openInputLedgers

/-- Checked W11 matrices used by this final layer. -/
structure ImportedTargetLedgers where
  generatedTarget : GeneratedTargetIntegratedW11.Matrix
  generatedFinal : GeneratedFinalIntegratedW11.Matrix
  crossBlockTarget : CrossBlockTargetIntegratedW11.Matrix
  crossBlockFinal : CrossBlockFinalIntegratedW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

/-- Imported checked matrices. -/
def importedTargetLedgers : ImportedTargetLedgers where
  generatedTarget := GeneratedTargetIntegratedW11.matrix
  generatedFinal := GeneratedFinalIntegratedW11.matrix
  crossBlockTarget := CrossBlockTargetIntegratedW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-- Numeric block certificates retained as fields, not public target
projections. -/
structure NumericCertificateLedger where
  generatedBlockScale : Nat
  generatedSeparation :
    forall {F : GeneratedCrossBlockFamily},
      GeneratedCrossBlockInequalityLedger F -> forall (k : Nat) (hk : 0 < k),
        CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k
          hk
  generatedBlockTargets :
    forall {F : GeneratedCrossBlockFamily},
      GeneratedCrossBlockInequalityLedger F -> forall k : Nat, 0 < k ->
        PachToth.targetUpperConstructionFiveSixteenAt
          (generatedBlockScale * k)
  crossBlockScale : Nat
  polynomialRows :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PolynomialRows F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  generatedPointTables :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      GeneratedPointTable F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  packedInequalities :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PackedInequalities F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  positionPolynomialCertificates :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PositionPolynomialCertificate F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  valueRows :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      ValueRows F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  valueMatrices :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      NonConnectorValueMatrix F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  lowerTables :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      NonConnectorLowerTable F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  positionValueCertificates :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PositionValueCertificate F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  sqDistanceTables :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      SqDistanceTable F k hk ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  inequalityLedgers :
    forall {F : CrossBlockFamily},
      CrossBlockInequalityLedger F -> forall k : Nat, 0 < k ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)
  closureLedgers :
    forall {F : CrossBlockFamily},
      CrossBlockClosureLedger F -> forall k : Nat, 0 < k ->
        PachToth.targetUpperConstructionFiveSixteenAt (crossBlockScale * k)

/-- Numeric certificate fields imported from the generated and cross-block
final ledgers. -/
def numericCertificateLedger : NumericCertificateLedger where
  generatedBlockScale := 16
  generatedSeparation := fun L k hk =>
    GeneratedFinalIntegratedW11.separated_of_crossBlockInequalityLedger L k hk
  generatedBlockTargets := fun L k hk =>
    GeneratedFinalIntegratedW11.exactBlockTarget_of_crossBlockInequalityLedger
      L k hk
  crossBlockScale := 16
  polynomialRows := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_polynomialRows
      (hk := hk) R
  generatedPointTables := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_generatedPointTables
      (hk := hk) R
  packedInequalities := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_packedInequalities
      (hk := hk) R
  positionPolynomialCertificates := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_positionPolynomialCertificates
      (hk := hk) R
  valueRows := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_valueRows
      (hk := hk) R
  valueMatrices := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_valueMatrices
      (hk := hk) R
  lowerTables := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_lowerTables
      (hk := hk) R
  positionValueCertificates := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_positionValueCertificates
      (hk := hk) R
  sqDistanceTables := fun hk R =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_sqDistanceTables
      (hk := hk) R
  inequalityLedgers := fun L k hk =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_crossBlockInequalityLedger
      L k hk
  closureLedgers := fun C k hk =>
    CrossBlockFinalIntegratedW11.exactBlockTarget_of_crossBlockClosureLedger
      C k hk

/-! ## Conditional route ledgers -/

/-- Generated-point and generated cross-block target projections. -/
structure GeneratedProjectionLedger where
  normalizedPolynomial :
    forall F : GeneratedPointFamily,
      ProjectionRoute (GeneratedPointNormalizedPolynomialFields F)
  normalizedValue :
    forall F : GeneratedPointFamily,
      ProjectionRoute (GeneratedPointNormalizedValueFields F)
  lowerBound :
    forall F : GeneratedPointFamily,
      ProjectionRoute (GeneratedPointLowerBoundFields F)
  finalConditionalFamily :
    ProjectionRoute GeneratedFinalConditionalFamily
  crossBlockInequality :
    forall F : GeneratedCrossBlockFamily,
      ProjectionRoute (GeneratedCrossBlockInequalityLedger F)
  crossBlockClosure :
    forall F : GeneratedCrossBlockFamily,
      ProjectionRoute (GeneratedCrossBlockClosureLedger F)

/-- Checked generated-point and generated cross-block projection routes. -/
def generatedProjectionLedger : GeneratedProjectionLedger where
  normalizedPolynomial := fun F =>
    ProjectionRoute.ofGeneratedFinalRoute
      (GeneratedFinalIntegratedW11.matrix.generatedPoint.normalizedPolynomial F)
  normalizedValue := fun F =>
    ProjectionRoute.ofGeneratedFinalRoute
      (GeneratedFinalIntegratedW11.matrix.generatedPoint.normalizedValue F)
  lowerBound := fun F =>
    ProjectionRoute.ofGeneratedFinalRoute
      (GeneratedFinalIntegratedW11.matrix.generatedPoint.lowerBound F)
  finalConditionalFamily :=
    ProjectionRoute.ofGeneratedFinalRoute
      GeneratedFinalIntegratedW11.matrix.generatedPoint.finalConditionalFamily
  crossBlockInequality := fun F =>
    ProjectionRoute.ofGeneratedFinalRoute
      (GeneratedFinalIntegratedW11.matrix.generatedCrossBlock F).directRoute
  crossBlockClosure := fun F =>
    ProjectionRoute.ofGeneratedFinalRoute
      (GeneratedFinalIntegratedW11.matrix.generatedCrossBlock F).closureRoute

/-- Target projections from the cross-block final layer. -/
structure CrossBlockProjectionLedger where
  polynomialRowFamilies :
    forall F : CrossBlockFamily,
      ProjectionRoute (PolynomialRowFamilies F)
  valueRowFamilies :
    forall F : CrossBlockFamily,
      ProjectionRoute (ValueRowFamilies F)
  valueMatrixFamilies :
    forall F : CrossBlockFamily,
      ProjectionRoute (NonConnectorValueMatrixFamily F)
  lowerTableFamilies :
    forall F : CrossBlockFamily,
      ProjectionRoute (NonConnectorLowerTableFamily F)
  inequalityLedgers :
    forall F : CrossBlockFamily,
      ProjectionRoute (CrossBlockInequalityLedger F)
  inequalityLedgersViaGeneratedTarget :
    forall F : CrossBlockFamily,
      ProjectionRoute (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : CrossBlockFamily,
      ProjectionRoute (CrossBlockClosureLedger F)
  closureLedgersViaPachTothIntegrated :
    forall F : CrossBlockFamily,
      ProjectionRoute (CrossBlockClosureLedger F)
  roleHingeInequalityPackages :
    forall F : RoleHingeCrossBlockFamily,
      ProjectionRoute (RoleHingeCrossBlockInequalityPackage F)

/-- Checked cross-block final projection routes. -/
def crossBlockProjectionLedger : CrossBlockProjectionLedger where
  polynomialRowFamilies := fun F =>
    ProjectionRoute.ofCrossBlockFamilyRoute
      (CrossBlockFinalIntegratedW11.matrix.polynomial.rowFamilies F)
  valueRowFamilies := fun F =>
    ProjectionRoute.ofCrossBlockFamilyRoute
      (CrossBlockFinalIntegratedW11.matrix.value.rowFamilies F)
  valueMatrixFamilies := fun F =>
    ProjectionRoute.ofCrossBlockFamilyRoute
      (CrossBlockFinalIntegratedW11.matrix.value.valueMatrixFamilies F)
  lowerTableFamilies := fun F =>
    ProjectionRoute.ofCrossBlockFamilyRoute
      (CrossBlockFinalIntegratedW11.matrix.value.lowerTableFamilies F)
  inequalityLedgers := fun F =>
    ProjectionRoute.ofCrossBlockFamilyRoute
      (CrossBlockFinalIntegratedW11.matrix.ledger.inequalityLedgers F)
  inequalityLedgersViaGeneratedTarget := fun F =>
    ProjectionRoute.ofCrossBlockFinalRoute
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.generatedTargetInequalityLedgers F)
  closureLedgers := fun F =>
    ProjectionRoute.ofCrossBlockFamilyRoute
      (CrossBlockFinalIntegratedW11.matrix.ledger.closureLedgers F)
  closureLedgersViaPachTothIntegrated := fun F =>
    ProjectionRoute.ofCrossBlockFinalRoute
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.pachTothIntegratedClosureLedgers F)
  roleHingeInequalityPackages := fun F =>
    ProjectionRoute.ofCrossBlockFinalRoute
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.roleHingeInequalityPackages F)

/-- Final consistency projections currently exposed by the broad W11 ledger. -/
structure FinalConsistencyProjectionLedger where
  generatedLowerBoundArbitrary :
    forall {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily},
      GeneratedTargetIntegratedW11.LowerBoundFields F -> ArbitraryTarget
  arbitraryNCrossBlockClosureArbitrary :
    forall {F : ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily},
      ArbitraryNIntegratedW11.CrossBlockClosureLedger F -> ArbitraryTarget
  transitionArbitrary :
    TransitionIntegratedW11.TransitionRouteFields -> ArbitraryTarget

/-- Checked final-consistency arbitrary projections. -/
def finalConsistencyProjectionLedger : FinalConsistencyProjectionLedger where
  generatedLowerBoundArbitrary := fun C =>
    PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBoundFields
      C
  arbitraryNCrossBlockClosureArbitrary := fun C =>
    PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
      C
  transitionArbitrary := fun R =>
    PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
      R

/-! ## Final matrix -/

/-- Final generated/cross-block target consistency matrix. -/
structure Matrix where
  inputs : ExplicitInputLedgers
  imports : ImportedTargetLedgers
  numericCertificates : NumericCertificateLedger
  generated : GeneratedProjectionLedger
  crossBlock : CrossBlockProjectionLedger
  finalConsistency : FinalConsistencyProjectionLedger
  blockers : GeneratedTargetIntegratedW11.TransitionBlockers

/-- Checked final generated/cross-block target consistency matrix. -/
def matrix : Matrix where
  inputs := explicitInputLedgers
  imports := importedTargetLedgers
  numericCertificates := numericCertificateLedger
  generated := generatedProjectionLedger
  crossBlock := crossBlockProjectionLedger
  finalConsistency := finalConsistencyProjectionLedger
  blockers := GeneratedTargetIntegratedW11.transitionBlockers

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public generated projections -/

theorem exactTarget_of_normalizedPolynomialFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    ExactTarget :=
  (matrix.generated.normalizedPolynomial F).exactTarget C

theorem eventualTarget_of_normalizedPolynomialFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    EventualTarget :=
  (matrix.generated.normalizedPolynomial F).eventualTarget C

theorem arbitraryTarget_of_normalizedPolynomialFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    ArbitraryTarget :=
  (matrix.generated.normalizedPolynomial F).arbitraryTarget C

theorem exactTarget_of_normalizedValueFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    ExactTarget :=
  (matrix.generated.normalizedValue F).exactTarget C

theorem eventualTarget_of_normalizedValueFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    EventualTarget :=
  (matrix.generated.normalizedValue F).eventualTarget C

theorem arbitraryTarget_of_normalizedValueFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    ArbitraryTarget :=
  (matrix.generated.normalizedValue F).arbitraryTarget C

theorem exactTarget_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ExactTarget :=
  (matrix.generated.lowerBound F).exactTarget C

theorem eventualTarget_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    EventualTarget :=
  (matrix.generated.lowerBound F).eventualTarget C

theorem arbitraryTarget_of_lowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.generated.lowerBound F).arbitraryTarget C

theorem exactTarget_of_finalConditionalFamily
    (C : GeneratedFinalConditionalFamily) :
    ExactTarget :=
  matrix.generated.finalConditionalFamily.exactTarget C

theorem eventualTarget_of_finalConditionalFamily
    (C : GeneratedFinalConditionalFamily) :
    EventualTarget :=
  matrix.generated.finalConditionalFamily.eventualTarget C

theorem arbitraryTarget_of_finalConditionalFamily
    (C : GeneratedFinalConditionalFamily) :
    ArbitraryTarget :=
  matrix.generated.finalConditionalFamily.arbitraryTarget C

theorem exactTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.generated.crossBlockInequality F).exactTarget L

theorem eventualTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    EventualTarget :=
  (matrix.generated.crossBlockInequality F).eventualTarget L

theorem arbitraryTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.generated.crossBlockInequality F).arbitraryTarget L

theorem exactTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.generated.crossBlockClosure F).exactTarget C

theorem eventualTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    EventualTarget :=
  (matrix.generated.crossBlockClosure F).eventualTarget C

theorem arbitraryTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.generated.crossBlockClosure F).arbitraryTarget C

/-! ## Public cross-block projections -/

theorem exactTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ExactTarget :=
  (matrix.crossBlock.polynomialRowFamilies F).exactTarget R

theorem eventualTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    EventualTarget :=
  (matrix.crossBlock.polynomialRowFamilies F).eventualTarget R

theorem arbitraryTarget_of_polynomialRowFamilies
    {F : CrossBlockFamily}
    (R : PolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.crossBlock.polynomialRowFamilies F).arbitraryTarget R

theorem exactTarget_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    ExactTarget :=
  (matrix.crossBlock.valueRowFamilies F).exactTarget R

theorem eventualTarget_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    EventualTarget :=
  (matrix.crossBlock.valueRowFamilies F).eventualTarget R

theorem arbitraryTarget_of_valueRowFamilies
    {F : CrossBlockFamily}
    (R : ValueRowFamilies F) :
    ArbitraryTarget :=
  (matrix.crossBlock.valueRowFamilies F).arbitraryTarget R

theorem exactTarget_of_valueMatrixFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorValueMatrixFamily F) :
    ExactTarget :=
  (matrix.crossBlock.valueMatrixFamilies F).exactTarget R

theorem eventualTarget_of_valueMatrixFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorValueMatrixFamily F) :
    EventualTarget :=
  (matrix.crossBlock.valueMatrixFamilies F).eventualTarget R

theorem arbitraryTarget_of_valueMatrixFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorValueMatrixFamily F) :
    ArbitraryTarget :=
  (matrix.crossBlock.valueMatrixFamilies F).arbitraryTarget R

theorem exactTarget_of_lowerTableFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorLowerTableFamily F) :
    ExactTarget :=
  (matrix.crossBlock.lowerTableFamilies F).exactTarget R

theorem eventualTarget_of_lowerTableFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorLowerTableFamily F) :
    EventualTarget :=
  (matrix.crossBlock.lowerTableFamilies F).eventualTarget R

theorem arbitraryTarget_of_lowerTableFamilies
    {F : CrossBlockFamily}
    (R : NonConnectorLowerTableFamily F) :
    ArbitraryTarget :=
  (matrix.crossBlock.lowerTableFamilies F).arbitraryTarget R

theorem exactTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.crossBlock.inequalityLedgers F).exactTarget L

theorem eventualTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    EventualTarget :=
  (matrix.crossBlock.inequalityLedgers F).eventualTarget L

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.inequalityLedgers F).arbitraryTarget L

theorem exactTarget_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.crossBlock.inequalityLedgersViaGeneratedTarget F).exactTarget L

theorem eventualTarget_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    EventualTarget :=
  (matrix.crossBlock.inequalityLedgersViaGeneratedTarget F).eventualTarget L

theorem arbitraryTarget_viaGeneratedTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.inequalityLedgersViaGeneratedTarget F).arbitraryTarget L

theorem exactTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.crossBlock.closureLedgers F).exactTarget C

theorem eventualTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    EventualTarget :=
  (matrix.crossBlock.closureLedgers F).eventualTarget C

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.closureLedgers F).arbitraryTarget C

theorem exactTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.crossBlock.closureLedgersViaPachTothIntegrated F).exactTarget C

theorem eventualTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    EventualTarget :=
  (matrix.crossBlock.closureLedgersViaPachTothIntegrated F).eventualTarget C

theorem arbitraryTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.closureLedgersViaPachTothIntegrated F).arbitraryTarget C

theorem exactTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ExactTarget :=
  (matrix.crossBlock.roleHingeInequalityPackages F).exactTarget R

theorem eventualTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    EventualTarget :=
  (matrix.crossBlock.roleHingeInequalityPackages F).eventualTarget R

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.crossBlock.roleHingeInequalityPackages F).arbitraryTarget R

/-! ## Public final-consistency projections -/

theorem arbitraryTarget_viaFinalConsistency_of_lowerBoundFields
    {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedTargetIntegratedW11.LowerBoundFields F) :
    ArbitraryTarget :=
  matrix.finalConsistency.generatedLowerBoundArbitrary C

theorem arbitraryTarget_viaFinalConsistency_of_crossBlockClosureLedger
    {F : ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily}
    (C : ArbitraryNIntegratedW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.finalConsistency.arbitraryNCrossBlockClosureArbitrary C

theorem arbitraryTarget_viaFinalConsistency_of_transitionRouteFields
    (R : TransitionIntegratedW11.TransitionRouteFields) :
    ArbitraryTarget :=
  matrix.finalConsistency.transitionArbitrary R

/-! ## Imported blockers -/

theorem transition_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.concreteFourTargetRouteClaim

theorem transition_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem transition_concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

end

end GeneratedTargetFinalW11
end PachToth
end ErdosProblems1066
