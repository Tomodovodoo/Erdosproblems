import ErdosProblems1066.PachToth.GeneratedTargetFinalW11
import ErdosProblems1066.PachToth.GeneratedFinalIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 generated/cross-block final consistency

This module is the generated/cross-block consistency layer over the checked
W11 final ledgers.  It records the numeric block certificates as data fields
and exposes target conclusions only through routes that require an explicit
input package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedCrossBlockFinalW11

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev GeneratedPointFamily :=
  GeneratedTargetFinalW11.GeneratedPointFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointFamily) :=
  GeneratedTargetFinalW11.GeneratedPointNormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointFamily) :=
  GeneratedTargetFinalW11.GeneratedPointNormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  GeneratedTargetFinalW11.GeneratedPointLowerBoundFields F

abbrev GeneratedFinalConditionalFamily :=
  GeneratedTargetFinalW11.GeneratedFinalConditionalFamily

abbrev GeneratedCrossBlockFamily :=
  GeneratedTargetFinalW11.GeneratedCrossBlockFamily

abbrev GeneratedCrossBlockInequalityLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedTargetFinalW11.GeneratedCrossBlockInequalityLedger F

abbrev GeneratedCrossBlockClosureLedger
    (F : GeneratedCrossBlockFamily) :=
  GeneratedTargetFinalW11.GeneratedCrossBlockClosureLedger F

abbrev CrossBlockFamily :=
  GeneratedTargetFinalW11.CrossBlockFamily

abbrev RoleHingeCrossBlockFamily :=
  GeneratedTargetFinalW11.RoleHingeCrossBlockFamily

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  GeneratedTargetFinalW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  GeneratedTargetFinalW11.CrossBlockClosureLedger F

abbrev PolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.PolynomialRows F k hk

abbrev PolynomialRowFamilies (F : CrossBlockFamily) :=
  GeneratedTargetFinalW11.PolynomialRowFamilies F

abbrev GeneratedPointTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.GeneratedPointTable F k hk

abbrev PackedInequalities
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.PackedInequalities F k hk

abbrev PositionPolynomialCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.PositionPolynomialCertificate F k hk

abbrev ValueRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.ValueRows F k hk

abbrev ValueRowFamilies (F : CrossBlockFamily) :=
  GeneratedTargetFinalW11.ValueRowFamilies F

abbrev NonConnectorValueMatrix
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.NonConnectorValueMatrix F k hk

abbrev NonConnectorValueMatrixFamily (F : CrossBlockFamily) :=
  GeneratedTargetFinalW11.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.NonConnectorLowerTable F k hk

abbrev NonConnectorLowerTableFamily (F : CrossBlockFamily) :=
  GeneratedTargetFinalW11.NonConnectorLowerTableFamily F

abbrev PositionValueCertificate
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.PositionValueCertificate F k hk

abbrev SqDistanceTable
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedTargetFinalW11.SqDistanceTable F k hk

abbrev RoleHingeCrossBlockInequalityPackage
    (F : RoleHingeCrossBlockFamily) :=
  GeneratedTargetFinalW11.RoleHingeCrossBlockInequalityPackage F

abbrev ExactTargetAssumptions :=
  ArbitraryNTargetFinalW11.ExactTargetAssumptions

abbrev ExactClosedChainPackage :=
  ArbitraryNTargetFinalW11.ExactClosedChainPackage

abbrev ExactGeneratedClosedChainPackage :=
  ArbitraryNTargetFinalW11.ExactGeneratedClosedChainPackage

abbrev SmallExactFields :=
  ArbitraryNTargetFinalW11.SmallExactFields

/-! ## Conditional route shapes -/

/-- Exact, eventual, and arbitrary target projections from one explicit input. -/
structure ConditionalRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace ConditionalRoute

def ofProjection
    {alpha : Sort u}
    (R : GeneratedTargetFinalW11.ProjectionRoute alpha) :
    ConditionalRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofGeneratedFinal
    {alpha : Sort u}
    (R : GeneratedFinalIntegratedW11.ConditionalTargetRoute alpha) :
    ConditionalRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofCrossBlockFinal
    {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.ConditionalPachTothRoute alpha) :
    ConditionalRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end ConditionalRoute

/-- Fixed-`n`, exact, eventual, and arbitrary projections from one input. -/
structure FixedConditionalRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace FixedConditionalRoute

def toConditionalRoute
    {alpha : Sort u}
    (R : FixedConditionalRoute alpha) :
    ConditionalRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofCrossBlockFinal
    {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.ConditionalPachTothRoute alpha) :
    FixedConditionalRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofCrossBlockFamily
    {F : CrossBlockFamily} {alpha : Sort u}
    (R : CrossBlockFinalIntegratedW11.FamilyTargetRoute F alpha) :
    FixedConditionalRoute alpha where
  exactTarget := R.route.exactTarget
  fixedTarget := R.route.fixedTarget
  eventualTarget := R.route.eventualTarget
  arbitraryTarget := R.route.arbitraryTarget

def ofArbitraryNExact
    {alpha : Sort u}
    (R : ArbitraryNTargetFinalW11.ExactTargetRoute alpha) :
    FixedConditionalRoute alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end FixedConditionalRoute

/-- Arbitrary-only routes from ledgers that currently expose only that face. -/
structure ArbitraryRoute (alpha : Sort u) : Sort (max 1 u) where
  arbitraryTarget : alpha -> ArbitraryTarget

/-! ## Imported and explicit ledgers -/

/-- Existing checked final ledgers used by this consistency layer. -/
structure ImportedFinalLedgers where
  generatedTargetFinal : GeneratedTargetFinalW11.Matrix
  generatedFinalIntegrated : GeneratedFinalIntegratedW11.Matrix
  crossBlockFinalIntegrated : CrossBlockFinalIntegratedW11.Matrix
  arbitraryNTargetFinal : ArbitraryNTargetFinalW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

def importedFinalLedgers : ImportedFinalLedgers where
  generatedTargetFinal := GeneratedTargetFinalW11.matrix
  generatedFinalIntegrated := GeneratedFinalIntegratedW11.matrix
  crossBlockFinalIntegrated := CrossBlockFinalIntegratedW11.matrix
  arbitraryNTargetFinal := ArbitraryNTargetFinalW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-- Explicit package ledgers retained beside the route data. -/
structure ExplicitFinalLedgers where
  generatedTargetInputs : GeneratedTargetFinalW11.ExplicitInputLedgers
  generatedPointFields : GeneratedFinalIntegratedW11.GeneratedPointFieldLedger
  generatedInequalityFields :
    GeneratedFinalIntegratedW11.InequalityLedgerFieldLedger
  crossBlockFields : CrossBlockFinalIntegratedW11.ExplicitCrossBlockFields
  arbitraryNGeneratedFields : ArbitraryNTargetFinalW11.GeneratedFields
  arbitraryNCrossBlockFields : ArbitraryNTargetFinalW11.CrossBlockFields
  finalConsistencyInputs : PachTothW11FinalConsistency.OpenInputLedgers

def explicitFinalLedgers : ExplicitFinalLedgers where
  generatedTargetInputs := GeneratedTargetFinalW11.explicitInputLedgers
  generatedPointFields := GeneratedFinalIntegratedW11.generatedPointFieldLedger
  generatedInequalityFields :=
    GeneratedFinalIntegratedW11.inequalityLedgerFieldLedger
  crossBlockFields := CrossBlockFinalIntegratedW11.explicitCrossBlockFields
  arbitraryNGeneratedFields := ArbitraryNTargetFinalW11.generatedFields
  arbitraryNCrossBlockFields := ArbitraryNTargetFinalW11.crossBlockFields
  finalConsistencyInputs := PachTothW11FinalConsistency.openInputLedgers

/-! ## Numeric certificate ledger -/

/-- Numeric block certificates retained as explicit fields. -/
structure NumericBlockCertificateLedger where
  generatedBlockScale : Nat
  generatedBlockScale_eq : generatedBlockScale = 16
  generatedSeparation :
    forall {F : GeneratedCrossBlockFamily},
      GeneratedCrossBlockInequalityLedger F -> forall (k : Nat) (hk : 0 < k),
        CrossBlockInequalityClosureW11.GeneratedGlobalSeparationAt F k hk
  generatedInequalityBlocks :
    forall {F : GeneratedCrossBlockFamily},
      GeneratedCrossBlockInequalityLedger F -> forall (k : Nat), 0 < k ->
        FixedTarget (generatedBlockScale * k)
  crossBlockScale : Nat
  crossBlockScale_eq : crossBlockScale = 16
  polynomialRows :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PolynomialRows F k hk -> FixedTarget (crossBlockScale * k)
  generatedPointTables :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      GeneratedPointTable F k hk -> FixedTarget (crossBlockScale * k)
  packedInequalities :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PackedInequalities F k hk -> FixedTarget (crossBlockScale * k)
  positionPolynomialCertificates :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PositionPolynomialCertificate F k hk ->
        FixedTarget (crossBlockScale * k)
  valueRows :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      ValueRows F k hk -> FixedTarget (crossBlockScale * k)
  valueMatrices :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      NonConnectorValueMatrix F k hk -> FixedTarget (crossBlockScale * k)
  lowerTables :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      NonConnectorLowerTable F k hk -> FixedTarget (crossBlockScale * k)
  positionValueCertificates :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      PositionValueCertificate F k hk -> FixedTarget (crossBlockScale * k)
  sqDistanceTables :
    forall {F : CrossBlockFamily} {k : Nat} (hk : 0 < k),
      SqDistanceTable F k hk -> FixedTarget (crossBlockScale * k)
  crossBlockInequalitySeparation :
    forall {F : CrossBlockFamily},
      CrossBlockInequalityLedger F -> forall (k : Nat) (hk : 0 < k),
        CrossBlockFinalIntegratedW11.GeneratedGlobalSeparationAt F k hk
  crossBlockClosureSeparation :
    forall {F : CrossBlockFamily},
      CrossBlockClosureLedger F -> forall (k : Nat) (hk : 0 < k),
        CrossBlockFinalIntegratedW11.GeneratedGlobalSeparationAt F k hk
  inequalityLedgers :
    forall {F : CrossBlockFamily},
      CrossBlockInequalityLedger F -> forall (k : Nat), 0 < k ->
        FixedTarget (crossBlockScale * k)
  closureLedgers :
    forall {F : CrossBlockFamily},
      CrossBlockClosureLedger F -> forall (k : Nat), 0 < k ->
        FixedTarget (crossBlockScale * k)
  smallLengthScale : Nat
  smallLengthScale_eq : smallLengthScale = 16
  smallExactLengthOne :
    SmallExactFields -> FixedTarget (smallLengthScale * 1)
  smallExactLengthFive :
    SmallExactFields -> FixedTarget (smallLengthScale * 5)

def numericBlockCertificateLedger : NumericBlockCertificateLedger where
  generatedBlockScale := 16
  generatedBlockScale_eq := rfl
  generatedSeparation := fun L k hk =>
    GeneratedTargetFinalW11.matrix.numericCertificates
      |>.generatedSeparation L k hk
  generatedInequalityBlocks := fun L k hk =>
    GeneratedTargetFinalW11.matrix.numericCertificates
      |>.generatedBlockTargets L k hk
  crossBlockScale := 16
  crossBlockScale_eq := rfl
  polynomialRows := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates.polynomialRows hk R
  generatedPointTables := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates
      |>.generatedPointTables hk R
  packedInequalities := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates.packedInequalities hk R
  positionPolynomialCertificates := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates
      |>.positionPolynomialCertificates hk R
  valueRows := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates.valueRows hk R
  valueMatrices := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates.valueMatrices hk R
  lowerTables := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates.lowerTables hk R
  positionValueCertificates := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates
      |>.positionValueCertificates hk R
  sqDistanceTables := fun hk R =>
    GeneratedTargetFinalW11.matrix.numericCertificates.sqDistanceTables hk R
  crossBlockInequalitySeparation := fun L k hk =>
    CrossBlockFinalIntegratedW11.separated_of_crossBlockInequalityLedger
      L k hk
  crossBlockClosureSeparation := fun C k hk =>
    CrossBlockFinalIntegratedW11.separated_of_crossBlockClosureLedger C k hk
  inequalityLedgers := fun L k hk =>
    GeneratedTargetFinalW11.matrix.numericCertificates.inequalityLedgers
      L k hk
  closureLedgers := fun C k hk =>
    GeneratedTargetFinalW11.matrix.numericCertificates.closureLedgers C k hk
  smallLengthScale := 16
  smallLengthScale_eq := rfl
  smallExactLengthOne := fun E =>
    ArbitraryNTargetFinalW11.targetAt_lengthOne_of_smallExactFields E
  smallExactLengthFive := fun E =>
    ArbitraryNTargetFinalW11.targetAt_lengthFive_of_smallExactFields E

/-! ## Conditional route ledgers -/

/-- Generated-point and generated cross-block conditional routes. -/
structure GeneratedRouteLedger where
  normalizedPolynomial :
    forall F : GeneratedPointFamily,
      ConditionalRoute (GeneratedPointNormalizedPolynomialFields F)
  normalizedValue :
    forall F : GeneratedPointFamily,
      ConditionalRoute (GeneratedPointNormalizedValueFields F)
  lowerBound :
    forall F : GeneratedPointFamily,
      ConditionalRoute (GeneratedPointLowerBoundFields F)
  finalConditionalFamily :
    ConditionalRoute GeneratedFinalConditionalFamily
  crossBlockInequality :
    forall F : GeneratedCrossBlockFamily,
      ConditionalRoute (GeneratedCrossBlockInequalityLedger F)
  crossBlockClosure :
    forall F : GeneratedCrossBlockFamily,
      ConditionalRoute (GeneratedCrossBlockClosureLedger F)

def generatedRouteLedger : GeneratedRouteLedger where
  normalizedPolynomial := fun F =>
    ConditionalRoute.ofProjection
      (GeneratedTargetFinalW11.matrix.generated.normalizedPolynomial F)
  normalizedValue := fun F =>
    ConditionalRoute.ofProjection
      (GeneratedTargetFinalW11.matrix.generated.normalizedValue F)
  lowerBound := fun F =>
    ConditionalRoute.ofProjection
      (GeneratedTargetFinalW11.matrix.generated.lowerBound F)
  finalConditionalFamily :=
    ConditionalRoute.ofProjection
      GeneratedTargetFinalW11.matrix.generated.finalConditionalFamily
  crossBlockInequality := fun F =>
    ConditionalRoute.ofProjection
      (GeneratedTargetFinalW11.matrix.generated.crossBlockInequality F)
  crossBlockClosure := fun F =>
    ConditionalRoute.ofProjection
      (GeneratedTargetFinalW11.matrix.generated.crossBlockClosure F)

/-- Cross-block fixed and conditional target routes. -/
structure CrossBlockRouteLedger where
  polynomialRowFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (PolynomialRowFamilies F)
  valueRowFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (ValueRowFamilies F)
  valueMatrixFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (NonConnectorValueMatrixFamily F)
  lowerTableFamilies :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (NonConnectorLowerTableFamily F)
  inequalityLedgers :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (CrossBlockInequalityLedger F)
  inequalityLedgersViaGeneratedTarget :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (CrossBlockInequalityLedger F)
  closureLedgers :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (CrossBlockClosureLedger F)
  closureLedgersViaPachTothIntegrated :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (CrossBlockClosureLedger F)
  roleHingeInequalityPackages :
    forall F : RoleHingeCrossBlockFamily,
      FixedConditionalRoute (RoleHingeCrossBlockInequalityPackage F)

def crossBlockRouteLedger : CrossBlockRouteLedger where
  polynomialRowFamilies := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.polynomial.rowFamilies F)
  valueRowFamilies := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.value.rowFamilies F)
  valueMatrixFamilies := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.value.valueMatrixFamilies F)
  lowerTableFamilies := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.value.lowerTableFamilies F)
  inequalityLedgers := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.ledger.inequalityLedgers F)
  inequalityLedgersViaGeneratedTarget := fun F =>
    FixedConditionalRoute.ofCrossBlockFinal
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.generatedTargetInequalityLedgers F)
  closureLedgers := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (CrossBlockFinalIntegratedW11.matrix.ledger.closureLedgers F)
  closureLedgersViaPachTothIntegrated := fun F =>
    FixedConditionalRoute.ofCrossBlockFinal
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.pachTothIntegratedClosureLedgers F)
  roleHingeInequalityPackages := fun F =>
    FixedConditionalRoute.ofCrossBlockFinal
      (CrossBlockFinalIntegratedW11.matrix.ledger
        |>.roleHingeInequalityPackages F)

/-- Arbitrary-`n` target routes that overlap the generated/cross-block ledgers. -/
structure ArbitraryNRouteLedger where
  exactAssumptions : FixedConditionalRoute ExactTargetAssumptions
  exactClosedChains : FixedConditionalRoute ExactClosedChainPackage
  exactGeneratedClosedChains :
    FixedConditionalRoute ExactGeneratedClosedChainPackage
  generatedNormalizedPolynomial :
    forall F : GeneratedPointFamily,
      ConditionalRoute (GeneratedPointNormalizedPolynomialFields F)
  generatedLowerBound :
    forall F : GeneratedPointFamily,
      ConditionalRoute (GeneratedPointLowerBoundFields F)
  crossBlockInequality :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (CrossBlockInequalityLedger F)
  crossBlockClosure :
    forall F : CrossBlockFamily,
      FixedConditionalRoute (CrossBlockClosureLedger F)
  generatedCrossBlockInequality :
    forall F : GeneratedCrossBlockFamily,
      ConditionalRoute (GeneratedCrossBlockInequalityLedger F)
  generatedCrossBlockClosure :
    forall F : GeneratedCrossBlockFamily,
      ConditionalRoute (GeneratedCrossBlockClosureLedger F)

def arbitraryNRouteLedger : ArbitraryNRouteLedger where
  exactAssumptions :=
    FixedConditionalRoute.ofArbitraryNExact
      ArbitraryNTargetFinalW11.matrix.exact.exactAssumptions
  exactClosedChains :=
    FixedConditionalRoute.ofArbitraryNExact
      ArbitraryNTargetFinalW11.matrix.exact.closedChains
  exactGeneratedClosedChains :=
    FixedConditionalRoute.ofArbitraryNExact
      ArbitraryNTargetFinalW11.matrix.exact.generatedClosedChains
  generatedNormalizedPolynomial := fun F =>
    ConditionalRoute.ofGeneratedFinal
      (ArbitraryNTargetFinalW11.matrix.generated.routes
        |>.normalizedPolynomial F)
  generatedLowerBound := fun F =>
    ConditionalRoute.ofGeneratedFinal
      (ArbitraryNTargetFinalW11.matrix.generated.routes.lowerBound F)
  crossBlockInequality := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (ArbitraryNTargetFinalW11.matrix.crossBlock.ledger
        |>.inequalityLedgers F)
  crossBlockClosure := fun F =>
    FixedConditionalRoute.ofCrossBlockFamily
      (ArbitraryNTargetFinalW11.matrix.crossBlock.ledger.closureLedgers F)
  generatedCrossBlockInequality := fun F =>
    ConditionalRoute.ofGeneratedFinal
      (ArbitraryNTargetFinalW11.matrix.crossBlock.generatedCrossBlock F
        |>.directRoute)
  generatedCrossBlockClosure := fun F =>
    ConditionalRoute.ofGeneratedFinal
      (ArbitraryNTargetFinalW11.matrix.crossBlock.generatedCrossBlock F
        |>.closureRoute)

/-- Final-consistency routes that currently expose arbitrary projections. -/
structure FinalConsistencyRouteLedger where
  generatedLowerBound :
    forall {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily},
      ArbitraryRoute (GeneratedTargetIntegratedW11.LowerBoundFields F)
  arbitraryNCrossBlockClosure :
    forall {F : ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily},
      ArbitraryRoute (ArbitraryNIntegratedW11.CrossBlockClosureLedger F)
  transitionRoute :
    ArbitraryRoute TransitionIntegratedW11.TransitionRouteFields
  periodExactCandidate :
    forall {T : PeriodIntegratedW11.Candidate},
      ArbitraryRoute (PeriodIntegratedW11.ExactCandidatePeriodFields T)

def finalConsistencyRouteLedger : FinalConsistencyRouteLedger where
  generatedLowerBound := fun {F} =>
    { arbitraryTarget := fun C =>
        PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBoundFields
          (F := F) C }
  arbitraryNCrossBlockClosure := fun {F} =>
    { arbitraryTarget := fun C =>
        PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
          (F := F) C }
  transitionRoute :=
    { arbitraryTarget := fun R =>
        PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
          R }
  periodExactCandidate := fun {T} =>
    { arbitraryTarget := fun D =>
        PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_periodExactCandidateFields
          (T := T) D }

/-! ## Final matrix -/

/-- Final generated/cross-block consistency matrix with explicit certificates. -/
structure Matrix where
  explicitLedgers : ExplicitFinalLedgers
  imported : ImportedFinalLedgers
  numeric : NumericBlockCertificateLedger
  generated : GeneratedRouteLedger
  crossBlock : CrossBlockRouteLedger
  arbitraryN : ArbitraryNRouteLedger
  finalConsistency : FinalConsistencyRouteLedger
  blockers : GeneratedTargetIntegratedW11.TransitionBlockers

def matrix : Matrix where
  explicitLedgers := explicitFinalLedgers
  imported := importedFinalLedgers
  numeric := numericBlockCertificateLedger
  generated := generatedRouteLedger
  crossBlock := crossBlockRouteLedger
  arbitraryN := arbitraryNRouteLedger
  finalConsistency := finalConsistencyRouteLedger
  blockers := GeneratedTargetIntegratedW11.transitionBlockers

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public numeric certificates -/

theorem generatedBlockScale_eq_sixteen :
    matrix.numeric.generatedBlockScale = 16 :=
  matrix.numeric.generatedBlockScale_eq

theorem crossBlockScale_eq_sixteen :
    matrix.numeric.crossBlockScale = 16 :=
  matrix.numeric.crossBlockScale_eq

theorem smallLengthScale_eq_sixteen :
    matrix.numeric.smallLengthScale = 16 :=
  matrix.numeric.smallLengthScale_eq

theorem targetAt_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (matrix.numeric.generatedBlockScale * k) :=
  matrix.numeric.generatedInequalityBlocks L k hk

theorem targetAt_crossBlockPolynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : PolynomialRows F k hk) :
    FixedTarget (matrix.numeric.crossBlockScale * k) :=
  matrix.numeric.polynomialRows hk R

theorem targetAt_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (matrix.numeric.crossBlockScale * k) :=
  matrix.numeric.inequalityLedgers L k hk

theorem targetAt_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F)
    (k : Nat) (hk : 0 < k) :
    FixedTarget (matrix.numeric.crossBlockScale * k) :=
  matrix.numeric.closureLedgers C k hk

theorem targetAt_smallExactLengthOne
    (E : SmallExactFields) :
    FixedTarget (matrix.numeric.smallLengthScale * 1) :=
  matrix.numeric.smallExactLengthOne E

theorem targetAt_smallExactLengthFive
    (E : SmallExactFields) :
    FixedTarget (matrix.numeric.smallLengthScale * 5) :=
  matrix.numeric.smallExactLengthFive E

/-! ## Public conditional generated routes -/

theorem exactTarget_of_generatedLowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ExactTarget :=
  (matrix.generated.lowerBound F).exactTarget C

theorem eventualTarget_of_generatedLowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    EventualTarget :=
  (matrix.generated.lowerBound F).eventualTarget C

theorem arbitraryTarget_of_generatedLowerBoundFields
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.generated.lowerBound F).arbitraryTarget C

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

/-! ## Public conditional cross-block routes -/

theorem fixedTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) (n : Nat) :
    FixedTarget n :=
  (matrix.crossBlock.inequalityLedgers F).fixedTarget L n

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

theorem exactTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.crossBlock.closureLedgersViaPachTothIntegrated F).exactTarget C

theorem arbitraryTarget_viaPachTothIntegrated_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.closureLedgersViaPachTothIntegrated F).arbitraryTarget C

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeCrossBlockFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.crossBlock.roleHingeInequalityPackages F).arbitraryTarget R

/-! ## Public arbitrary-`n` and final-consistency routes -/

theorem arbitraryTarget_viaArbitraryN_of_exactAssumptions
    (P : ExactTargetAssumptions) :
    ArbitraryTarget :=
  matrix.arbitraryN.exactAssumptions.arbitraryTarget P

theorem arbitraryTarget_viaArbitraryN_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.arbitraryN.crossBlockClosure F).arbitraryTarget C

theorem arbitraryTarget_viaArbitraryN_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.arbitraryN.generatedCrossBlockClosure F).arbitraryTarget C

theorem arbitraryTarget_viaFinalConsistency_of_generatedLowerBoundFields
    {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedTargetIntegratedW11.LowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.finalConsistency.generatedLowerBound (F := F)).arbitraryTarget C

theorem arbitraryTarget_viaFinalConsistency_of_crossBlockClosureLedger
    {F : ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily}
    (C : ArbitraryNIntegratedW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.finalConsistency.arbitraryNCrossBlockClosure (F := F))
    |>.arbitraryTarget C

theorem arbitraryTarget_viaFinalConsistency_of_transitionRouteFields
    (R : TransitionIntegratedW11.TransitionRouteFields) :
    ArbitraryTarget :=
  matrix.finalConsistency.transitionRoute.arbitraryTarget R

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

end GeneratedCrossBlockFinalW11
end PachToth
end ErdosProblems1066
