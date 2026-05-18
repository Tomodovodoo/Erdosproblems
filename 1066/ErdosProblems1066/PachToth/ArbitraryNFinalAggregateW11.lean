import ErdosProblems1066.PachToth.ArbitraryNTargetFinalW11
import ErdosProblems1066.PachToth.ArbitraryNFinalIntegratedW11
import ErdosProblems1066.PachToth.SmallLengthFinalIntegratedW11
import ErdosProblems1066.PachToth.GeneratedFinalIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final arbitrary-`n` aggregate consistency layer

This module is a terminal aggregate over the W11 arbitrary-`n` ledgers.  It
records the checked final matrices, the displayed source/package ledgers, and
the final W11 consistency witnesses in one place.

The public Pach--Toth target accessors below all require an explicit source
package argument.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNFinalAggregateW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev TargetFinalMatrix :=
  ArbitraryNTargetFinalW11.Matrix

abbrev FinalIntegratedMatrix :=
  ArbitraryNFinalIntegratedW11.Matrix

abbrev SmallLengthFinalMatrix :=
  SmallLengthFinalIntegratedW11.Matrix

abbrev GeneratedFinalMatrix :=
  GeneratedFinalIntegratedW11.Matrix

abbrev CrossBlockFinalMatrix :=
  CrossBlockFinalIntegratedW11.Matrix

abbrev FinalConsistencyMatrix :=
  PachTothW11FinalConsistency.Matrix

abbrev ExactTargetAssumptions :=
  ArbitraryNTargetFinalW11.ExactTargetAssumptions

abbrev ExactClosedChainPackage :=
  ArbitraryNTargetFinalW11.ExactClosedChainPackage

abbrev ExactGeneratedClosedChainPackage :=
  ArbitraryNTargetFinalW11.ExactGeneratedClosedChainPackage

abbrev EventualClosedChainPackage :=
  ArbitraryNTargetFinalW11.EventualClosedChainPackage

abbrev EventualGeneratedClosedChainPackage :=
  ArbitraryNTargetFinalW11.EventualGeneratedClosedChainPackage

abbrev SmallLengthEventualClosedChains :=
  ArbitraryNTargetFinalW11.SmallLengthEventualClosedChains

abbrev SmallLengthEventualGeneratedClosedChains :=
  ArbitraryNTargetFinalW11.SmallLengthEventualGeneratedClosedChains

abbrev SmallExactFields :=
  SmallLengthFinalIntegratedW11.ExactTargetFields

abbrev SmallEventualLargeFields :=
  SmallLengthFinalIntegratedW11.EventualLargeTargetFields

abbrev SmallEventualClosedChainFields :=
  SmallLengthFinalIntegratedW11.EventualClosedChainFields

abbrev SmallEventualGeneratedClosedChainFields :=
  SmallLengthFinalIntegratedW11.EventualGeneratedClosedChainFields

abbrev SmallEventualFiniteCertificateFields :=
  SmallLengthFinalIntegratedW11.EventualFiniteCertificateFields

abbrev SmallAggregateFields :=
  SmallLengthFinalIntegratedW11.AggregateFields

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

abbrev GeneratedFlexibleCandidateAssemblyFields :=
  GeneratedFinalIntegratedW11.FlexibleCandidateAssemblyFields

abbrev GeneratedFinalPackage :=
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

abbrev CrossBlockPolynomialRowFamilies
    (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.PolynomialRowFamilies F

abbrev CrossBlockValueRowFamilies
    (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.ValueRowFamilies F

abbrev CrossBlockInequalityLedger
    (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : CrossBlockFamily) :=
  CrossBlockFinalIntegratedW11.CrossBlockClosureLedger F

/-! ## Imported matrices and displayed source data -/

/-- Checked final matrices imported by this aggregate. -/
structure ImportedMatrices where
  targetFinal : TargetFinalMatrix
  finalIntegrated : FinalIntegratedMatrix
  smallLengthFinal : SmallLengthFinalMatrix
  generatedFinal : GeneratedFinalMatrix
  crossBlockFinal : CrossBlockFinalMatrix
  finalConsistency : FinalConsistencyMatrix

def importedMatrices : ImportedMatrices where
  targetFinal := ArbitraryNTargetFinalW11.matrix
  finalIntegrated := ArbitraryNFinalIntegratedW11.matrix
  smallLengthFinal := SmallLengthFinalIntegratedW11.matrix
  generatedFinal := GeneratedFinalIntegratedW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  finalConsistency := PachTothW11FinalConsistency.matrix

/-- Explicit package ledgers carried by the final aggregate. -/
structure ExplicitPackageData where
  smallLength :
    SmallLengthFinalIntegratedW11.FieldLedger
  generatedPoint :
    GeneratedFinalIntegratedW11.GeneratedPointFieldLedger
  generatedCrossBlock :
    GeneratedFinalIntegratedW11.InequalityLedgerFieldLedger
  crossBlock :
    CrossBlockFinalIntegratedW11.ExplicitCrossBlockFields
  finalOpenInputs :
    PachTothW11FinalConsistency.OpenInputLedgers

def explicitPackageData : ExplicitPackageData where
  smallLength := SmallLengthFinalIntegratedW11.fieldLedger
  generatedPoint := GeneratedFinalIntegratedW11.generatedPointFieldLedger
  generatedCrossBlock := GeneratedFinalIntegratedW11.inequalityLedgerFieldLedger
  crossBlock := CrossBlockFinalIntegratedW11.explicitCrossBlockFields
  finalOpenInputs := PachTothW11FinalConsistency.openInputLedgers

/-- Target-facing arbitrary-`n` route groups. -/
structure TargetFinalRouteData where
  exact : ArbitraryNTargetFinalW11.ExactFields
  eventual : ArbitraryNTargetFinalW11.EventualFields
  small : ArbitraryNTargetFinalW11.SmallFields
  generated : ArbitraryNTargetFinalW11.GeneratedFields
  crossBlock : ArbitraryNTargetFinalW11.CrossBlockFields

def targetFinalRouteData : TargetFinalRouteData where
  exact := ArbitraryNTargetFinalW11.matrix.exact
  eventual := ArbitraryNTargetFinalW11.matrix.eventual
  small := ArbitraryNTargetFinalW11.matrix.small
  generated := ArbitraryNTargetFinalW11.matrix.generated
  crossBlock := ArbitraryNTargetFinalW11.matrix.crossBlock

/-- Source-facing arbitrary-`n` route groups. -/
structure FinalIntegratedRouteData where
  exactClosedChain :
    ArbitraryNFinalIntegratedW11.ExactClosedChainFields
  eventualLargeChain :
    ArbitraryNFinalIntegratedW11.EventualLargeChainFields
  smallCases : ArbitraryNFinalIntegratedW11.SmallCaseFields
  generatedPointFields :
    ArbitraryNFinalIntegratedW11.GeneratedPointFields
  crossBlockFields :
    ArbitraryNFinalIntegratedW11.CrossBlockFields

def finalIntegratedRouteData : FinalIntegratedRouteData where
  exactClosedChain := ArbitraryNFinalIntegratedW11.matrix.exactClosedChain
  eventualLargeChain := ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain
  smallCases := ArbitraryNFinalIntegratedW11.matrix.smallCases
  generatedPointFields := ArbitraryNFinalIntegratedW11.matrix.generatedPointFields
  crossBlockFields := ArbitraryNFinalIntegratedW11.matrix.crossBlockFields

/-- Final small-length route groups. -/
structure SmallLengthRouteData where
  exactTargets :
    SmallLengthFinalIntegratedW11.ExactRouteRow SmallExactFields
  eventualLargeTargets :
    SmallLengthFinalIntegratedW11.ThresholdRouteRow
      SmallEventualLargeFields
  eventualClosedChains :
    SmallLengthFinalIntegratedW11.ThresholdRouteRow
      SmallEventualClosedChainFields
  eventualGeneratedClosedChains :
    SmallLengthFinalIntegratedW11.ThresholdRouteRow
      SmallEventualGeneratedClosedChainFields
  eventualFiniteCertificates :
    SmallLengthFinalIntegratedW11.ThresholdRouteRow
      SmallEventualFiniteCertificateFields
  aggregate : SmallLengthFinalIntegratedW11.AggregateRouteRow

def smallLengthRouteData : SmallLengthRouteData where
  exactTargets := SmallLengthFinalIntegratedW11.matrix.exactTargets
  eventualLargeTargets :=
    SmallLengthFinalIntegratedW11.matrix.eventualLargeTargets
  eventualClosedChains :=
    SmallLengthFinalIntegratedW11.matrix.eventualClosedChains
  eventualGeneratedClosedChains :=
    SmallLengthFinalIntegratedW11.matrix.eventualGeneratedClosedChains
  eventualFiniteCertificates :=
    SmallLengthFinalIntegratedW11.matrix.eventualFiniteCertificates
  aggregate := SmallLengthFinalIntegratedW11.matrix.aggregate

/-- Final generated-point and generated cross-block route groups. -/
structure GeneratedRouteData where
  generatedPoint : GeneratedFinalIntegratedW11.GeneratedPointRoutes
  generatedCrossBlock :
    forall F : GeneratedCrossBlockFamily,
      GeneratedFinalIntegratedW11.GeneratedCrossBlockRoute F
  integratedCrossBlock :
    GeneratedFinalIntegratedW11.IntegratedCrossBlockRoutes
  arbitraryNCrossBlock :
    GeneratedFinalIntegratedW11.ArbitraryNCrossBlockRoutes
  broadIntegrated :
    GeneratedFinalIntegratedW11.BroadIntegratedRoutes

def generatedRouteData : GeneratedRouteData where
  generatedPoint := GeneratedFinalIntegratedW11.matrix.generatedPoint
  generatedCrossBlock := GeneratedFinalIntegratedW11.matrix.generatedCrossBlock
  integratedCrossBlock := GeneratedFinalIntegratedW11.matrix.integratedCrossBlock
  arbitraryNCrossBlock := GeneratedFinalIntegratedW11.matrix.arbitraryNCrossBlock
  broadIntegrated := GeneratedFinalIntegratedW11.matrix.broadIntegrated

/-- Final cross-block route groups. -/
structure CrossBlockRouteData where
  polynomial : CrossBlockFinalIntegratedW11.PolynomialRoutes
  value : CrossBlockFinalIntegratedW11.ValueRoutes
  ledger : CrossBlockFinalIntegratedW11.LedgerRoutes

def crossBlockRouteData : CrossBlockRouteData where
  polynomial := CrossBlockFinalIntegratedW11.matrix.polynomial
  value := CrossBlockFinalIntegratedW11.matrix.value
  ledger := CrossBlockFinalIntegratedW11.matrix.ledger

/-- Final W11 cross-layer witnesses and blockers. -/
structure ConsistencyData where
  checkedRoutes : PachTothW11FinalConsistency.CheckedRouteLedgers
  crossLayer : PachTothW11FinalConsistency.CrossLayerConsistencyLedger
  blockers : PachTothW11FinalConsistency.FinalBlockerLedger

def consistencyData : ConsistencyData where
  checkedRoutes := PachTothW11FinalConsistency.matrix.routes
  crossLayer := PachTothW11FinalConsistency.matrix.consistency
  blockers := PachTothW11FinalConsistency.matrix.blockers

/-! ## Aggregate matrix -/

/-- Final arbitrary-`n` aggregate consistency matrix. -/
structure Matrix where
  imported : ImportedMatrices
  packages : ExplicitPackageData
  targetRoutes : TargetFinalRouteData
  finalIntegratedRoutes : FinalIntegratedRouteData
  smallLengthRoutes : SmallLengthRouteData
  generatedRoutes : GeneratedRouteData
  crossBlockRoutes : CrossBlockRouteData
  consistency : ConsistencyData

/-- The checked final arbitrary-`n` aggregate consistency matrix. -/
def matrix : Matrix where
  imported := importedMatrices
  packages := explicitPackageData
  targetRoutes := targetFinalRouteData
  finalIntegratedRoutes := finalIntegratedRouteData
  smallLengthRoutes := smallLengthRouteData
  generatedRoutes := generatedRouteData
  crossBlockRoutes := crossBlockRouteData
  consistency := consistencyData

/-! ## Conditional target projections: arbitrary-`n` source routes -/

theorem exactTarget_of_exactAssumptions
    (A : ExactTargetAssumptions) :
    ExactTarget :=
  matrix.targetRoutes.exact.exactAssumptions.exactTarget A

theorem fixedTarget_of_exactAssumptions
    (A : ExactTargetAssumptions) (n : Nat) :
    FixedTarget n :=
  matrix.targetRoutes.exact.exactAssumptions.fixedTarget A n

theorem arbitraryTarget_of_exactAssumptions
    (A : ExactTargetAssumptions) :
    ArbitraryTarget :=
  matrix.targetRoutes.exact.exactAssumptions.arbitraryTarget A

theorem arbitraryTarget_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.targetRoutes.exact.closedChains.arbitraryTarget P

theorem arbitraryTarget_of_exactGeneratedClosedChains
    (P : ExactGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.targetRoutes.exact.generatedClosedChains.arbitraryTarget P

theorem largeTarget_of_eventualClosedChains
    (P : EventualClosedChainPackage) (n : Nat)
    (hn : matrix.targetRoutes.eventual.closedChains.vertexThreshold P <= n) :
    FixedTarget n :=
  matrix.targetRoutes.eventual.closedChains.largeTarget P n hn

theorem arbitraryTarget_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    ArbitraryTarget :=
  matrix.targetRoutes.eventual.closedChains.arbitraryTarget P

theorem arbitraryTarget_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.targetRoutes.eventual.generatedClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallLengthEventualClosedChains
    (P : SmallLengthEventualClosedChains) :
    ArbitraryTarget :=
  matrix.targetRoutes.eventual.smallLengthClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallLengthEventualGeneratedClosedChains
    (P : SmallLengthEventualGeneratedClosedChains) :
    ArbitraryTarget :=
  matrix.targetRoutes.eventual.smallLengthGeneratedClosedChains
    |>.arbitraryTarget P

/-! ## Conditional target projections: small length -/

theorem smallTarget_of_smallExactFields
    (E : SmallExactFields) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo
      SmallLengthFinalIntegratedW11.vertexThreshold :=
  matrix.smallLengthRoutes.exactTargets.smallTarget E

theorem arbitraryTarget_of_smallEventualLargeFields
    (P : SmallEventualLargeFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.eventualLargeTargets.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualClosedChainFields
    (P : SmallEventualClosedChainFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.eventualClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualGeneratedClosedChainFields
    (P : SmallEventualGeneratedClosedChainFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.eventualGeneratedClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualFiniteCertificateFields
    (P : SmallEventualFiniteCertificateFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.eventualFiniteCertificates.arbitraryTarget P

theorem arbitraryTarget_of_smallAggregate_viaLargeTarget
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.aggregate.arbitraryTargetOfLargeTarget A

theorem arbitraryTarget_of_smallAggregate_viaClosedChains
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.aggregate.arbitraryTargetOfClosedChains A

theorem arbitraryTarget_of_smallAggregate_viaGeneratedClosedChains
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.aggregate
    |>.arbitraryTargetOfGeneratedClosedChains A

theorem arbitraryTarget_of_smallAggregate_viaFiniteCertificates
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.smallLengthRoutes.aggregate
    |>.arbitraryTargetOfFiniteCertificates A

/-! ## Conditional target projections: generated point -/

theorem arbitraryTarget_of_generatedNormalizedPolynomial
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    ArbitraryTarget :=
  (matrix.generatedRoutes.generatedPoint.normalizedPolynomial F)
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedNormalizedValue
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    ArbitraryTarget :=
  (matrix.generatedRoutes.generatedPoint.normalizedValue F)
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.generatedRoutes.generatedPoint.lowerBound F)
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedFlexibleCandidateAssembly
    (C : GeneratedFlexibleCandidateAssemblyFields) :
    ArbitraryTarget :=
  matrix.generatedRoutes.generatedPoint.flexibleCandidateAssembly
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedFinalPackage
    (C : GeneratedFinalPackage) :
    ArbitraryTarget :=
  matrix.generatedRoutes.generatedPoint.finalConditionalFamily
    |>.arbitraryTarget C

/-! ## Conditional target projections: cross block -/

theorem arbitraryTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.generatedRoutes.generatedCrossBlock F).directRoute
    |>.arbitraryTarget L

theorem arbitraryTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.generatedRoutes.generatedCrossBlock F).closureRoute
    |>.arbitraryTarget C

theorem arbitraryTarget_of_crossBlockPolynomialRowFamilies
    {F : CrossBlockFamily}
    (R : CrossBlockPolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.crossBlockRoutes.polynomial.rowFamilies F).route
    |>.arbitraryTarget R

theorem arbitraryTarget_of_crossBlockValueRowFamilies
    {F : CrossBlockFamily}
    (R : CrossBlockValueRowFamilies F) :
    ArbitraryTarget :=
  (matrix.crossBlockRoutes.value.rowFamilies F).route
    |>.arbitraryTarget R

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlockRoutes.ledger.inequalityLedgers F).route
    |>.arbitraryTarget L

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlockRoutes.ledger.closureLedgers F).route
    |>.arbitraryTarget C

/-! ## Consistency witness projections -/

theorem arbitraryNExactAssumptionsConsistency
    (A : ExactTargetAssumptions) :
    PachTothW11ConsistencyMatrix.ArbitraryNExactAssumptionsConsistency A :=
  matrix.consistency.crossLayer.arbitraryNExactAssumptions A

theorem smallLengthExactBlockConsistency
    (C : SmallLengthClosureW11.SmallLengthExactBlockTargets) :
    PachTothW11ConsistencyMatrix.SmallLengthExactBlockConsistency C :=
  matrix.consistency.crossLayer.smallLengthExactBlocks C

theorem smallLengthEventualClosedChainConsistency
    (P : SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix) :
    PachTothW11ConsistencyMatrix.SmallLengthEventualClosedChainConsistency P :=
  matrix.consistency.crossLayer.smallLengthEventualClosedChains P

theorem generatedPointCrossBlockLedgerConsistency
    {F : GeneratedPointIntegratedMatrixW11.CrossBlockPeriodSearchFamily}
    (L : GeneratedPointIntegratedMatrixW11.CrossBlockInequalityLedger F) :
    PachTothW11ConsistencyMatrix.GeneratedPointCrossBlockLedgerConsistency
      F L :=
  matrix.consistency.crossLayer.generatedPointCrossBlockLedger L

theorem crossBlockClosureConsistency
    {F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F) :
    PachTothW11ConsistencyMatrix.CrossBlockClosureConsistency F C :=
  matrix.consistency.crossLayer.crossBlockClosure C

/-! ## Blocker projections -/

theorem transition_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.consistency.blockers.generatedTarget
    |>.concreteFourTargetRouteClaim

theorem transition_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.consistency.blockers.generatedTarget
    |>.completedFilteredRoute

end

end ArbitraryNFinalAggregateW11
end PachToth
end ErdosProblems1066
