import ErdosProblems1066.PachToth.ArbitraryNFinalAggregateW11
import ErdosProblems1066.PachToth.ArbitraryNTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency
import ErdosProblems1066.PachToth.SmallLengthFinalIntegratedW11

set_option autoImplicit false

/-!
# W11 arbitrary-`n` route summary ledger

This module is a concise terminal summary over the checked W11 arbitrary-`n`
route aggregates.  It records the source-data shapes for the exact, eventual,
small-length, generated-point, and cross-block routes, then exposes only
package-indexed target projections.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNRouteSummaryFinalW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactTargetAssumptions :=
  ArbitraryNFinalAggregateW11.ExactTargetAssumptions

abbrev ExactClosedChainPackage :=
  ArbitraryNFinalAggregateW11.ExactClosedChainPackage

abbrev ExactGeneratedClosedChainPackage :=
  ArbitraryNFinalAggregateW11.ExactGeneratedClosedChainPackage

abbrev EventualSmallCaseAssumptions :=
  ArbitraryNTargetFinalW11.EventualSmallCaseAssumptions

abbrev EventualClosedChainPackage :=
  ArbitraryNFinalAggregateW11.EventualClosedChainPackage

abbrev EventualGeneratedClosedChainPackage :=
  ArbitraryNFinalAggregateW11.EventualGeneratedClosedChainPackage

abbrev SmallLengthEventualClosedChains :=
  ArbitraryNFinalAggregateW11.SmallLengthEventualClosedChains

abbrev SmallLengthEventualGeneratedClosedChains :=
  ArbitraryNFinalAggregateW11.SmallLengthEventualGeneratedClosedChains

abbrev SmallExactFields :=
  ArbitraryNFinalAggregateW11.SmallExactFields

abbrev SmallEventualLargeFields :=
  ArbitraryNFinalAggregateW11.SmallEventualLargeFields

abbrev SmallEventualClosedChainFields :=
  ArbitraryNFinalAggregateW11.SmallEventualClosedChainFields

abbrev SmallEventualGeneratedClosedChainFields :=
  ArbitraryNFinalAggregateW11.SmallEventualGeneratedClosedChainFields

abbrev SmallEventualFiniteCertificateFields :=
  ArbitraryNFinalAggregateW11.SmallEventualFiniteCertificateFields

abbrev SmallAggregateFields :=
  ArbitraryNFinalAggregateW11.SmallAggregateFields

abbrev GeneratedPointFamily :=
  ArbitraryNFinalAggregateW11.GeneratedPointFamily

abbrev GeneratedPointNormalizedPolynomialFields
    (F : GeneratedPointFamily) :=
  ArbitraryNFinalAggregateW11.GeneratedPointNormalizedPolynomialFields F

abbrev GeneratedPointNormalizedValueFields
    (F : GeneratedPointFamily) :=
  ArbitraryNFinalAggregateW11.GeneratedPointNormalizedValueFields F

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  ArbitraryNFinalAggregateW11.GeneratedPointLowerBoundFields F

abbrev GeneratedFlexibleCandidateAssemblyFields :=
  ArbitraryNFinalAggregateW11.GeneratedFlexibleCandidateAssemblyFields

abbrev GeneratedFinalPackage :=
  ArbitraryNFinalAggregateW11.GeneratedFinalPackage

abbrev GeneratedCrossBlockFamily :=
  ArbitraryNFinalAggregateW11.GeneratedCrossBlockFamily

abbrev GeneratedCrossBlockInequalityLedger
    (F : GeneratedCrossBlockFamily) :=
  ArbitraryNFinalAggregateW11.GeneratedCrossBlockInequalityLedger F

abbrev GeneratedCrossBlockClosureLedger
    (F : GeneratedCrossBlockFamily) :=
  ArbitraryNFinalAggregateW11.GeneratedCrossBlockClosureLedger F

abbrev CrossBlockFamily :=
  ArbitraryNFinalAggregateW11.CrossBlockFamily

abbrev CrossBlockPolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockFinalIntegratedW11.PolynomialRows F k hk

abbrev CrossBlockPolynomialRowFamilies
    (F : CrossBlockFamily) :=
  ArbitraryNFinalAggregateW11.CrossBlockPolynomialRowFamilies F

abbrev CrossBlockValueRowFamilies
    (F : CrossBlockFamily) :=
  ArbitraryNFinalAggregateW11.CrossBlockValueRowFamilies F

abbrev CrossBlockInequalityLedger
    (F : CrossBlockFamily) :=
  ArbitraryNFinalAggregateW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : CrossBlockFamily) :=
  ArbitraryNFinalAggregateW11.CrossBlockClosureLedger F

/-! ## Imported final ledgers -/

/-- The final checked W11 ledgers used by this route summary. -/
structure ImportedFinalLedgers where
  arbitraryNFinal : ArbitraryNFinalAggregateW11.Matrix
  targetFinal : ArbitraryNTargetFinalW11.Matrix
  pachTothFinal : PachTothW11FinalAggregate.Matrix
  consistencyFinal : PachTothW11FinalConsistency.Matrix
  smallLengthFinal : SmallLengthFinalIntegratedW11.Matrix

/-- Imported final ledgers, kept as data rather than re-exported imports. -/
def importedFinalLedgers : ImportedFinalLedgers where
  arbitraryNFinal := ArbitraryNFinalAggregateW11.matrix
  targetFinal := ArbitraryNTargetFinalW11.matrix
  pachTothFinal := PachTothW11FinalAggregate.matrix
  consistencyFinal := PachTothW11FinalConsistency.matrix
  smallLengthFinal := SmallLengthFinalIntegratedW11.matrix

/-! ## Explicit source-data summary -/

/-- Exact route source packages and rows. -/
structure ExactSourceData where
  targetAssumptions : Prop
  closedChains : Type
  generatedClosedChains : Type
  targetRoutes : ArbitraryNTargetFinalW11.ExactFields
  integratedRoutes : ArbitraryNFinalIntegratedW11.ExactClosedChainFields

def exactSourceData : ExactSourceData where
  targetAssumptions := ExactTargetAssumptions
  closedChains := ExactClosedChainPackage
  generatedClosedChains := ExactGeneratedClosedChainPackage
  targetRoutes := ArbitraryNTargetFinalW11.matrix.exact
  integratedRoutes := ArbitraryNFinalIntegratedW11.matrix.exactClosedChain

/-- Eventual route source packages and rows. -/
structure EventualSourceData where
  smallCaseAssumptions : Type
  closedChains : Type
  generatedClosedChains : Type
  smallLengthClosedChains : Type
  smallLengthGeneratedClosedChains : Type
  targetRoutes : ArbitraryNTargetFinalW11.EventualFields
  integratedRoutes : ArbitraryNFinalIntegratedW11.EventualLargeChainFields

def eventualSourceData : EventualSourceData where
  smallCaseAssumptions := EventualSmallCaseAssumptions
  closedChains := EventualClosedChainPackage
  generatedClosedChains := EventualGeneratedClosedChainPackage
  smallLengthClosedChains := SmallLengthEventualClosedChains
  smallLengthGeneratedClosedChains :=
    SmallLengthEventualGeneratedClosedChains
  targetRoutes := ArbitraryNTargetFinalW11.matrix.eventual
  integratedRoutes := ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain

/-- Small-length route source packages and rows. -/
structure SmallSourceData where
  fields : SmallLengthFinalIntegratedW11.FieldLedger
  exactTargets : Type
  eventualLargeTargets : Type
  eventualClosedChains : Type
  eventualGeneratedClosedChains : Type
  eventualFiniteCertificates : Type
  aggregateFields : Type
  routes : ArbitraryNFinalAggregateW11.SmallLengthRouteData

def smallSourceData : SmallSourceData where
  fields := SmallLengthFinalIntegratedW11.fieldLedger
  exactTargets := SmallExactFields
  eventualLargeTargets := SmallEventualLargeFields
  eventualClosedChains := SmallEventualClosedChainFields
  eventualGeneratedClosedChains := SmallEventualGeneratedClosedChainFields
  eventualFiniteCertificates := SmallEventualFiniteCertificateFields
  aggregateFields := SmallAggregateFields
  routes := ArbitraryNFinalAggregateW11.smallLengthRouteData

/-- Generated-point source packages and rows. -/
structure GeneratedSourceData where
  fields : GeneratedFinalIntegratedW11.GeneratedPointFieldLedger
  pointFamilies : Type
  normalizedPolynomial : GeneratedPointFamily -> Prop
  normalizedValue : GeneratedPointFamily -> Type
  lowerBound : GeneratedPointFamily -> Type
  flexibleCandidateAssembly : Type
  finalPackages : Type
  routes : ArbitraryNFinalAggregateW11.GeneratedRouteData

def generatedSourceData : GeneratedSourceData where
  fields := GeneratedFinalIntegratedW11.generatedPointFieldLedger
  pointFamilies := GeneratedPointFamily
  normalizedPolynomial := GeneratedPointNormalizedPolynomialFields
  normalizedValue := GeneratedPointNormalizedValueFields
  lowerBound := GeneratedPointLowerBoundFields
  flexibleCandidateAssembly :=
    GeneratedFlexibleCandidateAssemblyFields
  finalPackages := GeneratedFinalPackage
  routes := ArbitraryNFinalAggregateW11.generatedRouteData

/-- Cross-block source packages and rows, including generated cross-block rows. -/
structure CrossBlockSourceData where
  fields : CrossBlockFinalIntegratedW11.ExplicitCrossBlockFields
  periodFamilies : Type
  generatedFamilies : Type
  polynomialRows :
    forall _F : CrossBlockFamily, forall k : Nat, 0 < k -> Prop
  polynomialRowFamilies : CrossBlockFamily -> Prop
  valueRowFamilies : CrossBlockFamily -> Type
  inequalityLedgers : CrossBlockFamily -> Type
  closureLedgers : CrossBlockFamily -> Type
  generatedInequalityLedgers : GeneratedCrossBlockFamily -> Type
  generatedClosureLedgers : GeneratedCrossBlockFamily -> Type
  routes : ArbitraryNFinalAggregateW11.CrossBlockRouteData

def crossBlockSourceData : CrossBlockSourceData where
  fields := CrossBlockFinalIntegratedW11.explicitCrossBlockFields
  periodFamilies := CrossBlockFamily
  generatedFamilies := GeneratedCrossBlockFamily
  polynomialRows := CrossBlockPolynomialRows
  polynomialRowFamilies := CrossBlockPolynomialRowFamilies
  valueRowFamilies := CrossBlockValueRowFamilies
  inequalityLedgers := CrossBlockInequalityLedger
  closureLedgers := CrossBlockClosureLedger
  generatedInequalityLedgers := GeneratedCrossBlockInequalityLedger
  generatedClosureLedgers := GeneratedCrossBlockClosureLedger
  routes := ArbitraryNFinalAggregateW11.crossBlockRouteData

/-- Source-data summary for the arbitrary-`n` route. -/
structure RouteSourceSummary where
  exact : ExactSourceData
  eventual : EventualSourceData
  small : SmallSourceData
  generated : GeneratedSourceData
  crossBlock : CrossBlockSourceData
  openInputs : PachTothW11FinalConsistency.OpenInputLedgers
  pachTothOpenData : PachTothW11FinalAggregate.ExplicitOpenData

def routeSourceSummary : RouteSourceSummary where
  exact := exactSourceData
  eventual := eventualSourceData
  small := smallSourceData
  generated := generatedSourceData
  crossBlock := crossBlockSourceData
  openInputs := PachTothW11FinalConsistency.openInputLedgers
  pachTothOpenData := PachTothW11FinalAggregate.explicitOpenData

/-! ## Summary matrix -/

/-- Final arbitrary-`n` route summary matrix. -/
structure Matrix where
  imported : ImportedFinalLedgers
  source : RouteSourceSummary
  consistency : ArbitraryNFinalAggregateW11.ConsistencyData

/-- The checked final arbitrary-`n` route summary matrix. -/
def matrix : Matrix where
  imported := importedFinalLedgers
  source := routeSourceSummary
  consistency := ArbitraryNFinalAggregateW11.consistencyData

/-! ## Conditional target projections: exact and eventual -/

theorem exactTarget_of_exactAssumptions
    (A : ExactTargetAssumptions) :
    ExactTarget :=
  matrix.source.exact.targetRoutes.exactAssumptions.exactTarget A

theorem fixedTarget_of_exactAssumptions
    (A : ExactTargetAssumptions) (n : Nat) :
    FixedTarget n :=
  matrix.source.exact.targetRoutes.exactAssumptions.fixedTarget A n

theorem arbitraryTarget_of_exactAssumptions
    (A : ExactTargetAssumptions) :
    ArbitraryTarget :=
  matrix.source.exact.targetRoutes.exactAssumptions.arbitraryTarget A

theorem arbitraryTarget_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.source.exact.targetRoutes.closedChains.arbitraryTarget P

theorem arbitraryTarget_of_exactGeneratedClosedChains
    (P : ExactGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.source.exact.targetRoutes.generatedClosedChains.arbitraryTarget P

theorem largeTarget_of_eventualClosedChains
    (P : EventualClosedChainPackage) (n : Nat)
    (hn : matrix.source.eventual.targetRoutes.closedChains.vertexThreshold P
      <= n) :
    FixedTarget n :=
  matrix.source.eventual.targetRoutes.closedChains.largeTarget P n hn

theorem arbitraryTarget_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    ArbitraryTarget :=
  matrix.source.eventual.targetRoutes.closedChains.arbitraryTarget P

theorem arbitraryTarget_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.source.eventual.targetRoutes.generatedClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallLengthEventualClosedChains
    (P : SmallLengthEventualClosedChains) :
    ArbitraryTarget :=
  matrix.source.eventual.targetRoutes.smallLengthClosedChains
    |>.arbitraryTarget P

theorem arbitraryTarget_of_smallLengthEventualGeneratedClosedChains
    (P : SmallLengthEventualGeneratedClosedChains) :
    ArbitraryTarget :=
  matrix.source.eventual.targetRoutes.smallLengthGeneratedClosedChains
    |>.arbitraryTarget P

/-! ## Conditional target projections: small length -/

theorem smallTarget_of_smallExactFields
    (E : SmallExactFields) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo
      SmallLengthFinalIntegratedW11.vertexThreshold :=
  matrix.source.small.routes.exactTargets.smallTarget E

theorem arbitraryTarget_of_smallEventualLargeFields
    (P : SmallEventualLargeFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.eventualLargeTargets.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualClosedChainFields
    (P : SmallEventualClosedChainFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.eventualClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualGeneratedClosedChainFields
    (P : SmallEventualGeneratedClosedChainFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.eventualGeneratedClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualFiniteCertificateFields
    (P : SmallEventualFiniteCertificateFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.eventualFiniteCertificates.arbitraryTarget P

theorem arbitraryTarget_of_smallAggregate_viaLargeTarget
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.aggregate.arbitraryTargetOfLargeTarget A

theorem arbitraryTarget_of_smallAggregate_viaClosedChains
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.aggregate.arbitraryTargetOfClosedChains A

theorem arbitraryTarget_of_smallAggregate_viaGeneratedClosedChains
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.aggregate
    |>.arbitraryTargetOfGeneratedClosedChains A

theorem arbitraryTarget_of_smallAggregate_viaFiniteCertificates
    (A : SmallAggregateFields) :
    ArbitraryTarget :=
  matrix.source.small.routes.aggregate
    |>.arbitraryTargetOfFiniteCertificates A

/-! ## Conditional target projections: generated point -/

theorem arbitraryTarget_of_generatedNormalizedPolynomial
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    ArbitraryTarget :=
  (matrix.source.generated.routes.generatedPoint.normalizedPolynomial F)
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedNormalizedValue
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    ArbitraryTarget :=
  (matrix.source.generated.routes.generatedPoint.normalizedValue F)
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.source.generated.routes.generatedPoint.lowerBound F)
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedFlexibleCandidateAssembly
    (C : GeneratedFlexibleCandidateAssemblyFields) :
    ArbitraryTarget :=
  matrix.source.generated.routes.generatedPoint.flexibleCandidateAssembly
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedFinalPackage
    (C : GeneratedFinalPackage) :
    ArbitraryTarget :=
  matrix.source.generated.routes.generatedPoint.finalConditionalFamily
    |>.arbitraryTarget C

/-! ## Conditional target projections: cross block -/

theorem fixedTarget_of_crossBlockPolynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : CrossBlockPolynomialRows F k hk) :
    FixedTarget (16 * k) :=
  (matrix.source.crossBlock.routes.polynomial.rows F k hk)
    |>.exactBlockTarget R

theorem arbitraryTarget_of_crossBlockPolynomialRowFamilies
    {F : CrossBlockFamily}
    (R : CrossBlockPolynomialRowFamilies F) :
    ArbitraryTarget :=
  (matrix.source.crossBlock.routes.polynomial.rowFamilies F).route
    |>.arbitraryTarget R

theorem arbitraryTarget_of_crossBlockValueRowFamilies
    {F : CrossBlockFamily}
    (R : CrossBlockValueRowFamilies F) :
    ArbitraryTarget :=
  (matrix.source.crossBlock.routes.value.rowFamilies F).route
    |>.arbitraryTarget R

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.source.crossBlock.routes.ledger.inequalityLedgers F).route
    |>.arbitraryTarget L

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.source.crossBlock.routes.ledger.closureLedgers F).route
    |>.arbitraryTarget C

theorem arbitraryTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.source.generated.routes.generatedCrossBlock F).directRoute
    |>.arbitraryTarget L

theorem arbitraryTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.source.generated.routes.generatedCrossBlock F).closureRoute
    |>.arbitraryTarget C

/-! ## Consistency and blockers -/

theorem arbitraryNExactAssumptionsConsistency
    (A : ExactTargetAssumptions) :
    PachTothW11ConsistencyMatrix.ArbitraryNExactAssumptionsConsistency A :=
  matrix.consistency.crossLayer.arbitraryNExactAssumptions A

theorem crossBlockClosureConsistency
    {F : CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityClosureW11.CrossBlockClosureLedger F) :
    PachTothW11ConsistencyMatrix.CrossBlockClosureConsistency F C :=
  matrix.consistency.crossLayer.crossBlockClosure C

theorem transition_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.consistency.blockers.generatedTarget
    |>.concreteFourTargetRouteClaim

end

end ArbitraryNRouteSummaryFinalW11
end PachToth
end ErdosProblems1066
