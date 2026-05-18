import ErdosProblems1066.PachToth.ArbitraryNFinalIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNIntegratedW11
import ErdosProblems1066.PachToth.SmallLengthFinalIntegratedW11
import ErdosProblems1066.PachToth.GeneratedFinalIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockTargetIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockIntegratedW11

set_option autoImplicit false

/-!
# W11 final arbitrary-`n` target aggregate

This module gathers the W11 arbitrary-`n` target-facing ledgers into one final
aggregate.  It records the exact, eventual, small-length, generated-point, and
cross-block route surfaces explicitly.  The public target projections below
all remain parameterized by one of those displayed source packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNTargetFinalW11

noncomputable section

universe u

abbrev ArbitraryNFinalMatrix :=
  ArbitraryNFinalIntegratedW11.Matrix

abbrev ArbitraryNMatrix :=
  ArbitraryNIntegratedW11.Matrix

abbrev SmallLengthFinalMatrix :=
  SmallLengthFinalIntegratedW11.Matrix

abbrev GeneratedFinalMatrix :=
  GeneratedFinalIntegratedW11.Matrix

abbrev CrossBlockTargetMatrix :=
  CrossBlockTargetIntegratedW11.Matrix

abbrev CrossBlockMatrix :=
  CrossBlockIntegratedW11.Matrix

abbrev ArbitraryNTargetFacade :=
  ArbitraryNIntegratedW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNIntegratedW11.ThresholdTargetFacade

abbrev ExactTargetAssumptions :=
  ArbitraryNIntegratedW11.ExactTargetAssumptions

abbrev EventualSmallCaseAssumptions :=
  ArbitraryNIntegratedW11.EventualSmallCaseAssumptions

abbrev ExactClosedChainPackage :=
  ArbitraryNIntegratedW11.ExactClosedChainPackage

abbrev ExactGeneratedClosedChainPackage :=
  ArbitraryNIntegratedW11.ExactGeneratedClosedChainPackage

abbrev EventualClosedChainPackage :=
  ArbitraryNIntegratedW11.EventualClosedChainPackage

abbrev EventualGeneratedClosedChainPackage :=
  ArbitraryNIntegratedW11.EventualGeneratedClosedChainPackage

abbrev SmallLengthEventualClosedChains :=
  ArbitraryNIntegratedW11.SmallLengthEventualClosedChains

abbrev SmallLengthEventualGeneratedClosedChains :=
  ArbitraryNIntegratedW11.SmallLengthEventualGeneratedClosedChains

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
  CrossBlockTargetIntegratedW11.PeriodSearchFamily

abbrev CrossBlockPolynomialRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.PolynomialRows F k hk

abbrev CrossBlockPolynomialRowFamilies (F : CrossBlockFamily) :=
  CrossBlockTargetIntegratedW11.PolynomialRowFamilies F

abbrev CrossBlockValueRows
    (F : CrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  CrossBlockTargetIntegratedW11.ValueRows F k hk

abbrev CrossBlockValueRowFamilies (F : CrossBlockFamily) :=
  CrossBlockTargetIntegratedW11.ValueRowFamilies F

abbrev CrossBlockInequalityLedger (F : CrossBlockFamily) :=
  CrossBlockTargetIntegratedW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger (F : CrossBlockFamily) :=
  CrossBlockTargetIntegratedW11.CrossBlockClosureLedger F

/-! ## Shared conditional route shapes -/

/-- Exact-target route from an explicit input package. -/
structure ExactTargetRoute (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

namespace ExactTargetRoute

def ofExactBlockFacadeRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.ExactBlockFacadeRow alpha) :
    ExactTargetRoute alpha where
  exactTarget := R.blockTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

def ofExactClosedChainFacadeRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.ExactClosedChainFacadeRow alpha) :
    ExactTargetRoute alpha where
  exactTarget := R.blockTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

def ofExactGeneratedClosedChainFacadeRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.ExactGeneratedClosedChainFacadeRow alpha) :
    ExactTargetRoute alpha where
  exactTarget := R.blockTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

end ExactTargetRoute

/-- Eventual/threshold target route from an explicit input package. -/
structure EventualTargetRoute (alpha : Sort u) where
  vertexThreshold : alpha -> Nat
  largeTarget :
    forall a : alpha, forall n : Nat, vertexThreshold a <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n
  smallTarget :
    forall a : alpha,
      PachToth.targetUpperConstructionFiveSixteenSmallUpTo
        (vertexThreshold a)
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  thresholdFacade : alpha -> ThresholdTargetFacade
  targetFacade : alpha -> ArbitraryNTargetFacade

namespace EventualTargetRoute

def ofThresholdFacadeRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.ThresholdFacadeRow alpha) :
    EventualTargetRoute alpha where
  vertexThreshold := R.vertexThreshold
  largeTarget := R.largeTarget
  smallTarget := R.smallTarget
  arbitraryTarget := R.arbitraryTarget
  thresholdFacade := R.thresholdFacade
  targetFacade := R.targetFacade

def ofEventualClosedChainFacadeRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.EventualClosedChainFacadeRow alpha) :
    EventualTargetRoute alpha where
  vertexThreshold := R.vertexThreshold
  largeTarget := R.largeTarget
  smallTarget := R.smallTarget
  arbitraryTarget := R.arbitraryTarget
  thresholdFacade := R.thresholdFacade
  targetFacade := R.targetFacade

def ofEventualGeneratedClosedChainFacadeRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.EventualGeneratedClosedChainFacadeRow alpha) :
    EventualTargetRoute alpha where
  vertexThreshold := R.vertexThreshold
  largeTarget := R.largeTarget
  smallTarget := R.smallTarget
  arbitraryTarget := R.arbitraryTarget
  thresholdFacade := R.thresholdFacade
  targetFacade := R.targetFacade

end EventualTargetRoute

/-! ## Explicit final route groups -/

/-- Exact arbitrary-`n` target routes with their source packages visible. -/
structure ExactFields where
  exactAssumptions : ExactTargetRoute ExactTargetAssumptions
  closedChains : ExactTargetRoute ExactClosedChainPackage
  generatedClosedChains :
    ExactTargetRoute ExactGeneratedClosedChainPackage

/-- Eventual large-side routes with finite small complements visible. -/
structure EventualFields where
  smallCaseAssumptions :
    EventualTargetRoute EventualSmallCaseAssumptions
  closedChains : EventualTargetRoute EventualClosedChainPackage
  generatedClosedChains :
    EventualTargetRoute EventualGeneratedClosedChainPackage
  smallLengthClosedChains :
    EventualTargetRoute SmallLengthEventualClosedChains
  smallLengthGeneratedClosedChains :
    EventualTargetRoute SmallLengthEventualGeneratedClosedChains

/-- Final small-length target routes. -/
structure SmallFields where
  finalMatrix : SmallLengthFinalMatrix
  exact : SmallLengthFinalIntegratedW11.ExactRouteRow SmallExactFields
  eventualLarge :
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

/-- Final generated-point target routes. -/
structure GeneratedFields where
  finalMatrix : GeneratedFinalMatrix
  fieldLedger : GeneratedFinalIntegratedW11.GeneratedPointFieldLedger
  routes : GeneratedFinalIntegratedW11.GeneratedPointRoutes

/-- Final cross-block target routes from both target and generated ledgers. -/
structure CrossBlockFields where
  targetMatrix : CrossBlockTargetMatrix
  integratedMatrix : CrossBlockMatrix
  targetInputs :
    CrossBlockTargetIntegratedW11.ExplicitCrossBlockTargetInputs
  polynomial : CrossBlockTargetIntegratedW11.PolynomialTargetRows
  value : CrossBlockTargetIntegratedW11.ValueTargetRows
  ledger : CrossBlockTargetIntegratedW11.LedgerTargetRows
  generatedCrossBlock :
    forall F : GeneratedCrossBlockFamily,
      GeneratedFinalIntegratedW11.GeneratedCrossBlockRoute F
  integratedCrossBlock :
    GeneratedFinalIntegratedW11.IntegratedCrossBlockRoutes
  arbitraryNCrossBlock :
    GeneratedFinalIntegratedW11.ArbitraryNCrossBlockRoutes

/-! ## Final matrix -/

/-- Existing checked matrices imported by this final aggregate. -/
structure ImportedMatrices where
  arbitraryNFinal : ArbitraryNFinalMatrix
  arbitraryNIntegrated : ArbitraryNMatrix
  smallLengthFinal : SmallLengthFinalMatrix
  generatedFinal : GeneratedFinalMatrix
  crossBlockTarget : CrossBlockTargetMatrix
  crossBlockIntegrated : CrossBlockMatrix

def importedMatrices : ImportedMatrices where
  arbitraryNFinal := ArbitraryNFinalIntegratedW11.matrix
  arbitraryNIntegrated := ArbitraryNIntegratedW11.matrix
  smallLengthFinal := SmallLengthFinalIntegratedW11.matrix
  generatedFinal := GeneratedFinalIntegratedW11.matrix
  crossBlockTarget := CrossBlockTargetIntegratedW11.matrix
  crossBlockIntegrated := CrossBlockIntegratedW11.matrix

def exactFields : ExactFields where
  exactAssumptions :=
    ExactTargetRoute.ofExactBlockFacadeRow
      ArbitraryNIntegratedW11.matrix.exactTargetAssumptions
  closedChains :=
    ExactTargetRoute.ofExactClosedChainFacadeRow
      ArbitraryNFinalIntegratedW11.matrix.exactClosedChain.exactClosedChains
  generatedClosedChains :=
    ExactTargetRoute.ofExactGeneratedClosedChainFacadeRow
      (ArbitraryNFinalIntegratedW11.matrix.exactClosedChain
        |>.exactGeneratedClosedChains)

def eventualFields : EventualFields where
  smallCaseAssumptions :=
    EventualTargetRoute.ofThresholdFacadeRow
      ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions
  closedChains :=
    EventualTargetRoute.ofEventualClosedChainFacadeRow
      (ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain
        |>.eventualClosedChains)
  generatedClosedChains :=
    EventualTargetRoute.ofEventualGeneratedClosedChainFacadeRow
      (ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain
        |>.eventualGeneratedClosedChains)
  smallLengthClosedChains :=
    EventualTargetRoute.ofEventualClosedChainFacadeRow
      (ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain
        |>.smallLengthEventualClosedChains)
  smallLengthGeneratedClosedChains :=
    EventualTargetRoute.ofEventualGeneratedClosedChainFacadeRow
      (ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain
        |>.smallLengthEventualGeneratedClosedChains)

def smallFields : SmallFields where
  finalMatrix := SmallLengthFinalIntegratedW11.matrix
  exact := SmallLengthFinalIntegratedW11.matrix.exactTargets
  eventualLarge := SmallLengthFinalIntegratedW11.matrix.eventualLargeTargets
  eventualClosedChains :=
    SmallLengthFinalIntegratedW11.matrix.eventualClosedChains
  eventualGeneratedClosedChains :=
    SmallLengthFinalIntegratedW11.matrix.eventualGeneratedClosedChains
  eventualFiniteCertificates :=
    SmallLengthFinalIntegratedW11.matrix.eventualFiniteCertificates
  aggregate := SmallLengthFinalIntegratedW11.matrix.aggregate

def generatedFields : GeneratedFields where
  finalMatrix := GeneratedFinalIntegratedW11.matrix
  fieldLedger := GeneratedFinalIntegratedW11.matrix.generatedPointFields
  routes := GeneratedFinalIntegratedW11.matrix.generatedPoint

def crossBlockFields : CrossBlockFields where
  targetMatrix := CrossBlockTargetIntegratedW11.matrix
  integratedMatrix := CrossBlockIntegratedW11.matrix
  targetInputs := CrossBlockTargetIntegratedW11.matrix.requiredInputs
  polynomial := CrossBlockTargetIntegratedW11.matrix.polynomialRows
  value := CrossBlockTargetIntegratedW11.matrix.valueRows
  ledger := CrossBlockTargetIntegratedW11.matrix.ledgerRows
  generatedCrossBlock := GeneratedFinalIntegratedW11.matrix.generatedCrossBlock
  integratedCrossBlock := GeneratedFinalIntegratedW11.matrix.integratedCrossBlock
  arbitraryNCrossBlock := GeneratedFinalIntegratedW11.matrix.arbitraryNCrossBlock

/-- Final W11 arbitrary-`n` target aggregate.

The record stores checked route rows only.  It supplies no source package and
therefore no bare global target bound.
-/
structure Matrix where
  imported : ImportedMatrices
  exact : ExactFields
  eventual : EventualFields
  small : SmallFields
  generated : GeneratedFields
  crossBlock : CrossBlockFields

/-- The checked final arbitrary-`n` target aggregate. -/
def matrix : Matrix where
  imported := importedMatrices
  exact := exactFields
  eventual := eventualFields
  small := smallFields
  generated := generatedFields
  crossBlock := crossBlockFields

/-! ## Public conditional projections: exact and eventual -/

theorem exactTarget_of_exactAssumptions
    (P : ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.exact.exactAssumptions.exactTarget P

theorem arbitraryTarget_of_exactAssumptions
    (P : ExactTargetAssumptions) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exact.exactAssumptions.arbitraryTarget P

theorem arbitraryTarget_of_exactClosedChains
    (P : ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exact.closedChains.arbitraryTarget P

theorem arbitraryTarget_of_exactGeneratedClosedChains
    (P : ExactGeneratedClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exact.generatedClosedChains.arbitraryTarget P

theorem largeTarget_of_eventualClosedChains
    (P : EventualClosedChainPackage) (n : Nat)
    (hn : matrix.eventual.closedChains.vertexThreshold P <= n) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.eventual.closedChains.largeTarget P n hn

theorem arbitraryTarget_of_eventualClosedChains
    (P : EventualClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventual.closedChains.arbitraryTarget P

theorem arbitraryTarget_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventual.generatedClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallLengthEventualClosedChains
    (P : SmallLengthEventualClosedChains) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventual.smallLengthClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallLengthEventualGeneratedClosedChains
    (P : SmallLengthEventualGeneratedClosedChains) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventual.smallLengthGeneratedClosedChains.arbitraryTarget P

/-! ## Public conditional projections: small length -/

theorem targetAt_lengthOne_of_smallExactFields
    (E : SmallExactFields) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * 1) :=
  matrix.small.exact.lengthOne E

theorem targetAt_lengthFive_of_smallExactFields
    (E : SmallExactFields) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * 5) :=
  matrix.small.exact.lengthFive E

theorem smallTarget_of_smallExactFields
    (E : SmallExactFields) :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo
      SmallLengthFinalIntegratedW11.vertexThreshold :=
  matrix.small.exact.smallTarget E

theorem arbitraryTarget_of_smallEventualLargeFields
    (P : SmallEventualLargeFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.small.eventualLarge.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualClosedChainFields
    (P : SmallEventualClosedChainFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.small.eventualClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualGeneratedClosedChainFields
    (P : SmallEventualGeneratedClosedChainFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.small.eventualGeneratedClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_smallEventualFiniteCertificateFields
    (P : SmallEventualFiniteCertificateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.small.eventualFiniteCertificates.arbitraryTarget P

theorem arbitraryTarget_of_smallAggregateViaLargeTarget
    (A : SmallAggregateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.small.aggregate.arbitraryTargetOfLargeTarget A

/-! ## Public conditional projections: generated point -/

theorem exactTarget_of_generatedNormalizedPolynomial
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generated.routes.normalizedPolynomial F).exactTarget C

theorem arbitraryTarget_of_generatedNormalizedPolynomial
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedPolynomialFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generated.routes.normalizedPolynomial F).arbitraryTarget C

theorem arbitraryTarget_of_generatedNormalizedValue
    {F : GeneratedPointFamily}
    (C : GeneratedPointNormalizedValueFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generated.routes.normalizedValue F).arbitraryTarget C

theorem arbitraryTarget_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.generated.routes.lowerBound F).arbitraryTarget C

theorem arbitraryTarget_of_generatedFlexibleCandidateAssembly
    (C : GeneratedFlexibleCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.generated.routes.flexibleCandidateAssembly.arbitraryTarget C

theorem arbitraryTarget_of_generatedFinalConditionalFamily
    (C : GeneratedFinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.generated.routes.finalConditionalFamily.arbitraryTarget C

/-! ## Public conditional projections: cross block -/

theorem targetAt_exactBlock_of_crossBlockPolynomialRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : CrossBlockPolynomialRows F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.crossBlock.polynomial.rows F k hk).exactBlockTarget R

theorem arbitraryTarget_of_crossBlockPolynomialRowFamilies
    {F : CrossBlockFamily}
    (R : CrossBlockPolynomialRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlock.polynomial.rowFamilies F).route.arbitraryTarget R

theorem targetAt_exactBlock_of_crossBlockValueRows
    {F : CrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : CrossBlockValueRows F k hk) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  (matrix.crossBlock.value.rows F k hk).exactBlockTarget R

theorem arbitraryTarget_of_crossBlockValueRowFamilies
    {F : CrossBlockFamily}
    (R : CrossBlockValueRowFamilies F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlock.value.rowFamilies F).route.arbitraryTarget R

theorem arbitraryTarget_of_crossBlockInequalityLedger
    {F : CrossBlockFamily}
    (L : CrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlock.ledger.inequalityLedgers F).route.arbitraryTarget L

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : CrossBlockFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlock.ledger.closureLedgers F).route.arbitraryTarget C

theorem arbitraryTarget_of_generatedCrossBlockInequalityLedger
    {F : GeneratedCrossBlockFamily}
    (L : GeneratedCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlock.generatedCrossBlock F).directRoute.arbitraryTarget L

theorem arbitraryTarget_viaGeneratedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlock.generatedCrossBlock F).closureRoute.arbitraryTarget C

end

end ArbitraryNTargetFinalW11
end PachToth
end ErdosProblems1066
