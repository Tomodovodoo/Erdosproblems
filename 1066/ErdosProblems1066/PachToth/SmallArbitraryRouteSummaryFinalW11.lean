import ErdosProblems1066.PachToth.SmallLengthRouteSummaryFinalW11
import ErdosProblems1066.PachToth.ArbitraryNRouteSummaryFinalW11
import ErdosProblems1066.PachToth.SmallLengthArbitraryFinalW11
import ErdosProblems1066.PachToth.ArbitraryNFinalAggregateW11
import ErdosProblems1066.PachToth.PachTothW11RouteSummaryFinal

set_option autoImplicit false

/-!
# W11 final small/arbitrary route summary

This module is a compact facade over the final small-length and arbitrary-`n`
route summaries.  It records the imported checked summaries, displays the
explicit package fields used by the small and arbitrary sides, and exposes
target statements only as projections from those explicit packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallArbitraryRouteSummaryFinalW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev SmallTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenSmallUpTo n

abbrev ExactLengthFields :=
  SmallLengthArbitraryFinalW11.ExactLengthFields

abbrev EventualLargeDataFields :=
  SmallLengthArbitraryFinalW11.EventualLargeDataFields

abbrev SmallFinalAggregateFields :=
  SmallLengthArbitraryFinalW11.SmallFinalAggregateFields

abbrev SmallFinalEventualLargeFields :=
  SmallLengthArbitraryFinalW11.SmallFinalEventualLargeFields

abbrev SmallFinalEventualClosedChainFields :=
  SmallLengthArbitraryFinalW11.SmallFinalEventualClosedChainFields

abbrev SmallFinalEventualGeneratedClosedChainFields :=
  SmallLengthArbitraryFinalW11.SmallFinalEventualGeneratedClosedChainFields

abbrev SmallFinalEventualFiniteCertificateFields :=
  SmallLengthArbitraryFinalW11.SmallFinalEventualFiniteCertificateFields

abbrev ArbitraryNTargetFacade :=
  SmallLengthArbitraryFinalW11.ArbitraryNTargetFacade

abbrev blockThreshold : Nat :=
  SmallLengthArbitraryFinalW11.blockThreshold

abbrev vertexThreshold : Nat :=
  SmallLengthArbitraryFinalW11.vertexThreshold

abbrev ArbitraryNExactAssumptions :=
  ArbitraryNRouteSummaryFinalW11.ExactTargetAssumptions

abbrev ArbitraryNExactClosedChainPackage :=
  ArbitraryNRouteSummaryFinalW11.ExactClosedChainPackage

abbrev ArbitraryNExactGeneratedClosedChainPackage :=
  ArbitraryNRouteSummaryFinalW11.ExactGeneratedClosedChainPackage

abbrev ArbitraryNEventualClosedChainPackage :=
  ArbitraryNRouteSummaryFinalW11.EventualClosedChainPackage

abbrev ArbitraryNEventualGeneratedClosedChainPackage :=
  ArbitraryNRouteSummaryFinalW11.EventualGeneratedClosedChainPackage

abbrev ArbitraryNSmallLengthEventualClosedChains :=
  ArbitraryNRouteSummaryFinalW11.SmallLengthEventualClosedChains

abbrev ArbitraryNSmallLengthEventualGeneratedClosedChains :=
  ArbitraryNRouteSummaryFinalW11.SmallLengthEventualGeneratedClosedChains

abbrev ArbitraryNSmallAggregateFields :=
  ArbitraryNRouteSummaryFinalW11.SmallAggregateFields

abbrev GeneratedPointFamily :=
  ArbitraryNRouteSummaryFinalW11.GeneratedPointFamily

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  ArbitraryNRouteSummaryFinalW11.GeneratedPointLowerBoundFields F

abbrev GeneratedFinalPackage :=
  ArbitraryNRouteSummaryFinalW11.GeneratedFinalPackage

abbrev GeneratedCrossBlockFamily :=
  ArbitraryNRouteSummaryFinalW11.GeneratedCrossBlockFamily

abbrev GeneratedCrossBlockClosureLedger
    (F : GeneratedCrossBlockFamily) :=
  ArbitraryNRouteSummaryFinalW11.GeneratedCrossBlockClosureLedger F

abbrev ArbitraryNCrossBlockFamily :=
  ArbitraryNRouteSummaryFinalW11.CrossBlockFamily

abbrev ArbitraryNCrossBlockPolynomialRows
    (F : ArbitraryNCrossBlockFamily) (k : Nat) (hk : 0 < k) :=
  ArbitraryNRouteSummaryFinalW11.CrossBlockPolynomialRows F k hk

abbrev ArbitraryNCrossBlockClosureLedger
    (F : ArbitraryNCrossBlockFamily) :=
  ArbitraryNRouteSummaryFinalW11.CrossBlockClosureLedger F

/-! ## Checked summaries -/

/-- Checked final summaries imported by this facade. -/
structure CheckedSummaries where
  smallLengthRoute : SmallLengthRouteSummaryFinalW11.Matrix
  arbitraryNRoute : ArbitraryNRouteSummaryFinalW11.Matrix
  smallLengthArbitrary : SmallLengthArbitraryFinalW11.Matrix
  arbitraryNFinalAggregate : ArbitraryNFinalAggregateW11.Matrix
  pachTothRouteSummary : PachTothW11RouteSummaryFinal.Matrix

/-- The checked final summaries in this checkout. -/
def checkedSummaries : CheckedSummaries where
  smallLengthRoute := SmallLengthRouteSummaryFinalW11.matrix
  arbitraryNRoute := ArbitraryNRouteSummaryFinalW11.matrix
  smallLengthArbitrary := SmallLengthArbitraryFinalW11.matrix
  arbitraryNFinalAggregate := ArbitraryNFinalAggregateW11.matrix
  pachTothRouteSummary := PachTothW11RouteSummaryFinal.matrix

/-! ## Explicit fields -/

/-- Explicit field shapes on the small-length side. -/
structure ExplicitSmallFields where
  exactLengthFields : Type
  eventualLargeDataFields : Type
  smallFinalAggregateFields : Type
  smallFinalEventualLargeFields : Type
  smallFinalEventualClosedChainFields : Type
  smallFinalEventualGeneratedClosedChainFields : Type
  smallFinalEventualFiniteCertificateFields : Type

/-- Displayed small-length field shapes. -/
def explicitSmallFields : ExplicitSmallFields where
  exactLengthFields := ExactLengthFields
  eventualLargeDataFields := EventualLargeDataFields
  smallFinalAggregateFields := SmallFinalAggregateFields
  smallFinalEventualLargeFields := SmallFinalEventualLargeFields
  smallFinalEventualClosedChainFields :=
    SmallFinalEventualClosedChainFields
  smallFinalEventualGeneratedClosedChainFields :=
    SmallFinalEventualGeneratedClosedChainFields
  smallFinalEventualFiniteCertificateFields :=
    SmallFinalEventualFiniteCertificateFields

/-- Explicit field and package shapes on the arbitrary-`n` side. -/
structure ExplicitArbitraryNFields where
  exactAssumptions : Prop
  exactClosedChains : Type
  exactGeneratedClosedChains : Type
  eventualClosedChains : Type
  eventualGeneratedClosedChains : Type
  smallLengthEventualClosedChains : Type
  smallLengthEventualGeneratedClosedChains : Type
  smallAggregateFields : Type
  generatedPointFamilies : Type
  generatedFinalPackage : Type
  generatedCrossBlockFamilies : Type
  crossBlockFamilies : Type

/-- Displayed arbitrary-`n` field and package shapes. -/
def explicitArbitraryNFields : ExplicitArbitraryNFields where
  exactAssumptions := ArbitraryNExactAssumptions
  exactClosedChains := ArbitraryNExactClosedChainPackage
  exactGeneratedClosedChains := ArbitraryNExactGeneratedClosedChainPackage
  eventualClosedChains := ArbitraryNEventualClosedChainPackage
  eventualGeneratedClosedChains :=
    ArbitraryNEventualGeneratedClosedChainPackage
  smallLengthEventualClosedChains :=
    ArbitraryNSmallLengthEventualClosedChains
  smallLengthEventualGeneratedClosedChains :=
    ArbitraryNSmallLengthEventualGeneratedClosedChains
  smallAggregateFields := ArbitraryNSmallAggregateFields
  generatedPointFamilies := GeneratedPointFamily
  generatedFinalPackage := GeneratedFinalPackage
  generatedCrossBlockFamilies := GeneratedCrossBlockFamily
  crossBlockFamilies := ArbitraryNCrossBlockFamily

/-- Combined explicit package field summary. -/
structure ExplicitFieldSummary where
  small : ExplicitSmallFields
  arbitraryN : ExplicitArbitraryNFields
  arbitraryNSource : ArbitraryNRouteSummaryFinalW11.RouteSourceSummary
  pachTothOpenData : PachTothW11RouteSummaryFinal.ExplicitOpenData

/-- Displayed explicit package field summary. -/
def explicitFieldSummary : ExplicitFieldSummary where
  small := explicitSmallFields
  arbitraryN := explicitArbitraryNFields
  arbitraryNSource := ArbitraryNRouteSummaryFinalW11.routeSourceSummary
  pachTothOpenData := PachTothW11RouteSummaryFinal.explicitOpenData

/-! ## Conditional projections -/

/-- Exact small-length target projections from explicit exact fields. -/
structure SmallExactProjections where
  lengthOne : ExactLengthFields -> FixedTarget (16 * 1)
  lengthTwo : ExactLengthFields -> FixedTarget (16 * 2)
  lengthThree : ExactLengthFields -> FixedTarget (16 * 3)
  lengthFour : ExactLengthFields -> FixedTarget (16 * 4)
  lengthFive : ExactLengthFields -> FixedTarget (16 * 5)
  exactBlock :
    ExactLengthFields -> forall k : Nat, k < blockThreshold -> 0 < k ->
      FixedTarget (16 * k)
  smallTarget : ExactLengthFields -> SmallTarget vertexThreshold
  smallTargetViaAggregate :
    ExactLengthFields -> SmallTarget vertexThreshold

/-- Checked exact small-length target projections. -/
def smallExactProjections : SmallExactProjections where
  lengthOne := SmallLengthRouteSummaryFinalW11.targetAt_kOne
  lengthTwo := SmallLengthRouteSummaryFinalW11.targetAt_kTwo
  lengthThree := SmallLengthRouteSummaryFinalW11.targetAt_kThree
  lengthFour := SmallLengthRouteSummaryFinalW11.targetAt_kFour
  lengthFive := SmallLengthRouteSummaryFinalW11.targetAt_kFive
  exactBlock := SmallLengthRouteSummaryFinalW11.targetAt_smallBlock
  smallTarget := SmallLengthRouteSummaryFinalW11.smallTarget_of_exactLengthFields
  smallTargetViaAggregate :=
    SmallLengthRouteSummaryFinalW11.smallTarget_of_exactLengthFields_viaAggregate

/-- Large-side small-length projections from one explicit large data package. -/
structure SmallEventualProjections where
  aggregate :
    EventualLargeDataFields -> SmallFinalAggregateFields
  largeTarget :
    forall _P : EventualLargeDataFields, forall n : Nat,
      vertexThreshold <= n -> FixedTarget n
  targetFacadeViaLargeTarget :
    EventualLargeDataFields -> ArbitraryNTargetFacade
  arbitraryViaLargeTarget :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaClosedChains :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaGeneratedClosedChains :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaFiniteCertificates :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaAggregateLargeTarget :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaAggregateClosedChains :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaAggregateGeneratedClosedChains :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaAggregateFiniteCertificates :
    EventualLargeDataFields -> ArbitraryTarget
  arbitraryViaFinalConsistency :
    EventualLargeDataFields -> ArbitraryTarget

/-- Checked large-side small-length projections. -/
def smallEventualProjections : SmallEventualProjections where
  aggregate := SmallLengthRouteSummaryFinalW11.aggregateFields_of_eventualLargeData
  largeTarget := SmallLengthRouteSummaryFinalW11.largeTarget_of_eventualLargeData
  targetFacadeViaLargeTarget :=
    SmallLengthRouteSummaryFinalW11.targetFacade_of_eventualLargeData
  arbitraryViaLargeTarget :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaLargeTarget
  arbitraryViaClosedChains :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaClosedChains
  arbitraryViaGeneratedClosedChains :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaGeneratedClosedChains
  arbitraryViaFiniteCertificates :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaFiniteCertificates
  arbitraryViaAggregateLargeTarget :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaAggregateLargeTarget
  arbitraryViaAggregateClosedChains :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaAggregateClosedChains
  arbitraryViaAggregateGeneratedClosedChains :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaAggregateGeneratedClosedChains
  arbitraryViaAggregateFiniteCertificates :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaAggregateFiniteCertificates
  arbitraryViaFinalConsistency :=
    SmallLengthRouteSummaryFinalW11.arbitraryTarget_of_eventualLargeData_viaFinalConsistency

/-- Arbitrary-`n` projections from explicit arbitrary-side packages. -/
structure ArbitraryNProjections where
  exactTargetOfAssumptions :
    ArbitraryNExactAssumptions -> ExactTarget
  fixedTargetOfAssumptions :
    ArbitraryNExactAssumptions -> forall n : Nat, FixedTarget n
  arbitraryOfExactAssumptions :
    ArbitraryNExactAssumptions -> ArbitraryTarget
  arbitraryOfExactClosedChains :
    ArbitraryNExactClosedChainPackage -> ArbitraryTarget
  arbitraryOfExactGeneratedClosedChains :
    ArbitraryNExactGeneratedClosedChainPackage -> ArbitraryTarget
  largeOfEventualClosedChains :
    forall P : ArbitraryNEventualClosedChainPackage, forall n : Nat,
      (ArbitraryNRouteSummaryFinalW11.matrix.source.eventual.targetRoutes.closedChains.vertexThreshold
          P) <= n ->
        FixedTarget n
  arbitraryOfEventualClosedChains :
    ArbitraryNEventualClosedChainPackage -> ArbitraryTarget
  arbitraryOfEventualGeneratedClosedChains :
    ArbitraryNEventualGeneratedClosedChainPackage -> ArbitraryTarget
  arbitraryOfSmallLengthEventualClosedChains :
    ArbitraryNSmallLengthEventualClosedChains -> ArbitraryTarget
  arbitraryOfSmallLengthEventualGeneratedClosedChains :
    ArbitraryNSmallLengthEventualGeneratedClosedChains -> ArbitraryTarget
  arbitraryOfGeneratedLowerBound :
    forall {F : GeneratedPointFamily},
      GeneratedPointLowerBoundFields F -> ArbitraryTarget
  arbitraryOfGeneratedFinalPackage :
    GeneratedFinalPackage -> ArbitraryTarget
  fixedOfCrossBlockPolynomialRows :
    forall {F : ArbitraryNCrossBlockFamily} {k : Nat} {hk : 0 < k},
      ArbitraryNCrossBlockPolynomialRows F k hk -> FixedTarget (16 * k)
  arbitraryOfCrossBlockClosure :
    forall {F : ArbitraryNCrossBlockFamily},
      ArbitraryNCrossBlockClosureLedger F -> ArbitraryTarget
  arbitraryOfGeneratedCrossBlockClosure :
    forall {F : GeneratedCrossBlockFamily},
      GeneratedCrossBlockClosureLedger F -> ArbitraryTarget

/-- Checked arbitrary-`n` projections. -/
def arbitraryNProjections : ArbitraryNProjections where
  exactTargetOfAssumptions :=
    ArbitraryNRouteSummaryFinalW11.exactTarget_of_exactAssumptions
  fixedTargetOfAssumptions :=
    ArbitraryNRouteSummaryFinalW11.fixedTarget_of_exactAssumptions
  arbitraryOfExactAssumptions :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_exactAssumptions
  arbitraryOfExactClosedChains :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_exactClosedChains
  arbitraryOfExactGeneratedClosedChains :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_exactGeneratedClosedChains
  largeOfEventualClosedChains :=
    ArbitraryNRouteSummaryFinalW11.largeTarget_of_eventualClosedChains
  arbitraryOfEventualClosedChains :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_eventualClosedChains
  arbitraryOfEventualGeneratedClosedChains :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_eventualGeneratedClosedChains
  arbitraryOfSmallLengthEventualClosedChains :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_smallLengthEventualClosedChains
  arbitraryOfSmallLengthEventualGeneratedClosedChains :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_smallLengthEventualGeneratedClosedChains
  arbitraryOfGeneratedLowerBound :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_generatedLowerBound
  arbitraryOfGeneratedFinalPackage :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_generatedFinalPackage
  fixedOfCrossBlockPolynomialRows :=
    ArbitraryNRouteSummaryFinalW11.fixedTarget_of_crossBlockPolynomialRows
  arbitraryOfCrossBlockClosure :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_crossBlockClosureLedger
  arbitraryOfGeneratedCrossBlockClosure :=
    ArbitraryNRouteSummaryFinalW11.arbitraryTarget_of_generatedCrossBlockClosureLedger

/-- Projections as seen through the final Pach--Toth route facade. -/
structure PachTothProjectionLinks where
  arbitraryNExactClosedChains :
    ArbitraryNExactClosedChainPackage -> ArbitraryTarget
  arbitraryNEventualGeneratedClosedChains :
    ArbitraryNEventualGeneratedClosedChainPackage -> ArbitraryTarget
  largeArbitraryNEventualClosedChains :
    forall P : ArbitraryNEventualClosedChainPackage, forall n : Nat,
      (PachTothW11RouteSummaryFinal.matrix.projections.arbitraryNEventualClosedChains.vertexThreshold
          P) <= n ->
        FixedTarget n

/-- Checked Pach--Toth facade links. -/
def pachTothProjectionLinks : PachTothProjectionLinks where
  arbitraryNExactClosedChains :=
    PachTothW11RouteSummaryFinal.arbitraryTarget_of_arbitraryNExactClosedChains
  arbitraryNEventualGeneratedClosedChains :=
    PachTothW11RouteSummaryFinal.arbitraryTarget_of_arbitraryNEventualGeneratedClosedChains
  largeArbitraryNEventualClosedChains :=
    PachTothW11RouteSummaryFinal.largeTarget_of_arbitraryNEventualClosedChains

/-- All target-facing projections exposed by this facade. -/
structure ConditionalTargetProjections where
  smallExact : SmallExactProjections
  smallEventual : SmallEventualProjections
  arbitraryN : ArbitraryNProjections
  pachTothLinks : PachTothProjectionLinks

/-- Checked conditional projection table. -/
def conditionalTargetProjections : ConditionalTargetProjections where
  smallExact := smallExactProjections
  smallEventual := smallEventualProjections
  arbitraryN := arbitraryNProjections
  pachTothLinks := pachTothProjectionLinks

/-! ## Final summary matrix -/

/-- Concise final checked small/arbitrary route summary matrix. -/
structure Matrix where
  checked : CheckedSummaries
  fields : ExplicitFieldSummary
  projections : ConditionalTargetProjections

/-- The checked final small/arbitrary route summary matrix. -/
def matrix : Matrix where
  checked := checkedSummaries
  fields := explicitFieldSummary
  projections := conditionalTargetProjections

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

theorem checked_smallLengthRoute :
    matrix.checked.smallLengthRoute =
      SmallLengthRouteSummaryFinalW11.matrix := by
  rfl

theorem checked_arbitraryNRoute :
    matrix.checked.arbitraryNRoute =
      ArbitraryNRouteSummaryFinalW11.matrix := by
  rfl

theorem checked_smallLengthArbitrary :
    matrix.checked.smallLengthArbitrary =
      SmallLengthArbitraryFinalW11.matrix := by
  rfl

theorem checked_arbitraryNFinalAggregate :
    matrix.checked.arbitraryNFinalAggregate =
      ArbitraryNFinalAggregateW11.matrix := by
  rfl

theorem checked_pachTothRouteSummary :
    matrix.checked.pachTothRouteSummary =
      PachTothW11RouteSummaryFinal.matrix := by
  rfl

/-! ## Public conditional target projections -/

theorem targetAt_lengthOne (E : ExactLengthFields) :
    FixedTarget (16 * 1) :=
  matrix.projections.smallExact.lengthOne E

theorem targetAt_lengthTwo (E : ExactLengthFields) :
    FixedTarget (16 * 2) :=
  matrix.projections.smallExact.lengthTwo E

theorem targetAt_lengthThree (E : ExactLengthFields) :
    FixedTarget (16 * 3) :=
  matrix.projections.smallExact.lengthThree E

theorem targetAt_lengthFour (E : ExactLengthFields) :
    FixedTarget (16 * 4) :=
  matrix.projections.smallExact.lengthFour E

theorem targetAt_lengthFive (E : ExactLengthFields) :
    FixedTarget (16 * 5) :=
  matrix.projections.smallExact.lengthFive E

theorem targetAt_smallBlock
    (E : ExactLengthFields) (k : Nat) (hkLt : k < blockThreshold)
    (hkPos : 0 < k) :
    FixedTarget (16 * k) :=
  matrix.projections.smallExact.exactBlock E k hkLt hkPos

theorem smallTarget_of_exactLengthFields
    (E : ExactLengthFields) :
    SmallTarget vertexThreshold :=
  matrix.projections.smallExact.smallTarget E

theorem smallTarget_of_exactLengthFields_viaAggregate
    (E : ExactLengthFields) :
    SmallTarget vertexThreshold :=
  matrix.projections.smallExact.smallTargetViaAggregate E

def aggregateFields_of_eventualLargeData
    (P : EventualLargeDataFields) :
    SmallFinalAggregateFields :=
  matrix.projections.smallEventual.aggregate P

theorem largeTarget_of_eventualLargeData
    (P : EventualLargeDataFields) (n : Nat)
    (hn : vertexThreshold <= n) :
    FixedTarget n :=
  matrix.projections.smallEventual.largeTarget P n hn

def targetFacade_of_eventualLargeData
    (P : EventualLargeDataFields) :
    ArbitraryNTargetFacade :=
  matrix.projections.smallEventual.targetFacadeViaLargeTarget P

theorem arbitraryTarget_of_eventualLargeData_viaLargeTarget
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual.arbitraryViaLargeTarget P

theorem arbitraryTarget_of_eventualLargeData_viaClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual.arbitraryViaClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaGeneratedClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual.arbitraryViaGeneratedClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaFiniteCertificates
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual.arbitraryViaFiniteCertificates P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateLargeTarget
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual.arbitraryViaAggregateLargeTarget P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual.arbitraryViaAggregateClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateGeneratedClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual
    |>.arbitraryViaAggregateGeneratedClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateFiniteCertificates
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual
    |>.arbitraryViaAggregateFiniteCertificates P

theorem arbitraryTarget_of_eventualLargeData_viaFinalConsistency
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.projections.smallEventual.arbitraryViaFinalConsistency P

theorem exactTarget_of_arbitraryNExactAssumptions
    (A : ArbitraryNExactAssumptions) :
    ExactTarget :=
  matrix.projections.arbitraryN.exactTargetOfAssumptions A

theorem fixedTarget_of_arbitraryNExactAssumptions
    (A : ArbitraryNExactAssumptions) (n : Nat) :
    FixedTarget n :=
  matrix.projections.arbitraryN.fixedTargetOfAssumptions A n

theorem arbitraryTarget_of_arbitraryNExactAssumptions
    (A : ArbitraryNExactAssumptions) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfExactAssumptions A

theorem arbitraryTarget_of_arbitraryNExactClosedChains
    (P : ArbitraryNExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfExactClosedChains P

theorem arbitraryTarget_of_arbitraryNExactGeneratedClosedChains
    (P : ArbitraryNExactGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfExactGeneratedClosedChains P

theorem largeTarget_of_arbitraryNEventualClosedChains
    (P : ArbitraryNEventualClosedChainPackage) (n : Nat)
    (hn :
      (ArbitraryNRouteSummaryFinalW11.matrix.source.eventual.targetRoutes.closedChains.vertexThreshold
          P) <= n) :
    FixedTarget n :=
  matrix.projections.arbitraryN.largeOfEventualClosedChains P n hn

theorem arbitraryTarget_of_arbitraryNEventualClosedChains
    (P : ArbitraryNEventualClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfEventualClosedChains P

theorem arbitraryTarget_of_arbitraryNEventualGeneratedClosedChains
    (P : ArbitraryNEventualGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfEventualGeneratedClosedChains P

theorem arbitraryTarget_of_arbitraryNSmallLengthEventualClosedChains
    (P : ArbitraryNSmallLengthEventualClosedChains) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfSmallLengthEventualClosedChains P

theorem arbitraryTarget_of_arbitraryNSmallLengthEventualGeneratedClosedChains
    (P : ArbitraryNSmallLengthEventualGeneratedClosedChains) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN
    |>.arbitraryOfSmallLengthEventualGeneratedClosedChains P

theorem arbitraryTarget_of_generatedLowerBound
    {F : GeneratedPointFamily}
    (C : GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfGeneratedLowerBound C

theorem arbitraryTarget_of_generatedFinalPackage
    (C : GeneratedFinalPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfGeneratedFinalPackage C

theorem fixedTarget_of_crossBlockPolynomialRows
    {F : ArbitraryNCrossBlockFamily} {k : Nat} {hk : 0 < k}
    (R : ArbitraryNCrossBlockPolynomialRows F k hk) :
    FixedTarget (16 * k) :=
  matrix.projections.arbitraryN.fixedOfCrossBlockPolynomialRows R

theorem arbitraryTarget_of_crossBlockClosure
    {F : ArbitraryNCrossBlockFamily}
    (C : ArbitraryNCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfCrossBlockClosure C

theorem arbitraryTarget_of_generatedCrossBlockClosure
    {F : GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.projections.arbitraryN.arbitraryOfGeneratedCrossBlockClosure C

theorem arbitraryTarget_of_pachTothArbitraryNExactClosedChains
    (P : ArbitraryNExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.pachTothLinks.arbitraryNExactClosedChains P

theorem arbitraryTarget_of_pachTothArbitraryNEventualGeneratedClosedChains
    (P : ArbitraryNEventualGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.pachTothLinks
    |>.arbitraryNEventualGeneratedClosedChains P

theorem largeTarget_of_pachTothArbitraryNEventualClosedChains
    (P : ArbitraryNEventualClosedChainPackage) (n : Nat)
    (hn :
      (PachTothW11RouteSummaryFinal.matrix.projections.arbitraryNEventualClosedChains.vertexThreshold
          P) <= n) :
    FixedTarget n :=
  matrix.projections.pachTothLinks
    |>.largeArbitraryNEventualClosedChains P n hn

end

end SmallArbitraryRouteSummaryFinalW11
end PachToth
end ErdosProblems1066
