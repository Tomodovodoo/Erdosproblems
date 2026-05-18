import ErdosProblems1066.PachToth.SmallLengthArbitraryFinalW11
import ErdosProblems1066.PachToth.SmallLengthFinalIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNFinalAggregateW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final small-length route summary

This file is a compact facade for the final W11 small-length route.  The five
small block targets are exposed as separate `k = 1,2,3,4,5` projections from
explicit exact-length fields, and every arbitrary-target projection below is
indexed by explicit eventual large data.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthRouteSummaryFinalW11

noncomputable section

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev SmallTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenSmallUpTo n

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

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

/-! ## Checked ledgers -/

/-- The final ledgers summarized here. -/
structure CheckedLedgers where
  smallLengthArbitrary :
    SmallLengthArbitraryFinalW11.Matrix
  smallLengthFinal :
    SmallLengthFinalIntegratedW11.Matrix
  arbitraryNFinalAggregate :
    ArbitraryNFinalAggregateW11.Matrix
  pachTothFinalConsistency :
    PachTothW11FinalConsistency.Matrix

/-- Checked final ledgers imported by this summary. -/
def checkedLedgers : CheckedLedgers where
  smallLengthArbitrary := SmallLengthArbitraryFinalW11.matrix
  smallLengthFinal := SmallLengthFinalIntegratedW11.matrix
  arbitraryNFinalAggregate := ArbitraryNFinalAggregateW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Explicit field ledgers -/

/-- The external data shapes retained by the summary. -/
structure ExplicitDataLedgers where
  exactLengthFields : Type
  eventualLargeDataFields : Type
  smallFinalAggregateFields : Type
  smallFinalEventualLargeFields : Type
  smallFinalEventualClosedChainFields : Type
  smallFinalEventualGeneratedClosedChainFields : Type
  smallFinalEventualFiniteCertificateFields : Type

/-- Displayed field shapes for the small-length route. -/
def explicitDataLedgers : ExplicitDataLedgers where
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

/-! ## Summary rows -/

/-- The five exact small block targets, exposed only from exact input data. -/
structure ExactLengthSummary (alpha : Type) where
  exactFields : alpha -> ExactLengthFields
  kOne : alpha -> FixedTarget (16 * 1)
  kTwo : alpha -> FixedTarget (16 * 2)
  kThree : alpha -> FixedTarget (16 * 3)
  kFour : alpha -> FixedTarget (16 * 4)
  kFive : alpha -> FixedTarget (16 * 5)
  exactBlock :
    alpha -> forall k : Nat, k < blockThreshold -> 0 < k ->
      FixedTarget (16 * k)
  smallTarget : alpha -> SmallTarget vertexThreshold
  smallTargetViaAggregate : alpha -> SmallTarget vertexThreshold

/-- Checked exact-length row for `k = 1,2,3,4,5`. -/
def exactLengthSummary : ExactLengthSummary ExactLengthFields where
  exactFields := fun E => E
  kOne := SmallLengthArbitraryFinalW11.targetAt_lengthOne
  kTwo := SmallLengthArbitraryFinalW11.targetAt_lengthTwo
  kThree := SmallLengthArbitraryFinalW11.targetAt_lengthThree
  kFour := SmallLengthArbitraryFinalW11.targetAt_lengthFour
  kFive := SmallLengthArbitraryFinalW11.targetAt_lengthFive
  exactBlock := SmallLengthArbitraryFinalW11.exactBlockTarget
  smallTarget := SmallLengthArbitraryFinalW11.smallTarget
  smallTargetViaAggregate := fun E =>
    ArbitraryNFinalAggregateW11.smallTarget_of_smallExactFields
      E.toSmallFinalFields

/-- Eventual large-data routes, all indexed by one explicit data package. -/
structure EventualLargeDataSummary (alpha : Type) where
  aggregate : alpha -> SmallFinalAggregateFields
  eventualLargeTargetFields :
    alpha -> SmallFinalEventualLargeFields
  eventualClosedChainFields :
    alpha -> SmallFinalEventualClosedChainFields
  eventualGeneratedClosedChainFields :
    alpha -> SmallFinalEventualGeneratedClosedChainFields
  eventualFiniteCertificateFields :
    alpha -> SmallFinalEventualFiniteCertificateFields
  largeTarget :
    forall _a : alpha, forall n : Nat, vertexThreshold <= n ->
      FixedTarget n
  largeChain :
    forall _a : alpha, forall k : Nat, blockThreshold <= k -> 0 < k ->
      SplitSoundness.ExactChainUpper k
  largeGeneratedData :
    forall _a : alpha, forall k : Nat, blockThreshold <= k ->
      forall hk : 0 < k,
        SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  largeCertificates :
    alpha ->
      EventualRoleHingeClosure.EventualFiniteCertificateObligations
        blockThreshold
  targetFacadeViaLargeTarget : alpha -> ArbitraryNTargetFacade
  arbitraryViaSmallLengthLargeTarget : alpha -> ArbitraryTarget
  arbitraryViaSmallLengthClosedChains : alpha -> ArbitraryTarget
  arbitraryViaSmallLengthGeneratedClosedChains :
    alpha -> ArbitraryTarget
  arbitraryViaSmallLengthFiniteCertificates :
    alpha -> ArbitraryTarget
  arbitraryViaArbitraryNFinalAggregateLargeTarget :
    alpha -> ArbitraryTarget
  arbitraryViaArbitraryNFinalAggregateClosedChains :
    alpha -> ArbitraryTarget
  arbitraryViaArbitraryNFinalAggregateGeneratedClosedChains :
    alpha -> ArbitraryTarget
  arbitraryViaArbitraryNFinalAggregateFiniteCertificates :
    alpha -> ArbitraryTarget
  arbitraryViaPachTothFinalConsistency :
    alpha -> ArbitraryTarget

/-- Checked eventual large-data row. -/
def eventualLargeDataSummary :
    EventualLargeDataSummary EventualLargeDataFields where
  aggregate :=
    SmallLengthArbitraryFinalW11.EventualLargeDataFields.toSmallFinalAggregate
  eventualLargeTargetFields :=
    SmallLengthArbitraryFinalW11.EventualLargeDataFields.toSmallFinalEventualLarge
  eventualClosedChainFields :=
    SmallLengthArbitraryFinalW11.EventualLargeDataFields.toSmallFinalEventualClosedChain
  eventualGeneratedClosedChainFields :=
    SmallLengthArbitraryFinalW11.EventualLargeDataFields.toSmallFinalEventualGeneratedClosedChain
  eventualFiniteCertificateFields :=
    SmallLengthArbitraryFinalW11.EventualLargeDataFields.toSmallFinalEventualFiniteCertificate
  largeTarget := fun P => P.largeTarget
  largeChain := fun P => P.largeChain
  largeGeneratedData := fun P => P.largeGeneratedData
  largeCertificates := fun P => P.largeCertificates
  targetFacadeViaLargeTarget :=
    SmallLengthArbitraryFinalW11.EventualLargeDataFields.targetFacadeViaLargeTarget
  arbitraryViaSmallLengthLargeTarget :=
    SmallLengthArbitraryFinalW11.arbitraryTarget_of_largeDataViaLargeTarget
  arbitraryViaSmallLengthClosedChains :=
    SmallLengthArbitraryFinalW11.arbitraryTarget_of_largeDataViaClosedChains
  arbitraryViaSmallLengthGeneratedClosedChains :=
    SmallLengthArbitraryFinalW11.arbitraryTarget_of_largeDataViaGeneratedClosedChains
  arbitraryViaSmallLengthFiniteCertificates :=
    SmallLengthArbitraryFinalW11.arbitraryTarget_of_largeDataViaFiniteCertificates
  arbitraryViaArbitraryNFinalAggregateLargeTarget := fun P =>
    ArbitraryNFinalAggregateW11.arbitraryTarget_of_smallAggregate_viaLargeTarget
      P.toSmallFinalAggregate
  arbitraryViaArbitraryNFinalAggregateClosedChains := fun P =>
    ArbitraryNFinalAggregateW11.arbitraryTarget_of_smallAggregate_viaClosedChains
      P.toSmallFinalAggregate
  arbitraryViaArbitraryNFinalAggregateGeneratedClosedChains := fun P =>
    ArbitraryNFinalAggregateW11.arbitraryTarget_of_smallAggregate_viaGeneratedClosedChains
      P.toSmallFinalAggregate
  arbitraryViaArbitraryNFinalAggregateFiniteCertificates := fun P =>
    ArbitraryNFinalAggregateW11.arbitraryTarget_of_smallAggregate_viaFiniteCertificates
      P.toSmallFinalAggregate
  arbitraryViaPachTothFinalConsistency :=
    SmallLengthArbitraryFinalW11.arbitraryTarget_of_largeDataViaPachTothFinalConsistency

/-! ## Final summary matrix -/

/-- Concise final small-length route summary matrix. -/
structure Matrix where
  checked : CheckedLedgers
  explicitData : ExplicitDataLedgers
  exactLengths : ExactLengthSummary ExactLengthFields
  eventualLargeData :
    EventualLargeDataSummary EventualLargeDataFields
  blockers : PachTothW11FinalConsistency.FinalBlockerLedger

/-- The checked final small-length route summary matrix. -/
def matrix : Matrix where
  checked := checkedLedgers
  explicitData := explicitDataLedgers
  exactLengths := exactLengthSummary
  eventualLargeData := eventualLargeDataSummary
  blockers := PachTothW11FinalConsistency.finalBlockerLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

theorem checked_smallLengthArbitrary :
    matrix.checked.smallLengthArbitrary =
      SmallLengthArbitraryFinalW11.matrix := by
  rfl

theorem checked_smallLengthFinal :
    matrix.checked.smallLengthFinal =
      SmallLengthFinalIntegratedW11.matrix := by
  rfl

theorem checked_arbitraryNFinalAggregate :
    matrix.checked.arbitraryNFinalAggregate =
      ArbitraryNFinalAggregateW11.matrix := by
  rfl

theorem checked_pachTothFinalConsistency :
    matrix.checked.pachTothFinalConsistency =
      PachTothW11FinalConsistency.matrix := by
  rfl

/-! ## Conditional projections -/

theorem targetAt_kOne (E : ExactLengthFields) :
    FixedTarget (16 * 1) :=
  matrix.exactLengths.kOne E

theorem targetAt_kTwo (E : ExactLengthFields) :
    FixedTarget (16 * 2) :=
  matrix.exactLengths.kTwo E

theorem targetAt_kThree (E : ExactLengthFields) :
    FixedTarget (16 * 3) :=
  matrix.exactLengths.kThree E

theorem targetAt_kFour (E : ExactLengthFields) :
    FixedTarget (16 * 4) :=
  matrix.exactLengths.kFour E

theorem targetAt_kFive (E : ExactLengthFields) :
    FixedTarget (16 * 5) :=
  matrix.exactLengths.kFive E

theorem targetAt_smallBlock
    (E : ExactLengthFields) (k : Nat) (hkLt : k < blockThreshold)
    (hkPos : 0 < k) :
    FixedTarget (16 * k) :=
  matrix.exactLengths.exactBlock E k hkLt hkPos

theorem smallTarget_of_exactLengthFields
    (E : ExactLengthFields) :
    SmallTarget vertexThreshold :=
  matrix.exactLengths.smallTarget E

theorem smallTarget_of_exactLengthFields_viaAggregate
    (E : ExactLengthFields) :
    SmallTarget vertexThreshold :=
  matrix.exactLengths.smallTargetViaAggregate E

def aggregateFields_of_eventualLargeData
    (P : EventualLargeDataFields) :
    SmallFinalAggregateFields :=
  matrix.eventualLargeData.aggregate P

theorem largeTarget_of_eventualLargeData
    (P : EventualLargeDataFields) (n : Nat)
    (hn : vertexThreshold <= n) :
    FixedTarget n :=
  matrix.eventualLargeData.largeTarget P n hn

def targetFacade_of_eventualLargeData
    (P : EventualLargeDataFields) :
    ArbitraryNTargetFacade :=
  matrix.eventualLargeData.targetFacadeViaLargeTarget P

theorem arbitraryTarget_of_eventualLargeData_viaLargeTarget
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallLengthLargeTarget P

theorem arbitraryTarget_of_eventualLargeData_viaClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallLengthClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaGeneratedClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallLengthGeneratedClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaFiniteCertificates
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallLengthFiniteCertificates P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateLargeTarget
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaArbitraryNFinalAggregateLargeTarget P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaArbitraryNFinalAggregateClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateGeneratedClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData
    |>.arbitraryViaArbitraryNFinalAggregateGeneratedClosedChains P

theorem arbitraryTarget_of_eventualLargeData_viaAggregateFiniteCertificates
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData
    |>.arbitraryViaArbitraryNFinalAggregateFiniteCertificates P

theorem arbitraryTarget_of_eventualLargeData_viaFinalConsistency
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaPachTothFinalConsistency P

/-! ## Consistency witness projections -/

theorem exactLengthConsistency
    (E : ExactLengthFields) :
    PachTothW11ConsistencyMatrix.SmallLengthExactBlockConsistency
      E.toSmallLengthExactBlockTargets :=
  matrix.checked.pachTothFinalConsistency.consistency
    |>.smallLengthExactBlocks E.toSmallLengthExactBlockTargets

theorem eventualClosedChainConsistency
    (P : EventualLargeDataFields) :
    PachTothW11ConsistencyMatrix.SmallLengthEventualClosedChainConsistency
      P.toSmallClosureEventualClosedChain :=
  matrix.checked.pachTothFinalConsistency.consistency
    |>.smallLengthEventualClosedChains P.toSmallClosureEventualClosedChain

end

end SmallLengthRouteSummaryFinalW11
end PachToth
end ErdosProblems1066
