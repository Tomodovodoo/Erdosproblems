import ErdosProblems1066.PachToth.SmallLengthTargetIntegratedW11
import ErdosProblems1066.PachToth.SmallLengthIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# Final W11 small-length threshold aggregate

This module is a terminal ledger for the W11 small-length threshold route.
It keeps the exact target inputs for block lengths `k = 1,2,3,4,5`
as displayed fields, and keeps every large-side route as displayed data.

All public arbitrary-`n` target projections below are conditional on one of
those explicit packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthFinalIntegratedW11

noncomputable section

universe u

abbrev TargetExactFields :=
  SmallLengthTargetIntegratedW11.ExactBlockTargetFields

abbrev TargetEventualLargeFields :=
  SmallLengthTargetIntegratedW11.EventualLargeTargetFields

abbrev TargetEventualClosedChainFields :=
  SmallLengthTargetIntegratedW11.EventualClosedChainTargetFields

abbrev TargetEventualGeneratedClosedChainFields :=
  SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields

abbrev TargetEventualFiniteCertificateFields :=
  SmallLengthTargetIntegratedW11.EventualFiniteCertificateTargetFields

abbrev TargetRouteMatrix :=
  SmallLengthTargetIntegratedW11.Matrix

abbrev SmallLengthMatrix :=
  SmallLengthIntegratedW11.Matrix

abbrev ArbitraryNMatrix :=
  ArbitraryNIntegratedW11.Matrix

abbrev PachTothIntegratedMatrix :=
  PachTothW11IntegratedMatrix.Matrix

abbrev SmallLengthExactBlockTargets :=
  SmallLengthClosureW11.SmallLengthExactBlockTargets

abbrev ThresholdTargetFacade :=
  ArbitraryNClosureW11.ThresholdTargetFacade

abbrev ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.ArbitraryNTargetFacade

abbrev blockThreshold : Nat :=
  SmallLengthTargetIntegratedW11.blockThreshold

abbrev vertexThreshold : Nat :=
  SmallLengthTargetIntegratedW11.vertexThreshold

/-! ## Displayed exact fields -/

/-- Explicit exact target data for the five positive block lengths below the
threshold block six. -/
structure ExactTargetFields : Type where
  lengthOne : targetUpperConstructionFiveSixteenAt (16 * 1)
  lengthTwo : targetUpperConstructionFiveSixteenAt (16 * 2)
  lengthThree : targetUpperConstructionFiveSixteenAt (16 * 3)
  lengthFour : targetUpperConstructionFiveSixteenAt (16 * 4)
  lengthFive : targetUpperConstructionFiveSixteenAt (16 * 5)

namespace ExactTargetFields

def toTargetExactFields (E : ExactTargetFields) :
    TargetExactFields where
  lengthOne := E.lengthOne
  lengthTwo := E.lengthTwo
  lengthThree := E.lengthThree
  lengthFour := E.lengthFour
  lengthFive := E.lengthFive

def toSmallLengthExactBlockTargets (E : ExactTargetFields) :
    SmallLengthExactBlockTargets :=
  E.toTargetExactFields.toSmallLengthExactBlockTargets

theorem exactBlock (E : ExactTargetFields) :
    forall k : Nat, k < blockThreshold -> 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k) :=
  E.toTargetExactFields.exactBlock

theorem smallTarget (E : ExactTargetFields) :
    targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold :=
  E.toTargetExactFields.smallTarget

def thresholdFacadeOfLarge
    (E : ExactTargetFields)
    (largeTarget :
      forall n : Nat, vertexThreshold <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    ThresholdTargetFacade :=
  E.toTargetExactFields.thresholdFacadeOfEventualLarge largeTarget

def targetFacadeOfLarge
    (E : ExactTargetFields)
    (largeTarget :
      forall n : Nat, vertexThreshold <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    ArbitraryNTargetFacade :=
  E.toTargetExactFields.targetFacadeOfEventualLarge largeTarget

theorem arbitraryTargetOfLarge
    (E : ExactTargetFields)
    (largeTarget :
      forall n : Nat, vertexThreshold <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    targetUpperConstructionFiveSixteenArbitrary :=
  E.toTargetExactFields.arbitraryTargetOfEventualLarge largeTarget

end ExactTargetFields

/-! ## Conditional threshold data packages -/

/-- Exact small targets plus an explicit large target route from the threshold
onward. -/
structure EventualLargeTargetFields extends ExactTargetFields where
  largeTarget :
    forall n : Nat, vertexThreshold <= n ->
      targetUpperConstructionFiveSixteenAt n

namespace EventualLargeTargetFields

def exactTargets (P : EventualLargeTargetFields) :
    ExactTargetFields :=
  P.toExactTargetFields

def toTargetFields (P : EventualLargeTargetFields) :
    TargetEventualLargeFields where
  toExactBlockTargetFields := P.exactTargets.toTargetExactFields
  largeTarget := P.largeTarget

def thresholdFacade (P : EventualLargeTargetFields) :
    ThresholdTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualLargeTargetFields.thresholdFacade
    P.toTargetFields

def targetFacade (P : EventualLargeTargetFields) :
    ArbitraryNTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualLargeTargetFields.targetFacade
    P.toTargetFields

theorem fixedTarget (P : EventualLargeTargetFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  SmallLengthTargetIntegratedW11.EventualLargeTargetFields.fixedTarget
    P.toTargetFields n

theorem arbitraryTarget (P : EventualLargeTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthTargetIntegratedW11.EventualLargeTargetFields.arbitraryTarget
    P.toTargetFields

end EventualLargeTargetFields

/-- Exact small targets plus eventual exact closed-chain data from block six
onward. -/
structure EventualClosedChainFields extends ExactTargetFields where
  largeChain :
    forall k : Nat, blockThreshold <= k -> 0 < k ->
      SplitSoundness.ExactChainUpper k

namespace EventualClosedChainFields

def exactTargets (P : EventualClosedChainFields) :
    ExactTargetFields :=
  P.toExactTargetFields

def toTargetFields (P : EventualClosedChainFields) :
    TargetEventualClosedChainFields where
  toExactBlockTargetFields := P.exactTargets.toTargetExactFields
  largeChain := P.largeChain

def thresholdFacade (P : EventualClosedChainFields) :
    ThresholdTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualClosedChainTargetFields.thresholdFacade
    P.toTargetFields

def targetFacade (P : EventualClosedChainFields) :
    ArbitraryNTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualClosedChainTargetFields.targetFacade
    P.toTargetFields

theorem fixedTarget (P : EventualClosedChainFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  SmallLengthTargetIntegratedW11.EventualClosedChainTargetFields.fixedTarget
    P.toTargetFields n

theorem arbitraryTarget (P : EventualClosedChainFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthTargetIntegratedW11.EventualClosedChainTargetFields.arbitraryTarget
    P.toTargetFields

end EventualClosedChainFields

/-- Exact small targets plus eventual generated closed-chain data from block
six onward. -/
structure EventualGeneratedClosedChainFields extends ExactTargetFields where
  largeData :
    forall k : Nat, blockThreshold <= k -> forall hk : 0 < k,
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk

namespace EventualGeneratedClosedChainFields

def exactTargets (P : EventualGeneratedClosedChainFields) :
    ExactTargetFields :=
  P.toExactTargetFields

def toTargetFields (P : EventualGeneratedClosedChainFields) :
    TargetEventualGeneratedClosedChainFields where
  toExactBlockTargetFields := P.exactTargets.toTargetExactFields
  largeData := P.largeData

def thresholdFacade (P : EventualGeneratedClosedChainFields) :
    ThresholdTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields.thresholdFacade
    P.toTargetFields

def targetFacade (P : EventualGeneratedClosedChainFields) :
    ArbitraryNTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields.targetFacade
    P.toTargetFields

theorem fixedTarget (P : EventualGeneratedClosedChainFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields.fixedTarget
    P.toTargetFields n

theorem arbitraryTarget (P : EventualGeneratedClosedChainFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields.arbitraryTarget
    P.toTargetFields

end EventualGeneratedClosedChainFields

/-- Exact small targets plus the finite-certificate obligations for all
blocks from six onward. -/
structure EventualFiniteCertificateFields extends ExactTargetFields where
  largeCertificates :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations
      blockThreshold

namespace EventualFiniteCertificateFields

def exactTargets (P : EventualFiniteCertificateFields) :
    ExactTargetFields :=
  P.toExactTargetFields

def toTargetFields (P : EventualFiniteCertificateFields) :
    TargetEventualFiniteCertificateFields where
  toExactBlockTargetFields := P.exactTargets.toTargetExactFields
  largeCertificates := P.largeCertificates

def thresholdFacade (P : EventualFiniteCertificateFields) :
    ThresholdTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualFiniteCertificateTargetFields.thresholdFacade
    P.toTargetFields

def targetFacade (P : EventualFiniteCertificateFields) :
    ArbitraryNTargetFacade :=
  SmallLengthTargetIntegratedW11.EventualFiniteCertificateTargetFields.targetFacade
    P.toTargetFields

theorem fixedTarget (P : EventualFiniteCertificateFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  SmallLengthTargetIntegratedW11.EventualFiniteCertificateTargetFields.fixedTarget
    P.toTargetFields n

theorem arbitraryTarget (P : EventualFiniteCertificateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthTargetIntegratedW11.EventualFiniteCertificateTargetFields.arbitraryTarget
    P.toTargetFields

end EventualFiniteCertificateFields

/-! ## Full displayed aggregate -/

/-- A full displayed aggregate carrying the exact small targets and every
large-side data route used by this final ledger. -/
structure AggregateFields extends ExactTargetFields where
  largeTarget :
    forall n : Nat, vertexThreshold <= n ->
      targetUpperConstructionFiveSixteenAt n
  largeChain :
    forall k : Nat, blockThreshold <= k -> 0 < k ->
      SplitSoundness.ExactChainUpper k
  largeGeneratedData :
    forall k : Nat, blockThreshold <= k -> forall hk : 0 < k,
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  largeCertificates :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations
      blockThreshold

namespace AggregateFields

def exactTargets (A : AggregateFields) : ExactTargetFields :=
  A.toExactTargetFields

def toEventualLargeTargetFields
    (A : AggregateFields) :
    EventualLargeTargetFields where
  toExactTargetFields := A.exactTargets
  largeTarget := A.largeTarget

def toEventualClosedChainFields
    (A : AggregateFields) :
    EventualClosedChainFields where
  toExactTargetFields := A.exactTargets
  largeChain := A.largeChain

def toEventualGeneratedClosedChainFields
    (A : AggregateFields) :
    EventualGeneratedClosedChainFields where
  toExactTargetFields := A.exactTargets
  largeData := A.largeGeneratedData

def toEventualFiniteCertificateFields
    (A : AggregateFields) :
    EventualFiniteCertificateFields where
  toExactTargetFields := A.exactTargets
  largeCertificates := A.largeCertificates

def thresholdFacadeOfLargeTarget
    (A : AggregateFields) :
    ThresholdTargetFacade :=
  A.toEventualLargeTargetFields.thresholdFacade

def targetFacadeOfLargeTarget
    (A : AggregateFields) :
    ArbitraryNTargetFacade :=
  A.toEventualLargeTargetFields.targetFacade

theorem arbitraryTargetOfLargeTarget
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  A.toEventualLargeTargetFields.arbitraryTarget

def thresholdFacadeOfClosedChains
    (A : AggregateFields) :
    ThresholdTargetFacade :=
  A.toEventualClosedChainFields.thresholdFacade

def targetFacadeOfClosedChains
    (A : AggregateFields) :
    ArbitraryNTargetFacade :=
  A.toEventualClosedChainFields.targetFacade

theorem arbitraryTargetOfClosedChains
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  A.toEventualClosedChainFields.arbitraryTarget

def thresholdFacadeOfGeneratedClosedChains
    (A : AggregateFields) :
    ThresholdTargetFacade :=
  A.toEventualGeneratedClosedChainFields.thresholdFacade

def targetFacadeOfGeneratedClosedChains
    (A : AggregateFields) :
    ArbitraryNTargetFacade :=
  A.toEventualGeneratedClosedChainFields.targetFacade

theorem arbitraryTargetOfGeneratedClosedChains
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  A.toEventualGeneratedClosedChainFields.arbitraryTarget

def thresholdFacadeOfFiniteCertificates
    (A : AggregateFields) :
    ThresholdTargetFacade :=
  A.toEventualFiniteCertificateFields.thresholdFacade

def targetFacadeOfFiniteCertificates
    (A : AggregateFields) :
    ArbitraryNTargetFacade :=
  A.toEventualFiniteCertificateFields.targetFacade

theorem arbitraryTargetOfFiniteCertificates
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  A.toEventualFiniteCertificateFields.arbitraryTarget

end AggregateFields

/-! ## Route rows -/

/-- Exact route row with each target length exposed separately. -/
structure ExactRouteRow (alpha : Sort u) where
  exactTargets : alpha -> ExactTargetFields
  lengthOne :
    alpha -> targetUpperConstructionFiveSixteenAt (16 * 1)
  lengthTwo :
    alpha -> targetUpperConstructionFiveSixteenAt (16 * 2)
  lengthThree :
    alpha -> targetUpperConstructionFiveSixteenAt (16 * 3)
  lengthFour :
    alpha -> targetUpperConstructionFiveSixteenAt (16 * 4)
  lengthFive :
    alpha -> targetUpperConstructionFiveSixteenAt (16 * 5)
  exactBlock :
    alpha -> forall k : Nat, k < blockThreshold -> 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k)
  smallTarget :
    alpha -> targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold

def exactRouteRow : ExactRouteRow ExactTargetFields where
  exactTargets := fun E => E
  lengthOne := fun E => E.lengthOne
  lengthTwo := fun E => E.lengthTwo
  lengthThree := fun E => E.lengthThree
  lengthFour := fun E => E.lengthFour
  lengthFive := fun E => E.lengthFive
  exactBlock := fun E => E.exactBlock
  smallTarget := fun E => E.smallTarget

/-- Conditional threshold route row. -/
structure ThresholdRouteRow (alpha : Sort u) where
  exactTargets : alpha -> ExactTargetFields
  smallTarget :
    alpha -> targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold
  largeTarget :
    forall _a : alpha, forall n : Nat, vertexThreshold <= n ->
      targetUpperConstructionFiveSixteenAt n
  thresholdFacade : alpha -> ThresholdTargetFacade
  targetFacade : alpha -> ArbitraryNTargetFacade
  fixedTarget :
    alpha -> forall n : Nat, targetUpperConstructionFiveSixteenAt n
  arbitraryTarget :
    alpha -> targetUpperConstructionFiveSixteenArbitrary

def eventualLargeTargetRouteRow :
    ThresholdRouteRow EventualLargeTargetFields where
  exactTargets := EventualLargeTargetFields.exactTargets
  smallTarget := fun P => P.exactTargets.smallTarget
  largeTarget := fun P => P.largeTarget
  thresholdFacade := EventualLargeTargetFields.thresholdFacade
  targetFacade := EventualLargeTargetFields.targetFacade
  fixedTarget := EventualLargeTargetFields.fixedTarget
  arbitraryTarget := EventualLargeTargetFields.arbitraryTarget

def eventualClosedChainRouteRow :
    ThresholdRouteRow EventualClosedChainFields where
  exactTargets := EventualClosedChainFields.exactTargets
  smallTarget := fun P => P.exactTargets.smallTarget
  largeTarget := fun P n hn => P.thresholdFacade.largeTarget n hn
  thresholdFacade := EventualClosedChainFields.thresholdFacade
  targetFacade := EventualClosedChainFields.targetFacade
  fixedTarget := EventualClosedChainFields.fixedTarget
  arbitraryTarget := EventualClosedChainFields.arbitraryTarget

def eventualGeneratedClosedChainRouteRow :
    ThresholdRouteRow EventualGeneratedClosedChainFields where
  exactTargets := EventualGeneratedClosedChainFields.exactTargets
  smallTarget := fun P => P.exactTargets.smallTarget
  largeTarget := fun P n hn => P.thresholdFacade.largeTarget n hn
  thresholdFacade := EventualGeneratedClosedChainFields.thresholdFacade
  targetFacade := EventualGeneratedClosedChainFields.targetFacade
  fixedTarget := EventualGeneratedClosedChainFields.fixedTarget
  arbitraryTarget := EventualGeneratedClosedChainFields.arbitraryTarget

def eventualFiniteCertificateRouteRow :
    ThresholdRouteRow EventualFiniteCertificateFields where
  exactTargets := EventualFiniteCertificateFields.exactTargets
  smallTarget := fun P => P.exactTargets.smallTarget
  largeTarget := fun P n hn => P.thresholdFacade.largeTarget n hn
  thresholdFacade := EventualFiniteCertificateFields.thresholdFacade
  targetFacade := EventualFiniteCertificateFields.targetFacade
  fixedTarget := EventualFiniteCertificateFields.fixedTarget
  arbitraryTarget := EventualFiniteCertificateFields.arbitraryTarget

/-- Route row for the full displayed aggregate. -/
structure AggregateRouteRow where
  exactTargets : AggregateFields -> ExactTargetFields
  largeTarget :
    forall _A : AggregateFields, forall n : Nat, vertexThreshold <= n ->
      targetUpperConstructionFiveSixteenAt n
  largeChain :
    forall _A : AggregateFields, forall k : Nat, blockThreshold <= k ->
      0 < k -> SplitSoundness.ExactChainUpper k
  largeGeneratedData :
    forall _A : AggregateFields, forall k : Nat, blockThreshold <= k ->
      forall hk : 0 < k,
        SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  largeCertificates :
    AggregateFields ->
      EventualRoleHingeClosure.EventualFiniteCertificateObligations
        blockThreshold
  targetFacadeOfLargeTarget :
    AggregateFields -> ArbitraryNTargetFacade
  targetFacadeOfClosedChains :
    AggregateFields -> ArbitraryNTargetFacade
  targetFacadeOfGeneratedClosedChains :
    AggregateFields -> ArbitraryNTargetFacade
  targetFacadeOfFiniteCertificates :
    AggregateFields -> ArbitraryNTargetFacade
  arbitraryTargetOfLargeTarget :
    AggregateFields -> targetUpperConstructionFiveSixteenArbitrary
  arbitraryTargetOfClosedChains :
    AggregateFields -> targetUpperConstructionFiveSixteenArbitrary
  arbitraryTargetOfGeneratedClosedChains :
    AggregateFields -> targetUpperConstructionFiveSixteenArbitrary
  arbitraryTargetOfFiniteCertificates :
    AggregateFields -> targetUpperConstructionFiveSixteenArbitrary

def aggregateRouteRow : AggregateRouteRow where
  exactTargets := AggregateFields.exactTargets
  largeTarget := fun A => A.largeTarget
  largeChain := fun A => A.largeChain
  largeGeneratedData := fun A => A.largeGeneratedData
  largeCertificates := fun A => A.largeCertificates
  targetFacadeOfLargeTarget := AggregateFields.targetFacadeOfLargeTarget
  targetFacadeOfClosedChains := AggregateFields.targetFacadeOfClosedChains
  targetFacadeOfGeneratedClosedChains :=
    AggregateFields.targetFacadeOfGeneratedClosedChains
  targetFacadeOfFiniteCertificates :=
    AggregateFields.targetFacadeOfFiniteCertificates
  arbitraryTargetOfLargeTarget := AggregateFields.arbitraryTargetOfLargeTarget
  arbitraryTargetOfClosedChains := AggregateFields.arbitraryTargetOfClosedChains
  arbitraryTargetOfGeneratedClosedChains :=
    AggregateFields.arbitraryTargetOfGeneratedClosedChains
  arbitraryTargetOfFiniteCertificates :=
    AggregateFields.arbitraryTargetOfFiniteCertificates

/-! ## Matrix -/

/-- Source package shapes consumed by this final aggregate. -/
structure FieldLedger where
  exactTargets : Type
  eventualLargeTargets : Type
  eventualClosedChains : Type
  eventualGeneratedClosedChains : Type
  eventualFiniteCertificates : Type
  aggregateFields : Type

def fieldLedger : FieldLedger where
  exactTargets := ExactTargetFields
  eventualLargeTargets := EventualLargeTargetFields
  eventualClosedChains := EventualClosedChainFields
  eventualGeneratedClosedChains := EventualGeneratedClosedChainFields
  eventualFiniteCertificates := EventualFiniteCertificateFields
  aggregateFields := AggregateFields

/-- Final small-length threshold matrix.  It records route functions only; it
does not construct the small exact fields or the large-side data. -/
structure Matrix where
  fields : FieldLedger
  targetRoutes : TargetRouteMatrix
  smallLengthIntegrated : SmallLengthMatrix
  arbitraryNIntegrated : ArbitraryNMatrix
  pachTothIntegrated : PachTothIntegratedMatrix
  exactTargets : ExactRouteRow ExactTargetFields
  eventualLargeTargets :
    ThresholdRouteRow EventualLargeTargetFields
  eventualClosedChains :
    ThresholdRouteRow EventualClosedChainFields
  eventualGeneratedClosedChains :
    ThresholdRouteRow EventualGeneratedClosedChainFields
  eventualFiniteCertificates :
    ThresholdRouteRow EventualFiniteCertificateFields
  aggregate : AggregateRouteRow

/-- The checked final small-length threshold matrix. -/
def matrix : Matrix where
  fields := fieldLedger
  targetRoutes := SmallLengthTargetIntegratedW11.matrix
  smallLengthIntegrated := SmallLengthIntegratedW11.matrix
  arbitraryNIntegrated := ArbitraryNIntegratedW11.matrix
  pachTothIntegrated := PachTothW11IntegratedMatrix.matrix
  exactTargets := exactRouteRow
  eventualLargeTargets := eventualLargeTargetRouteRow
  eventualClosedChains := eventualClosedChainRouteRow
  eventualGeneratedClosedChains := eventualGeneratedClosedChainRouteRow
  eventualFiniteCertificates := eventualFiniteCertificateRouteRow
  aggregate := aggregateRouteRow

/-! ## Public projections -/

theorem targetUpperConstructionFiveSixteenAt_lengthOne
    (E : ExactTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 1) :=
  matrix.exactTargets.lengthOne E

theorem targetUpperConstructionFiveSixteenAt_lengthTwo
    (E : ExactTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 2) :=
  matrix.exactTargets.lengthTwo E

theorem targetUpperConstructionFiveSixteenAt_lengthThree
    (E : ExactTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 3) :=
  matrix.exactTargets.lengthThree E

theorem targetUpperConstructionFiveSixteenAt_lengthFour
    (E : ExactTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 4) :=
  matrix.exactTargets.lengthFour E

theorem targetUpperConstructionFiveSixteenAt_lengthFive
    (E : ExactTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 5) :=
  matrix.exactTargets.lengthFive E

theorem targetUpperConstructionFiveSixteenSmallUpTo_threshold
    (E : ExactTargetFields) :
    targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold :=
  matrix.exactTargets.smallTarget E

def targetFacade_of_eventualLargeTargetFields
    (P : EventualLargeTargetFields) :
    ArbitraryNTargetFacade :=
  matrix.eventualLargeTargets.targetFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualLargeTargetFields
    (P : EventualLargeTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualLargeTargets.arbitraryTarget P

def targetFacade_of_eventualClosedChainFields
    (P : EventualClosedChainFields) :
    ArbitraryNTargetFacade :=
  matrix.eventualClosedChains.targetFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualClosedChainFields
    (P : EventualClosedChainFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualClosedChains.arbitraryTarget P

def targetFacade_of_eventualGeneratedClosedChainFields
    (P : EventualGeneratedClosedChainFields) :
    ArbitraryNTargetFacade :=
  matrix.eventualGeneratedClosedChains.targetFacade P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualGeneratedClosedChainFields
    (P : EventualGeneratedClosedChainFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualGeneratedClosedChains.arbitraryTarget P

def targetFacade_of_eventualFiniteCertificateFields
    (P : EventualFiniteCertificateFields) :
    ArbitraryNTargetFacade :=
  matrix.eventualFiniteCertificates.targetFacade P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualFiniteCertificateFields
    (P : EventualFiniteCertificateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualFiniteCertificates.arbitraryTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_aggregate_largeTarget
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.aggregate.arbitraryTargetOfLargeTarget A

theorem targetUpperConstructionFiveSixteenArbitrary_of_aggregate_closedChains
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.aggregate.arbitraryTargetOfClosedChains A

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_aggregate_generatedClosedChains
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.aggregate.arbitraryTargetOfGeneratedClosedChains A

theorem targetUpperConstructionFiveSixteenArbitrary_of_aggregate_finiteCertificates
    (A : AggregateFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.aggregate.arbitraryTargetOfFiniteCertificates A

end

end SmallLengthFinalIntegratedW11
end PachToth
end ErdosProblems1066
