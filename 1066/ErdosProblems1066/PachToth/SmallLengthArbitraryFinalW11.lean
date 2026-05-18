import ErdosProblems1066.PachToth.SmallLengthFinalIntegratedW11
import ErdosProblems1066.PachToth.SmallLengthTargetIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNFinalIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final small-length/arbitrary-`n` consistency layer

This file packages the final small-length threshold routes together with the
final arbitrary-`n` ledgers.  The finite side is displayed as separate
`k = 1,2,3,4,5` fields, and each all-`n` route still takes an explicit
large-side data package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthArbitraryFinalW11

noncomputable section

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev SmallTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenSmallUpTo n

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev SmallFinalMatrix :=
  SmallLengthFinalIntegratedW11.Matrix

abbrev SmallTargetMatrix :=
  SmallLengthTargetIntegratedW11.Matrix

abbrev ArbitraryFinalMatrix :=
  ArbitraryNFinalIntegratedW11.Matrix

abbrev ArbitraryTargetFinalMatrix :=
  ArbitraryNTargetFinalW11.Matrix

abbrev PachTothFinalConsistencyMatrix :=
  PachTothW11FinalConsistency.Matrix

abbrev SmallFinalExactFields :=
  SmallLengthFinalIntegratedW11.ExactTargetFields

abbrev SmallTargetExactFields :=
  SmallLengthTargetIntegratedW11.ExactBlockTargetFields

abbrev SmallLengthExactBlockTargets :=
  SmallLengthClosureW11.SmallLengthExactBlockTargets

abbrev SmallFinalEventualLargeFields :=
  SmallLengthFinalIntegratedW11.EventualLargeTargetFields

abbrev SmallFinalEventualClosedChainFields :=
  SmallLengthFinalIntegratedW11.EventualClosedChainFields

abbrev SmallFinalEventualGeneratedClosedChainFields :=
  SmallLengthFinalIntegratedW11.EventualGeneratedClosedChainFields

abbrev SmallFinalEventualFiniteCertificateFields :=
  SmallLengthFinalIntegratedW11.EventualFiniteCertificateFields

abbrev SmallFinalAggregateFields :=
  SmallLengthFinalIntegratedW11.AggregateFields

abbrev SmallTargetEventualLargeFields :=
  SmallLengthTargetIntegratedW11.EventualLargeTargetFields

abbrev SmallTargetEventualClosedChainFields :=
  SmallLengthTargetIntegratedW11.EventualClosedChainTargetFields

abbrev SmallTargetEventualGeneratedClosedChainFields :=
  SmallLengthTargetIntegratedW11.EventualGeneratedClosedChainTargetFields

abbrev SmallTargetEventualFiniteCertificateFields :=
  SmallLengthTargetIntegratedW11.EventualFiniteCertificateTargetFields

abbrev SmallIntegratedEventualLargeFields :=
  SmallLengthIntegratedW11.EventualLargeTargetAssumptionsBelowSix

abbrev SmallIntegratedEventualFiniteCertificateFields :=
  SmallLengthIntegratedW11.EventualFiniteCertificateAssumptionsBelowSix

abbrev SmallClosureEventualClosedChainFields :=
  SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix

abbrev SmallClosureEventualGeneratedClosedChainFields :=
  SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix

abbrev ThresholdTargetFacade :=
  ArbitraryNIntegratedW11.ThresholdTargetFacade

abbrev ArbitraryNTargetFacade :=
  ArbitraryNIntegratedW11.ArbitraryNTargetFacade

abbrev blockThreshold : Nat :=
  SmallLengthFinalIntegratedW11.blockThreshold

abbrev vertexThreshold : Nat :=
  SmallLengthFinalIntegratedW11.vertexThreshold

/-! ## Imported final ledgers -/

/-- The checked final ledgers that must coexist for this pass. -/
structure ImportedFinalLedgers where
  smallFinal : SmallFinalMatrix
  smallTarget : SmallTargetMatrix
  arbitraryFinal : ArbitraryFinalMatrix
  arbitraryTargetFinal : ArbitraryTargetFinalMatrix
  pachTothFinalConsistency : PachTothFinalConsistencyMatrix

/-- The imported final ledgers in the current environment. -/
def importedFinalLedgers : ImportedFinalLedgers where
  smallFinal := SmallLengthFinalIntegratedW11.matrix
  smallTarget := SmallLengthTargetIntegratedW11.matrix
  arbitraryFinal := ArbitraryNFinalIntegratedW11.matrix
  arbitraryTargetFinal := ArbitraryNTargetFinalW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Displayed small and large field packages -/

/-- Exact target data for the five positive block lengths below block six. -/
structure ExactLengthFields : Type where
  lengthOne : FixedTarget (16 * 1)
  lengthTwo : FixedTarget (16 * 2)
  lengthThree : FixedTarget (16 * 3)
  lengthFour : FixedTarget (16 * 4)
  lengthFive : FixedTarget (16 * 5)

namespace ExactLengthFields

def toSmallFinalFields (E : ExactLengthFields) :
    SmallFinalExactFields where
  lengthOne := E.lengthOne
  lengthTwo := E.lengthTwo
  lengthThree := E.lengthThree
  lengthFour := E.lengthFour
  lengthFive := E.lengthFive

def toSmallTargetFields (E : ExactLengthFields) :
    SmallTargetExactFields where
  lengthOne := E.lengthOne
  lengthTwo := E.lengthTwo
  lengthThree := E.lengthThree
  lengthFour := E.lengthFour
  lengthFive := E.lengthFive

def toSmallLengthExactBlockTargets (E : ExactLengthFields) :
    SmallLengthExactBlockTargets :=
  E.toSmallFinalFields.toSmallLengthExactBlockTargets

theorem exactBlock (E : ExactLengthFields) :
    forall k : Nat, k < blockThreshold -> 0 < k ->
      FixedTarget (16 * k) :=
  E.toSmallFinalFields.exactBlock

theorem smallTarget (E : ExactLengthFields) :
    SmallTarget vertexThreshold :=
  E.toSmallFinalFields.smallTarget

end ExactLengthFields

/-- Exact small targets plus every large-side route used by the final ledgers.
-/
structure EventualLargeDataFields : Type extends ExactLengthFields where
  largeTarget :
    forall n : Nat, vertexThreshold <= n -> FixedTarget n
  largeChain :
    forall k : Nat, blockThreshold <= k -> 0 < k ->
      SplitSoundness.ExactChainUpper k
  largeGeneratedData :
    forall k : Nat, blockThreshold <= k -> forall hk : 0 < k,
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  largeCertificates :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations
      blockThreshold

namespace EventualLargeDataFields

def exactFields (P : EventualLargeDataFields) :
    ExactLengthFields :=
  P.toExactLengthFields

def toSmallFinalAggregate (P : EventualLargeDataFields) :
    SmallFinalAggregateFields where
  lengthOne := P.lengthOne
  lengthTwo := P.lengthTwo
  lengthThree := P.lengthThree
  lengthFour := P.lengthFour
  lengthFive := P.lengthFive
  largeTarget := P.largeTarget
  largeChain := P.largeChain
  largeGeneratedData := P.largeGeneratedData
  largeCertificates := P.largeCertificates

def toSmallFinalEventualLarge (P : EventualLargeDataFields) :
    SmallFinalEventualLargeFields :=
  P.toSmallFinalAggregate.toEventualLargeTargetFields

def toSmallFinalEventualClosedChain (P : EventualLargeDataFields) :
    SmallFinalEventualClosedChainFields :=
  P.toSmallFinalAggregate.toEventualClosedChainFields

def toSmallFinalEventualGeneratedClosedChain
    (P : EventualLargeDataFields) :
    SmallFinalEventualGeneratedClosedChainFields :=
  P.toSmallFinalAggregate.toEventualGeneratedClosedChainFields

def toSmallFinalEventualFiniteCertificate
    (P : EventualLargeDataFields) :
    SmallFinalEventualFiniteCertificateFields :=
  P.toSmallFinalAggregate.toEventualFiniteCertificateFields

def toSmallTargetEventualLarge (P : EventualLargeDataFields) :
    SmallTargetEventualLargeFields where
  toExactBlockTargetFields := P.exactFields.toSmallTargetFields
  largeTarget := P.largeTarget

def toSmallTargetEventualClosedChain (P : EventualLargeDataFields) :
    SmallTargetEventualClosedChainFields where
  toExactBlockTargetFields := P.exactFields.toSmallTargetFields
  largeChain := P.largeChain

def toSmallTargetEventualGeneratedClosedChain
    (P : EventualLargeDataFields) :
    SmallTargetEventualGeneratedClosedChainFields where
  toExactBlockTargetFields := P.exactFields.toSmallTargetFields
  largeData := P.largeGeneratedData

def toSmallTargetEventualFiniteCertificate
    (P : EventualLargeDataFields) :
    SmallTargetEventualFiniteCertificateFields where
  toExactBlockTargetFields := P.exactFields.toSmallTargetFields
  largeCertificates := P.largeCertificates

def toSmallIntegratedEventualLarge (P : EventualLargeDataFields) :
    SmallIntegratedEventualLargeFields where
  largeTarget := P.largeTarget
  exactBlocks := P.exactFields.toSmallLengthExactBlockTargets

def toSmallClosureEventualClosedChain
    (P : EventualLargeDataFields) :
    SmallClosureEventualClosedChainFields where
  largeChain := P.largeChain
  exactBlocks := P.exactFields.toSmallLengthExactBlockTargets

def toSmallClosureEventualGeneratedClosedChain
    (P : EventualLargeDataFields) :
    SmallClosureEventualGeneratedClosedChainFields where
  largeData := P.largeGeneratedData
  exactBlocks := P.exactFields.toSmallLengthExactBlockTargets

def toSmallIntegratedEventualFiniteCertificate
    (P : EventualLargeDataFields) :
    SmallIntegratedEventualFiniteCertificateFields where
  largeCertificates := P.largeCertificates
  exactBlocks := P.exactFields.toSmallLengthExactBlockTargets

def thresholdFacadeViaLargeTarget (P : EventualLargeDataFields) :
    ThresholdTargetFacade :=
  P.toSmallFinalEventualLarge.thresholdFacade

def targetFacadeViaLargeTarget (P : EventualLargeDataFields) :
    ArbitraryNTargetFacade :=
  P.toSmallFinalEventualLarge.targetFacade

theorem arbitraryTargetViaLargeTarget (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  P.toSmallFinalEventualLarge.arbitraryTarget

theorem arbitraryTargetViaClosedChains (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  P.toSmallFinalEventualClosedChain.arbitraryTarget

theorem arbitraryTargetViaGeneratedClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  P.toSmallFinalEventualGeneratedClosedChain.arbitraryTarget

theorem arbitraryTargetViaFiniteCertificates
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  P.toSmallFinalEventualFiniteCertificate.arbitraryTarget

end EventualLargeDataFields

/-! ## Route rows -/

/-- Routes exposing all five finite block targets through each final ledger. -/
structure ExactLengthRouteRow (alpha : Type) where
  exactFields : alpha -> ExactLengthFields
  smallFinalFields : alpha -> SmallFinalExactFields
  smallTargetFields : alpha -> SmallTargetExactFields
  exactBlock :
    alpha -> forall k : Nat, k < blockThreshold -> 0 < k ->
      FixedTarget (16 * k)
  lengthOne : alpha -> FixedTarget (16 * 1)
  lengthTwo : alpha -> FixedTarget (16 * 2)
  lengthThree : alpha -> FixedTarget (16 * 3)
  lengthFour : alpha -> FixedTarget (16 * 4)
  lengthFive : alpha -> FixedTarget (16 * 5)
  smallTarget : alpha -> SmallTarget vertexThreshold
  lengthOneViaArbitraryTargetFinal :
    alpha -> FixedTarget (16 * 1)
  lengthTwoViaArbitraryTargetFinal :
    alpha -> FixedTarget (16 * 2)
  lengthThreeViaArbitraryTargetFinal :
    alpha -> FixedTarget (16 * 3)
  lengthFourViaArbitraryTargetFinal :
    alpha -> FixedTarget (16 * 4)
  lengthFiveViaArbitraryTargetFinal :
    alpha -> FixedTarget (16 * 5)

def exactLengthRouteRow :
    ExactLengthRouteRow ExactLengthFields where
  exactFields := fun E => E
  smallFinalFields := ExactLengthFields.toSmallFinalFields
  smallTargetFields := ExactLengthFields.toSmallTargetFields
  exactBlock := fun E => E.exactBlock
  lengthOne := fun E =>
    SmallLengthFinalIntegratedW11.matrix.exactTargets.lengthOne
      E.toSmallFinalFields
  lengthTwo := fun E =>
    SmallLengthFinalIntegratedW11.matrix.exactTargets.lengthTwo
      E.toSmallFinalFields
  lengthThree := fun E =>
    SmallLengthFinalIntegratedW11.matrix.exactTargets.lengthThree
      E.toSmallFinalFields
  lengthFour := fun E =>
    SmallLengthFinalIntegratedW11.matrix.exactTargets.lengthFour
      E.toSmallFinalFields
  lengthFive := fun E =>
    SmallLengthFinalIntegratedW11.matrix.exactTargets.lengthFive
      E.toSmallFinalFields
  smallTarget := fun E =>
    SmallLengthFinalIntegratedW11.matrix.exactTargets.smallTarget
      E.toSmallFinalFields
  lengthOneViaArbitraryTargetFinal := fun E =>
    ArbitraryNTargetFinalW11.matrix.small.exact.lengthOne
      E.toSmallFinalFields
  lengthTwoViaArbitraryTargetFinal := fun E =>
    ArbitraryNTargetFinalW11.matrix.small.exact.lengthTwo
      E.toSmallFinalFields
  lengthThreeViaArbitraryTargetFinal := fun E =>
    ArbitraryNTargetFinalW11.matrix.small.exact.lengthThree
      E.toSmallFinalFields
  lengthFourViaArbitraryTargetFinal := fun E =>
    ArbitraryNTargetFinalW11.matrix.small.exact.lengthFour
      E.toSmallFinalFields
  lengthFiveViaArbitraryTargetFinal := fun E =>
    ArbitraryNTargetFinalW11.matrix.small.exact.lengthFive
      E.toSmallFinalFields

/-- Routes from the full large-data package to the final all-`n` facades. -/
structure EventualLargeDataRouteRow (alpha : Type) where
  aggregate : alpha -> SmallFinalAggregateFields
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
  arbitraryViaSmallFinalLargeTarget : alpha -> ArbitraryTarget
  arbitraryViaSmallFinalClosedChains : alpha -> ArbitraryTarget
  arbitraryViaSmallFinalGeneratedClosedChains : alpha -> ArbitraryTarget
  arbitraryViaSmallFinalFiniteCertificates : alpha -> ArbitraryTarget
  arbitraryViaArbitraryFinalLargeTarget : alpha -> ArbitraryTarget
  arbitraryViaArbitraryFinalClosedChains : alpha -> ArbitraryTarget
  arbitraryViaArbitraryFinalGeneratedClosedChains : alpha -> ArbitraryTarget
  arbitraryViaArbitraryFinalFiniteCertificates : alpha -> ArbitraryTarget
  arbitraryViaArbitraryTargetFinalLargeTarget : alpha -> ArbitraryTarget
  arbitraryViaPachTothFinalGeneratedClosedChains : alpha -> ArbitraryTarget

def eventualLargeDataRouteRow :
    EventualLargeDataRouteRow EventualLargeDataFields where
  aggregate := EventualLargeDataFields.toSmallFinalAggregate
  largeTarget := fun P => P.largeTarget
  largeChain := fun P => P.largeChain
  largeGeneratedData := fun P => P.largeGeneratedData
  largeCertificates := fun P => P.largeCertificates
  targetFacadeViaLargeTarget :=
    EventualLargeDataFields.targetFacadeViaLargeTarget
  arbitraryViaSmallFinalLargeTarget :=
    EventualLargeDataFields.arbitraryTargetViaLargeTarget
  arbitraryViaSmallFinalClosedChains :=
    EventualLargeDataFields.arbitraryTargetViaClosedChains
  arbitraryViaSmallFinalGeneratedClosedChains :=
    EventualLargeDataFields.arbitraryTargetViaGeneratedClosedChains
  arbitraryViaSmallFinalFiniteCertificates :=
    EventualLargeDataFields.arbitraryTargetViaFiniteCertificates
  arbitraryViaArbitraryFinalLargeTarget := fun P =>
    ArbitraryNFinalIntegratedW11.matrix.smallCases
      |>.eventualLargeTargets
      |>.arbitraryTarget P.toSmallIntegratedEventualLarge
  arbitraryViaArbitraryFinalClosedChains := fun P =>
    ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain
      |>.smallLengthEventualClosedChains
      |>.arbitraryTarget P.toSmallClosureEventualClosedChain
  arbitraryViaArbitraryFinalGeneratedClosedChains := fun P =>
    ArbitraryNFinalIntegratedW11.matrix.eventualLargeChain
      |>.smallLengthEventualGeneratedClosedChains
      |>.arbitraryTarget P.toSmallClosureEventualGeneratedClosedChain
  arbitraryViaArbitraryFinalFiniteCertificates := fun P =>
    ArbitraryNFinalIntegratedW11.matrix.smallCases
      |>.eventualFiniteCertificates
      |>.arbitraryTarget P.toSmallIntegratedEventualFiniteCertificate
  arbitraryViaArbitraryTargetFinalLargeTarget := fun P =>
    ArbitraryNTargetFinalW11.arbitraryTarget_of_smallAggregateViaLargeTarget
      P.toSmallFinalAggregate
  arbitraryViaPachTothFinalGeneratedClosedChains := fun P =>
    PachTothW11FinalConsistency.matrix.routes.smallLengthTarget
      |>.eventualGeneratedClosedChains
      |>.arbitraryTarget P.toSmallTargetEventualGeneratedClosedChain

/-! ## Final consistency matrix -/

/-- Field shapes exposed by this final small-length/arbitrary-`n` layer. -/
structure FieldLedger where
  exactLengthFields : Type
  eventualLargeDataFields : Type
  smallFinalAggregateFields : Type

def fieldLedger : FieldLedger where
  exactLengthFields := ExactLengthFields
  eventualLargeDataFields := EventualLargeDataFields
  smallFinalAggregateFields := SmallFinalAggregateFields

/-- Final consistency matrix for the small-length and arbitrary-`n` ledgers.
-/
structure Matrix where
  imported : ImportedFinalLedgers
  fields : FieldLedger
  exactLengths : ExactLengthRouteRow ExactLengthFields
  eventualLargeData : EventualLargeDataRouteRow EventualLargeDataFields

/-- The checked final consistency matrix. -/
def matrix : Matrix where
  imported := importedFinalLedgers
  fields := fieldLedger
  exactLengths := exactLengthRouteRow
  eventualLargeData := eventualLargeDataRouteRow

theorem checked_smallFinal :
    matrix.imported.smallFinal = SmallLengthFinalIntegratedW11.matrix := by
  rfl

theorem checked_smallTarget :
    matrix.imported.smallTarget = SmallLengthTargetIntegratedW11.matrix := by
  rfl

theorem checked_arbitraryFinal :
    matrix.imported.arbitraryFinal = ArbitraryNFinalIntegratedW11.matrix := by
  rfl

theorem checked_arbitraryTargetFinal :
    matrix.imported.arbitraryTargetFinal =
      ArbitraryNTargetFinalW11.matrix := by
  rfl

theorem checked_pachTothFinalConsistency :
    matrix.imported.pachTothFinalConsistency =
      PachTothW11FinalConsistency.matrix := by
  rfl

/-! ## Public projections -/

theorem targetAt_lengthOne (E : ExactLengthFields) :
    FixedTarget (16 * 1) :=
  matrix.exactLengths.lengthOne E

theorem targetAt_lengthTwo (E : ExactLengthFields) :
    FixedTarget (16 * 2) :=
  matrix.exactLengths.lengthTwo E

theorem targetAt_lengthThree (E : ExactLengthFields) :
    FixedTarget (16 * 3) :=
  matrix.exactLengths.lengthThree E

theorem targetAt_lengthFour (E : ExactLengthFields) :
    FixedTarget (16 * 4) :=
  matrix.exactLengths.lengthFour E

theorem targetAt_lengthFive (E : ExactLengthFields) :
    FixedTarget (16 * 5) :=
  matrix.exactLengths.lengthFive E

theorem exactBlockTarget
    (E : ExactLengthFields) (k : Nat) (hkLt : k < blockThreshold)
    (hkPos : 0 < k) :
    FixedTarget (16 * k) :=
  matrix.exactLengths.exactBlock E k hkLt hkPos

theorem smallTarget (E : ExactLengthFields) :
    SmallTarget vertexThreshold :=
  matrix.exactLengths.smallTarget E

theorem targetAt_lengthOne_viaArbitraryTargetFinal
    (E : ExactLengthFields) :
    FixedTarget (16 * 1) :=
  matrix.exactLengths.lengthOneViaArbitraryTargetFinal E

theorem targetAt_lengthTwo_viaArbitraryTargetFinal
    (E : ExactLengthFields) :
    FixedTarget (16 * 2) :=
  matrix.exactLengths.lengthTwoViaArbitraryTargetFinal E

theorem targetAt_lengthThree_viaArbitraryTargetFinal
    (E : ExactLengthFields) :
    FixedTarget (16 * 3) :=
  matrix.exactLengths.lengthThreeViaArbitraryTargetFinal E

theorem targetAt_lengthFour_viaArbitraryTargetFinal
    (E : ExactLengthFields) :
    FixedTarget (16 * 4) :=
  matrix.exactLengths.lengthFourViaArbitraryTargetFinal E

theorem targetAt_lengthFive_viaArbitraryTargetFinal
    (E : ExactLengthFields) :
    FixedTarget (16 * 5) :=
  matrix.exactLengths.lengthFiveViaArbitraryTargetFinal E

def targetFacade_of_largeDataViaLargeTarget
    (P : EventualLargeDataFields) :
    ArbitraryNTargetFacade :=
  matrix.eventualLargeData.targetFacadeViaLargeTarget P

theorem arbitraryTarget_of_largeDataViaLargeTarget
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallFinalLargeTarget P

theorem arbitraryTarget_of_largeDataViaClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallFinalClosedChains P

theorem arbitraryTarget_of_largeDataViaGeneratedClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallFinalGeneratedClosedChains P

theorem arbitraryTarget_of_largeDataViaFiniteCertificates
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaSmallFinalFiniteCertificates P

theorem arbitraryTarget_of_largeDataViaArbitraryFinalLargeTarget
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaArbitraryFinalLargeTarget P

theorem arbitraryTarget_of_largeDataViaArbitraryFinalClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaArbitraryFinalClosedChains P

theorem arbitraryTarget_of_largeDataViaArbitraryFinalGeneratedClosedChains
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaArbitraryFinalGeneratedClosedChains P

theorem arbitraryTarget_of_largeDataViaArbitraryFinalFiniteCertificates
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaArbitraryFinalFiniteCertificates P

theorem arbitraryTarget_of_largeDataViaArbitraryTargetFinal
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaArbitraryTargetFinalLargeTarget P

theorem arbitraryTarget_of_largeDataViaPachTothFinalConsistency
    (P : EventualLargeDataFields) :
    ArbitraryTarget :=
  matrix.eventualLargeData.arbitraryViaPachTothFinalGeneratedClosedChains P

end

end SmallLengthArbitraryFinalW11
end PachToth
end ErdosProblems1066
