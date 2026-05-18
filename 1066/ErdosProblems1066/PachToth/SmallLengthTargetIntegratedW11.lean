import ErdosProblems1066.PachToth.SmallLengthIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 small-length target integration facade

This module is a target-facing wrapper around the checked W11 small-length
and arbitrary-`n` closure layers.  It keeps the exact target inputs for
`k = 1,2,3,4,5` as displayed fields, then routes those fields through the
threshold-six facades already checked in `SmallLengthIntegratedW11`.

Every public all-`n` projection below remains conditional on an explicit
large-target, eventual closed-chain, generated closed-chain, or finite
certificate package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthTargetIntegratedW11

noncomputable section

universe u

abbrev SmallLengthExactBlockTargets :=
  SmallLengthClosureW11.SmallLengthExactBlockTargets

abbrev ThresholdTargetFacade :=
  ArbitraryNClosureW11.ThresholdTargetFacade

abbrev ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.ArbitraryNTargetFacade

abbrev IntegratedMatrix :=
  SmallLengthIntegratedW11.Matrix

abbrev PachTothIntegratedMatrix :=
  PachTothW11IntegratedMatrix.Matrix

def blockThreshold : Nat := SmallLengthIntegratedW11.blockThreshold

def vertexThreshold : Nat := SmallLengthIntegratedW11.vertexThreshold

/-! ## Explicit target fields -/

/-- Explicit target data for the five positive block lengths below the
threshold block six. -/
structure ExactBlockTargetFields where
  lengthOne : targetUpperConstructionFiveSixteenAt (16 * 1)
  lengthTwo : targetUpperConstructionFiveSixteenAt (16 * 2)
  lengthThree : targetUpperConstructionFiveSixteenAt (16 * 3)
  lengthFour : targetUpperConstructionFiveSixteenAt (16 * 4)
  lengthFive : targetUpperConstructionFiveSixteenAt (16 * 5)

namespace ExactBlockTargetFields

def toSmallLengthExactBlockTargets
    (C : ExactBlockTargetFields) :
    SmallLengthExactBlockTargets where
  lengthOne := C.lengthOne
  lengthTwo := C.lengthTwo
  lengthThree := C.lengthThree
  lengthFour := C.lengthFour
  lengthFive := C.lengthFive

def ofSmallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlockTargetFields where
  lengthOne := C.lengthOne
  lengthTwo := C.lengthTwo
  lengthThree := C.lengthThree
  lengthFour := C.lengthFour
  lengthFive := C.lengthFive

theorem exactBlock
    (C : ExactBlockTargetFields) :
    forall k : Nat, k < 6 -> 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k) :=
  C.toSmallLengthExactBlockTargets.exactBlock

theorem smallTarget
    (C : ExactBlockTargetFields) :
    targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold :=
  C.toSmallLengthExactBlockTargets.smallUpToSix

def thresholdFacadeOfEventualLarge
    (C : ExactBlockTargetFields)
    (Hlarge :
      forall n : Nat, vertexThreshold <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    ThresholdTargetFacade :=
  C.toSmallLengthExactBlockTargets.thresholdFacadeOfEventualLarge Hlarge

def targetFacadeOfEventualLarge
    (C : ExactBlockTargetFields)
    (Hlarge :
      forall n : Nat, vertexThreshold <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    ArbitraryNTargetFacade :=
  C.toSmallLengthExactBlockTargets.targetFacadeOfEventualLarge Hlarge

theorem arbitraryTargetOfEventualLarge
    (C : ExactBlockTargetFields)
    (Hlarge :
      forall n : Nat, vertexThreshold <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    targetUpperConstructionFiveSixteenArbitrary :=
  C.toSmallLengthExactBlockTargets.arbitraryTargetOfEventualLarge Hlarge

end ExactBlockTargetFields

/-! ## Target-facing threshold packages -/

/-- Exact small blocks plus an explicit target route from the threshold onward.
-/
structure EventualLargeTargetFields extends ExactBlockTargetFields where
  largeTarget :
    forall n : Nat, vertexThreshold <= n ->
      targetUpperConstructionFiveSixteenAt n

namespace EventualLargeTargetFields

def exactBlocks
    (P : EventualLargeTargetFields) :
    ExactBlockTargetFields :=
  P.toExactBlockTargetFields

def toSmallLengthIntegratedAssumptions
    (P : EventualLargeTargetFields) :
    SmallLengthIntegratedW11.EventualLargeTargetAssumptionsBelowSix where
  largeTarget := P.largeTarget
  exactBlocks := P.exactBlocks.toSmallLengthExactBlockTargets

def thresholdFacade
    (P : EventualLargeTargetFields) :
    ThresholdTargetFacade :=
  SmallLengthIntegratedW11.EventualLargeTargetAssumptionsBelowSix.thresholdFacade
    P.toSmallLengthIntegratedAssumptions

def targetFacade
    (P : EventualLargeTargetFields) :
    ArbitraryNTargetFacade :=
  SmallLengthIntegratedW11.EventualLargeTargetAssumptionsBelowSix.targetFacade
    P.toSmallLengthIntegratedAssumptions

theorem fixedTarget
    (P : EventualLargeTargetFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  P.targetFacade.fixedTarget n

theorem arbitraryTarget
    (P : EventualLargeTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthIntegratedW11.EventualLargeTargetAssumptionsBelowSix.arbitraryTarget
    P.toSmallLengthIntegratedAssumptions

end EventualLargeTargetFields

/-- Exact small blocks plus eventual exact closed chains from block six onward.
-/
structure EventualClosedChainTargetFields extends ExactBlockTargetFields where
  largeChain :
    forall k : Nat, blockThreshold <= k -> 0 < k ->
      SplitSoundness.ExactChainUpper k

namespace EventualClosedChainTargetFields

def exactBlocks
    (P : EventualClosedChainTargetFields) :
    ExactBlockTargetFields :=
  P.toExactBlockTargetFields

def toSmallLengthAssumptions
    (P : EventualClosedChainTargetFields) :
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix where
  largeChain := P.largeChain
  exactBlocks := P.exactBlocks.toSmallLengthExactBlockTargets

def thresholdFacade
    (P : EventualClosedChainTargetFields) :
    ThresholdTargetFacade :=
  SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.thresholdFacade
    P.toSmallLengthAssumptions

def targetFacade
    (P : EventualClosedChainTargetFields) :
    ArbitraryNTargetFacade :=
  SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.checkedTargetFacade
    P.toSmallLengthAssumptions

theorem fixedTarget
    (P : EventualClosedChainTargetFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  P.targetFacade.fixedTarget n

theorem arbitraryTarget
    (P : EventualClosedChainTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.arbitraryTarget
    P.toSmallLengthAssumptions

end EventualClosedChainTargetFields

/-- Exact small blocks plus eventual generated closed-chain data from block
six onward. -/
structure EventualGeneratedClosedChainTargetFields
    extends ExactBlockTargetFields where
  largeData :
    forall k : Nat, blockThreshold <= k -> forall hk : 0 < k,
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk

namespace EventualGeneratedClosedChainTargetFields

def exactBlocks
    (P : EventualGeneratedClosedChainTargetFields) :
    ExactBlockTargetFields :=
  P.toExactBlockTargetFields

def toSmallLengthAssumptions
    (P : EventualGeneratedClosedChainTargetFields) :
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix where
  largeData := P.largeData
  exactBlocks := P.exactBlocks.toSmallLengthExactBlockTargets

def thresholdFacade
    (P : EventualGeneratedClosedChainTargetFields) :
    ThresholdTargetFacade :=
  SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.thresholdFacade
    P.toSmallLengthAssumptions

def targetFacade
    (P : EventualGeneratedClosedChainTargetFields) :
    ArbitraryNTargetFacade :=
  SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.checkedTargetFacade
    P.toSmallLengthAssumptions

theorem fixedTarget
    (P : EventualGeneratedClosedChainTargetFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  P.targetFacade.fixedTarget n

theorem arbitraryTarget
    (P : EventualGeneratedClosedChainTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.arbitraryTarget
    P.toSmallLengthAssumptions

end EventualGeneratedClosedChainTargetFields

/-- Exact small blocks plus the finite-certificate route for all blocks from
six onward. -/
structure EventualFiniteCertificateTargetFields
    extends ExactBlockTargetFields where
  largeCertificates :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations blockThreshold

namespace EventualFiniteCertificateTargetFields

def exactBlocks
    (P : EventualFiniteCertificateTargetFields) :
    ExactBlockTargetFields :=
  P.toExactBlockTargetFields

def toSmallLengthIntegratedAssumptions
    (P : EventualFiniteCertificateTargetFields) :
    SmallLengthIntegratedW11.EventualFiniteCertificateAssumptionsBelowSix where
  largeCertificates := P.largeCertificates
  exactBlocks := P.exactBlocks.toSmallLengthExactBlockTargets

def thresholdFacade
    (P : EventualFiniteCertificateTargetFields) :
    ThresholdTargetFacade :=
  SmallLengthIntegratedW11.EventualFiniteCertificateAssumptionsBelowSix.thresholdFacade
    P.toSmallLengthIntegratedAssumptions

def targetFacade
    (P : EventualFiniteCertificateTargetFields) :
    ArbitraryNTargetFacade :=
  SmallLengthIntegratedW11.EventualFiniteCertificateAssumptionsBelowSix.targetFacade
    P.toSmallLengthIntegratedAssumptions

theorem fixedTarget
    (P : EventualFiniteCertificateTargetFields) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  P.targetFacade.fixedTarget n

theorem arbitraryTarget
    (P : EventualFiniteCertificateTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthIntegratedW11.EventualFiniteCertificateAssumptionsBelowSix.arbitraryTarget
    P.toSmallLengthIntegratedAssumptions

end EventualFiniteCertificateTargetFields

/-! ## Uniform target rows -/

/-- Row shape exposing every exact small block separately. -/
structure ExactBlockTargetRouteRow (alpha : Sort u) where
  exactBlocks : alpha -> ExactBlockTargetFields
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

def exactBlockTargetRouteRow :
    ExactBlockTargetRouteRow ExactBlockTargetFields where
  exactBlocks := fun C => C
  lengthOne := fun C => C.lengthOne
  lengthTwo := fun C => C.lengthTwo
  lengthThree := fun C => C.lengthThree
  lengthFour := fun C => C.lengthFour
  lengthFive := fun C => C.lengthFive
  exactBlock := fun C => C.exactBlock
  smallTarget := fun C => C.smallTarget

/-- Target-facing threshold route row. -/
structure ThresholdTargetRouteRow (alpha : Sort u) where
  exactBlocks : alpha -> ExactBlockTargetFields
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
    ThresholdTargetRouteRow EventualLargeTargetFields where
  exactBlocks := EventualLargeTargetFields.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallTarget
  largeTarget := fun P => P.largeTarget
  thresholdFacade := EventualLargeTargetFields.thresholdFacade
  targetFacade := EventualLargeTargetFields.targetFacade
  fixedTarget := EventualLargeTargetFields.fixedTarget
  arbitraryTarget := EventualLargeTargetFields.arbitraryTarget

def eventualClosedChainRouteRow :
    ThresholdTargetRouteRow EventualClosedChainTargetFields where
  exactBlocks := EventualClosedChainTargetFields.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallTarget
  largeTarget := fun P n hn => (P.thresholdFacade).largeTarget n hn
  thresholdFacade := EventualClosedChainTargetFields.thresholdFacade
  targetFacade := EventualClosedChainTargetFields.targetFacade
  fixedTarget := EventualClosedChainTargetFields.fixedTarget
  arbitraryTarget := EventualClosedChainTargetFields.arbitraryTarget

def eventualGeneratedClosedChainRouteRow :
    ThresholdTargetRouteRow EventualGeneratedClosedChainTargetFields where
  exactBlocks := EventualGeneratedClosedChainTargetFields.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallTarget
  largeTarget := fun P n hn => (P.thresholdFacade).largeTarget n hn
  thresholdFacade := EventualGeneratedClosedChainTargetFields.thresholdFacade
  targetFacade := EventualGeneratedClosedChainTargetFields.targetFacade
  fixedTarget := EventualGeneratedClosedChainTargetFields.fixedTarget
  arbitraryTarget := EventualGeneratedClosedChainTargetFields.arbitraryTarget

def eventualFiniteCertificateRouteRow :
    ThresholdTargetRouteRow EventualFiniteCertificateTargetFields where
  exactBlocks := EventualFiniteCertificateTargetFields.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallTarget
  largeTarget := fun P n hn => (P.thresholdFacade).largeTarget n hn
  thresholdFacade := EventualFiniteCertificateTargetFields.thresholdFacade
  targetFacade := EventualFiniteCertificateTargetFields.targetFacade
  fixedTarget := EventualFiniteCertificateTargetFields.fixedTarget
  arbitraryTarget := EventualFiniteCertificateTargetFields.arbitraryTarget

/-! ## Matrix -/

/-- Target-facing W11 small-length threshold ledger.

The matrix records checked route functions only.  It does not construct the
exact small-block fields or any eventual large-chain data. -/
structure Matrix where
  smallLengthIntegrated : IntegratedMatrix
  pachTothIntegrated : PachTothIntegratedMatrix
  targetClosure : ArbitraryNTargetClosureW11.Matrix
  exactBlocks : ExactBlockTargetRouteRow ExactBlockTargetFields
  eventualLargeTargets : ThresholdTargetRouteRow EventualLargeTargetFields
  eventualClosedChains :
    ThresholdTargetRouteRow EventualClosedChainTargetFields
  eventualGeneratedClosedChains :
    ThresholdTargetRouteRow EventualGeneratedClosedChainTargetFields
  eventualFiniteCertificates :
    ThresholdTargetRouteRow EventualFiniteCertificateTargetFields

/-- The checked target-facing W11 small-length threshold ledger. -/
def matrix : Matrix where
  smallLengthIntegrated := SmallLengthIntegratedW11.matrix
  pachTothIntegrated := PachTothW11IntegratedMatrix.matrix
  targetClosure := ArbitraryNTargetClosureW11.matrix
  exactBlocks := exactBlockTargetRouteRow
  eventualLargeTargets := eventualLargeTargetRouteRow
  eventualClosedChains := eventualClosedChainRouteRow
  eventualGeneratedClosedChains := eventualGeneratedClosedChainRouteRow
  eventualFiniteCertificates := eventualFiniteCertificateRouteRow

/-! ## Public projections -/

theorem targetUpperConstructionFiveSixteenAt_lengthOne
    (C : ExactBlockTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 1) :=
  matrix.exactBlocks.lengthOne C

theorem targetUpperConstructionFiveSixteenAt_lengthTwo
    (C : ExactBlockTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 2) :=
  matrix.exactBlocks.lengthTwo C

theorem targetUpperConstructionFiveSixteenAt_lengthThree
    (C : ExactBlockTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 3) :=
  matrix.exactBlocks.lengthThree C

theorem targetUpperConstructionFiveSixteenAt_lengthFour
    (C : ExactBlockTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 4) :=
  matrix.exactBlocks.lengthFour C

theorem targetUpperConstructionFiveSixteenAt_lengthFive
    (C : ExactBlockTargetFields) :
    targetUpperConstructionFiveSixteenAt (16 * 5) :=
  matrix.exactBlocks.lengthFive C

theorem targetUpperConstructionFiveSixteenSmallUpTo_threshold
    (C : ExactBlockTargetFields) :
    targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold :=
  matrix.exactBlocks.smallTarget C

def thresholdFacade_of_eventualLargeTargetFields
    (P : EventualLargeTargetFields) :
    ThresholdTargetFacade :=
  matrix.eventualLargeTargets.thresholdFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualLargeTargetFields
    (P : EventualLargeTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualLargeTargets.arbitraryTarget P

def thresholdFacade_of_eventualClosedChainTargetFields
    (P : EventualClosedChainTargetFields) :
    ThresholdTargetFacade :=
  matrix.eventualClosedChains.thresholdFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualClosedChainTargetFields
    (P : EventualClosedChainTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualClosedChains.arbitraryTarget P

def thresholdFacade_of_eventualGeneratedClosedChainTargetFields
    (P : EventualGeneratedClosedChainTargetFields) :
    ThresholdTargetFacade :=
  matrix.eventualGeneratedClosedChains.thresholdFacade P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualGeneratedClosedChainTargetFields
    (P : EventualGeneratedClosedChainTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualGeneratedClosedChains.arbitraryTarget P

def thresholdFacade_of_eventualFiniteCertificateTargetFields
    (P : EventualFiniteCertificateTargetFields) :
    ThresholdTargetFacade :=
  matrix.eventualFiniteCertificates.thresholdFacade P

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_eventualFiniteCertificateTargetFields
    (P : EventualFiniteCertificateTargetFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualFiniteCertificates.arbitraryTarget P

end

end SmallLengthTargetIntegratedW11
end PachToth
end ErdosProblems1066
