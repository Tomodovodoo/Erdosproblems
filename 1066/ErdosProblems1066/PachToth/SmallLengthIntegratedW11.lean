import ErdosProblems1066.PachToth.SmallLengthClosureW11
import ErdosProblems1066.PachToth.ArbitraryNTargetClosureW11

set_option autoImplicit false

/-!
# W11 small-length integrated threshold matrix

This module integrates the checked small-length closure with the W11
arbitrary-`n` facade matrix.  The finite side is always the explicit
`k = 1,2,3,4,5` exact-block package, while the large side remains visible as
one of the named eventual input packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthIntegratedW11

noncomputable section

universe u

abbrev SmallLengthExactBlockTargets :=
  SmallLengthClosureW11.SmallLengthExactBlockTargets

abbrev SmallLengthMissingNonConnectorInequalities :=
  SmallLengthClosureW11.SmallLengthMissingNonConnectorInequalities

abbrev SmallLengthValueMatrices :=
  SmallLengthClosureW11.SmallLengthValueMatrices

abbrev SmallLengthClosureObligations :=
  SmallLengthClosureW11.SmallLengthClosureObligations

abbrev EventualClosedChainAssumptionsBelowSix :=
  SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix

abbrev EventualGeneratedClosedChainAssumptionsBelowSix :=
  SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix

abbrev ArbitraryNTargetFacade :=
  ArbitraryNClosureW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNClosureW11.ThresholdTargetFacade

abbrev TargetClosureMatrix :=
  ArbitraryNTargetClosureW11.Matrix

def blockThreshold : Nat := 6

def vertexThreshold : Nat := 16 * blockThreshold

/-! ## Exact block packing -/

/-- The exact block targets not supplied by the length-four/five rows. -/
structure LengthOneTwoThreeExactBlockTargets where
  lengthOne : targetUpperConstructionFiveSixteenAt (16 * 1)
  lengthTwo : targetUpperConstructionFiveSixteenAt (16 * 2)
  lengthThree : targetUpperConstructionFiveSixteenAt (16 * 3)

namespace LengthOneTwoThreeExactBlockTargets

def withLengthFourFive
    (C : LengthOneTwoThreeExactBlockTargets)
    (D : LengthFourFiveCaseW11.LengthFourFiveExactBlockTargets) :
    SmallLengthExactBlockTargets where
  lengthOne := C.lengthOne
  lengthTwo := C.lengthTwo
  lengthThree := C.lengthThree
  lengthFour := D.lengthFour
  lengthFive := D.lengthFive

end LengthOneTwoThreeExactBlockTargets

def exactBlocksOfLengthFourFiveTargets
    (C : LengthOneTwoThreeExactBlockTargets)
    (D : LengthFourFiveCaseW11.LengthFourFiveExactBlockTargets) :
    SmallLengthExactBlockTargets :=
  C.withLengthFourFive D

def exactBlocksOfPeriodLowerTables
    {periodSearch : LengthFourFiveCaseW11.PeriodSearchData}
    (C : LengthOneTwoThreeExactBlockTargets)
    (D :
      LengthFourFiveCaseW11.LengthFourFivePeriodNonConnectorLowerTables
        periodSearch) :
    SmallLengthExactBlockTargets :=
  C.withLengthFourFive
    (LengthFourFiveCaseW11.LengthFourFivePeriodNonConnectorLowerTables.toExactBlockTargets
      D)

def exactBlocksOfCandidateLowerTables
    {period : LengthFourFiveCaseW11.PeriodCandidateFamily}
    (C : LengthOneTwoThreeExactBlockTargets)
    (D :
      LengthFourFiveCaseW11.LengthFourFiveCandidateNonConnectorLowerTables
        period) :
    SmallLengthExactBlockTargets :=
  C.withLengthFourFive
    (LengthFourFiveCaseW11.LengthFourFiveCandidateNonConnectorLowerTables.toExactBlockTargets
      D)

def exactBlocksOfPeriodMissingInequalities
    (periodSearch : LengthFourFiveCaseW11.PeriodSearchData)
    (C : LengthOneTwoThreeExactBlockTargets)
    (H :
      LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities
        periodSearch.toRoleHingedPeriodSearchFamily) :
    SmallLengthExactBlockTargets :=
  exactBlocksOfPeriodLowerTables C
    (LengthFourFiveCaseW11.lengthFourFivePeriodLowerTablesOfMissingInequalities
      periodSearch H)

def exactBlocksOfCandidateMissingInequalities
    (period : LengthFourFiveCaseW11.PeriodCandidateFamily)
    (C : LengthOneTwoThreeExactBlockTargets)
    (H :
      LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities
        period.toRoleHingedPeriodSearchFamily) :
    SmallLengthExactBlockTargets :=
  exactBlocksOfCandidateLowerTables C
    (LengthFourFiveCaseW11.lengthFourFiveCandidateLowerTablesOfMissingInequalities
      period H)

/-- A row exposing the exact finite block complement below block six. -/
structure ExactBlockRouteRow (alpha : Sort u) where
  exactBlocks : alpha -> SmallLengthExactBlockTargets
  exactBlock :
    alpha -> forall k : Nat, k < 6 -> 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k)
  smallTarget :
    alpha -> targetUpperConstructionFiveSixteenSmallUpTo (16 * 6)

def exactBlockTargetsRow :
    ExactBlockRouteRow SmallLengthExactBlockTargets where
  exactBlocks := fun C => C
  exactBlock := fun C => C.exactBlock
  smallTarget := fun C => C.smallUpToSix

/-! ## Threshold routes -/

/-- A generic large-target route with the finite side fixed to k=1..5. -/
structure EventualLargeTargetAssumptionsBelowSix where
  largeTarget :
    forall n : Nat, 16 * 6 <= n ->
      targetUpperConstructionFiveSixteenAt n
  exactBlocks : SmallLengthExactBlockTargets

namespace EventualLargeTargetAssumptionsBelowSix

def thresholdFacade
    (P : EventualLargeTargetAssumptionsBelowSix) :
    ThresholdTargetFacade :=
  P.exactBlocks.thresholdFacadeOfEventualLarge P.largeTarget

def targetFacade
    (P : EventualLargeTargetAssumptionsBelowSix) :
    ArbitraryNTargetFacade :=
  P.exactBlocks.targetFacadeOfEventualLarge P.largeTarget

theorem arbitraryTarget
    (P : EventualLargeTargetAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  P.exactBlocks.arbitraryTargetOfEventualLarge P.largeTarget

end EventualLargeTargetAssumptionsBelowSix

/-- Eventual finite certificates from block six onward, with k=1..5 exact
block targets supplied separately. -/
structure EventualFiniteCertificateAssumptionsBelowSix where
  largeCertificates :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations 6
  exactBlocks : SmallLengthExactBlockTargets

namespace EventualFiniteCertificateAssumptionsBelowSix

def thresholdFacade
    (P : EventualFiniteCertificateAssumptionsBelowSix) :
    ThresholdTargetFacade :=
  SmallLengthClosureW11.thresholdFacadeOfEventualFiniteCertificatesBelowSix
    P.largeCertificates P.exactBlocks

def targetFacade
    (P : EventualFiniteCertificateAssumptionsBelowSix) :
    ArbitraryNTargetFacade :=
  SmallLengthClosureW11.targetFacadeOfEventualFiniteCertificatesBelowSix
    P.largeCertificates P.exactBlocks

theorem arbitraryTarget
    (P : EventualFiniteCertificateAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  SmallLengthClosureW11.arbitraryTargetOfEventualFiniteCertificatesBelowSix
    P.largeCertificates P.exactBlocks

end EventualFiniteCertificateAssumptionsBelowSix

/-- A threshold row records both the split facade and the arbitrary facade. -/
structure ThresholdRouteRow (alpha : Sort u) where
  exactBlocks : alpha -> SmallLengthExactBlockTargets
  smallTarget :
    alpha -> targetUpperConstructionFiveSixteenSmallUpTo (16 * 6)
  largeTarget :
    forall _a : alpha, forall n : Nat, 16 * 6 <= n ->
      targetUpperConstructionFiveSixteenAt n
  thresholdFacade : alpha -> ThresholdTargetFacade
  targetFacade : alpha -> ArbitraryNTargetFacade
  arbitraryTarget : alpha -> targetUpperConstructionFiveSixteenArbitrary

def eventualLargeTargetRouteRow :
    ThresholdRouteRow EventualLargeTargetAssumptionsBelowSix where
  exactBlocks := fun P => P.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallUpToSix
  largeTarget := fun P => P.largeTarget
  thresholdFacade := EventualLargeTargetAssumptionsBelowSix.thresholdFacade
  targetFacade := EventualLargeTargetAssumptionsBelowSix.targetFacade
  arbitraryTarget := EventualLargeTargetAssumptionsBelowSix.arbitraryTarget

def eventualClosedChainRouteRow :
    ThresholdRouteRow EventualClosedChainAssumptionsBelowSix where
  exactBlocks := fun P => P.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallUpToSix
  largeTarget := fun P n hn =>
    (SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.thresholdFacade
      P).largeTarget n hn
  thresholdFacade :=
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.thresholdFacade
  targetFacade :=
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.checkedTargetFacade
  arbitraryTarget :=
    SmallLengthClosureW11.EventualClosedChainAssumptionsBelowSix.arbitraryTarget

def eventualGeneratedClosedChainRouteRow :
    ThresholdRouteRow EventualGeneratedClosedChainAssumptionsBelowSix where
  exactBlocks := fun P => P.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallUpToSix
  largeTarget := fun P n hn =>
    (SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.thresholdFacade
      P).largeTarget n hn
  thresholdFacade :=
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.thresholdFacade
  targetFacade :=
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.checkedTargetFacade
  arbitraryTarget :=
    SmallLengthClosureW11.EventualGeneratedClosedChainAssumptionsBelowSix.arbitraryTarget

def eventualFiniteCertificateRouteRow :
    ThresholdRouteRow EventualFiniteCertificateAssumptionsBelowSix where
  exactBlocks := fun P => P.exactBlocks
  smallTarget := fun P => P.exactBlocks.smallUpToSix
  largeTarget := fun P n hn => (P.thresholdFacade).largeTarget n hn
  thresholdFacade := EventualFiniteCertificateAssumptionsBelowSix.thresholdFacade
  targetFacade := EventualFiniteCertificateAssumptionsBelowSix.targetFacade
  arbitraryTarget := EventualFiniteCertificateAssumptionsBelowSix.arbitraryTarget

/-! ## Matrix -/

/-- Integrated small-length matrix over threshold-six target routes. -/
structure Matrix where
  targetClosure : TargetClosureMatrix
  exactBlocks : ExactBlockRouteRow SmallLengthExactBlockTargets
  eventualLargeTargets :
    ThresholdRouteRow EventualLargeTargetAssumptionsBelowSix
  eventualClosedChains :
    ThresholdRouteRow EventualClosedChainAssumptionsBelowSix
  eventualGeneratedClosedChains :
    ThresholdRouteRow EventualGeneratedClosedChainAssumptionsBelowSix
  eventualFiniteCertificates :
    ThresholdRouteRow EventualFiniteCertificateAssumptionsBelowSix

/-- The checked small-length threshold matrix assembled from W11 facades. -/
def matrix : Matrix where
  targetClosure := ArbitraryNTargetClosureW11.matrix
  exactBlocks := exactBlockTargetsRow
  eventualLargeTargets := eventualLargeTargetRouteRow
  eventualClosedChains := eventualClosedChainRouteRow
  eventualGeneratedClosedChains := eventualGeneratedClosedChainRouteRow
  eventualFiniteCertificates := eventualFiniteCertificateRouteRow

/-! ## Public projections -/

theorem targetUpperConstructionFiveSixteenSmallUpTo_sixteen_mul_six
    (C : SmallLengthExactBlockTargets) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * 6) :=
  matrix.exactBlocks.smallTarget C

def thresholdFacade_of_eventualLargeTargets
    (P : EventualLargeTargetAssumptionsBelowSix) :
    ThresholdTargetFacade :=
  matrix.eventualLargeTargets.thresholdFacade P

theorem targetFacade_of_eventualLargeTargets
    (P : EventualLargeTargetAssumptionsBelowSix) :
    ArbitraryNTargetFacade :=
  matrix.eventualLargeTargets.targetFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualLargeTargets
    (P : EventualLargeTargetAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualLargeTargets.arbitraryTarget P

def thresholdFacade_of_eventualClosedChains
    (P : EventualClosedChainAssumptionsBelowSix) :
    ThresholdTargetFacade :=
  matrix.eventualClosedChains.thresholdFacade P

theorem targetFacade_of_eventualClosedChains
    (P : EventualClosedChainAssumptionsBelowSix) :
    ArbitraryNTargetFacade :=
  matrix.eventualClosedChains.targetFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualClosedChains
    (P : EventualClosedChainAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualClosedChains.arbitraryTarget P

def thresholdFacade_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainAssumptionsBelowSix) :
    ThresholdTargetFacade :=
  matrix.eventualGeneratedClosedChains.thresholdFacade P

theorem targetFacade_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainAssumptionsBelowSix) :
    ArbitraryNTargetFacade :=
  matrix.eventualGeneratedClosedChains.targetFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualGeneratedClosedChains
    (P : EventualGeneratedClosedChainAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualGeneratedClosedChains.arbitraryTarget P

def thresholdFacade_of_eventualFiniteCertificates
    (P : EventualFiniteCertificateAssumptionsBelowSix) :
    ThresholdTargetFacade :=
  matrix.eventualFiniteCertificates.thresholdFacade P

theorem targetFacade_of_eventualFiniteCertificates
    (P : EventualFiniteCertificateAssumptionsBelowSix) :
    ArbitraryNTargetFacade :=
  matrix.eventualFiniteCertificates.targetFacade P

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualFiniteCertificates
    (P : EventualFiniteCertificateAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  matrix.eventualFiniteCertificates.arbitraryTarget P

end

end SmallLengthIntegratedW11
end PachToth
end ErdosProblems1066
