import ErdosProblems1066.PachToth.LengthFourFiveCaseW11
import ErdosProblems1066.PachToth.LengthTwoThreeCaseW10
import ErdosProblems1066.PachToth.SmallCaseCertificates
import ErdosProblems1066.PachToth.ArbitraryNClosureW11
import ErdosProblems1066.PachToth.EventualRoleHingeClosure

set_option autoImplicit false

/-!
# W11 small-length threshold closure

This module is a thin checked adapter over the W10/W11 small-length files.
It gathers the k=2,3,4,5 non-connector ledgers for bookkeeping, keeps the
k=1..5 exact block targets as explicit fields, and uses those fields to close
the finite complement below the block threshold six.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthClosureW11

noncomputable section

open SmallCaseCertificates

abbrev RoleHingedPeriodSearchFamily :=
  LengthTwoThreeCaseW10.RoleHingedPeriodSearchFamily

abbrev LengthTwoThreeMissingNonConnectorInequalities :=
  LengthTwoThreeCaseW10.LengthTwoThreeMissingNonConnectorInequalities

abbrev LengthFourFiveMissingNonConnectorInequalities :=
  LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities

abbrev LengthTwoThreeValueMatrices :=
  LengthTwoThreeCaseW10.LengthTwoThreeValueMatrices

abbrev LengthFourFiveValueMatrices :=
  LengthFourFiveCaseW11.LengthFourFiveValueMatrices

/-- The small non-connector inequality ledger currently available from the
length files.  The k=1 block has no upper-triangle pair in this ledger; its
exact block target is kept as a separate field below. -/
structure SmallLengthMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwoThree : LengthTwoThreeMissingNonConnectorInequalities F
  lengthFourFive : LengthFourFiveMissingNonConnectorInequalities F

/-- Value matrices produced by the length-two/three and length-four/five
small ledgers. -/
structure SmallLengthValueMatrices
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwoThree : LengthTwoThreeValueMatrices F
  lengthFourFive : LengthFourFiveValueMatrices F

def smallLengthMatricesOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : SmallLengthMissingNonConnectorInequalities F) :
    SmallLengthValueMatrices F where
  lengthTwoThree :=
    LengthTwoThreeCaseW10.lengthTwoThreeMatricesOfMissingInequalities
      F H.lengthTwoThree
  lengthFourFive :=
    LengthFourFiveCaseW11.lengthFourFiveMatricesOfMissingInequalities
      F H.lengthFourFive

/-- Explicit exact block targets for the positive block counts below six. -/
structure SmallLengthExactBlockTargets where
  lengthOne : targetUpperConstructionFiveSixteenAt (16 * 1)
  lengthTwo : targetUpperConstructionFiveSixteenAt (16 * 2)
  lengthThree : targetUpperConstructionFiveSixteenAt (16 * 3)
  lengthFour : targetUpperConstructionFiveSixteenAt (16 * 4)
  lengthFive : targetUpperConstructionFiveSixteenAt (16 * 5)

namespace SmallLengthExactBlockTargets

def toLengthFourFiveExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    LengthFourFiveCaseW11.LengthFourFiveExactBlockTargets where
  lengthFour := C.lengthFour
  lengthFive := C.lengthFive

def toExactBlockTargetsBelowSix
    (C : SmallLengthExactBlockTargets) :
    LengthFourFiveCaseW11.ExactBlockTargetsBelowSix where
  lengthOne := C.lengthOne
  lengthTwo := C.lengthTwo
  lengthThree := C.lengthThree
  lengthFourFive := C.toLengthFourFiveExactBlockTargets

def exactBlock
    (C : SmallLengthExactBlockTargets) :
    forall k : Nat, k < 6 -> 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k) :=
  LengthFourFiveCaseW11.ExactBlockTargetsBelowSix.exactBlock
    C.toExactBlockTargetsBelowSix

theorem smallUpToSix
    (C : SmallLengthExactBlockTargets) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * 6) := by
  exact
    targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
      6 C.exactBlock

def thresholdFacadeOfEventualLarge
    (C : SmallLengthExactBlockTargets)
    (Hlarge :
      forall n : Nat, 16 * 6 <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    ArbitraryNClosureW11.ThresholdTargetFacade where
  vertexThreshold := 16 * 6
  largeTarget := Hlarge
  smallTarget := C.smallUpToSix
  arbitraryTarget :=
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * 6) Hlarge C.smallUpToSix

def targetFacadeOfEventualLarge
    (C : SmallLengthExactBlockTargets)
    (Hlarge :
      forall n : Nat, 16 * 6 <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    ArbitraryNClosureW11.ArbitraryNTargetFacade :=
  (C.thresholdFacadeOfEventualLarge Hlarge).toArbitraryNTargetFacade

theorem arbitraryTargetOfEventualLarge
    (C : SmallLengthExactBlockTargets)
    (Hlarge :
      forall n : Nat, 16 * 6 <= n ->
        targetUpperConstructionFiveSixteenAt n) :
    targetUpperConstructionFiveSixteenArbitrary :=
  (C.thresholdFacadeOfEventualLarge Hlarge).arbitraryTarget

end SmallLengthExactBlockTargets

/-- Combined bookkeeping for a small-length finite search layer: it records the
non-connector ledger and still leaves the exact block targets explicit. -/
structure SmallLengthClosureObligations
    (F : RoleHingedPeriodSearchFamily) where
  missing : SmallLengthMissingNonConnectorInequalities F
  exactBlocks : SmallLengthExactBlockTargets

namespace SmallLengthClosureObligations

def valueMatrices
    {F : RoleHingedPeriodSearchFamily}
    (O : SmallLengthClosureObligations F) :
    SmallLengthValueMatrices F :=
  smallLengthMatricesOfMissingInequalities F O.missing

theorem smallUpToSix
    {F : RoleHingedPeriodSearchFamily}
    (O : SmallLengthClosureObligations F) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * 6) :=
  O.exactBlocks.smallUpToSix

end SmallLengthClosureObligations

/-- Eventual exact closed chains from block six onward, paired with explicit
exact block targets for the five smaller positive block counts. -/
structure EventualClosedChainAssumptionsBelowSix where
  largeChain :
    forall k : Nat, 6 <= k -> 0 < k ->
      SplitSoundness.ExactChainUpper k
  exactBlocks : SmallLengthExactBlockTargets

namespace EventualClosedChainAssumptionsBelowSix

def toEventualClosedChainPackage
    (P : EventualClosedChainAssumptionsBelowSix) :
    ArbitraryNClosureW11.EventualClosedChainPackage where
  threshold := 6
  largeChain := P.largeChain
  smallCases := P.exactBlocks.smallUpToSix

def thresholdFacade
    (P : EventualClosedChainAssumptionsBelowSix) :
    ArbitraryNClosureW11.ThresholdTargetFacade :=
  P.toEventualClosedChainPackage.thresholdFacade
    ArbitraryNClosureW11.checkedFiniteRemainders

def checkedTargetFacade
    (P : EventualClosedChainAssumptionsBelowSix) :
    ArbitraryNClosureW11.ArbitraryNTargetFacade :=
  P.toEventualClosedChainPackage.checkedTargetFacade

theorem arbitraryTarget
    (P : EventualClosedChainAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  P.toEventualClosedChainPackage.arbitraryTarget
    ArbitraryNClosureW11.checkedFiniteRemainders

end EventualClosedChainAssumptionsBelowSix

/-- Eventual generated closed chains from block six onward, with the same
explicit exact block targets below six. -/
structure EventualGeneratedClosedChainAssumptionsBelowSix where
  largeData :
    forall k : Nat, 6 <= k -> forall hk : 0 < k,
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  exactBlocks : SmallLengthExactBlockTargets

namespace EventualGeneratedClosedChainAssumptionsBelowSix

def toEventualGeneratedClosedChainPackage
    (P : EventualGeneratedClosedChainAssumptionsBelowSix) :
    ArbitraryNClosureW11.EventualGeneratedClosedChainPackage where
  threshold := 6
  largeData := P.largeData
  smallCases := P.exactBlocks.smallUpToSix

def thresholdFacade
    (P : EventualGeneratedClosedChainAssumptionsBelowSix) :
    ArbitraryNClosureW11.ThresholdTargetFacade :=
  P.toEventualGeneratedClosedChainPackage.thresholdFacade
    ArbitraryNClosureW11.checkedFiniteRemainders

def checkedTargetFacade
    (P : EventualGeneratedClosedChainAssumptionsBelowSix) :
    ArbitraryNClosureW11.ArbitraryNTargetFacade :=
  P.toEventualGeneratedClosedChainPackage.checkedTargetFacade

theorem arbitraryTarget
    (P : EventualGeneratedClosedChainAssumptionsBelowSix) :
    targetUpperConstructionFiveSixteenArbitrary :=
  P.toEventualGeneratedClosedChainPackage.arbitraryTarget
    ArbitraryNClosureW11.checkedFiniteRemainders

end EventualGeneratedClosedChainAssumptionsBelowSix

def thresholdFacadeOfEventualFiniteCertificatesBelowSix
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations 6)
    (C : SmallLengthExactBlockTargets) :
    ArbitraryNClosureW11.ThresholdTargetFacade where
  vertexThreshold := 16 * 6
  largeTarget := fun _n hn => O.targetUpperConstructionFiveSixteenAt_large hn
  smallTarget := C.smallUpToSix
  arbitraryTarget :=
    LengthFourFiveCaseW11.targetUpperConstructionFiveSixteenArbitrary_of_eventualBelowSix
      O C.toExactBlockTargetsBelowSix

def targetFacadeOfEventualFiniteCertificatesBelowSix
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations 6)
    (C : SmallLengthExactBlockTargets) :
    ArbitraryNClosureW11.ArbitraryNTargetFacade :=
  (thresholdFacadeOfEventualFiniteCertificatesBelowSix O C)
    |>.toArbitraryNTargetFacade

theorem arbitraryTargetOfEventualFiniteCertificatesBelowSix
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations 6)
    (C : SmallLengthExactBlockTargets) :
    targetUpperConstructionFiveSixteenArbitrary :=
  (thresholdFacadeOfEventualFiniteCertificatesBelowSix O C).arbitraryTarget

theorem smallLength_remainder_arithmetic_sample :
    Arithmetic.ceilDiv (5 * (16 * 6 + 15)) 16 = 35 := by
  norm_num [Arithmetic.ceilDiv]

end

end SmallLengthClosureW11
end PachToth
end ErdosProblems1066
