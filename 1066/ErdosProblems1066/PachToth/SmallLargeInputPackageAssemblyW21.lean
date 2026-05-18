import ErdosProblems1066.PachToth.SmallKClosedPlacementSourceW20
import ErdosProblems1066.PachToth.LargeKClosedPlacementSourceW20

set_option autoImplicit false

/-!
# W21 small/large closed-placement package assembly

This file splices the W20 small-k closed-placement source to the W20 large-k
source without pretending the large threshold gap has disappeared.  For a
general large threshold `K0`, the missing datum is exactly the finite small
complement below `16 * K0`.  The W20 small-k source closes that complement
only through the certified block range `K0 <= 6`; the large W20 input-package
route closes everything by itself only at thresholds `K0 <= 1`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLargeInputPackageAssemblyW21

noncomputable section

abbrev ExactTarget : Prop :=
  LargeThresholdSmallCasesW15.ExactTarget

abbrev EventualTarget : Prop :=
  LargeThresholdSmallCasesW15.EventualTarget

abbrev ArbitraryTarget : Prop :=
  LargeThresholdSmallCasesW15.ArbitraryTarget

abbrev SmallComplement (K0 : Nat) : Prop :=
  LargeThresholdSmallCasesW15.SmallComplement K0

abbrev SmallKExactClosedPlacementSource :=
  SmallKClosedPlacementSourceW20.SmallKExactClosedPlacementSource

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeKClosedPlacementSourceW20.LargeClosedPlacementFields K0

abbrev LargeKCrossBlockDistanceFields (K0 : Nat) :=
  LargeKClosedPlacementSourceW20.LargeKCrossBlockDistanceFields K0

abbrev LargeKNonConnectorSqDistanceFields (K0 : Nat) :=
  LargeKClosedPlacementSourceW20.LargeKNonConnectorSqDistanceFields K0

abbrev blockThresholdSix : Nat :=
  SmallComplementConcreteBlocksW17.blockThresholdSix

/-! ## The finite gap is exactly the missing small complement -/

theorem smallComplement_of_arbitraryTarget
    (K0 : Nat) (H : ArbitraryTarget) :
    SmallComplement K0 := by
  intro n _hn
  exact H n

theorem arbitraryTarget_of_largeClosedPlacementFields_iff_smallComplement
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    ArbitraryTarget <-> SmallComplement K0 := by
  constructor
  case mp =>
    intro H
    exact smallComplement_of_arbitraryTarget K0 H
  case mpr =>
    intro small
    exact
      LargeThresholdSmallCasesW15.arbitraryTarget_of_largeClosedPlacementFields_smallComplement
        L small

theorem exact_eventual_arbitrary_of_largeClosedPlacementFields_iff_smallComplement
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    (ExactTarget /\ EventualTarget /\ ArbitraryTarget) <-> SmallComplement K0 := by
  constructor
  case mp =>
    intro H
    exact smallComplement_of_arbitraryTarget K0 H.2.2
  case mpr =>
    intro small
    exact
      (LargeThresholdSmallCasesW15.LargeWithThresholdSmallCases.exact_eventual_arbitrary
        { large := L, small := small })

/-! ## The W20 small-k source closes large thresholds only up to six blocks -/

theorem smallComplement_of_smallKSource_le_six
    {K0 : Nat} (S : SmallKExactClosedPlacementSource)
    (hK0 : K0 <= blockThresholdSix) :
    SmallComplement K0 := by
  intro n hn
  exact
    S.targetUpperConstructionFiveSixteenSmallUpTo_six n
      (Nat.lt_of_lt_of_le hn (Nat.mul_le_mul_left 16 hK0))

structure SmallLargeThresholdPackage (K0 : Nat) where
  small : SmallKExactClosedPlacementSource
  large : LargeClosedPlacementFields K0
  threshold_le_six : K0 <= blockThresholdSix

namespace SmallLargeThresholdPackage

def smallComplement
    {K0 : Nat} (P : SmallLargeThresholdPackage K0) :
    SmallComplement K0 :=
  smallComplement_of_smallKSource_le_six P.small P.threshold_le_six

def toLargeWithThresholdSmallCases
    {K0 : Nat} (P : SmallLargeThresholdPackage K0) :
    LargeThresholdSmallCasesW15.LargeWithThresholdSmallCases K0 where
  large := P.large
  small := P.smallComplement

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : SmallLargeThresholdPackage K0) :
    ExactTarget :=
  P.toLargeWithThresholdSmallCases.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : SmallLargeThresholdPackage K0) :
    EventualTarget :=
  P.toLargeWithThresholdSmallCases.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : SmallLargeThresholdPackage K0) :
    ArbitraryTarget :=
  P.toLargeWithThresholdSmallCases.targetUpperConstructionFiveSixteenArbitrary

theorem exact_eventual_arbitrary
    {K0 : Nat} (P : SmallLargeThresholdPackage K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  P.toLargeWithThresholdSmallCases.exact_eventual_arbitrary

end SmallLargeThresholdPackage

/-! ## Constructors from the two W20 large-k source families -/

def smallLargePackageOfCrossBlockFields
    {K0 : Nat} (S : SmallKExactClosedPlacementSource)
    (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= blockThresholdSix) :
    SmallLargeThresholdPackage K0 where
  small := S
  large := F.largeClosedPlacementFields
  threshold_le_six := hK0

theorem exact_eventual_arbitrary_of_crossBlockFields_le_six
    {K0 : Nat} (S : SmallKExactClosedPlacementSource)
    (F : LargeKCrossBlockDistanceFields K0)
    (hK0 : K0 <= blockThresholdSix) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (smallLargePackageOfCrossBlockFields S F hK0).exact_eventual_arbitrary

def smallLargePackageOfNonConnectorFields
    {K0 : Nat} (S : SmallKExactClosedPlacementSource)
    (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= blockThresholdSix) :
    SmallLargeThresholdPackage K0 where
  small := S
  large := F.largeClosedPlacementFields
  threshold_le_six := hK0

theorem exact_eventual_arbitrary_of_nonConnectorFields_le_six
    {K0 : Nat} (S : SmallKExactClosedPlacementSource)
    (F : LargeKNonConnectorSqDistanceFields K0)
    (hK0 : K0 <= blockThresholdSix) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (smallLargePackageOfNonConnectorFields S F hK0).exact_eventual_arbitrary

/-! ## Threshold-at-most-one data remains the all-k large endpoint -/

theorem exact_eventual_arbitrary_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  LargeThresholdSmallCasesW15.exact_eventual_arbitrary_atMostOne L hK0

theorem exact_eventual_arbitrary_of_crossBlockSourceFields_atMostOne
    {K0 : Nat} (S : LargeKClosedPlacementSourceW20.CrossBlockSourceFields K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  exact_eventual_arbitrary_of_largeClosedPlacementFields_atMostOne
    S.toLargeClosedPlacementFields S.threshold_atMostOne

theorem targetUpperConstructionFiveSixteen_of_crossBlockSourceFields_atMostOne
    {K0 : Nat} (S : LargeKClosedPlacementSourceW20.CrossBlockSourceFields K0) :
    ExactTarget :=
  (exact_eventual_arbitrary_of_crossBlockSourceFields_atMostOne S).1

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockSourceFields_atMostOne
    {K0 : Nat} (S : LargeKClosedPlacementSourceW20.CrossBlockSourceFields K0) :
    ArbitraryTarget :=
  (exact_eventual_arbitrary_of_crossBlockSourceFields_atMostOne S).2.2

end

end SmallLargeInputPackageAssemblyW21
end PachToth
end ErdosProblems1066
