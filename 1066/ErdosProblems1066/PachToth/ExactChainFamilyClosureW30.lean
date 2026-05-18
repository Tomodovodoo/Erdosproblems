import ErdosProblems1066.PachToth.ExactChainFamilySourceW29
import ErdosProblems1066.PachToth.RemainderSplitClosureW29
import ErdosProblems1066.PachToth.LargeTailFieldsSourceW29

set_option autoImplicit false

/-!
# W30 exact-chain family closure

This leaf keeps the Pach--Toth route source-facing.  It identifies the W29
remainder split dependency with the W29 exact-chain family source package, and
records source constructors from closed placements and from the small-block
plus large-tail block split.

No final target wrapper is introduced here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactChainFamilyClosureW30

noncomputable section

abbrev ExactChainFamilySourcePackage : Type :=
  ExactChainFamilySourceW29.ExactChainFamilySourcePackage

abbrev ExactChainFamily : Type :=
  RemainderSplitClosureW29.ExactChainFamily

abbrev RemainingExactChainFamilyDependency : Prop :=
  RemainderSplitClosureW29.RemainingExactChainFamilyDependency

abbrev ClosedPlacementFamily : Type :=
  ExactChainFamilySourceW29.ClosedPlacementFamily

abbrev ClosedPlacementPackage : Type :=
  ExactChainFamilySourceW29.ClosedPlacementPackage

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  ExactChainFamilySourceW29.ExplicitClosedPlacementCertificateFamily

abbrev ExactBlocksOneThroughFive : Prop :=
  ExactChainFamilySourceW29.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  ExactChainFamilySourceW29.LargeExactBlockTargetsFromSix

abbrev SmallAndLargeExactBlockTargets : Prop :=
  ExactChainFamilySourceW29.SmallAndLargeExactBlockTargets

abbrev LargeTailExactSourcePackage : Type :=
  ExactChainFamilySourceW29.LargeTailExactSourcePackage

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFieldsFromSix

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFamilyFromSix

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeRawClosedPlacementFieldsFromSix

/-! ## The W29 source package is the W29 remainder dependency -/

def exactChainFamilyOfSourcePackage
    (P : ExactChainFamilySourcePackage) :
    ExactChainFamily :=
  P.toExactChainFamily

def sourcePackageOfExactChainFamily
    (H : ExactChainFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfExactChainFamily H

theorem remainingDependency_of_sourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainingExactChainFamilyDependency :=
  Nonempty.intro (exactChainFamilyOfSourcePackage P)

theorem remainingDependency_of_sourcePackage_nonempty
    (H : Nonempty ExactChainFamilySourcePackage) :
    RemainingExactChainFamilyDependency := by
  cases H with
  | intro P =>
      exact remainingDependency_of_sourcePackage P

theorem sourcePackage_nonempty_of_remainingDependency
    (H : RemainingExactChainFamilyDependency) :
    Nonempty ExactChainFamilySourcePackage := by
  cases H with
  | intro F =>
      exact Nonempty.intro (sourcePackageOfExactChainFamily F)

theorem remainingDependency_iff_sourcePackage_nonempty :
    RemainingExactChainFamilyDependency <->
      Nonempty ExactChainFamilySourcePackage := by
  constructor
  case mp =>
    exact sourcePackage_nonempty_of_remainingDependency
  case mpr =>
    exact remainingDependency_of_sourcePackage_nonempty

/-! ## Closed-placement source constructors -/

def sourcePackageOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfClosedPlacementFamily H

def sourcePackageOfClosedPlacementPackage
    (P : ClosedPlacementPackage) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfClosedPlacementPackage P

def sourcePackageOfExplicitClosedPlacementCertificateFamily
    (H : ExplicitClosedPlacementCertificateFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfExplicitClosedPlacementCertificateFamily
    H

theorem remainingDependency_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfClosedPlacementFamily H)

theorem remainingDependency_of_closedPlacementPackage
    (P : ClosedPlacementPackage) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfClosedPlacementPackage P)

theorem remainingDependency_of_explicitClosedPlacementCertificateFamily
    (H : ExplicitClosedPlacementCertificateFamily) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfExplicitClosedPlacementCertificateFamily H)

theorem remainingDependency_of_closedPlacementFamily_nonempty
    (H : Nonempty ClosedPlacementFamily) :
    RemainingExactChainFamilyDependency := by
  cases H with
  | intro F =>
      exact remainingDependency_of_closedPlacementFamily F

theorem remainingDependency_of_closedPlacementPackage_nonempty
    (H : Nonempty ClosedPlacementPackage) :
    RemainingExactChainFamilyDependency := by
  cases H with
  | intro P =>
      exact remainingDependency_of_closedPlacementPackage P

theorem remainingDependency_of_explicitClosedPlacementCertificateFamily_nonempty
    (H : Nonempty ExplicitClosedPlacementCertificateFamily) :
    RemainingExactChainFamilyDependency := by
  cases H with
  | intro F =>
      exact remainingDependency_of_explicitClosedPlacementCertificateFamily F

/-! ## Small-block plus large-tail source constructors -/

def sourcePackageOfSmallAndLargeExactBlockTargets
    (D : SmallAndLargeExactBlockTargets) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfSmallAndLargeExactBlockTargets D

def sourcePackageOfSmallBlocksAndLargeTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfSmallBlocksAndLargeTail small large

def sourcePackageOfLargeTailSourceAndSmallBlocks
    (P : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfLargeTailExactSourcePackage P small

def sourcePackageOfSmallBlocksAndLargeClosedPlacementFields
    (small : ExactBlocksOneThroughFive)
    (L : LargeClosedPlacementFieldsFromSix) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfLargeTailSourceAndSmallBlocks
    (LargeTailExactSourceW28.packageOfLargeClosedPlacementFieldsFromSix L)
    small

def sourcePackageOfSmallBlocksAndLargeClosedPlacementFamily
    (small : ExactBlocksOneThroughFive)
    (H : LargeClosedPlacementFamilyFromSix) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfSmallBlocksAndLargeClosedPlacementFields
    small
    (LargeTailFieldsSourceW29.largeClosedPlacementFieldsFromSixOfClosedPlacementFamilyFromSix
      H)

def sourcePackageOfSmallBlocksAndLargeRawFields
    (small : ExactBlocksOneThroughFive)
    (R : LargeRawClosedPlacementFieldsFromSix) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfSmallBlocksAndLargeClosedPlacementFields
    small
    (LargeTailFieldsSourceW29.largeClosedPlacementFieldsFromSixOfRawFields R)

theorem remainingDependency_of_smallAndLargeExactBlockTargets
    (D : SmallAndLargeExactBlockTargets) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfSmallAndLargeExactBlockTargets D)

theorem remainingDependency_of_smallBlocks_and_largeTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfSmallBlocksAndLargeTail small large)

theorem remainingDependency_of_largeTailSource_and_smallBlocks
    (P : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfLargeTailSourceAndSmallBlocks P small)

theorem remainingDependency_of_smallBlocks_and_largeClosedPlacementFields
    (small : ExactBlocksOneThroughFive)
    (L : LargeClosedPlacementFieldsFromSix) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfSmallBlocksAndLargeClosedPlacementFields small L)

theorem remainingDependency_of_smallBlocks_and_largeClosedPlacementFamily
    (small : ExactBlocksOneThroughFive)
    (H : LargeClosedPlacementFamilyFromSix) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfSmallBlocksAndLargeClosedPlacementFamily small H)

theorem remainingDependency_of_smallBlocks_and_largeRawFields
    (small : ExactBlocksOneThroughFive)
    (R : LargeRawClosedPlacementFieldsFromSix) :
    RemainingExactChainFamilyDependency :=
  remainingDependency_of_sourcePackage
    (sourcePackageOfSmallBlocksAndLargeRawFields small R)

theorem remainingDependency_of_largeTailSource_nonempty_and_smallBlocks
    (Hlarge : Nonempty LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    RemainingExactChainFamilyDependency := by
  cases Hlarge with
  | intro P =>
      exact remainingDependency_of_largeTailSource_and_smallBlocks P small

theorem remainingDependency_of_largeClosedPlacementFields_nonempty_and_smallBlocks
    (Hlarge : Nonempty LargeClosedPlacementFieldsFromSix)
    (small : ExactBlocksOneThroughFive) :
    RemainingExactChainFamilyDependency := by
  cases Hlarge with
  | intro L =>
      exact remainingDependency_of_smallBlocks_and_largeClosedPlacementFields
        small L

theorem remainingDependency_of_largeClosedPlacementFamily_nonempty_and_smallBlocks
    (Hlarge : Nonempty LargeClosedPlacementFamilyFromSix)
    (small : ExactBlocksOneThroughFive) :
    RemainingExactChainFamilyDependency := by
  cases Hlarge with
  | intro H =>
      exact remainingDependency_of_smallBlocks_and_largeClosedPlacementFamily
        small H

theorem remainingDependency_of_largeRawFields_nonempty_and_smallBlocks
    (Hlarge : Nonempty LargeRawClosedPlacementFieldsFromSix)
    (small : ExactBlocksOneThroughFive) :
    RemainingExactChainFamilyDependency := by
  cases Hlarge with
  | intro R =>
      exact remainingDependency_of_smallBlocks_and_largeRawFields small R

theorem remainingDependency_iff_smallBlocks_and_largeTail :
    RemainingExactChainFamilyDependency <->
      And ExactBlocksOneThroughFive LargeExactBlockTargetsFromSix := by
  exact
    Iff.trans remainingDependency_iff_sourcePackage_nonempty
      ExactChainFamilySourceW29.nonempty_package_iff_smallBlocks_and_largeTail

end

end ExactChainFamilyClosureW30
end PachToth

namespace Verified

abbrev PachTothW30ExactChainFamilySourcePackage : Type :=
  PachToth.ExactChainFamilyClosureW30.ExactChainFamilySourcePackage

abbrev PachTothW30RemainingExactChainFamilyDependency : Prop :=
  PachToth.ExactChainFamilyClosureW30.RemainingExactChainFamilyDependency

abbrev PachTothW30ClosedPlacementFamily : Type :=
  PachToth.ExactChainFamilyClosureW30.ClosedPlacementFamily

abbrev PachTothW30ExactBlocksOneThroughFive : Prop :=
  PachToth.ExactChainFamilyClosureW30.ExactBlocksOneThroughFive

abbrev PachTothW30LargeExactBlockTargetsFromSix : Prop :=
  PachToth.ExactChainFamilyClosureW30.LargeExactBlockTargetsFromSix

theorem pachtoth_w30_remainingDependency_iff_sourcePackage_nonempty :
    PachTothW30RemainingExactChainFamilyDependency <->
      Nonempty PachTothW30ExactChainFamilySourcePackage :=
  PachToth.ExactChainFamilyClosureW30.remainingDependency_iff_sourcePackage_nonempty

theorem pachtoth_w30_remainingDependency_of_closedPlacementFamily
    (H : PachTothW30ClosedPlacementFamily) :
    PachTothW30RemainingExactChainFamilyDependency :=
  PachToth.ExactChainFamilyClosureW30.remainingDependency_of_closedPlacementFamily
    H

theorem pachtoth_w30_remainingDependency_of_smallBlocks_and_largeTail
    (small : PachTothW30ExactBlocksOneThroughFive)
    (large : PachTothW30LargeExactBlockTargetsFromSix) :
    PachTothW30RemainingExactChainFamilyDependency :=
  PachToth.ExactChainFamilyClosureW30.remainingDependency_of_smallBlocks_and_largeTail
    small large

theorem pachtoth_w30_remainingDependency_iff_smallBlocks_and_largeTail :
    PachTothW30RemainingExactChainFamilyDependency <->
      And
        PachTothW30ExactBlocksOneThroughFive
        PachTothW30LargeExactBlockTargetsFromSix :=
  PachToth.ExactChainFamilyClosureW30.remainingDependency_iff_smallBlocks_and_largeTail

end Verified
end ErdosProblems1066
