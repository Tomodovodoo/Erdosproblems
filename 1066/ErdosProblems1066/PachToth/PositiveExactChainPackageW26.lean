import ErdosProblems1066.PachToth.NonRoleSplitSourceInhabitationW25
import ErdosProblems1066.PachToth.ClosedPlacementWitnessAssemblyW25
import ErdosProblems1066.PachToth.AppendedRemainderSeparationInhabitationW25

set_option autoImplicit false

/-!
# W26 positive exact-chain package

This file characterizes
`NonRoleSplitSourceInhabitationW25.PositiveExactChainPackage` without adding
any inhabitance assumptions.  The package is exactly the exact `16 * k`
target, exactly the W25 non-role split source, and exactly the combination of
small exact blocks one through five with the large exact-block tail from six
onward.  The checked finite remainders and translated split constructors are
recorded as downstream consequences, not as missing hypotheses.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveExactChainPackageW26

open Arithmetic

noncomputable section

abbrev PositiveExactChainPackage : Type :=
  NonRoleSplitSourceInhabitationW25.PositiveExactChainPackage

abbrev NonRoleSplitSource : Type :=
  NonRoleSplitSourceInhabitationW25.NonRoleSplitSource

abbrev ExactChainUpper (k : Nat) : Type :=
  SplitSoundness.ExactChainUpper k

abbrev RemainderUpper (r : Nat) : Type :=
  SplitSoundness.RemainderUpper r

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactVertexTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ExactBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

abbrev ExactBlocksOneThroughFive : Prop :=
  SmallLengthExactTargetsConcreteW24.ExactBlocksOneThroughFive

abbrev SmallLengthExactBlockTargets : Prop :=
  SmallLengthExactTargetsConcreteW24.SmallLengthExactBlockTargets

abbrev ExactFiniteTargetsBelowSix : Prop :=
  SmallLengthExactTargetsConcreteW24.ExactFiniteTargetsBelowSix

abbrev ClosedPlacementFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ClosedPlacementFamily

abbrev ClosedPlacementPackage : Type :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

abbrev MinimalFreePlacementFields : Type :=
  ClosedPlacementWitnessAssemblyW25.MinimalFreePlacementFields

abbrev FullMetricClosedPlacementWitness : Type :=
  ClosedPlacementWitnessAssemblyW25.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  ClosedPlacementWitnessAssemblyW25.ReducedMetricClosedPlacementWitness

abbrev AlternativeValueMatrixFamily : Type :=
  NonRoleSplitSourceInhabitationW25.AlternativeValueMatrixFamily

/-! ## The package and the exact target -/

def packageOfPositiveExactChains
    (H : forall k : Nat, 0 < k -> ExactChainUpper k) :
    PositiveExactChainPackage where
  exactChain := H

def packageOfExactTarget
    (H : ExactTarget) :
    PositiveExactChainPackage where
  exactChain := fun k _hk =>
    SplitSoundness.exactChainUpperOfTarget H k

theorem exactTarget_of_package
    (P : PositiveExactChainPackage) :
    ExactTarget :=
  ArbitraryNBridgeW10.PositiveExactChainPackage.targetUpperConstructionFiveSixteen
    P

theorem nonempty_package_iff_exactTarget :
    Iff (Nonempty PositiveExactChainPackage) ExactTarget := by
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro P => exact exactTarget_of_package P
  case mpr =>
    intro H
    exact Nonempty.intro (packageOfExactTarget H)

def exactTargetPackageOfPackage
    (P : PositiveExactChainPackage) :
    ArbitraryNBridgeW10.ExactTargetPackage where
  exactTarget := exactTarget_of_package P

def packageOfExactTargetPackage
    (P : ArbitraryNBridgeW10.ExactTargetPackage) :
    PositiveExactChainPackage :=
  packageOfExactTarget P.exactTarget

/-! ## Exact block targets -/

theorem exactBlockTarget_of_package
    (P : PositiveExactChainPackage)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
    (P.exactChain k hk)

def packageOfExactBlockTargets
    (H : forall k : Nat, 0 < k -> ExactBlockTarget k) :
    PositiveExactChainPackage where
  exactChain := fun k hk =>
    SmallLengthExactTargetsConcreteW24.exactChainUpperOfExactBlockTarget
      (H k hk)

theorem nonempty_package_iff_exactBlockTargets :
    Iff (Nonempty PositiveExactChainPackage)
      (forall k : Nat, 0 < k -> ExactBlockTarget k) := by
  apply Iff.intro
  case mp =>
    intro h k hk
    cases h with
    | intro P => exact exactBlockTarget_of_package P k hk
  case mpr =>
    intro H
    exact Nonempty.intro (packageOfExactBlockTargets H)

/-! ## Small blocks plus the large positive tail -/

abbrev LargeExactBlockTargetsFromSix : Prop :=
  forall k : Nat, 6 <= k -> ExactBlockTarget k

structure SmallAndLargeExactBlockTargets where
  small : ExactBlocksOneThroughFive
  large : LargeExactBlockTargetsFromSix

def smallAndLargeExactBlockTargetsOfPackage
    (P : PositiveExactChainPackage) :
    SmallAndLargeExactBlockTargets where
  small :=
    SmallLengthExactTargetsConcreteW24.exactBlocksOneThroughFive_of_exactFiniteTargetsBelowSix
      (fun k hklt hkpos => exactBlockTarget_of_package P k hkpos)
  large := by
    intro k hklarge
    have hkpos : 0 < k := by omega
    exact exactBlockTarget_of_package P k hkpos

def packageOfSmallAndLargeExactBlockTargets
    (D : SmallAndLargeExactBlockTargets) :
    PositiveExactChainPackage where
  exactChain := by
    intro k hkpos
    by_cases hklt : k < 6
    case pos =>
      exact
        SmallLengthExactTargetsConcreteW24.exactChainUpperOfExactBlockTarget
          (SmallLengthExactTargetsConcreteW24.exactBlockTargetBelowSix_of_exactBlocksOneThroughFive
            D.small k hklt hkpos)
    case neg =>
      have hklarge : 6 <= k := Nat.le_of_not_gt hklt
      exact
        SmallLengthExactTargetsConcreteW24.exactChainUpperOfExactBlockTarget
          (D.large k hklarge)

theorem nonempty_package_iff_smallAndLargeExactBlockTargets :
    Iff (Nonempty PositiveExactChainPackage)
      (Nonempty SmallAndLargeExactBlockTargets) := by
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (smallAndLargeExactBlockTargetsOfPackage P)
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact
          Nonempty.intro
            (packageOfSmallAndLargeExactBlockTargets D)

theorem nonempty_package_iff_smallBlocks_and_largeTail :
    Iff (Nonempty PositiveExactChainPackage)
      (And ExactBlocksOneThroughFive LargeExactBlockTargetsFromSix) := by
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          And.intro
            (smallAndLargeExactBlockTargetsOfPackage P).small
            (smallAndLargeExactBlockTargetsOfPackage P).large
  case mpr =>
    intro h
    exact
      Nonempty.intro
        (packageOfSmallAndLargeExactBlockTargets
          { small := h.left
            large := h.right })

theorem smallLengthExactBlockTargets_of_package
    (P : PositiveExactChainPackage) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsConcreteW24.smallLengthExactBlockTargetsOfExactBlocksOneThroughFive
    (smallAndLargeExactBlockTargetsOfPackage P).small

theorem exactFiniteTargetsBelowSix_of_package
    (P : PositiveExactChainPackage) :
    ExactFiniteTargetsBelowSix :=
  SmallLengthExactTargetsConcreteW24.exactFiniteTargetsBelowSix_of_exactBlocksOneThroughFive
    (smallAndLargeExactBlockTargetsOfPackage P).small

/-! ## Non-role source and closed-placement routes -/

def nonRoleSplitSourceOfPackage
    (P : PositiveExactChainPackage) :
    NonRoleSplitSource :=
  NonRoleSplitSourceInhabitationW25.nonRoleSplitSourceOfPositiveExactChainPackage
    P

def packageOfNonRoleSplitSource
    (S : NonRoleSplitSource) :
    PositiveExactChainPackage :=
  NonRoleSplitSourceInhabitationW25.positiveExactChainPackageOfNonRoleSplitSource
    S

theorem nonempty_package_iff_nonRoleSplitSource :
    Iff (Nonempty PositiveExactChainPackage)
      (Nonempty NonRoleSplitSource) :=
  NonRoleSplitSourceInhabitationW25.nonempty_nonRoleSplitSource_iff_positiveExactChainPackage.symm

def packageOfClosedPlacements
    (H : ClosedPlacementFamily) :
    PositiveExactChainPackage where
  exactChain := fun k hk =>
    SplitArbitraryNNonRigidBridge.exactChainUpperOfClosedPlacement
      (H k hk)

def packageOfClosedPlacementPackage
    (P : ClosedPlacementPackage) :
    PositiveExactChainPackage :=
  ArbitraryNBridgeW10.ClosedPlacementPackage.toPositiveExactChainPackage P

def closedPlacementPackageOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    ClosedPlacementPackage where
  placement := H

theorem nonempty_package_of_closedPlacementFamily_nonempty :
    Nonempty ClosedPlacementFamily -> Nonempty PositiveExactChainPackage := by
  intro h
  cases h with
  | intro H => exact Nonempty.intro (packageOfClosedPlacements H)

def packageOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    PositiveExactChainPackage :=
  packageOfClosedPlacements
    (ClosedPlacementWitnessAssemblyW25.closedPlacementFamilyOfMinimalFreePlacementFields
      S)

def packageOfFullMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementWitness) :
    PositiveExactChainPackage :=
  packageOfClosedPlacements
    (ClosedPlacementWitnessAssemblyW25.closedPlacementFamilyOfFullMetricWitness
      W)

def packageOfReducedMetricClosedPlacementWitness
    (W : ReducedMetricClosedPlacementWitness) :
    PositiveExactChainPackage :=
  packageOfClosedPlacements
    (ClosedPlacementWitnessAssemblyW25.closedPlacementFamilyOfReducedMetricWitness
      W)

def packageOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamily) :
    PositiveExactChainPackage :=
  packageOfExactTarget
    (AlternativeValueMatrixFamilyW24.exactTarget_of_alternativeValueMatrixFamily
      A)

/-! ## Checked remainders and arbitrary vertex counts -/

def checkedRemainderUpperOfLtSixteen
    {r : Nat} (hr : r < 16) :
    RemainderUpper r :=
  SmallLengthExactTargetsConcreteW24.checkedRemainderUpperOfLtSixteen hr

theorem nonempty_remainderUpper_of_lt_sixteen
    {r : Nat} (hr : r < 16) :
    Nonempty (RemainderUpper r) :=
  SmallLengthExactTargetsConcreteW24.nonempty_remainderUpper_of_lt_sixteen
    hr

theorem exactVertexTarget_remainder_of_lt_sixteen
    {r : Nat} (hr : r < 16) :
    ExactVertexTarget r :=
  SmallLengthExactTargetsConcreteW24.exactVertexTarget_remainder_of_lt_sixteen
    hr

def exactChainUpperOfPackageDiv
    (P : PositiveExactChainPackage) (n : Nat) :
    ExactChainUpper (n / 16) :=
  SplitArbitraryNNonRigidBridge.exactChainUpperOfPositiveExactChainsDiv
    P.exactChain n

theorem exactVertexTarget_divMod_of_package
    (P : PositiveExactChainPackage) (n : Nat) :
    ExactVertexTarget (16 * (n / 16) + n % 16) :=
  SplitArbitraryNNonRigidBridge.targetUpperConstructionFiveSixteenAt_divMod_of_positiveExactChains
    P.exactChain n

theorem exactVertexTarget_of_package
    (P : PositiveExactChainPackage) (n : Nat) :
    ExactVertexTarget n :=
  ArbitraryNBridgeW10.PositiveExactChainPackage.targetUpperConstructionFiveSixteenAt_checkedRemainders
    P n

theorem exactVertexTarget_of_package_translatedSeparation
    (P : PositiveExactChainPackage) (n : Nat) :
    ExactVertexTarget n :=
  ConcreteRemainderSplitW24.targetUpperConstructionFiveSixteenAt_of_exactTarget_divMod_checkedRemainder_translatedSeparation
    (exactTarget_of_package P) n

theorem arbitraryTarget_of_package_checkedRemainders
    (P : PositiveExactChainPackage) :
    ArbitraryTarget :=
  ArbitraryNBridgeW10.PositiveExactChainPackage.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
    P

theorem arbitraryTarget_of_package_splitBridge
    (P : PositiveExactChainPackage) :
    ArbitraryTarget :=
  ArbitraryNBridgeW10.PositiveExactChainPackage.targetUpperConstructionFiveSixteenArbitrary_splitBridge
    P

theorem arbitraryTarget_of_package_translatedSeparation
    (P : PositiveExactChainPackage) :
    ArbitraryTarget :=
  ConcreteRemainderSplitW24.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder_translatedSeparation
    (exactTarget_of_package P)

/-! ## Exact blocker statement -/

abbrev RemainingPositiveExactChainBlocker : Prop :=
  LargeExactBlockTargetsFromSix

theorem remainingBlocker_is_largeExactBlockTail_after_small_blocks :
    Iff (Nonempty PositiveExactChainPackage)
      (And ExactBlocksOneThroughFive RemainingPositiveExactChainBlocker) :=
  nonempty_package_iff_smallBlocks_and_largeTail

end

end PositiveExactChainPackageW26
end PachToth
end ErdosProblems1066
