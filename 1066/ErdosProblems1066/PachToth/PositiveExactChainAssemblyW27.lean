import ErdosProblems1066.PachToth.PositiveExactChainPackageW26
import ErdosProblems1066.PachToth.NonRoleSplitSourceConstructionW26

set_option autoImplicit false

/-!
# W27 positive exact-chain assembly

This worker is the PT5 exact-chain assembly point.  If a future lane supplies
the W26 small-block data together with the large exact-block tail, this file
assembles the `PositiveExactChainPackage` directly.  In the current tree no
independent large-tail inhabitant is available, so the exposed frontier is the
smallest exact source package that does not store the Pach--Toth target as a
field: the W11 exact closed-chain package.

No constructor here builds a source from the target statement.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveExactChainAssemblyW27

noncomputable section

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev NonRoleSplitSource : Type :=
  NonRoleSplitSourceConstructionW26.NonRoleSplitSource

abbrev MinimalExactSourcePackage : Type :=
  NonRoleSplitSourceConstructionW26.W11ExactClosedChainPackage

abbrev ExactChainUpper (k : Nat) : Type :=
  PositiveExactChainPackageW26.ExactChainUpper k

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PositiveExactChainPackageW26.ExactBlockTarget k

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainPackageW26.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  PositiveExactChainPackageW26.LargeExactBlockTargetsFromSix

abbrev SmallAndLargeExactBlockTargets : Prop :=
  PositiveExactChainPackageW26.SmallAndLargeExactBlockTargets

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainPackageW26.RemainingPositiveExactChainBlocker

/-! ## Direct assembly when the large tail is supplied -/

def packageOfPositiveExactChains
    (H : forall k : Nat, 0 < k -> ExactChainUpper k) :
    PositiveExactChainPackage :=
  PositiveExactChainPackageW26.packageOfPositiveExactChains H

def packageOfSmallAndLargeExactBlockTargets
    (D : SmallAndLargeExactBlockTargets) :
    PositiveExactChainPackage :=
  PositiveExactChainPackageW26.packageOfSmallAndLargeExactBlockTargets D

def packageOfSmallBlocksAndLargeTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    PositiveExactChainPackage :=
  packageOfSmallAndLargeExactBlockTargets
    { small := small
      large := large }

theorem nonempty_package_of_smallBlocks_and_largeTail
    (H : And ExactBlocksOneThroughFive LargeExactBlockTargetsFromSix) :
    Nonempty PositiveExactChainPackage :=
  PositiveExactChainPackageW26.nonempty_package_iff_smallBlocks_and_largeTail.mpr
    H

theorem nonempty_package_iff_smallBlocks_and_largeTail :
    Nonempty PositiveExactChainPackage <->
      And ExactBlocksOneThroughFive LargeExactBlockTargetsFromSix :=
  PositiveExactChainPackageW26.nonempty_package_iff_smallBlocks_and_largeTail

theorem remainingBlocker_is_largeExactBlockTail_after_small_blocks :
    Nonempty PositiveExactChainPackage <->
      And ExactBlocksOneThroughFive RemainingPositiveExactChainBlocker :=
  PositiveExactChainPackageW26.remainingBlocker_is_largeExactBlockTail_after_small_blocks

/-! ## Current exact-source frontier -/

structure ExposedExactChainSource where
  minimalExactSource : MinimalExactSourcePackage

def packageOfMinimalExactSource
    (P : MinimalExactSourcePackage) :
    PositiveExactChainPackage :=
  NonRoleSplitSourceConstructionW26.positiveExactChainPackageOfW11ExactClosedChainPackage
    P

def minimalExactSourceOfPackage
    (P : PositiveExactChainPackage) :
    MinimalExactSourcePackage :=
  NonRoleSplitSourceConstructionW26.w11ExactClosedChainPackageOfPositiveExactChainPackage
    P

def exposedExactChainSourceOfMinimal
    (P : MinimalExactSourcePackage) :
    ExposedExactChainSource where
  minimalExactSource := P

def exposedExactChainSourceOfPackage
    (P : PositiveExactChainPackage) :
    ExposedExactChainSource :=
  exposedExactChainSourceOfMinimal (minimalExactSourceOfPackage P)

def packageOfExposedExactChainSource
    (S : ExposedExactChainSource) :
    PositiveExactChainPackage :=
  packageOfMinimalExactSource S.minimalExactSource

theorem package_minimalExactSource_left_inverse
    (P : PositiveExactChainPackage) :
    packageOfMinimalExactSource (minimalExactSourceOfPackage P) = P :=
  NonRoleSplitSourceConstructionW26.positiveExactChain_w11_left_inverse P

theorem package_minimalExactSource_right_inverse
    (P : MinimalExactSourcePackage) :
    minimalExactSourceOfPackage (packageOfMinimalExactSource P) = P :=
  NonRoleSplitSourceConstructionW26.positiveExactChain_w11_right_inverse P

theorem nonempty_package_iff_minimalExactSource :
    Nonempty PositiveExactChainPackage <->
      Nonempty MinimalExactSourcePackage :=
  NonRoleSplitSourceConstructionW26.nonempty_positiveExactChainPackage_iff_w11ExactClosedChainPackage

theorem nonempty_package_iff_exposedExactChainSource :
    Nonempty PositiveExactChainPackage <->
      Nonempty ExposedExactChainSource := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (exposedExactChainSourceOfPackage P)
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro (packageOfExposedExactChainSource S)

/-! ## Non-role source compatibility, still without target-to-source cycling -/

def nonRoleSplitSourceOfMinimalExactSource
    (P : MinimalExactSourcePackage) :
    NonRoleSplitSource :=
  NonRoleSplitSourceConstructionW26.nonRoleSplitSourceOfW11ExactClosedChainPackage
    P

def nonRoleSplitSourceOfExposedExactChainSource
    (S : ExposedExactChainSource) :
    NonRoleSplitSource :=
  nonRoleSplitSourceOfMinimalExactSource S.minimalExactSource

theorem nonempty_nonRoleSplitSource_iff_minimalExactSource :
    Nonempty NonRoleSplitSource <->
      Nonempty MinimalExactSourcePackage :=
  NonRoleSplitSourceConstructionW26.nonempty_nonRoleSplitSource_iff_w11ExactClosedChainPackage

theorem nonempty_nonRoleSplitSource_iff_exposedExactChainSource :
    Nonempty NonRoleSplitSource <->
      Nonempty ExposedExactChainSource := by
  constructor
  case mp =>
    intro h
    cases nonempty_nonRoleSplitSource_iff_minimalExactSource.mp h with
    | intro P =>
        exact Nonempty.intro (exposedExactChainSourceOfMinimal P)
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact
          nonempty_nonRoleSplitSource_iff_minimalExactSource.mpr
            (Nonempty.intro S.minimalExactSource)

end

end PositiveExactChainAssemblyW27
end PachToth

namespace Verified

abbrev PachTothW27PositiveExactChainPackage : Type :=
  PachToth.PositiveExactChainAssemblyW27.PositiveExactChainPackage

abbrev PachTothW27ExposedExactChainSource : Type :=
  PachToth.PositiveExactChainAssemblyW27.ExposedExactChainSource

abbrev PachTothW27MinimalExactSourcePackage : Type :=
  PachToth.PositiveExactChainAssemblyW27.MinimalExactSourcePackage

theorem pachtoth_w27_positiveExactChainPackage_iff_minimalExactSource :
    Nonempty PachTothW27PositiveExactChainPackage <->
      Nonempty PachTothW27MinimalExactSourcePackage :=
  PachToth.PositiveExactChainAssemblyW27.nonempty_package_iff_minimalExactSource

theorem pachtoth_w27_positiveExactChainPackage_iff_exposedExactChainSource :
    Nonempty PachTothW27PositiveExactChainPackage <->
      Nonempty PachTothW27ExposedExactChainSource :=
  PachToth.PositiveExactChainAssemblyW27.nonempty_package_iff_exposedExactChainSource

end Verified
end ErdosProblems1066
