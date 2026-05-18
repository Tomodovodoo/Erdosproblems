import ErdosProblems1066.PachToth.PositiveExactChainAssemblyW27
import ErdosProblems1066.PachToth.PositiveExactLargeTailW27
import ErdosProblems1066.PachToth.ExactTargetClosureW26

set_option autoImplicit false

/-!
# W28 positive-chain concrete source

This module keeps the Pach--Toth exact-chain frontier on the source side.
The source data is the checked small block package together with the large
tail of exact block targets from six onward.  From those two components we
assemble the W27 exposed exact-chain source, the W11 exact closed-chain
package, and the W26 smallest exact source package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveChainConcreteSourceW28

noncomputable section

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainAssemblyW27.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainAssemblyW27.RemainingPositiveExactChainBlocker

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainAssemblyW27.PositiveExactChainPackage

abbrev ExposedExactChainSource : Type :=
  PositiveExactChainAssemblyW27.ExposedExactChainSource

abbrev W11ExactClosedChainPackage : Type :=
  PositiveExactChainAssemblyW27.MinimalExactSourcePackage

abbrev SmallestExactSourcePackage : Type :=
  ExactTargetClosureW26.SmallestExactSourcePackage

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  PositiveExactLargeTailW27.LargeClosedPlacementFieldsFromSix

abbrev ExactPositiveChainComponents : Prop :=
  ExactBlocksOneThroughFive /\ RemainingPositiveExactChainBlocker

structure PositiveChainComponentSource : Type where
  small : ExactBlocksOneThroughFive
  large : RemainingPositiveExactChainBlocker

def componentSourceOfComponents
    (H : ExactPositiveChainComponents) :
    PositiveChainComponentSource where
  small := H.1
  large := H.2

def componentsOfComponentSource
    (S : PositiveChainComponentSource) :
    ExactPositiveChainComponents :=
  And.intro S.small S.large

def positiveExactChainPackageOfComponentSource
    (S : PositiveChainComponentSource) :
    PositiveExactChainPackage :=
  PositiveExactLargeTailW27.positiveExactChainPackageOfSmallBlocksAndLargeTail
    S.small S.large

def componentSourceOfPositiveExactChainPackage
    (P : PositiveExactChainPackage) :
    PositiveChainComponentSource := by
  have h :
      Nonempty PositiveExactChainPackage :=
    Nonempty.intro P
  have hcomponents :
      ExactPositiveChainComponents :=
    PositiveExactChainAssemblyW27.remainingBlocker_is_largeExactBlockTail_after_small_blocks.mp
      h
  exact componentSourceOfComponents hcomponents

def exposedExactChainSourceOfComponentSource
    (S : PositiveChainComponentSource) :
    ExposedExactChainSource :=
  PositiveExactChainAssemblyW27.exposedExactChainSourceOfPackage
    (positiveExactChainPackageOfComponentSource S)

def componentSourceOfExposedExactChainSource
    (S : ExposedExactChainSource) :
    PositiveChainComponentSource :=
  componentSourceOfPositiveExactChainPackage
    (PositiveExactChainAssemblyW27.packageOfExposedExactChainSource S)

def w11ExactClosedChainPackageOfComponentSource
    (S : PositiveChainComponentSource) :
    W11ExactClosedChainPackage :=
  PositiveExactChainAssemblyW27.minimalExactSourceOfPackage
    (positiveExactChainPackageOfComponentSource S)

def componentSourceOfW11ExactClosedChainPackage
    (P : W11ExactClosedChainPackage) :
    PositiveChainComponentSource :=
  componentSourceOfPositiveExactChainPackage
    (PositiveExactChainAssemblyW27.packageOfMinimalExactSource P)

def smallestExactSourcePackageOfComponentSource
    (S : PositiveChainComponentSource) :
    SmallestExactSourcePackage :=
  positiveExactChainPackageOfComponentSource S

def componentSourceOfSmallestExactSourcePackage
    (P : SmallestExactSourcePackage) :
    PositiveChainComponentSource :=
  componentSourceOfPositiveExactChainPackage P

def componentSourceOfSmallBlocksAndLargeClosedPlacements
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    PositiveChainComponentSource where
  small := small
  large :=
    PositiveExactLargeTailW27.remainingBlocker_of_largeClosedPlacementFieldsFromSix
      large

theorem nonempty_componentSource_iff_components :
    Nonempty PositiveChainComponentSource <->
      ExactPositiveChainComponents := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact componentsOfComponentSource S
  case mpr =>
    intro H
    exact Nonempty.intro (componentSourceOfComponents H)

theorem nonempty_componentSource_iff_positiveExactChainPackage :
    Nonempty PositiveChainComponentSource <->
      Nonempty PositiveExactChainPackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro
          (positiveExactChainPackageOfComponentSource S)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro
          (componentSourceOfPositiveExactChainPackage P)

theorem nonempty_componentSource_iff_exposedExactChainSource :
    Nonempty PositiveChainComponentSource <->
      Nonempty ExposedExactChainSource := by
  exact
    Iff.trans nonempty_componentSource_iff_positiveExactChainPackage
      PositiveExactChainAssemblyW27.nonempty_package_iff_exposedExactChainSource

theorem nonempty_componentSource_iff_w11ExactClosedChainPackage :
    Nonempty PositiveChainComponentSource <->
      Nonempty W11ExactClosedChainPackage := by
  exact
    Iff.trans nonempty_componentSource_iff_positiveExactChainPackage
      PositiveExactChainAssemblyW27.nonempty_package_iff_minimalExactSource

theorem nonempty_componentSource_iff_smallestExactSourcePackage :
    Nonempty PositiveChainComponentSource <->
      Nonempty SmallestExactSourcePackage := by
  exact nonempty_componentSource_iff_positiveExactChainPackage

theorem nonempty_exposedExactChainSource_iff_components :
    Nonempty ExposedExactChainSource <->
      ExactPositiveChainComponents := by
  exact
    Iff.trans nonempty_componentSource_iff_exposedExactChainSource.symm
      nonempty_componentSource_iff_components

theorem nonempty_w11ExactClosedChainPackage_iff_components :
    Nonempty W11ExactClosedChainPackage <->
      ExactPositiveChainComponents := by
  exact
    Iff.trans nonempty_componentSource_iff_w11ExactClosedChainPackage.symm
      nonempty_componentSource_iff_components

theorem nonempty_smallestExactSourcePackage_iff_components :
    Nonempty SmallestExactSourcePackage <->
      ExactPositiveChainComponents := by
  exact
    Iff.trans nonempty_componentSource_iff_smallestExactSourcePackage.symm
      nonempty_componentSource_iff_components

theorem nonempty_componentSource_of_smallBlocks_and_largeClosedPlacements
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    Nonempty PositiveChainComponentSource :=
  Nonempty.intro
    (componentSourceOfSmallBlocksAndLargeClosedPlacements small large)

theorem nonempty_exposedExactChainSource_of_smallBlocks_and_largeClosedPlacements
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    Nonempty ExposedExactChainSource :=
  nonempty_componentSource_iff_exposedExactChainSource.mp
    (nonempty_componentSource_of_smallBlocks_and_largeClosedPlacements
      small large)

theorem exactTarget_of_componentSource
    (S : PositiveChainComponentSource) :
    ExactTargetClosureW26.ExactTarget :=
  ExactTargetClosureW26.exactTarget_of_smallestExactSourcePackage
    (smallestExactSourcePackageOfComponentSource S)

theorem exactTarget_of_nonempty_componentSource
    (H : Nonempty PositiveChainComponentSource) :
    ExactTargetClosureW26.ExactTarget := by
  cases H with
  | intro S =>
      exact exactTarget_of_componentSource S

theorem exactTarget_of_smallBlocks_and_largeClosedPlacements
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactTargetClosureW26.ExactTarget :=
  exactTarget_of_nonempty_componentSource
    (nonempty_componentSource_of_smallBlocks_and_largeClosedPlacements
      small large)

end

end PositiveChainConcreteSourceW28
end PachToth

namespace Verified

abbrev PachTothW28PositiveChainComponentSource : Type :=
  PachToth.PositiveChainConcreteSourceW28.PositiveChainComponentSource

abbrev PachTothW28ExactPositiveChainComponents : Prop :=
  PachToth.PositiveChainConcreteSourceW28.ExactPositiveChainComponents

abbrev PachTothW28PositiveChainExposedExactChainSource : Type :=
  PachToth.PositiveChainConcreteSourceW28.ExposedExactChainSource

abbrev PachTothW28W11ExactClosedChainPackage : Type :=
  PachToth.PositiveChainConcreteSourceW28.W11ExactClosedChainPackage

theorem pachtoth_w28_componentSource_iff_components :
    Nonempty PachTothW28PositiveChainComponentSource <->
      PachTothW28ExactPositiveChainComponents :=
  PachToth.PositiveChainConcreteSourceW28.nonempty_componentSource_iff_components

theorem pachtoth_w28_componentSource_iff_exposedExactChainSource :
    Nonempty PachTothW28PositiveChainComponentSource <->
      Nonempty PachTothW28PositiveChainExposedExactChainSource :=
  PachToth.PositiveChainConcreteSourceW28.nonempty_componentSource_iff_exposedExactChainSource

theorem pachtoth_w28_componentSource_iff_w11ExactClosedChainPackage :
    Nonempty PachTothW28PositiveChainComponentSource <->
      Nonempty PachTothW28W11ExactClosedChainPackage :=
  PachToth.PositiveChainConcreteSourceW28.nonempty_componentSource_iff_w11ExactClosedChainPackage

theorem pachtoth_w28_exposedExactChainSource_iff_components :
    Nonempty PachTothW28PositiveChainExposedExactChainSource <->
      PachTothW28ExactPositiveChainComponents :=
  PachToth.PositiveChainConcreteSourceW28.nonempty_exposedExactChainSource_iff_components

end Verified
end ErdosProblems1066
