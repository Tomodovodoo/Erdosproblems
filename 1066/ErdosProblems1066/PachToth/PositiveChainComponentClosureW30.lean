import ErdosProblems1066.PachToth.LargeTailFieldsSourceW29
import ErdosProblems1066.PachToth.PositiveChainComponentsSourceW29

set_option autoImplicit false

/-!
# W30 positive-chain component closure

This file closes the W29 positive-chain component interface from source-side
data.  The main path combines small exact blocks with a large-tail source
package, large closed-placement fields from six onward, or the raw W29
threshold-six fields.  It also records the exact remaining source blocker when
the large-tail package itself is still conditional.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveChainComponentClosureW30

noncomputable section

/-! ## W29 vocabulary -/

abbrev ExactPositiveChainComponents : Prop :=
  PositiveChainComponentsSourceW29.ExactPositiveChainComponents

abbrev ExactPositiveChainComponentData : Type :=
  PositiveChainComponentsSourceW29.ExactPositiveChainComponentData

abbrev PositiveChainComponentSource : Type :=
  PositiveChainComponentsSourceW29.PositiveChainComponentSource

abbrev ExactPositiveChainComponentBlockers : Prop :=
  PositiveChainComponentsSourceW29.ExactPositiveChainComponentBlockers

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveChainComponentsSourceW29.ExactBlocksOneThroughFive

abbrev SmallLengthExactBlockTargets :=
  PositiveChainComponentsSourceW29.SmallLengthExactBlockTargets

abbrev ExactBlockSourcePackage : Type :=
  PositiveChainComponentsSourceW29.ExactBlockSourcePackage

abbrev LargeTailExactSourcePackage : Type :=
  PositiveChainComponentsSourceW29.LargeTailExactSourcePackage

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeClosedPlacementFieldsFromSix

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  LargeTailFieldsSourceW29.LargeRawClosedPlacementFieldsFromSix

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailFieldsSourceW29.RemainingLargeTailExactSourceBlocker

abbrev ExactPositiveChainSourceBlocker : Prop :=
  ExactBlocksOneThroughFive /\ RemainingLargeTailExactSourceBlocker

/-! ## Exact blocker bridge -/

theorem componentData_iff_components :
    Nonempty ExactPositiveChainComponentData <->
      ExactPositiveChainComponents :=
  PositiveChainComponentsSourceW29.nonempty_componentData_iff_components

theorem componentData_iff_namedBlockers :
    Nonempty ExactPositiveChainComponentData <->
      ExactPositiveChainComponentBlockers := by
  exact
    Iff.trans componentData_iff_components
      PositiveChainComponentsSourceW29.exactPositiveChainComponents_iff_namedBlockers

theorem components_of_sourceBlocker
    (H : ExactPositiveChainSourceBlocker) :
    ExactPositiveChainComponents :=
  And.intro H.1
    (PositiveChainComponentsSourceW29.remainingBlocker_of_remainingLargeTailExactSourceBlocker
      H.2)

def componentDataOfSourceBlocker
    (H : ExactPositiveChainSourceBlocker) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents
    (components_of_sourceBlocker H)

theorem nonempty_componentData_of_sourceBlocker
    (H : ExactPositiveChainSourceBlocker) :
    Nonempty ExactPositiveChainComponentData :=
  Nonempty.intro (componentDataOfSourceBlocker H)

/-! ## Large-tail source packages from W29 field surfaces -/

def largeTailExactSourcePackageOfFields
    (L : LargeClosedPlacementFieldsFromSix) :
    LargeTailExactSourcePackage :=
  LargeTailExactSourceW28.packageOfLargeClosedPlacementFieldsFromSix L

def largeTailExactSourcePackageOfRawFields
    (R : LargeRawClosedPlacementFieldsFromSix) :
    LargeTailExactSourcePackage :=
  largeTailExactSourcePackageOfFields
    (LargeTailFieldsSourceW29.largeClosedPlacementFieldsFromSixOfRawFields R)

/-! ## Exact small blocks plus large tail source -/

theorem exactPositiveChainComponents_of_exactBlocks_and_largeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    ExactPositiveChainComponents :=
  And.intro small
    (PositiveChainComponentsSourceW29.remainingBlocker_of_largeTailExactSourcePackage
      large)

def componentDataOfExactBlocksAndLargeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents
    (exactPositiveChainComponents_of_exactBlocks_and_largeTailSource
      small large)

def componentSourceOfExactBlocksAndLargeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    PositiveChainComponentSource :=
  PositiveChainComponentsSourceW29.positiveChainComponentSourceOfComponentData
    (componentDataOfExactBlocksAndLargeTailSource small large)

theorem nonempty_componentData_of_exactBlocks_and_largeTailSource
    (small : ExactBlocksOneThroughFive)
    (large : LargeTailExactSourcePackage) :
    Nonempty ExactPositiveChainComponentData :=
  Nonempty.intro
    (componentDataOfExactBlocksAndLargeTailSource small large)

/-! ## Exact small blocks plus concrete large-tail fields -/

theorem exactPositiveChainComponents_of_exactBlocks_and_fields
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponents :=
  exactPositiveChainComponents_of_exactBlocks_and_largeTailSource
    small (largeTailExactSourcePackageOfFields large)

theorem exactPositiveChainComponents_of_exactBlocks_and_rawFields
    (small : ExactBlocksOneThroughFive)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponents :=
  And.intro small
    (LargeTailFieldsSourceW29.remainingPositiveExactChainBlocker_of_rawFieldsFromSix
      large)

def componentDataOfExactBlocksAndFields
    (small : ExactBlocksOneThroughFive)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents
    (exactPositiveChainComponents_of_exactBlocks_and_fields small large)

def componentDataOfExactBlocksAndRawFields
    (small : ExactBlocksOneThroughFive)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents
    (exactPositiveChainComponents_of_exactBlocks_and_rawFields small large)

/-! ## Small source surfaces plus concrete large-tail fields -/

theorem exactPositiveChainComponents_of_smallLengthTargets_and_fields
    (small : SmallLengthExactBlockTargets)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponents :=
  exactPositiveChainComponents_of_exactBlocks_and_fields
    (PositiveChainComponentsSourceW29.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
      small)
    large

theorem exactPositiveChainComponents_of_smallLengthTargets_and_rawFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponents :=
  exactPositiveChainComponents_of_exactBlocks_and_rawFields
    (PositiveChainComponentsSourceW29.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
      small)
    large

def componentDataOfSmallLengthTargetsAndFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents
    (exactPositiveChainComponents_of_smallLengthTargets_and_fields
      small large)

def componentDataOfSmallLengthTargetsAndRawFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents
    (exactPositiveChainComponents_of_smallLengthTargets_and_rawFields
      small large)

theorem exactPositiveChainComponents_of_exactBlockSource_and_fields
    (small : ExactBlockSourcePackage)
    (large : LargeClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponents :=
  exactPositiveChainComponents_of_exactBlocks_and_fields
    (PositiveChainComponentsSourceW29.exactBlocksOneThroughFiveOfExactBlockSourcePackage
      small)
    large

theorem exactPositiveChainComponents_of_exactBlockSource_and_rawFields
    (small : ExactBlockSourcePackage)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    ExactPositiveChainComponents :=
  exactPositiveChainComponents_of_exactBlocks_and_rawFields
    (PositiveChainComponentsSourceW29.exactBlocksOneThroughFiveOfExactBlockSourcePackage
      small)
    large

/-! ## Bundled source records -/

structure SmallTargetsAndLargeTailFields where
  small : SmallLengthExactBlockTargets
  large : LargeClosedPlacementFieldsFromSix

structure SmallTargetsAndRawLargeTailFields where
  small : SmallLengthExactBlockTargets
  large : LargeRawClosedPlacementFieldsFromSix

def SmallTargetsAndLargeTailFields.components
    (S : SmallTargetsAndLargeTailFields) :
    ExactPositiveChainComponents :=
  exactPositiveChainComponents_of_smallLengthTargets_and_fields
    S.small S.large

def SmallTargetsAndRawLargeTailFields.components
    (S : SmallTargetsAndRawLargeTailFields) :
    ExactPositiveChainComponents :=
  exactPositiveChainComponents_of_smallLengthTargets_and_rawFields
    S.small S.large

def SmallTargetsAndLargeTailFields.componentData
    (S : SmallTargetsAndLargeTailFields) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents S.components

def SmallTargetsAndRawLargeTailFields.componentData
    (S : SmallTargetsAndRawLargeTailFields) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentsSourceW29.componentDataOfComponents S.components

theorem nonempty_componentData_of_smallTargetsAndLargeTailFields
    (S : SmallTargetsAndLargeTailFields) :
    Nonempty ExactPositiveChainComponentData :=
  Nonempty.intro S.componentData

theorem nonempty_componentData_of_smallTargetsAndRawLargeTailFields
    (S : SmallTargetsAndRawLargeTailFields) :
    Nonempty ExactPositiveChainComponentData :=
  Nonempty.intro S.componentData

end

end PositiveChainComponentClosureW30
end PachToth

namespace Verified

abbrev PachTothW30ExactPositiveChainComponents : Prop :=
  PachToth.PositiveChainComponentClosureW30.ExactPositiveChainComponents

abbrev PachTothW30ExactPositiveChainComponentData : Type :=
  PachToth.PositiveChainComponentClosureW30.ExactPositiveChainComponentData

abbrev PachTothW30ExactPositiveChainSourceBlocker : Prop :=
  PachToth.PositiveChainComponentClosureW30.ExactPositiveChainSourceBlocker

abbrev PachTothW30SmallTargetsAndLargeTailFields : Type :=
  PachToth.PositiveChainComponentClosureW30.SmallTargetsAndLargeTailFields

abbrev PachTothW30SmallTargetsAndRawLargeTailFields : Type :=
  PachToth.PositiveChainComponentClosureW30.SmallTargetsAndRawLargeTailFields

open PachToth.PositiveChainComponentClosureW30

theorem pachtoth_w30_componentData_iff_components :
    Nonempty PachTothW30ExactPositiveChainComponentData <->
      PachTothW30ExactPositiveChainComponents :=
  componentData_iff_components

theorem pachtoth_w30_componentData_iff_namedBlockers :
    Nonempty PachTothW30ExactPositiveChainComponentData <->
      PachToth.PositiveChainComponentClosureW30.ExactPositiveChainComponentBlockers :=
  componentData_iff_namedBlockers

theorem pachtoth_w30_components_of_sourceBlocker
    (H : PachTothW30ExactPositiveChainSourceBlocker) :
    PachTothW30ExactPositiveChainComponents :=
  components_of_sourceBlocker H

theorem pachtoth_w30_nonempty_componentData_of_sourceBlocker
    (H : PachTothW30ExactPositiveChainSourceBlocker) :
    Nonempty PachTothW30ExactPositiveChainComponentData :=
  nonempty_componentData_of_sourceBlocker H

theorem pachtoth_w30_nonempty_componentData_of_smallTargetsAndLargeTailFields
    (S : PachTothW30SmallTargetsAndLargeTailFields) :
    Nonempty PachTothW30ExactPositiveChainComponentData :=
  nonempty_componentData_of_smallTargetsAndLargeTailFields S

theorem pachtoth_w30_nonempty_componentData_of_smallTargetsAndRawLargeTailFields
    (S : PachTothW30SmallTargetsAndRawLargeTailFields) :
    Nonempty PachTothW30ExactPositiveChainComponentData :=
  nonempty_componentData_of_smallTargetsAndRawLargeTailFields S

end Verified
end ErdosProblems1066
