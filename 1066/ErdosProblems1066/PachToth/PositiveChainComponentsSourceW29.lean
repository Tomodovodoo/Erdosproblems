import ErdosProblems1066.PachToth.PositiveChainConcreteSourceW28
import ErdosProblems1066.PachToth.LargeTailExactSourceW28
import ErdosProblems1066.PachToth.SmallKClosedPlacementSourceW20

set_option autoImplicit false

/-!
# W29 positive-chain component source

This worker pushes the W28 component proposition one step closer to concrete
component data.  The small side is exposed as exact-chain data for blocks
one through five, and the large side as exact-chain tail data from six onward.
The closed-placement and finite-row source surfaces are recorded as
constructors into those blockers; no target-to-source cycle is used.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveChainComponentsSourceW29

noncomputable section

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PositiveExactChainPackageW26.ExactBlockTarget k

abbrev ExactChainUpper (k : Nat) : Type :=
  PositiveExactChainPackageW26.ExactChainUpper k

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveChainConcreteSourceW28.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveChainConcreteSourceW28.RemainingPositiveExactChainBlocker

abbrev ExactPositiveChainComponents : Prop :=
  PositiveChainConcreteSourceW28.ExactPositiveChainComponents

abbrev PositiveChainComponentSource : Type :=
  PositiveChainConcreteSourceW28.PositiveChainComponentSource

abbrev PositiveExactChainPackage : Type :=
  PositiveChainConcreteSourceW28.PositiveExactChainPackage

abbrev SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsConcreteW24.SmallLengthExactBlockTargets

abbrev ExactFiniteTargetsBelowSix : Prop :=
  SmallLengthExactTargetsConcreteW24.ExactFiniteTargetsBelowSix

abbrev ExactBlocksTwoThroughFive :=
  SmallLengthExactTargetsConcreteW24.ExactBlocksTwoThroughFive

abbrev ConcreteOneBlockCertificate
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :=
  SmallLengthExactTargetsConcreteW24.ConcreteOneBlockCertificate orientation

abbrev PeriodCandidateFamily :=
  ExactBlocksTwoThroughFiveProducerW18.PeriodCandidateFamily

abbrev CandidateSmallRowValueRows
    (period : PeriodCandidateFamily) :=
  ExactBlocksTwoThroughFiveProducerW18.CandidateSmallRowValueRows period

abbrev ExactBlockSourcePackage :=
  SmallKClosedPlacementSourceW20.ExactBlockSourcePackage

abbrev CandidateSmallRowExactSourcePackage :=
  SmallKClosedPlacementSourceW20.CandidateSmallRowExactSourcePackage

abbrev LargeTailExactSourcePackage :=
  LargeTailExactSourceW28.LargeTailExactSourcePackage

abbrev LargeClosedPlacementFieldsFromSix :=
  LargeTailExactSourceW28.LargeClosedPlacementFieldsFromSix

abbrev ExplicitClosedPlacementCertificateFamily :=
  LargeTailExactSourceW28.ExplicitClosedPlacementCertificateFamily

abbrev W19InputPackage :=
  LargeTailExactSourceW28.W19InputPackage

abbrev W20SourceFields :=
  LargeTailExactSourceW28.W20SourceFields

abbrev W21SourceFields :=
  LargeTailExactSourceW28.W21SourceFields

abbrev W21KnownBoundsGate : Prop :=
  LargeTailExactSourceW28.W21KnownBoundsGate

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailExactSourceW28.RemainingLargeTailExactSourceBlocker

/-! ## Exact-chain component blockers -/

abbrev SmallExactChainComponentsOneThroughFive : Type :=
  forall k : Nat, k < 6 -> 0 < k -> ExactChainUpper k

abbrev LargeExactChainTailFromSix : Type :=
  forall k : Nat, 6 <= k -> ExactChainUpper k

abbrev ExactBlocksOneThroughFiveChainBlocker : Prop :=
  Nonempty SmallExactChainComponentsOneThroughFive

abbrev RemainingPositiveExactChainTailBlocker : Prop :=
  Nonempty LargeExactChainTailFromSix

abbrev ExactPositiveChainComponentBlockers : Prop :=
  ExactBlocksOneThroughFiveChainBlocker /\
    RemainingPositiveExactChainTailBlocker

structure ExactPositiveChainComponentData where
  smallChains : SmallExactChainComponentsOneThroughFive
  largeChains : LargeExactChainTailFromSix

def smallExactChainComponentsOfExactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    SmallExactChainComponentsOneThroughFive :=
  SmallLengthExactTargetsConcreteW24.exactChainUpperBelowSix_of_exactBlocksOneThroughFive
    H

theorem exactBlocksOneThroughFive_of_smallExactChainComponents
    (S : SmallExactChainComponentsOneThroughFive) :
    ExactBlocksOneThroughFive := by
  exact
    And.intro
      (SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
        (S 1 (by norm_num) (by norm_num)))
      (And.intro
        (SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
          (S 2 (by norm_num) (by norm_num)))
        (And.intro
          (SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
            (S 3 (by norm_num) (by norm_num)))
          (And.intro
            (SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
              (S 4 (by norm_num) (by norm_num)))
            (SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
              (S 5 (by norm_num) (by norm_num))))))

theorem nonempty_smallExactChainComponents_iff_exactBlocksOneThroughFive :
    Nonempty SmallExactChainComponentsOneThroughFive <->
      ExactBlocksOneThroughFive := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact exactBlocksOneThroughFive_of_smallExactChainComponents S
  case mpr =>
    intro H
    exact
      Nonempty.intro
        (smallExactChainComponentsOfExactBlocksOneThroughFive H)

theorem exactBlocksOneThroughFive_iff_chainBlocker :
    ExactBlocksOneThroughFive <->
      ExactBlocksOneThroughFiveChainBlocker :=
  nonempty_smallExactChainComponents_iff_exactBlocksOneThroughFive.symm

def largeExactChainTailFromSixOfRemainingBlocker
    (H : RemainingPositiveExactChainBlocker) :
    LargeExactChainTailFromSix := by
  intro k hk
  exact
    SmallLengthExactTargetsConcreteW24.exactChainUpperOfExactBlockTarget
      (H k hk)

theorem remainingBlocker_of_largeExactChainTailFromSix
    (T : LargeExactChainTailFromSix) :
    RemainingPositiveExactChainBlocker :=
  PositiveExactLargeTailW27.remainingBlocker_of_exactChainTailFromSix T

theorem nonempty_largeExactChainTailFromSix_iff_remainingBlocker :
    Nonempty LargeExactChainTailFromSix <->
      RemainingPositiveExactChainBlocker := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
        exact remainingBlocker_of_largeExactChainTailFromSix T
  case mpr =>
    intro H
    exact
      Nonempty.intro (largeExactChainTailFromSixOfRemainingBlocker H)

theorem remainingBlocker_iff_chainTailBlocker :
    RemainingPositiveExactChainBlocker <->
      RemainingPositiveExactChainTailBlocker :=
  nonempty_largeExactChainTailFromSix_iff_remainingBlocker.symm

def componentDataOfComponents
    (H : ExactPositiveChainComponents) :
    ExactPositiveChainComponentData where
  smallChains :=
    smallExactChainComponentsOfExactBlocksOneThroughFive H.1
  largeChains :=
    largeExactChainTailFromSixOfRemainingBlocker H.2

def componentsOfComponentData
    (D : ExactPositiveChainComponentData) :
    ExactPositiveChainComponents :=
  And.intro
    (exactBlocksOneThroughFive_of_smallExactChainComponents D.smallChains)
    (remainingBlocker_of_largeExactChainTailFromSix D.largeChains)

theorem nonempty_componentData_iff_components :
    Nonempty ExactPositiveChainComponentData <->
      ExactPositiveChainComponents := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact componentsOfComponentData D
  case mpr =>
    intro H
    exact Nonempty.intro (componentDataOfComponents H)

theorem exactPositiveChainComponents_iff_namedBlockers :
    ExactPositiveChainComponents <->
      ExactPositiveChainComponentBlockers := by
  constructor
  case mp =>
    intro H
    exact
      And.intro
        (exactBlocksOneThroughFive_iff_chainBlocker.mp H.1)
        (remainingBlocker_iff_chainTailBlocker.mp H.2)
  case mpr =>
    intro H
    exact
      And.intro
        (exactBlocksOneThroughFive_iff_chainBlocker.mpr H.1)
        (remainingBlocker_iff_chainTailBlocker.mpr H.2)

def componentDataOfSmallAndLargeChainSources
    (small : SmallExactChainComponentsOneThroughFive)
    (large : LargeExactChainTailFromSix) :
    ExactPositiveChainComponentData where
  smallChains := small
  largeChains := large

def positiveChainComponentSourceOfComponentData
    (D : ExactPositiveChainComponentData) :
    PositiveChainComponentSource :=
  PositiveChainConcreteSourceW28.componentSourceOfComponents
    (componentsOfComponentData D)

def componentDataOfPositiveChainComponentSource
    (S : PositiveChainComponentSource) :
    ExactPositiveChainComponentData :=
  componentDataOfComponents
    (PositiveChainConcreteSourceW28.componentsOfComponentSource S)

theorem nonempty_componentData_iff_w28_componentSource :
    Nonempty ExactPositiveChainComponentData <->
      Nonempty PositiveChainComponentSource := by
  exact
    Iff.trans nonempty_componentData_iff_components
      PositiveChainConcreteSourceW28.nonempty_componentSource_iff_components.symm

theorem nonempty_componentData_iff_positiveExactChainPackage :
    Nonempty ExactPositiveChainComponentData <->
      Nonempty PositiveExactChainPackage := by
  exact
    Iff.trans nonempty_componentData_iff_w28_componentSource
      PositiveChainConcreteSourceW28.nonempty_componentSource_iff_positiveExactChainPackage

/-! ## Small-block constructors and equivalences -/

def smallLengthExactBlockTargetsOfExactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsConcreteW24.smallLengthExactBlockTargetsOfExactBlocksOneThroughFive
    H

theorem exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlocksOneThroughFive :=
  SmallLengthExactTargetsConcreteW24.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    C

theorem nonempty_smallLengthExactBlockTargets_iff_exactBlocksOneThroughFive :
    Nonempty SmallLengthExactBlockTargets <-> ExactBlocksOneThroughFive :=
  SmallLengthExactTargetsConcreteW24.nonempty_smallLengthExactBlockTargets_iff_exactBlocksOneThroughFive

theorem exactBlocksOneThroughFive_iff_exactFiniteTargetsBelowSix :
    ExactBlocksOneThroughFive <-> ExactFiniteTargetsBelowSix :=
  SmallLengthExactTargetsConcreteW24.exactFiniteTargetsBelowSix_iff_exactBlocksOneThroughFive.symm

def exactBlocksOneThroughFiveOfExactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactBlocksOneThroughFive :=
  SmallLengthExactTargetsConcreteW24.exactBlocksOneThroughFiveOfExactBlocksTwoThroughFive
    blocks oneBlock

def exactBlocksOneThroughFiveOfCandidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (rows : CandidateSmallRowValueRows period)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFiveOfExactBlocksTwoThroughFive
    (ExactBlocksTwoThroughFiveProducerW18.exactBlocksOfCandidateSmallRowValueRows
      rows)
    oneBlock

def exactBlocksOneThroughFiveOfExactBlockSourcePackage
    (P : ExactBlockSourcePackage) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    P.toSmallLengthExactBlockTargets

def exactBlocksOneThroughFiveOfCandidateSmallRowExactSourcePackage
    (P : CandidateSmallRowExactSourcePackage) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFiveOfExactBlockSourcePackage
    P.toExactBlockSourcePackage

/-! ## Large-tail constructors and named blocker facts -/

theorem remainingBlocker_of_largeTailExactSourcePackage
    (P : LargeTailExactSourcePackage) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_largeTailExactSourcePackage P

theorem remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_largeClosedPlacementFieldsFromSix
    L

theorem remainingBlocker_of_certificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_certificateFamily C

theorem remainingBlocker_of_w19InputPackage
    (P : W19InputPackage) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_w19InputPackage P

theorem remainingBlocker_of_w20SourceFields
    (S : W20SourceFields) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_w20SourceFields S

theorem remainingBlocker_of_w21SourceFields
    (S : W21SourceFields) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_w21SourceFields S

theorem remainingBlocker_of_w21KnownBoundsGate
    (G : W21KnownBoundsGate) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_w21KnownBoundsGate G

theorem remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix :
    RemainingLargeTailExactSourceBlocker <->
      Nonempty LargeClosedPlacementFieldsFromSix :=
  LargeTailExactSourceW28.remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix

theorem remainingBlocker_of_remainingLargeTailExactSourceBlocker
    (H : RemainingLargeTailExactSourceBlocker) :
    RemainingPositiveExactChainBlocker :=
  LargeTailExactSourceW28.remainingBlocker_of_remainingLargeTailExactSourceBlocker
    H

/-! ## Reassembled component constructors from actual source surfaces -/

theorem exactPositiveChainComponents_of_smallLengthTargets_and_largeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    ExactPositiveChainComponents :=
  And.intro
    (exactBlocksOneThroughFive_of_smallLengthExactBlockTargets small)
    (remainingBlocker_of_largeTailExactSourcePackage large)

theorem exactPositiveChainComponents_of_exactBlocksTwoThroughFive_and_largeTailSource
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation)
    (large : LargeTailExactSourcePackage) :
    ExactPositiveChainComponents :=
  And.intro
    (exactBlocksOneThroughFiveOfExactBlocksTwoThroughFive blocks oneBlock)
    (remainingBlocker_of_largeTailExactSourcePackage large)

theorem exactPositiveChainComponents_of_candidateRows_and_largeTailSource
    {period : PeriodCandidateFamily}
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (rows : CandidateSmallRowValueRows period)
    (oneBlock : ConcreteOneBlockCertificate orientation)
    (large : LargeTailExactSourcePackage) :
    ExactPositiveChainComponents :=
  And.intro
    (exactBlocksOneThroughFiveOfCandidateSmallRowValueRows rows oneBlock)
    (remainingBlocker_of_largeTailExactSourcePackage large)

theorem exactPositiveChainComponents_of_exactBlockSource_and_largeTailSource
    (small : ExactBlockSourcePackage)
    (large : LargeTailExactSourcePackage) :
    ExactPositiveChainComponents :=
  And.intro
    (exactBlocksOneThroughFiveOfExactBlockSourcePackage small)
    (remainingBlocker_of_largeTailExactSourcePackage large)

def componentDataOfSmallLengthTargetsAndLargeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    ExactPositiveChainComponentData :=
  componentDataOfComponents
    (exactPositiveChainComponents_of_smallLengthTargets_and_largeTailSource
      small large)

def componentSourceOfSmallLengthTargetsAndLargeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    PositiveChainComponentSource :=
  positiveChainComponentSourceOfComponentData
    (componentDataOfSmallLengthTargetsAndLargeTailSource small large)

theorem nonempty_componentData_of_smallLengthTargets_and_largeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    Nonempty ExactPositiveChainComponentData :=
  Nonempty.intro
    (componentDataOfSmallLengthTargetsAndLargeTailSource small large)

theorem nonempty_w28_componentSource_of_smallLengthTargets_and_largeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    Nonempty PositiveChainComponentSource :=
  nonempty_componentData_iff_w28_componentSource.mp
    (nonempty_componentData_of_smallLengthTargets_and_largeTailSource
      small large)

end

end PositiveChainComponentsSourceW29
end PachToth

namespace Verified

abbrev PachTothW29ExactPositiveChainComponentData : Type :=
  PachToth.PositiveChainComponentsSourceW29.ExactPositiveChainComponentData

abbrev PachTothW29ExactPositiveChainComponents : Prop :=
  PachToth.PositiveChainComponentsSourceW29.ExactPositiveChainComponents

abbrev PachTothW29ExactPositiveChainComponentBlockers : Prop :=
  PachToth.PositiveChainComponentsSourceW29.ExactPositiveChainComponentBlockers

theorem pachtoth_w29_componentData_iff_components :
    Nonempty PachTothW29ExactPositiveChainComponentData <->
      PachTothW29ExactPositiveChainComponents :=
  PachToth.PositiveChainComponentsSourceW29.nonempty_componentData_iff_components

theorem pachtoth_w29_exactPositiveChainComponents_iff_namedBlockers :
    PachTothW29ExactPositiveChainComponents <->
      PachTothW29ExactPositiveChainComponentBlockers :=
  PachToth.PositiveChainComponentsSourceW29.exactPositiveChainComponents_iff_namedBlockers

theorem pachtoth_w29_remainingBlocker_iff_chainTailBlocker :
    PachToth.PositiveChainComponentsSourceW29.RemainingPositiveExactChainBlocker <->
      PachToth.PositiveChainComponentsSourceW29.RemainingPositiveExactChainTailBlocker :=
  PachToth.PositiveChainComponentsSourceW29.remainingBlocker_iff_chainTailBlocker

end Verified
end ErdosProblems1066
