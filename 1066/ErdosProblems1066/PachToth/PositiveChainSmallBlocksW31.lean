import ErdosProblems1066.PachToth.PositiveChainComponentClosureW30
import ErdosProblems1066.PachToth.PositiveChainComponentsSourceW29
import ErdosProblems1066.PachToth.SmallLengthExactTargetsConcreteW24
import ErdosProblems1066.PachToth.SmallLengthExactTargetsInhabitationW23
import ErdosProblems1066.PachToth.PositiveExactLargeTailW27

set_option autoImplicit false

/-!
# W31 positive-chain small blocks

This file exposes the positive-chain component route from concrete small-block
data.  The small side is sourced through the W23/W24 checked constructors; the
large side remains an explicit source dependency unless an actual large-tail
source package, threshold-six closed-placement field package, or raw field
package is supplied.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveChainSmallBlocksW31

noncomputable section

/-! ## Vocabulary -/

abbrev SmallLengthExactBlockTargets : Prop :=
  SmallLengthExactTargetsConcreteW24.SmallLengthExactBlockTargets

abbrev ExactFiniteTargetsBelowSix : Prop :=
  SmallLengthExactTargetsConcreteW24.ExactFiniteTargetsBelowSix

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveChainComponentClosureW30.ExactBlocksOneThroughFive

abbrev ExactBlocksTwoThroughFive : Prop :=
  SmallLengthExactTargetsConcreteW24.ExactBlocksTwoThroughFive

abbrev ConcreteOneBlockCertificate
    (orientation : Fin 1 -> OrientationData.BlockOrientation) : Prop :=
  SmallLengthExactTargetsConcreteW24.ConcreteOneBlockCertificate orientation

abbrev AllPositiveFields : Type :=
  SmallLengthExactTargetsInhabitationW23.AllPositiveFields

abbrev AllPositiveCertificateRows : Type :=
  SmallLengthExactTargetsInhabitationW23.AllPositiveCertificateRows

abbrev ConcreteValueMatrixFamily : Type :=
  SmallLengthExactTargetsInhabitationW23.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily : Type :=
  SmallLengthExactTargetsInhabitationW23.CandidateValueMatrixFamily

abbrev PeriodCandidateFamily :=
  PositiveChainComponentsSourceW29.PeriodCandidateFamily

abbrev CandidateSmallRowValueRows
    (period : PeriodCandidateFamily) :=
  PositiveChainComponentsSourceW29.CandidateSmallRowValueRows period

abbrev LargeTailExactSourcePackage : Type :=
  PositiveChainComponentClosureW30.LargeTailExactSourcePackage

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  PositiveChainComponentClosureW30.LargeClosedPlacementFieldsFromSix

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  PositiveChainComponentClosureW30.LargeRawClosedPlacementFieldsFromSix

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  PositiveChainComponentClosureW30.RemainingLargeTailExactSourceBlocker

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactLargeTailW27.RemainingPositiveExactChainBlocker

abbrev ExactPositiveChainComponents : Prop :=
  PositiveChainComponentClosureW30.ExactPositiveChainComponents

abbrev ExactPositiveChainComponentData : Type :=
  PositiveChainComponentClosureW30.ExactPositiveChainComponentData

abbrev PositiveChainComponentSource : Type :=
  PositiveChainComponentClosureW30.PositiveChainComponentSource

abbrev ExactPositiveChainSourceBlocker : Prop :=
  PositiveChainComponentClosureW30.ExactPositiveChainSourceBlocker

abbrev PositiveExactChainPackage : Type :=
  PositiveExactLargeTailW27.PositiveExactChainPackage

/-! ## Concrete small-block constructors -/

def smallLengthExactBlockTargetsOfExactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsInhabitationW23.smallLengthExactBlockTargetsOfExactFiniteTargetsBelowSix
    E

def smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsInhabitationW23.smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
    blocks oneBlock

def smallLengthExactBlockTargetsOfAllPositiveFields
    (F : AllPositiveFields) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsInhabitationW23.smallLengthExactBlockTargetsOfAllPositiveFields
    F

def smallLengthExactBlockTargetsOfAllPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsInhabitationW23.smallLengthExactBlockTargetsOfAllPositiveCertificateRows
    C

def smallLengthExactBlockTargetsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsInhabitationW23.smallLengthExactBlockTargetsOfConcreteValueMatrixFamily
    C

def smallLengthExactBlockTargetsOfCandidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsInhabitationW23.smallLengthExactBlockTargetsOfCandidateValueMatrixFamily
    C

def smallLengthExactBlockTargetsOfCandidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (rows : CandidateSmallRowValueRows period)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
    (ExactBlocksTwoThroughFiveProducerW18.exactBlocksOfCandidateSmallRowValueRows
      rows)
    oneBlock

theorem exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (small : SmallLengthExactBlockTargets) :
    ExactBlocksOneThroughFive :=
  SmallLengthExactTargetsConcreteW24.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    small

theorem exactBlocksOneThroughFive_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfExactFiniteTargetsBelowSix E)

theorem exactBlocksOneThroughFive_of_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive blocks oneBlock)

theorem exactBlocksOneThroughFive_of_allPositiveFields
    (F : AllPositiveFields) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfAllPositiveFields F)

theorem exactBlocksOneThroughFive_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfAllPositiveCertificateRows C)

theorem exactBlocksOneThroughFive_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfConcreteValueMatrixFamily C)

theorem exactBlocksOneThroughFive_of_candidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfCandidateValueMatrixFamily C)

theorem exactBlocksOneThroughFive_of_candidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (rows : CandidateSmallRowValueRows period)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfCandidateSmallRowValueRows rows oneBlock)

/-! ## Large-tail dependency stays explicit -/

abbrev RemainingLargeTailDependency : Prop :=
  RemainingLargeTailExactSourceBlocker

abbrev PositiveChainSmallBlockSourceGate : Prop :=
  Nonempty SmallLengthExactBlockTargets /\ RemainingLargeTailDependency

theorem remainingLargeTailDependency_iff_largeTailSourcePackage :
    RemainingLargeTailDependency <->
      Nonempty LargeTailExactSourcePackage :=
  Iff.rfl

theorem remainingLargeTailDependency_iff_largeClosedPlacementFields :
    RemainingLargeTailDependency <->
      Nonempty LargeClosedPlacementFieldsFromSix :=
  PositiveChainComponentsSourceW29.remainingLargeTailExactSourceBlocker_iff_largeClosedPlacementFieldsFromSix

theorem remainingLargeTailDependency_iff_rawFields :
    RemainingLargeTailDependency <->
      Nonempty LargeRawClosedPlacementFieldsFromSix :=
  LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_iff_rawFieldsFromSix

theorem remainingLargeTailDependency_of_largeTailSourcePackage
    (large : LargeTailExactSourcePackage) :
    RemainingLargeTailDependency :=
  Nonempty.intro large

theorem remainingLargeTailDependency_of_largeClosedPlacementFields
    (large : LargeClosedPlacementFieldsFromSix) :
    RemainingLargeTailDependency :=
  LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_of_largeClosedPlacementFieldsFromSix
    large

theorem remainingLargeTailDependency_of_rawFields
    (large : LargeRawClosedPlacementFieldsFromSix) :
    RemainingLargeTailDependency :=
  LargeTailFieldsSourceW29.remainingLargeTailExactSourceBlocker_of_rawFieldsFromSix
    large

theorem remainingPositiveExactChainBlocker_of_largeTailDependency
    (large : RemainingLargeTailDependency) :
    RemainingPositiveExactChainBlocker :=
  PositiveChainComponentsSourceW29.remainingBlocker_of_remainingLargeTailExactSourceBlocker
    large

/-! ## Small blocks plus explicit large-tail blocker -/

structure PositiveChainSmallBlockSource : Type where
  small : SmallLengthExactBlockTargets
  large : RemainingLargeTailDependency

namespace PositiveChainSmallBlockSource

def exactBlocksOneThroughFive
    (S : PositiveChainSmallBlockSource) :
    ExactBlocksOneThroughFive :=
  PositiveChainSmallBlocksW31.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    S.small

def sourceBlocker
    (S : PositiveChainSmallBlockSource) :
    ExactPositiveChainSourceBlocker :=
  And.intro S.exactBlocksOneThroughFive S.large

theorem remainingPositiveExactChainBlocker
    (S : PositiveChainSmallBlockSource) :
    RemainingPositiveExactChainBlocker :=
  remainingPositiveExactChainBlocker_of_largeTailDependency S.large

def components
    (S : PositiveChainSmallBlockSource) :
    ExactPositiveChainComponents :=
  PositiveChainComponentClosureW30.components_of_sourceBlocker
    S.sourceBlocker

def componentData
    (S : PositiveChainSmallBlockSource) :
    ExactPositiveChainComponentData :=
  PositiveChainComponentClosureW30.componentDataOfSourceBlocker
    S.sourceBlocker

def componentSource
    (S : PositiveChainSmallBlockSource) :
    PositiveChainComponentSource :=
  PositiveChainComponentsSourceW29.positiveChainComponentSourceOfComponentData
    S.componentData

def positiveExactChainPackage
    (S : PositiveChainSmallBlockSource) :
    PositiveExactChainPackage :=
  PositiveExactLargeTailW27.positiveExactChainPackageOfSmallBlocksAndLargeTail
    S.exactBlocksOneThroughFive
    S.remainingPositiveExactChainBlocker

theorem nonempty_componentData
    (S : PositiveChainSmallBlockSource) :
    Nonempty ExactPositiveChainComponentData :=
  Nonempty.intro S.componentData

theorem nonempty_componentSource
    (S : PositiveChainSmallBlockSource) :
    Nonempty PositiveChainComponentSource :=
  Nonempty.intro S.componentSource

theorem nonempty_positiveExactChainPackage
    (S : PositiveChainSmallBlockSource) :
    Nonempty PositiveExactChainPackage :=
  Nonempty.intro S.positiveExactChainPackage

end PositiveChainSmallBlockSource

def positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (small : SmallLengthExactBlockTargets)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource where
  small := small
  large := large

def positiveChainSmallBlockSourceOfExactFiniteTargetsBelowSix
    (small : ExactFiniteTargetsBelowSix)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (smallLengthExactBlockTargetsOfExactFiniteTargetsBelowSix small)
    large

def positiveChainSmallBlockSourceOfExactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive blocks oneBlock)
    large

def positiveChainSmallBlockSourceOfAllPositiveFields
    (small : AllPositiveFields)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (smallLengthExactBlockTargetsOfAllPositiveFields small)
    large

def positiveChainSmallBlockSourceOfAllPositiveCertificateRows
    (small : AllPositiveCertificateRows)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (smallLengthExactBlockTargetsOfAllPositiveCertificateRows small)
    large

def positiveChainSmallBlockSourceOfConcreteValueMatrixFamily
    (small : ConcreteValueMatrixFamily)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (smallLengthExactBlockTargetsOfConcreteValueMatrixFamily small)
    large

def positiveChainSmallBlockSourceOfCandidateValueMatrixFamily
    (small : CandidateValueMatrixFamily)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (smallLengthExactBlockTargetsOfCandidateValueMatrixFamily small)
    large

def positiveChainSmallBlockSourceOfCandidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (rows : CandidateSmallRowValueRows period)
    (oneBlock : ConcreteOneBlockCertificate orientation)
    (large : RemainingLargeTailDependency) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    (smallLengthExactBlockTargetsOfCandidateSmallRowValueRows rows oneBlock)
    large

theorem nonempty_positiveChainSmallBlockSource_iff_gate :
    Nonempty PositiveChainSmallBlockSource <->
      PositiveChainSmallBlockSourceGate := by
  constructor
  case mp =>
    intro h
    rcases h with ⟨S⟩
    exact And.intro (Nonempty.intro S.small) S.large
  case mpr =>
    intro H
    rcases H.1 with ⟨small⟩
    exact
      Nonempty.intro
        (positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
          small H.2)

theorem positiveChainSmallBlockSourceGate_of_source
    (S : PositiveChainSmallBlockSource) :
    PositiveChainSmallBlockSourceGate :=
  nonempty_positiveChainSmallBlockSource_iff_gate.mp (Nonempty.intro S)

theorem nonempty_componentData_of_positiveChainSmallBlockSourceGate
    (H : PositiveChainSmallBlockSourceGate) :
    Nonempty ExactPositiveChainComponentData := by
  rcases (nonempty_positiveChainSmallBlockSource_iff_gate.mpr H) with ⟨S⟩
  exact S.nonempty_componentData

theorem nonempty_componentSource_of_positiveChainSmallBlockSourceGate
    (H : PositiveChainSmallBlockSourceGate) :
    Nonempty PositiveChainComponentSource := by
  rcases (nonempty_positiveChainSmallBlockSource_iff_gate.mpr H) with ⟨S⟩
  exact S.nonempty_componentSource

/-! ## Source-facing constructors from large-tail packages and fields -/

def positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    small
    (remainingLargeTailDependency_of_largeTailSourcePackage large)

def positiveChainSmallBlockSourceOfSmallTargetsAndLargeClosedPlacementFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeClosedPlacementFieldsFromSix) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    small
    (remainingLargeTailDependency_of_largeClosedPlacementFields large)

def positiveChainSmallBlockSourceOfSmallTargetsAndRawFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    PositiveChainSmallBlockSource :=
  positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    small
    (remainingLargeTailDependency_of_rawFields large)

def componentDataOfSmallTargetsAndLargeTailDependency
    (small : SmallLengthExactBlockTargets)
    (large : RemainingLargeTailDependency) :
    ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    small large).componentData

def componentSourceOfSmallTargetsAndLargeTailDependency
    (small : SmallLengthExactBlockTargets)
    (large : RemainingLargeTailDependency) :
    PositiveChainComponentSource :=
  (positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    small large).componentSource

theorem nonempty_componentData_of_smallTargets_and_largeTailDependency
    (small : SmallLengthExactBlockTargets)
    (large : RemainingLargeTailDependency) :
    Nonempty ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    small large).nonempty_componentData

theorem nonempty_componentData_of_allPositiveCertificateRows_and_largeTailDependency
    (small : AllPositiveCertificateRows)
    (large : RemainingLargeTailDependency) :
    Nonempty ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfAllPositiveCertificateRows
    small large).nonempty_componentData

theorem nonempty_componentData_of_exactBlocksTwoThroughFive_and_largeTailDependency
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation)
    (large : RemainingLargeTailDependency) :
    Nonempty ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfExactBlocksTwoThroughFive
    blocks oneBlock large).nonempty_componentData

theorem nonempty_componentData_of_candidateRows_and_largeTailDependency
    {period : PeriodCandidateFamily}
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (rows : CandidateSmallRowValueRows period)
    (oneBlock : ConcreteOneBlockCertificate orientation)
    (large : RemainingLargeTailDependency) :
    Nonempty ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfCandidateSmallRowValueRows
    rows oneBlock large).nonempty_componentData

theorem nonempty_componentData_of_smallTargets_and_largeTailSource
    (small : SmallLengthExactBlockTargets)
    (large : LargeTailExactSourcePackage) :
    Nonempty ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailSource
    small large).nonempty_componentData

theorem nonempty_componentData_of_smallTargets_and_largeClosedPlacementFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeClosedPlacementFieldsFromSix) :
    Nonempty ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfSmallTargetsAndLargeClosedPlacementFields
    small large).nonempty_componentData

theorem nonempty_componentData_of_smallTargets_and_rawFields
    (small : SmallLengthExactBlockTargets)
    (large : LargeRawClosedPlacementFieldsFromSix) :
    Nonempty ExactPositiveChainComponentData :=
  (positiveChainSmallBlockSourceOfSmallTargetsAndRawFields
    small large).nonempty_componentData

theorem explicitRemainingLargeTailBlockerSummary :
    (PositiveChainSmallBlockSourceGate ->
        Nonempty ExactPositiveChainComponentData) /\
      (RemainingLargeTailDependency <->
        Nonempty LargeTailExactSourcePackage) /\
        (RemainingLargeTailDependency <->
          Nonempty LargeClosedPlacementFieldsFromSix) /\
          (RemainingLargeTailDependency <->
            Nonempty LargeRawClosedPlacementFieldsFromSix) :=
  And.intro nonempty_componentData_of_positiveChainSmallBlockSourceGate
    (And.intro remainingLargeTailDependency_iff_largeTailSourcePackage
      (And.intro remainingLargeTailDependency_iff_largeClosedPlacementFields
        remainingLargeTailDependency_iff_rawFields))

end

end PositiveChainSmallBlocksW31
end PachToth

namespace Verified

abbrev PachTothW31SmallLengthExactBlockTargets : Prop :=
  PachToth.PositiveChainSmallBlocksW31.SmallLengthExactBlockTargets

abbrev PachTothW31RemainingLargeTailDependency : Prop :=
  PachToth.PositiveChainSmallBlocksW31.RemainingLargeTailDependency

abbrev PachTothW31PositiveChainSmallBlockSource : Type :=
  PachToth.PositiveChainSmallBlocksW31.PositiveChainSmallBlockSource

abbrev PachTothW31PositiveChainSmallBlockSourceGate : Prop :=
  PachToth.PositiveChainSmallBlocksW31.PositiveChainSmallBlockSourceGate

abbrev PachTothW31ExactPositiveChainComponentData : Type :=
  PachToth.PositiveChainSmallBlocksW31.ExactPositiveChainComponentData

open PachToth.PositiveChainSmallBlocksW31

theorem pachtoth_w31_nonempty_positiveChainSmallBlockSource_iff_gate :
    Nonempty PachTothW31PositiveChainSmallBlockSource <->
      PachTothW31PositiveChainSmallBlockSourceGate :=
  nonempty_positiveChainSmallBlockSource_iff_gate

theorem pachtoth_w31_nonempty_componentData_of_sourceGate
    (H : PachTothW31PositiveChainSmallBlockSourceGate) :
    Nonempty PachTothW31ExactPositiveChainComponentData :=
  nonempty_componentData_of_positiveChainSmallBlockSourceGate H

theorem pachtoth_w31_remainingLargeTailDependency_iff_largeTailSourcePackage :
    PachTothW31RemainingLargeTailDependency <->
      Nonempty PachToth.PositiveChainSmallBlocksW31.LargeTailExactSourcePackage :=
  remainingLargeTailDependency_iff_largeTailSourcePackage

theorem pachtoth_w31_remainingLargeTailDependency_iff_largeClosedPlacementFields :
    PachTothW31RemainingLargeTailDependency <->
      Nonempty PachToth.PositiveChainSmallBlocksW31.LargeClosedPlacementFieldsFromSix :=
  remainingLargeTailDependency_iff_largeClosedPlacementFields

theorem pachtoth_w31_explicitRemainingLargeTailBlockerSummary :
    (PachTothW31PositiveChainSmallBlockSourceGate ->
        Nonempty PachTothW31ExactPositiveChainComponentData) /\
      (PachTothW31RemainingLargeTailDependency <->
        Nonempty PachToth.PositiveChainSmallBlocksW31.LargeTailExactSourcePackage) /\
        (PachTothW31RemainingLargeTailDependency <->
          Nonempty PachToth.PositiveChainSmallBlocksW31.LargeClosedPlacementFieldsFromSix) /\
          (PachTothW31RemainingLargeTailDependency <->
            Nonempty PachToth.PositiveChainSmallBlocksW31.LargeRawClosedPlacementFieldsFromSix) :=
  explicitRemainingLargeTailBlockerSummary

end Verified
end ErdosProblems1066
