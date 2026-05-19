import ErdosProblems1066.PachToth.PositiveChainSmallBlocksW31
import ErdosProblems1066.PachToth.LargeTailRowsRealizationW31

set_option autoImplicit false

/-!
# W32 positive-chain large-tail assembly

This leaf replaces the W31 large-tail dependency in the positive-chain
small-block gate by the row-realized closed-placement surface from W31.  The
source package below stores only exact small-block evidence and actual
closed-placement rows for every tail block count from six onward.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveChainLargeTailAssemblyW32

noncomputable section

/-! ## Source vocabulary -/

abbrev SmallLengthExactBlockTargets : Prop :=
  PositiveChainSmallBlocksW31.SmallLengthExactBlockTargets

abbrev ExactFiniteTargetsBelowSix : Prop :=
  PositiveChainSmallBlocksW31.ExactFiniteTargetsBelowSix

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveChainSmallBlocksW31.ExactBlocksOneThroughFive

abbrev AllPositiveCertificateRows : Type :=
  PositiveChainSmallBlocksW31.AllPositiveCertificateRows

abbrev RemainingLargeTailDependency : Prop :=
  PositiveChainSmallBlocksW31.RemainingLargeTailDependency

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveChainSmallBlocksW31.RemainingPositiveExactChainBlocker

abbrev PositiveChainSmallBlockSource : Type :=
  PositiveChainSmallBlocksW31.PositiveChainSmallBlockSource

abbrev PositiveChainSmallBlockSourceGate : Prop :=
  PositiveChainSmallBlocksW31.PositiveChainSmallBlockSourceGate

abbrev ExactPositiveChainComponents : Prop :=
  PositiveChainSmallBlocksW31.ExactPositiveChainComponents

abbrev ExactPositiveChainComponentData : Type :=
  PositiveChainSmallBlocksW31.ExactPositiveChainComponentData

abbrev PositiveChainComponentSource : Type :=
  PositiveChainSmallBlocksW31.PositiveChainComponentSource

abbrev PositiveExactChainPackage : Type :=
  PositiveChainSmallBlocksW31.PositiveExactChainPackage

abbrev LargeTailClosedPlacementRows : Type :=
  LargeTailRowsRealizationW31.LargeTailClosedPlacementRows

abbrev LargeTailClosedPlacementRowsGate : Prop :=
  Nonempty LargeTailClosedPlacementRows

abbrev LargeTailCertificateRows : Type :=
  LargeTailRowsRealizationW31.LargeTailCertificateRows

abbrev LargeRawClosedPlacementFieldsFromSix : Type :=
  LargeTailRowsRealizationW31.LargeRawClosedPlacementFieldsFromSix

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeTailRowsRealizationW31.LargeClosedPlacementFieldsFromSix

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailRowsRealizationW31.LargeTailExactSourcePackage

abbrev PositiveChainLargeTailRowsGate : Prop :=
  Nonempty SmallLengthExactBlockTargets /\ LargeTailClosedPlacementRowsGate

/-! ## Large-tail rows feed the W31 large-tail dependency -/

def certificateRowsOfClosedPlacementRows
    (rows : LargeTailClosedPlacementRows) :
    LargeTailCertificateRows :=
  LargeTailRowsRealizationW31.certificateRowsOfClosedPlacementRows rows

def rawFieldsOfClosedPlacementRows
    (rows : LargeTailClosedPlacementRows) :
    LargeRawClosedPlacementFieldsFromSix :=
  LargeTailRowsRealizationW31.rawFieldsOfClosedPlacementRows rows

def largeClosedPlacementFieldsFromSixOfClosedPlacementRows
    (rows : LargeTailClosedPlacementRows) :
    LargeClosedPlacementFieldsFromSix :=
  LargeTailRowsRealizationW31.largeClosedPlacementFieldsFromSixOfClosedPlacementRows
    rows

def largeTailExactSourcePackageOfClosedPlacementRows
    (rows : LargeTailClosedPlacementRows) :
    LargeTailExactSourcePackage :=
  LargeTailRowsRealizationW31.largeTailExactSourcePackageOfClosedPlacementRows
    rows

theorem largeTailClosedPlacementRows_iff_certificateRows :
    LargeTailClosedPlacementRowsGate <->
      Nonempty LargeTailCertificateRows :=
  LargeTailRowsRealizationW31.nonempty_closedPlacementRows_iff_certificateRows

theorem largeTailClosedPlacementRows_iff_rawFieldsFromSix :
    LargeTailClosedPlacementRowsGate <->
      Nonempty LargeRawClosedPlacementFieldsFromSix :=
  LargeTailRowsRealizationW31.nonempty_closedPlacementRows_iff_rawFieldsFromSix

theorem largeTailClosedPlacementRows_iff_largeClosedPlacementFieldsFromSix :
    LargeTailClosedPlacementRowsGate <->
      Nonempty LargeClosedPlacementFieldsFromSix :=
  LargeTailRowsRealizationW31.nonempty_closedPlacementRows_iff_largeClosedPlacementFieldsFromSix

theorem remainingLargeTailDependency_iff_closedPlacementRows :
    RemainingLargeTailDependency <-> LargeTailClosedPlacementRowsGate :=
  LargeTailRowsRealizationW31.remainingLargeTailExactSourceBlocker_iff_closedPlacementRows

theorem remainingLargeTailDependency_of_closedPlacementRows
    (rows : LargeTailClosedPlacementRows) :
    RemainingLargeTailDependency :=
  LargeTailRowsRealizationW31.remainingLargeTailExactSourceBlocker_of_closedPlacementRows
    rows

theorem remainingLargeTailDependency_of_nonempty_closedPlacementRows
    (rows : LargeTailClosedPlacementRowsGate) :
    RemainingLargeTailDependency :=
  remainingLargeTailDependency_iff_closedPlacementRows.mpr rows

theorem remainingPositiveExactChainBlocker_of_closedPlacementRows
    (rows : LargeTailClosedPlacementRows) :
    RemainingPositiveExactChainBlocker :=
  LargeTailRowsRealizationW31.remainingPositiveExactChainBlocker_of_closedPlacementRows
    rows

theorem remainingPositiveExactChainBlocker_of_nonempty_closedPlacementRows
    (rows : LargeTailClosedPlacementRowsGate) :
    RemainingPositiveExactChainBlocker :=
  LargeTailRowsRealizationW31.remainingPositiveExactChainBlocker_of_nonempty_closedPlacementRows
    rows

/-! ## Bundled exact small blocks plus realized large-tail rows -/

structure PositiveChainLargeTailSourcePackage where
  small : SmallLengthExactBlockTargets
  rows : LargeTailClosedPlacementRows

namespace PositiveChainLargeTailSourcePackage

def exactBlocksOneThroughFive
    (P : PositiveChainLargeTailSourcePackage) :
    ExactBlocksOneThroughFive :=
  PositiveChainSmallBlocksW31.exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    P.small

def largeTailDependency
    (P : PositiveChainLargeTailSourcePackage) :
    RemainingLargeTailDependency :=
  remainingLargeTailDependency_of_closedPlacementRows P.rows

def largeTailCertificateRows
    (P : PositiveChainLargeTailSourcePackage) :
    LargeTailCertificateRows :=
  certificateRowsOfClosedPlacementRows P.rows

def largeRawClosedPlacementFieldsFromSix
    (P : PositiveChainLargeTailSourcePackage) :
    LargeRawClosedPlacementFieldsFromSix :=
  rawFieldsOfClosedPlacementRows P.rows

def largeClosedPlacementFieldsFromSix
    (P : PositiveChainLargeTailSourcePackage) :
    LargeClosedPlacementFieldsFromSix :=
  largeClosedPlacementFieldsFromSixOfClosedPlacementRows P.rows

def largeTailExactSourcePackage
    (P : PositiveChainLargeTailSourcePackage) :
    LargeTailExactSourcePackage :=
  largeTailExactSourcePackageOfClosedPlacementRows P.rows

def remainingPositiveExactChainBlocker
    (P : PositiveChainLargeTailSourcePackage) :
    RemainingPositiveExactChainBlocker :=
  remainingPositiveExactChainBlocker_of_closedPlacementRows P.rows

def smallBlockSource
    (P : PositiveChainLargeTailSourcePackage) :
    PositiveChainSmallBlockSource :=
  PositiveChainSmallBlocksW31.positiveChainSmallBlockSourceOfSmallTargetsAndLargeTailDependency
    P.small P.largeTailDependency

def components
    (P : PositiveChainLargeTailSourcePackage) :
    ExactPositiveChainComponents :=
  P.smallBlockSource.components

def componentData
    (P : PositiveChainLargeTailSourcePackage) :
    ExactPositiveChainComponentData :=
  P.smallBlockSource.componentData

def componentSource
    (P : PositiveChainLargeTailSourcePackage) :
    PositiveChainComponentSource :=
  P.smallBlockSource.componentSource

def positiveExactChainPackage
    (P : PositiveChainLargeTailSourcePackage) :
    PositiveExactChainPackage :=
  P.smallBlockSource.positiveExactChainPackage

theorem sourceGate
    (P : PositiveChainLargeTailSourcePackage) :
    PositiveChainSmallBlockSourceGate :=
  PositiveChainSmallBlocksW31.positiveChainSmallBlockSourceGate_of_source
    P.smallBlockSource

theorem nonempty_componentData
    (P : PositiveChainLargeTailSourcePackage) :
    Nonempty ExactPositiveChainComponentData :=
  Nonempty.intro P.componentData

theorem nonempty_componentSource
    (P : PositiveChainLargeTailSourcePackage) :
    Nonempty PositiveChainComponentSource :=
  Nonempty.intro P.componentSource

theorem nonempty_positiveExactChainPackage
    (P : PositiveChainLargeTailSourcePackage) :
    Nonempty PositiveExactChainPackage :=
  Nonempty.intro P.positiveExactChainPackage

theorem nonempty_largeTailCertificateRows
    (P : PositiveChainLargeTailSourcePackage) :
    Nonempty LargeTailCertificateRows :=
  Nonempty.intro P.largeTailCertificateRows

end PositiveChainLargeTailSourcePackage

def sourcePackageOfSmallTargetsAndClosedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    PositiveChainLargeTailSourcePackage where
  small := small
  rows := rows

def sourcePackageOfExactFiniteTargetsBelowSixAndClosedPlacementRows
    (small : ExactFiniteTargetsBelowSix)
    (rows : LargeTailClosedPlacementRows) :
    PositiveChainLargeTailSourcePackage :=
  sourcePackageOfSmallTargetsAndClosedPlacementRows
    (PositiveChainSmallBlocksW31.smallLengthExactBlockTargetsOfExactFiniteTargetsBelowSix
      small)
    rows

def sourcePackageOfAllPositiveCertificateRowsAndClosedPlacementRows
    (small : AllPositiveCertificateRows)
    (rows : LargeTailClosedPlacementRows) :
    PositiveChainLargeTailSourcePackage :=
  sourcePackageOfSmallTargetsAndClosedPlacementRows
    (PositiveChainSmallBlocksW31.smallLengthExactBlockTargetsOfAllPositiveCertificateRows
      small)
    rows

def positiveChainSmallBlockSourceOfSmallTargetsAndClosedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    PositiveChainSmallBlockSource :=
  (sourcePackageOfSmallTargetsAndClosedPlacementRows small rows).smallBlockSource

def componentDataOfSmallTargetsAndClosedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    ExactPositiveChainComponentData :=
  (sourcePackageOfSmallTargetsAndClosedPlacementRows small rows).componentData

def componentSourceOfSmallTargetsAndClosedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    PositiveChainComponentSource :=
  (sourcePackageOfSmallTargetsAndClosedPlacementRows small rows).componentSource

def positiveExactChainPackageOfSmallTargetsAndClosedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    PositiveExactChainPackage :=
  (sourcePackageOfSmallTargetsAndClosedPlacementRows small rows).positiveExactChainPackage

/-! ## Exact reductions for the W32 source gate -/

theorem nonempty_sourcePackage_iff_largeTailRowsGate :
    Nonempty PositiveChainLargeTailSourcePackage <->
      PositiveChainLargeTailRowsGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact And.intro (Nonempty.intro P.small) (Nonempty.intro P.rows)
  case mpr =>
    intro H
    cases H.1 with
    | intro small =>
        cases H.2 with
        | intro rows =>
            exact
              Nonempty.intro
                (sourcePackageOfSmallTargetsAndClosedPlacementRows small rows)

theorem positiveChainSmallBlockSourceGate_iff_largeTailRowsGate :
    PositiveChainSmallBlockSourceGate <-> PositiveChainLargeTailRowsGate := by
  constructor
  case mp =>
    intro H
    exact
      And.intro H.1
        (remainingLargeTailDependency_iff_closedPlacementRows.mp H.2)
  case mpr =>
    intro H
    exact
      And.intro H.1
        (remainingLargeTailDependency_of_nonempty_closedPlacementRows H.2)

theorem positiveChainSmallBlockSourceGate_of_sourcePackage
    (P : PositiveChainLargeTailSourcePackage) :
    PositiveChainSmallBlockSourceGate :=
  positiveChainSmallBlockSourceGate_iff_largeTailRowsGate.mpr
    (And.intro (Nonempty.intro P.small) (Nonempty.intro P.rows))

theorem nonempty_positiveChainSmallBlockSource_of_largeTailRowsGate
    (H : PositiveChainLargeTailRowsGate) :
    Nonempty PositiveChainSmallBlockSource :=
  PositiveChainSmallBlocksW31.nonempty_positiveChainSmallBlockSource_iff_gate.mpr
    (positiveChainSmallBlockSourceGate_iff_largeTailRowsGate.mpr H)

theorem nonempty_componentData_of_largeTailRowsGate
    (H : PositiveChainLargeTailRowsGate) :
    Nonempty ExactPositiveChainComponentData :=
  PositiveChainSmallBlocksW31.nonempty_componentData_of_positiveChainSmallBlockSourceGate
    (positiveChainSmallBlockSourceGate_iff_largeTailRowsGate.mpr H)

theorem nonempty_componentSource_of_largeTailRowsGate
    (H : PositiveChainLargeTailRowsGate) :
    Nonempty PositiveChainComponentSource :=
  PositiveChainSmallBlocksW31.nonempty_componentSource_of_positiveChainSmallBlockSourceGate
    (positiveChainSmallBlockSourceGate_iff_largeTailRowsGate.mpr H)

theorem nonempty_positiveExactChainPackage_of_largeTailRowsGate
    (H : PositiveChainLargeTailRowsGate) :
    Nonempty PositiveExactChainPackage := by
  cases H.1 with
  | intro small =>
      cases H.2 with
      | intro rows =>
          exact
            (sourcePackageOfSmallTargetsAndClosedPlacementRows
              small rows).nonempty_positiveExactChainPackage

theorem nonempty_largeTailCertificateRows_of_largeTailRowsGate
    (H : PositiveChainLargeTailRowsGate) :
    Nonempty LargeTailCertificateRows :=
  largeTailClosedPlacementRows_iff_certificateRows.mp H.2

theorem exactPositiveChainComponents_of_smallTargets_and_closedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    ExactPositiveChainComponents :=
  (sourcePackageOfSmallTargetsAndClosedPlacementRows small rows).components

theorem nonempty_componentData_of_smallTargets_and_closedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    Nonempty ExactPositiveChainComponentData :=
  (sourcePackageOfSmallTargetsAndClosedPlacementRows
    small rows).nonempty_componentData

theorem nonempty_positiveExactChainPackage_of_smallTargets_and_closedPlacementRows
    (small : SmallLengthExactBlockTargets)
    (rows : LargeTailClosedPlacementRows) :
    Nonempty PositiveExactChainPackage :=
  (sourcePackageOfSmallTargetsAndClosedPlacementRows
    small rows).nonempty_positiveExactChainPackage

structure PositiveChainLargeTailAssemblyCertificate : Prop where
  sourcePackageIffRowsGate :
    Nonempty PositiveChainLargeTailSourcePackage <->
      PositiveChainLargeTailRowsGate
  smallBlockGateIffRowsGate :
    PositiveChainSmallBlockSourceGate <->
      PositiveChainLargeTailRowsGate
  rowsFeedLargeTailDependency :
    LargeTailClosedPlacementRowsGate -> RemainingLargeTailDependency
  rowsGateFeedsComponentData :
    PositiveChainLargeTailRowsGate -> Nonempty ExactPositiveChainComponentData
  rowsGateFeedsComponentSource :
    PositiveChainLargeTailRowsGate -> Nonempty PositiveChainComponentSource
  rowsGateFeedsPositiveExactChainPackage :
    PositiveChainLargeTailRowsGate -> Nonempty PositiveExactChainPackage
  rowsGateFeedsCertificateRows :
    PositiveChainLargeTailRowsGate -> Nonempty LargeTailCertificateRows

theorem positiveChainLargeTailAssemblyCertificate :
    PositiveChainLargeTailAssemblyCertificate where
  sourcePackageIffRowsGate := nonempty_sourcePackage_iff_largeTailRowsGate
  smallBlockGateIffRowsGate :=
    positiveChainSmallBlockSourceGate_iff_largeTailRowsGate
  rowsFeedLargeTailDependency :=
    remainingLargeTailDependency_of_nonempty_closedPlacementRows
  rowsGateFeedsComponentData :=
    nonempty_componentData_of_largeTailRowsGate
  rowsGateFeedsComponentSource :=
    nonempty_componentSource_of_largeTailRowsGate
  rowsGateFeedsPositiveExactChainPackage :=
    nonempty_positiveExactChainPackage_of_largeTailRowsGate
  rowsGateFeedsCertificateRows :=
    nonempty_largeTailCertificateRows_of_largeTailRowsGate

end

end PositiveChainLargeTailAssemblyW32
end PachToth

namespace Verified

abbrev PachTothW32PositiveChainLargeTailSourcePackage : Type :=
  PachToth.PositiveChainLargeTailAssemblyW32.PositiveChainLargeTailSourcePackage

abbrev PachTothW32PositiveChainLargeTailRowsGate : Prop :=
  PachToth.PositiveChainLargeTailAssemblyW32.PositiveChainLargeTailRowsGate

abbrev PachTothW32PositiveChainSmallBlockSourceGate : Prop :=
  PachToth.PositiveChainLargeTailAssemblyW32.PositiveChainSmallBlockSourceGate

abbrev PachTothW32ExactPositiveChainComponentData : Type :=
  PachToth.PositiveChainLargeTailAssemblyW32.ExactPositiveChainComponentData

abbrev PachTothW32PositiveExactChainPackage : Type :=
  PachToth.PositiveChainLargeTailAssemblyW32.PositiveExactChainPackage

abbrev PachTothW32PositiveChainLargeTailClosedPlacementRows : Type :=
  PachToth.PositiveChainLargeTailAssemblyW32.LargeTailClosedPlacementRows

abbrev PachTothW32LargeTailCertificateRows : Type :=
  PachToth.PositiveChainLargeTailAssemblyW32.LargeTailCertificateRows

abbrev PachTothW32AssemblyCertificate : Prop :=
  PachToth.PositiveChainLargeTailAssemblyW32.PositiveChainLargeTailAssemblyCertificate

open PachToth.PositiveChainLargeTailAssemblyW32

theorem pachtoth_w32_sourcePackage_iff_largeTailRowsGate :
    Nonempty PachTothW32PositiveChainLargeTailSourcePackage <->
      PachTothW32PositiveChainLargeTailRowsGate :=
  nonempty_sourcePackage_iff_largeTailRowsGate

theorem pachtoth_w32_smallBlockSourceGate_iff_largeTailRowsGate :
    PachTothW32PositiveChainSmallBlockSourceGate <->
      PachTothW32PositiveChainLargeTailRowsGate :=
  positiveChainSmallBlockSourceGate_iff_largeTailRowsGate

theorem pachtoth_w32_nonempty_componentData_of_largeTailRowsGate
    (H : PachTothW32PositiveChainLargeTailRowsGate) :
    Nonempty PachTothW32ExactPositiveChainComponentData :=
  nonempty_componentData_of_largeTailRowsGate H

theorem pachtoth_w32_nonempty_positiveExactChainPackage_of_largeTailRowsGate
    (H : PachTothW32PositiveChainLargeTailRowsGate) :
    Nonempty PachTothW32PositiveExactChainPackage :=
  nonempty_positiveExactChainPackage_of_largeTailRowsGate H

theorem pachtoth_w32_largeTailRows_iff_certificateRows :
    Nonempty PachTothW32PositiveChainLargeTailClosedPlacementRows <->
      Nonempty PachTothW32LargeTailCertificateRows :=
  largeTailClosedPlacementRows_iff_certificateRows

theorem pachtoth_w32_assemblyCertificate :
    PachTothW32AssemblyCertificate :=
  positiveChainLargeTailAssemblyCertificate

end Verified
end ErdosProblems1066
