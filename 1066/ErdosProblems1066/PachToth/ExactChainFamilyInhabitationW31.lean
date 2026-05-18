import ErdosProblems1066.PachToth.ExactChainFamilyClosureW30
import ErdosProblems1066.PachToth.ExactChainFamilySourceW29
import ErdosProblems1066.PachToth.PositiveExactChainPackageW26
import ErdosProblems1066.PachToth.PositiveExactChainAssemblyW27
import ErdosProblems1066.PachToth.RemainderExactDependencyClosureW30

set_option autoImplicit false

/-!
# W31 exact-chain family source inhabitation

This leaf is an adapter layer around the W29/W30 exact-chain family source
surface.  It keeps the direction source-facing: actual exact-chain source
packages, exact closed-chain packages, and closed-placement certificate
families can be unpacked into the W30 dependency gates, but no endpoint target
is used to manufacture source evidence.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactChainFamilyInhabitationW31

noncomputable section

/-! ## Source vocabulary -/

abbrev ExactChainUpper (k : Nat) : Type :=
  ExactChainFamilySourceW29.ExactChainUpper k

abbrev ExactChainFamily : Type :=
  ExactChainFamilySourceW29.ExactChainFamily

abbrev ExactChainFamilySourcePackage : Type :=
  ExactChainFamilySourceW29.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourcePackageGate : Prop :=
  Nonempty ExactChainFamilySourcePackage

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev ExactClosedChainPackage : Type :=
  ExactChainFamilySourceW29.ExactClosedChainPackage

abbrev MinimalExactSourcePackage : Type :=
  PositiveExactChainAssemblyW27.MinimalExactSourcePackage

abbrev ExposedExactChainSource : Type :=
  PositiveExactChainAssemblyW27.ExposedExactChainSource

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

/-! ## W30 dependency vocabulary -/

abbrev ClosureRemainingExactChainFamilyDependency : Prop :=
  ExactChainFamilyClosureW30.RemainingExactChainFamilyDependency

abbrev RemainderExactChainFamilySourceGate : Prop :=
  RemainderExactDependencyClosureW30.ExactChainFamilySourceGate

abbrev RemainderRemainingExactChainFamilyDependency : Prop :=
  RemainderExactDependencyClosureW30.RemainingExactChainFamilyDependency

abbrev ExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.ExactSourcePackageGate

abbrev RemainingSplitBlocker : Prop :=
  RemainderExactDependencyClosureW30.RemainingSplitBlocker

abbrev RemainderExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.RemainderExactSourcePackageGate

abbrev RemainderSplitExactSourcePackageGate : Prop :=
  RemainderExactDependencyClosureW30.RemainderSplitExactSourcePackageGate

/-! ## Direct source-package adapters -/

def sourcePackageOfExactChainFamily
    (H : ExactChainFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfExactChainFamily H

def sourcePackageOfPositiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfPositiveExactChainPackage P

def sourcePackageOfExactClosedChainPackage
    (P : ExactClosedChainPackage) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfExactClosedChainPackage P

def positiveExactChainPackageOfMinimalExactSource
    (P : MinimalExactSourcePackage) :
    PositiveExactChainPackage :=
  PositiveExactChainAssemblyW27.packageOfMinimalExactSource P

def sourcePackageOfMinimalExactSource
    (P : MinimalExactSourcePackage) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfPositiveExactChainPackage
    (positiveExactChainPackageOfMinimalExactSource P)

def sourcePackageOfExposedExactChainSource
    (S : ExposedExactChainSource) :
    ExactChainFamilySourcePackage :=
  sourcePackageOfPositiveExactChainPackage
    (PositiveExactChainAssemblyW27.packageOfExposedExactChainSource S)

@[simp]
theorem sourcePackageOfExactChainFamily_exactChain
    (H : ExactChainFamily) :
    (sourcePackageOfExactChainFamily H).exactChain = H :=
  rfl

@[simp]
theorem sourcePackageOfPositiveExactChainPackage_exactChain
    (P : PositiveExactChainPackage) :
    (sourcePackageOfPositiveExactChainPackage P).exactChain =
      P.exactChain :=
  rfl

@[simp]
theorem sourcePackageOfExactClosedChainPackage_exactChain
    (P : ExactClosedChainPackage) :
    (sourcePackageOfExactClosedChainPackage P).exactChain = P.chain :=
  rfl

/-! ## Closed-placement certificate adapters -/

structure ClosedPlacementCertificateFamilySource where
  certificates : ExplicitClosedPlacementCertificateFamily

namespace ClosedPlacementCertificateFamilySource

def toExactChainFamilySourcePackage
    (S : ClosedPlacementCertificateFamilySource) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfExplicitClosedPlacementCertificateFamily
    S.certificates

def toPositiveExactChainPackage
    (S : ClosedPlacementCertificateFamilySource) :
    PositiveExactChainPackage :=
  S.toExactChainFamilySourcePackage.toPositiveExactChainPackage

def toExactChainFamily
    (S : ClosedPlacementCertificateFamilySource) :
    ExactChainFamily :=
  S.toExactChainFamilySourcePackage.exactChain

end ClosedPlacementCertificateFamilySource

def closedPlacementCertificateFamilySourceOfCertificates
    (H : ExplicitClosedPlacementCertificateFamily) :
    ClosedPlacementCertificateFamilySource where
  certificates := H

theorem nonempty_closedPlacementCertificateFamilySource_iff_certificates :
    Nonempty ClosedPlacementCertificateFamilySource <->
      Nonempty ExplicitClosedPlacementCertificateFamily := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.certificates
  case mpr =>
    intro h
    cases h with
    | intro H =>
        exact
          Nonempty.intro
            (closedPlacementCertificateFamilySourceOfCertificates H)

def sourcePackageOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfClosedPlacementFamily H

def sourcePackageOfClosedPlacementPackage
    (P : ClosedPlacementPackage) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfClosedPlacementPackage P

def sourcePackageOfExplicitClosedPlacementCertificateFamily
    (H : ExplicitClosedPlacementCertificateFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfExplicitClosedPlacementCertificateFamily
    H

def sourcePackageOfClosedPlacementCertificateFamilySource
    (S : ClosedPlacementCertificateFamilySource) :
    ExactChainFamilySourcePackage :=
  S.toExactChainFamilySourcePackage

theorem sourceGate_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro (sourcePackageOfClosedPlacementFamily H)

theorem sourceGate_of_closedPlacementPackage
    (P : ClosedPlacementPackage) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro (sourcePackageOfClosedPlacementPackage P)

theorem sourceGate_of_explicitClosedPlacementCertificateFamily
    (H : ExplicitClosedPlacementCertificateFamily) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro
    (sourcePackageOfExplicitClosedPlacementCertificateFamily H)

theorem sourceGate_of_closedPlacementCertificateFamilySource
    (S : ClosedPlacementCertificateFamilySource) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro
    (sourcePackageOfClosedPlacementCertificateFamilySource S)

theorem sourceGate_of_closedPlacementFamily_nonempty
    (H : Nonempty ClosedPlacementFamily) :
    ExactChainFamilySourcePackageGate := by
  cases H with
  | intro F =>
      exact sourceGate_of_closedPlacementFamily F

theorem sourceGate_of_closedPlacementPackage_nonempty
    (H : Nonempty ClosedPlacementPackage) :
    ExactChainFamilySourcePackageGate := by
  cases H with
  | intro P =>
      exact sourceGate_of_closedPlacementPackage P

theorem sourceGate_of_explicitClosedPlacementCertificateFamily_nonempty
    (H : Nonempty ExplicitClosedPlacementCertificateFamily) :
    ExactChainFamilySourcePackageGate := by
  cases H with
  | intro F =>
      exact sourceGate_of_explicitClosedPlacementCertificateFamily F

theorem sourceGate_of_closedPlacementCertificateFamilySource_nonempty
    (H : Nonempty ClosedPlacementCertificateFamilySource) :
    ExactChainFamilySourcePackageGate := by
  cases H with
  | intro S =>
      exact sourceGate_of_closedPlacementCertificateFamilySource S

/-! ## Small-block plus large-tail adapters -/

def sourcePackageOfSmallAndLargeExactBlockTargets
    (D : SmallAndLargeExactBlockTargets) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfSmallAndLargeExactBlockTargets D

def sourcePackageOfSmallBlocksAndLargeTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfSmallBlocksAndLargeTail
    small large

def sourcePackageOfLargeTailSourceAndSmallBlocks
    (P : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilyClosureW30.sourcePackageOfLargeTailSourceAndSmallBlocks
    P small

theorem sourceGate_of_smallBlocks_and_largeTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro (sourcePackageOfSmallBlocksAndLargeTail small large)

theorem sourceGate_of_largeTailSource_and_smallBlocks
    (P : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    ExactChainFamilySourcePackageGate :=
  Nonempty.intro (sourcePackageOfLargeTailSourceAndSmallBlocks P small)

theorem sourceGate_of_largeTailSource_nonempty_and_smallBlocks
    (Hlarge : Nonempty LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    ExactChainFamilySourcePackageGate := by
  cases Hlarge with
  | intro P =>
      exact sourceGate_of_largeTailSource_and_smallBlocks P small

/-! ## Exact source nonempty equivalences -/

theorem sourceGate_iff_positiveExactChainPackage :
    ExactChainFamilySourcePackageGate <->
      Nonempty PositiveExactChainPackage :=
  ExactChainFamilySourceW29.nonempty_package_iff_positiveExactChainPackage

theorem sourceGate_iff_exactClosedChainPackage :
    ExactChainFamilySourcePackageGate <->
      Nonempty ExactClosedChainPackage :=
  ExactChainFamilySourceW29.nonempty_package_iff_exactClosedChainPackage

theorem sourceGate_iff_minimalExactSource :
    ExactChainFamilySourcePackageGate <->
      Nonempty MinimalExactSourcePackage := by
  exact
    Iff.trans sourceGate_iff_positiveExactChainPackage
      PositiveExactChainAssemblyW27.nonempty_package_iff_minimalExactSource

theorem sourceGate_iff_exposedExactChainSource :
    ExactChainFamilySourcePackageGate <->
      Nonempty ExposedExactChainSource := by
  exact
    Iff.trans sourceGate_iff_positiveExactChainPackage
      PositiveExactChainAssemblyW27.nonempty_package_iff_exposedExactChainSource

theorem sourceGate_iff_smallBlocks_and_largeTail :
    ExactChainFamilySourcePackageGate <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix :=
  ExactChainFamilySourceW29.nonempty_package_iff_smallBlocks_and_largeTail

/-! ## W30 dependency gates from source inhabitants -/

theorem closureDependency_of_sourcePackage
    (P : ExactChainFamilySourcePackage) :
    ClosureRemainingExactChainFamilyDependency :=
  ExactChainFamilyClosureW30.remainingDependency_of_sourcePackage P

theorem closureDependency_of_sourceGate
    (H : ExactChainFamilySourcePackageGate) :
    ClosureRemainingExactChainFamilyDependency :=
  ExactChainFamilyClosureW30.remainingDependency_of_sourcePackage_nonempty H

theorem sourceGate_of_closureDependency
    (H : ClosureRemainingExactChainFamilyDependency) :
    ExactChainFamilySourcePackageGate :=
  ExactChainFamilyClosureW30.sourcePackage_nonempty_of_remainingDependency
    H

theorem sourceGate_iff_closureDependency :
    ExactChainFamilySourcePackageGate <->
      ClosureRemainingExactChainFamilyDependency :=
  ExactChainFamilyClosureW30.remainingDependency_iff_sourcePackage_nonempty.symm

theorem closureDependency_iff_sourceGate :
    ClosureRemainingExactChainFamilyDependency <->
      ExactChainFamilySourcePackageGate :=
  ExactChainFamilyClosureW30.remainingDependency_iff_sourcePackage_nonempty

theorem remainderSourceGate_of_sourceGate
    (H : ExactChainFamilySourcePackageGate) :
    RemainderExactChainFamilySourceGate :=
  H

theorem sourceGate_of_remainderSourceGate
    (H : RemainderExactChainFamilySourceGate) :
    ExactChainFamilySourcePackageGate :=
  H

theorem sourceGate_iff_remainderSourceGate :
    ExactChainFamilySourcePackageGate <->
      RemainderExactChainFamilySourceGate :=
  Iff.rfl

theorem remainderDependency_of_sourceGate
    (H : ExactChainFamilySourcePackageGate) :
    RemainderRemainingExactChainFamilyDependency :=
  RemainderExactDependencyClosureW30.remainingExactChainFamilyDependency_of_sourceGate
    H

theorem sourceGate_iff_remainderDependency :
    ExactChainFamilySourcePackageGate <->
      RemainderRemainingExactChainFamilyDependency :=
  RemainderExactDependencyClosureW30.sourceGate_iff_remainingExactChainFamilyDependency

theorem sourceGate_iff_exactSourcePackageGate :
    ExactChainFamilySourcePackageGate <-> ExactSourcePackageGate :=
  RemainderExactDependencyClosureW30.sourceGate_iff_exactSourcePackageGate

theorem sourceGate_iff_remainingSplitBlocker :
    ExactChainFamilySourcePackageGate <-> RemainingSplitBlocker :=
  RemainderExactDependencyClosureW30.sourceGate_iff_remainingSplitBlocker

theorem sourceGate_iff_remainderExactSourcePackageGate :
    ExactChainFamilySourcePackageGate <->
      RemainderExactSourcePackageGate :=
  RemainderExactDependencyClosureW30.sourceGate_iff_remainderExactSourcePackageGate

theorem remainderSplitExactSourcePackageGate_of_sourceGate
    (H : ExactChainFamilySourcePackageGate) :
    RemainderSplitExactSourcePackageGate :=
  RemainderExactDependencyClosureW30.remainderSplitExactSourcePackageGate_of_sourceGate
    H

theorem closureDependency_of_closedPlacementCertificateFamilySource
    (S : ClosedPlacementCertificateFamilySource) :
    ClosureRemainingExactChainFamilyDependency :=
  closureDependency_of_sourceGate
    (sourceGate_of_closedPlacementCertificateFamilySource S)

theorem remainderDependency_of_closedPlacementCertificateFamilySource
    (S : ClosedPlacementCertificateFamilySource) :
    RemainderRemainingExactChainFamilyDependency :=
  remainderDependency_of_sourceGate
    (sourceGate_of_closedPlacementCertificateFamilySource S)

/-! ## Compact adaptor certificate -/

structure ExactChainFamilySourceInhabitationCertificate : Prop where
  source_iff_positive :
    ExactChainFamilySourcePackageGate <->
      Nonempty PositiveExactChainPackage
  source_iff_minimal :
    ExactChainFamilySourcePackageGate <->
      Nonempty MinimalExactSourcePackage
  source_iff_exposed :
    ExactChainFamilySourcePackageGate <->
      Nonempty ExposedExactChainSource
  source_iff_closed_chain :
    ExactChainFamilySourcePackageGate <->
      Nonempty ExactClosedChainPackage
  source_iff_small_large :
    ExactChainFamilySourcePackageGate <->
      ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix
  source_iff_closure_dependency :
    ExactChainFamilySourcePackageGate <->
      ClosureRemainingExactChainFamilyDependency
  source_iff_remainder_dependency :
    ExactChainFamilySourcePackageGate <->
      RemainderRemainingExactChainFamilyDependency
  source_to_remainder_split :
    ExactChainFamilySourcePackageGate ->
      RemainderSplitExactSourcePackageGate
  certificates_to_source :
    Nonempty ClosedPlacementCertificateFamilySource ->
      ExactChainFamilySourcePackageGate

theorem exactChainFamilySourceInhabitationCertificate :
    ExactChainFamilySourceInhabitationCertificate where
  source_iff_positive := sourceGate_iff_positiveExactChainPackage
  source_iff_minimal := sourceGate_iff_minimalExactSource
  source_iff_exposed := sourceGate_iff_exposedExactChainSource
  source_iff_closed_chain := sourceGate_iff_exactClosedChainPackage
  source_iff_small_large := sourceGate_iff_smallBlocks_and_largeTail
  source_iff_closure_dependency := sourceGate_iff_closureDependency
  source_iff_remainder_dependency := sourceGate_iff_remainderDependency
  source_to_remainder_split := remainderSplitExactSourcePackageGate_of_sourceGate
  certificates_to_source :=
    sourceGate_of_closedPlacementCertificateFamilySource_nonempty

end

end ExactChainFamilyInhabitationW31
end PachToth

namespace Verified

abbrev PachTothW31ExactChainFamilySourcePackage : Type :=
  PachToth.ExactChainFamilyInhabitationW31.ExactChainFamilySourcePackage

abbrev PachTothW31ExactChainFamilySourcePackageGate : Prop :=
  PachToth.ExactChainFamilyInhabitationW31.ExactChainFamilySourcePackageGate

abbrev PachTothW31ClosedPlacementCertificateFamilySource : Type :=
  PachToth.ExactChainFamilyInhabitationW31.ClosedPlacementCertificateFamilySource

abbrev PachTothW31ExactChainFamilySourceInhabitationCertificate : Prop :=
  PachToth.ExactChainFamilyInhabitationW31.ExactChainFamilySourceInhabitationCertificate

theorem pachtoth_w31_sourceGate_iff_smallBlocks_and_largeTail :
    PachTothW31ExactChainFamilySourcePackageGate <->
      PachToth.ExactChainFamilyInhabitationW31.ExactBlocksOneThroughFive /\
        PachToth.ExactChainFamilyInhabitationW31.LargeExactBlockTargetsFromSix :=
  PachToth.ExactChainFamilyInhabitationW31.sourceGate_iff_smallBlocks_and_largeTail

theorem pachtoth_w31_sourceGate_iff_closureDependency :
    PachTothW31ExactChainFamilySourcePackageGate <->
      PachToth.ExactChainFamilyInhabitationW31.ClosureRemainingExactChainFamilyDependency :=
  PachToth.ExactChainFamilyInhabitationW31.sourceGate_iff_closureDependency

theorem pachtoth_w31_sourceGate_iff_remainderDependency :
    PachTothW31ExactChainFamilySourcePackageGate <->
      PachToth.ExactChainFamilyInhabitationW31.RemainderRemainingExactChainFamilyDependency :=
  PachToth.ExactChainFamilyInhabitationW31.sourceGate_iff_remainderDependency

theorem pachtoth_w31_sourceGate_of_closedPlacementCertificateFamilySource
    (S : PachTothW31ClosedPlacementCertificateFamilySource) :
    PachTothW31ExactChainFamilySourcePackageGate :=
  PachToth.ExactChainFamilyInhabitationW31.sourceGate_of_closedPlacementCertificateFamilySource
    S

theorem pachtoth_w31_exactChainFamilySourceInhabitationCertificate :
    PachTothW31ExactChainFamilySourceInhabitationCertificate :=
  PachToth.ExactChainFamilyInhabitationW31.exactChainFamilySourceInhabitationCertificate

end Verified
end ErdosProblems1066
