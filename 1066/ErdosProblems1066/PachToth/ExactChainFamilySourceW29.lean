import ErdosProblems1066.PachToth.RemainderSplitExactSourceW28
import ErdosProblems1066.PachToth.LargeTailExactSourceW28
import ErdosProblems1066.PachToth.EventualReduction

set_option autoImplicit false

/-!
# W29 exact-chain family source

This file isolates the source object needed by
`RemainderSplitExactSourceW28`: exact-chain upper certificates for every
positive block count.  It also records the smallest honest alternatives that
produce the same family, without constructing the family from the global exact
Pach--Toth target statement.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactChainFamilySourceW29

noncomputable section

abbrev ExactChainUpper (k : Nat) : Type :=
  SplitSoundness.ExactChainUpper k

abbrev ExactChainFamily : Type :=
  forall k : Nat, 0 < k -> ExactChainUpper k

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev RemainderSplitExactSourcePackage : Type :=
  RemainderSplitExactSourceW28.RemainderSplitExactSourcePackage

abbrev ExactClosedChainPackage : Type :=
  ArbitraryNClosureW11.ExactClosedChainPackage

abbrev ClosedPlacementFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ClosedPlacementFamily

abbrev ClosedPlacementPackage : Type :=
  ArbitraryNBridgeW10.ClosedPlacementPackage

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainPackageW26.ExactBlocksOneThroughFive

abbrev LargeExactBlockTargetsFromSix : Prop :=
  PositiveExactChainPackageW26.LargeExactBlockTargetsFromSix

abbrev SmallAndLargeExactBlockTargets : Prop :=
  PositiveExactChainPackageW26.SmallAndLargeExactBlockTargets

abbrev LargeTailExactSourcePackage : Type :=
  LargeTailExactSourceW28.LargeTailExactSourcePackage

abbrev ExplicitClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) : Type :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  forall k : Nat, forall hk : 0 < k,
    ExplicitClosedPlacementCertificate k hk

abbrev EventualExplicitClosedPlacementCertificateFamily
    (K0 : Nat) : Type :=
  forall k : Nat, K0 <= k -> forall hk : 0 < k,
    ExplicitClosedPlacementCertificate k hk

/-! ## The exact-chain source package -/

/-- Exact-chain source data for every positive block count. -/
structure ExactChainFamilySourcePackage where
  exactChain : ExactChainFamily

namespace ExactChainFamilySourcePackage

def toExactChainFamily
    (P : ExactChainFamilySourcePackage) :
    RemainderSplitExactSourceW28.ExactChainFamily :=
  P.exactChain

def toPositiveExactChainPackage
    (P : ExactChainFamilySourcePackage) :
    PositiveExactChainPackage :=
  PositiveExactChainPackageW26.packageOfPositiveExactChains P.exactChain

def toExactClosedChainPackage
    (P : ExactChainFamilySourcePackage) :
    ExactClosedChainPackage where
  chain := P.exactChain

def toRemainderSplitExactSourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderSplitExactSourcePackage :=
  RemainderSplitExactSourceW28.packageOfExactChainFamily P.toExactChainFamily

theorem arbitraryTarget
    (P : ExactChainFamilySourcePackage) :
    RemainderSplitExactSourceW28.ArbitraryTarget :=
  RemainderSplitExactSourceW28.arbitraryTarget_of_exactChainFamily
    P.toExactChainFamily

end ExactChainFamilySourcePackage

def packageOfExactChainFamily
    (H : ExactChainFamily) :
    ExactChainFamilySourcePackage where
  exactChain := H

def packageOfPositiveExactChainPackage
    (P : PositiveExactChainPackage) :
    ExactChainFamilySourcePackage where
  exactChain := P.exactChain

def packageOfExactClosedChainPackage
    (P : ExactClosedChainPackage) :
    ExactChainFamilySourcePackage where
  exactChain := P.chain

theorem nonempty_package_iff_positiveExactChainPackage :
    Nonempty ExactChainFamilySourcePackage <->
      Nonempty PositiveExactChainPackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toPositiveExactChainPackage
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (packageOfPositiveExactChainPackage P)

theorem nonempty_package_iff_exactClosedChainPackage :
    Nonempty ExactChainFamilySourcePackage <->
      Nonempty ExactClosedChainPackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toExactClosedChainPackage
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (packageOfExactClosedChainPackage P)

/-! ## Closed-placement source constructors -/

def packageOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    ExactChainFamilySourcePackage where
  exactChain := fun k hk =>
    SplitCertificateBridge.exactChainUpperOfClosedPlacement (H k hk)

def packageOfClosedPlacementPackage
    (P : ClosedPlacementPackage) :
    ExactChainFamilySourcePackage :=
  packageOfClosedPlacementFamily P.placement

def packageOfExplicitClosedPlacementCertificateFamily
    (H : ExplicitClosedPlacementCertificateFamily) :
    ExactChainFamilySourcePackage where
  exactChain := fun k hk =>
    ClosedChainReduction.exactChainUpperOfExplicitClosedPlacementCertificate
      (H k hk)

theorem nonempty_package_of_closedPlacementFamily :
    Nonempty ClosedPlacementFamily ->
      Nonempty ExactChainFamilySourcePackage := by
  intro h
  cases h with
  | intro H =>
      exact Nonempty.intro (packageOfClosedPlacementFamily H)

theorem nonempty_package_of_closedPlacementPackage :
    Nonempty ClosedPlacementPackage ->
      Nonempty ExactChainFamilySourcePackage := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (packageOfClosedPlacementPackage P)

theorem nonempty_package_of_explicitClosedPlacementCertificateFamily :
    Nonempty ExplicitClosedPlacementCertificateFamily ->
      Nonempty ExactChainFamilySourcePackage := by
  intro h
  cases h with
  | intro H =>
      exact
        Nonempty.intro
          (packageOfExplicitClosedPlacementCertificateFamily H)

/-! ## Small-block plus large-tail source constructors -/

def packageOfSmallAndLargeExactBlockTargets
    (D : SmallAndLargeExactBlockTargets) :
    ExactChainFamilySourcePackage :=
  packageOfPositiveExactChainPackage
    (PositiveExactChainPackageW26.packageOfSmallAndLargeExactBlockTargets D)

def packageOfSmallBlocksAndLargeTail
    (small : ExactBlocksOneThroughFive)
    (large : LargeExactBlockTargetsFromSix) :
    ExactChainFamilySourcePackage :=
  packageOfSmallAndLargeExactBlockTargets
    { small := small
      large := large }

def packageOfLargeTailExactSourcePackage
    (P : LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    ExactChainFamilySourcePackage :=
  packageOfPositiveExactChainPackage
    (P.positiveExactChainPackage small)

theorem nonempty_package_iff_smallBlocks_and_largeTail :
    Nonempty ExactChainFamilySourcePackage <->
      And ExactBlocksOneThroughFive LargeExactBlockTargetsFromSix := by
  exact
    Iff.trans nonempty_package_iff_positiveExactChainPackage
      PositiveExactChainPackageW26.nonempty_package_iff_smallBlocks_and_largeTail

theorem nonempty_package_of_largeTailSource_and_smallBlocks
    (Hlarge : Nonempty LargeTailExactSourcePackage)
    (small : ExactBlocksOneThroughFive) :
    Nonempty ExactChainFamilySourcePackage := by
  cases Hlarge with
  | intro P =>
      exact Nonempty.intro (packageOfLargeTailExactSourcePackage P small)

/-! ## Eventual exact-chain source packages -/

/-- Eventual exact-chain data together with exact-chain certificates for the
finite complement.  This is stronger than the target-only eventual reduction
and is exactly what is needed to recover a full family. -/
structure EventualExactChainSourcePackage where
  threshold : Nat
  largeChain :
    forall k : Nat, threshold <= k -> 0 < k -> ExactChainUpper k
  smallChain :
    forall k : Nat, k < threshold -> 0 < k -> ExactChainUpper k

namespace EventualExactChainSourcePackage

def exactChain
    (P : EventualExactChainSourcePackage) :
    ExactChainFamily := by
  intro k hk
  by_cases hlarge : P.threshold <= k
  case pos =>
    exact P.largeChain k hlarge hk
  case neg =>
    exact P.smallChain k (Nat.lt_of_not_ge hlarge) hk

def toExactChainFamilySourcePackage
    (P : EventualExactChainSourcePackage) :
    ExactChainFamilySourcePackage where
  exactChain := P.exactChain

def toEventualClosedChainPackage
    (P : EventualExactChainSourcePackage) :
    ArbitraryNClosureW11.EventualClosedChainPackage :=
  ArbitraryNClosureW11.EventualClosedChainPackage.ofLargeAndSmallChains
    P.threshold P.largeChain P.smallChain

end EventualExactChainSourcePackage

def packageOfEventualExactChains
    (K0 : Nat)
    (largeChain :
      forall k : Nat, K0 <= k -> 0 < k -> ExactChainUpper k)
    (smallChain :
      forall k : Nat, k < K0 -> 0 < k -> ExactChainUpper k) :
    ExactChainFamilySourcePackage :=
  (EventualExactChainSourcePackage.mk K0 largeChain smallChain)
    |>.toExactChainFamilySourcePackage

/-- Eventual explicit closed-placement certificates plus exact small chains
recover the full exact-chain family. -/
structure EventualExplicitClosedPlacementSourcePackage where
  threshold : Nat
  largeCertificates :
    EventualExplicitClosedPlacementCertificateFamily threshold
  smallChain :
    forall k : Nat, k < threshold -> 0 < k -> ExactChainUpper k

namespace EventualExplicitClosedPlacementSourcePackage

def toEventualExactChainSourcePackage
    (P : EventualExplicitClosedPlacementSourcePackage) :
    EventualExactChainSourcePackage where
  threshold := P.threshold
  largeChain := fun k hK hk =>
    ClosedChainReduction.exactChainUpperOfExplicitClosedPlacementCertificate
      (P.largeCertificates k hK hk)
  smallChain := P.smallChain

def toExactChainFamilySourcePackage
    (P : EventualExplicitClosedPlacementSourcePackage) :
    ExactChainFamilySourcePackage :=
  P.toEventualExactChainSourcePackage.toExactChainFamilySourcePackage

end EventualExplicitClosedPlacementSourcePackage

def packageOfEventualExplicitClosedPlacementCertificates
    (K0 : Nat)
    (largeCertificates :
      EventualExplicitClosedPlacementCertificateFamily K0)
    (smallChain :
      forall k : Nat, k < K0 -> 0 < k -> ExactChainUpper k) :
    ExactChainFamilySourcePackage :=
  (EventualExplicitClosedPlacementSourcePackage.mk
    K0 largeCertificates smallChain).toExactChainFamilySourcePackage

/-! ## Remainder split handoff -/

def remainderSplitPackageOfExactChainFamilySourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderSplitExactSourcePackage :=
  P.toRemainderSplitExactSourcePackage

theorem arbitraryTarget_of_exactChainFamilySourcePackage
    (P : ExactChainFamilySourcePackage) :
    RemainderSplitExactSourceW28.ArbitraryTarget :=
  P.arbitraryTarget

abbrev RemainingExactChainFamilySourceBlocker : Prop :=
  Nonempty ExactChainFamilySourcePackage

theorem remainingBlocker_iff_minimal_honest_components :
    RemainingExactChainFamilySourceBlocker <->
      And ExactBlocksOneThroughFive LargeExactBlockTargetsFromSix :=
  nonempty_package_iff_smallBlocks_and_largeTail

end

end ExactChainFamilySourceW29
end PachToth

namespace Verified

abbrev PachTothW29ExactChainFamilySourcePackage : Type :=
  PachToth.ExactChainFamilySourceW29.ExactChainFamilySourcePackage

abbrev PachTothW29RemainingExactChainFamilySourceBlocker : Prop :=
  PachToth.ExactChainFamilySourceW29.RemainingExactChainFamilySourceBlocker

noncomputable def pachtoth_w29_remainderSplitPackage_of_exactChainFamilySourcePackage
    (P : PachTothW29ExactChainFamilySourcePackage) :
    PachToth.ExactChainFamilySourceW29.RemainderSplitExactSourcePackage :=
  PachToth.ExactChainFamilySourceW29.remainderSplitPackageOfExactChainFamilySourcePackage
    P

theorem pachtoth_w29_arbitraryTarget_of_exactChainFamilySourcePackage
    (P : PachTothW29ExactChainFamilySourcePackage) :
    PachToth.RemainderSplitExactSourceW28.ArbitraryTarget :=
  PachToth.ExactChainFamilySourceW29.arbitraryTarget_of_exactChainFamilySourcePackage
    P

theorem pachtoth_w29_remainingBlocker_iff_minimal_honest_components :
    PachTothW29RemainingExactChainFamilySourceBlocker <->
      And
        PachToth.ExactChainFamilySourceW29.ExactBlocksOneThroughFive
        PachToth.ExactChainFamilySourceW29.LargeExactBlockTargetsFromSix :=
  PachToth.ExactChainFamilySourceW29.remainingBlocker_iff_minimal_honest_components

end Verified
end ErdosProblems1066
