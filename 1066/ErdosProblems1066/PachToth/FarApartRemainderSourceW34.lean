import ErdosProblems1066.PachToth.RemainderSplitSourceClosureW32
import ErdosProblems1066.PachToth.SmallLengthExactTargetsConcreteW24

set_option autoImplicit false

/-!
# W34 far-apart remainder source

W32 already exposes source-facing split data.  This file isolates the
geometric part of that handoff: once an exact-chain upper certificate and a
checked remainder upper certificate are available, the existing translated
remainder construction supplies the concrete `FarApartRemainderCertificate`
and the canonical split realization.

The API below depends only on exact-chain source data and checked finite
remainders.  It does not route through the refuted exact-base flexible gate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FarApartRemainderSourceW34

noncomputable section

abbrev ExactChainUpper (k : Nat) : Type :=
  SplitSoundness.ExactChainUpper k

abbrev RemainderUpper (r : Nat) : Type :=
  SplitSoundness.RemainderUpper r

abbrev FarApartRemainderCertificate {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Type :=
  SplitCertificateBridge.FarApartRemainderCertificate chain remainder

abbrev CanonicalSplitRealization (k r : Nat) : Type :=
  SplitSoundness.CanonicalSplitRealization k r

abbrev ExistsCanonicalSplitRealization (k r : Nat) : Prop :=
  SplitCertificateBridge.exists_canonicalSplitRealization k r

abbrev ExactChainFamilySourcePackage : Type :=
  RemainderSplitSourceClosureW32.ExactChainFamilySourcePackage

abbrev ExactChainFamilySourceGate : Prop :=
  RemainderSplitSourceClosureW32.ExactChainFamilySourceGate

abbrev ExactClosedChainPackage : Type :=
  RemainderSplitSourceClosureW32.ExactClosedChainPackage

abbrev ClosedPlacementFamily : Type :=
  RemainderSplitSourceClosureW32.ClosedPlacementFamily

abbrev MinimalExactRemainderSplitSourceBlocker : Prop :=
  RemainderSplitSourceClosureW32.MinimalExactRemainderSplitSourceBlocker

abbrev LargeExactBlockTargetsFromSix : Prop :=
  RemainderSplitSourceClosureW32.LargeExactBlockTargetsFromSix

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  RemainderSplitSourceClosureW32.LargeClosedPlacementFieldsFromSix

abbrev DeformedLengthOneExactBlocksTwoThroughFiveSource : Type :=
  SmallLengthExactTargetsConcreteW24.DeformedLengthOneExactBlocksTwoThroughFiveSource

abbrev ExactRemainderSplitSourceAt
    (P : ExactChainFamilySourcePackage) (n : Nat) : Type :=
  RemainderSplitSourceClosureW32.ExactRemainderSplitSourceAt P n

abbrev ExactRemainderSplitSourcePackage : Type :=
  RemainderSplitSourceClosureW32.ExactRemainderSplitSourcePackage

/-! ## Pointwise translated-remainder certificate source -/

/-- The source-facing far-apart remainder object for one split.  The
remainder stored in `translatedRemainder` is the spatially translated
remainder used by the combined configuration. -/
structure FarApartRemainderSourceAt (k r : Nat) where
  chain : ExactChainUpper k
  checkedRemainder : RemainderUpper r
  translatedRemainder : RemainderUpper r
  translatedRemainder_eq :
    translatedRemainder =
      RemainderPlacement.translatedRemainderUpper chain.config checkedRemainder
  farApart :
    FarApartRemainderCertificate chain.config translatedRemainder.config
  realization : CanonicalSplitRealization k r
  realization_eq :
    realization =
      RemainderPlacement.canonicalSplitRealizationOfExactChainTranslatedRemainder
        chain checkedRemainder

/-- The actual far-apart certificate supplied by translating the remainder. -/
def farApartCertificateOfExactChainRemainder {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    FarApartRemainderCertificate
      chain.config
      (RemainderPlacement.translatedRemainderUpper
        chain.config remainder).config :=
  RemainderPlacement.farApartRemainderCertificate
    chain.config remainder.config

/-- The canonical split realization supplied by the same translated
remainder certificate. -/
def canonicalSplitRealizationOfExactChainRemainder {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    CanonicalSplitRealization k r :=
  RemainderPlacement.canonicalSplitRealizationOfExactChainTranslatedRemainder
    chain remainder

/-- Exact-chain and checked-remainder upper certificates give the pointwise
far-apart source directly. -/
def sourceAtOfExactChainRemainder {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    FarApartRemainderSourceAt k r where
  chain := chain
  checkedRemainder := remainder
  translatedRemainder :=
    RemainderPlacement.translatedRemainderUpper chain.config remainder
  translatedRemainder_eq := rfl
  farApart := farApartCertificateOfExactChainRemainder chain remainder
  realization := canonicalSplitRealizationOfExactChainRemainder chain remainder
  realization_eq := rfl

theorem nonempty_sourceAt_of_exactChainRemainder {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    Nonempty (FarApartRemainderSourceAt k r) :=
  Nonempty.intro (sourceAtOfExactChainRemainder chain remainder)

theorem exists_canonicalSplitRealization_of_sourceAt {k r : Nat}
    (S : FarApartRemainderSourceAt k r) :
    ExistsCanonicalSplitRealization k r := by
  exact Exists.intro S.realization True.intro

theorem exists_canonicalSplitRealization_of_exactChainRemainder {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    ExistsCanonicalSplitRealization k r :=
  exists_canonicalSplitRealization_of_sourceAt
    (sourceAtOfExactChainRemainder chain remainder)

/-! ## Direct exact-source-to-canonical realization route -/

def exactChainUpperOfSourcePackage
    (P : ExactChainFamilySourcePackage) (k : Nat) :
    ExactChainUpper k := by
  by_cases hk : 0 < k
  · exact P.exactChain k hk
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    exact SplitSoundness.emptyExactChainUpper

def checkedRemainderUpper (r : Nat) : RemainderUpper r :=
  SplitSoundness.remainderUpperOfConstruction r

def sourceAtOfExactChainSourcePackage
    (P : ExactChainFamilySourcePackage) (k r : Nat) :
    FarApartRemainderSourceAt k r :=
  sourceAtOfExactChainRemainder
    (exactChainUpperOfSourcePackage P k)
    (checkedRemainderUpper r)

def canonicalSplitRealizationOfExactChainSourcePackage
    (P : ExactChainFamilySourcePackage) (k r : Nat) :
    CanonicalSplitRealization k r :=
  (sourceAtOfExactChainSourcePackage P k r).realization

theorem exists_canonicalSplitRealization_of_exactChainSourcePackage
    (P : ExactChainFamilySourcePackage) (k r : Nat) :
    ExistsCanonicalSplitRealization k r :=
  exists_canonicalSplitRealization_of_sourceAt
    (sourceAtOfExactChainSourcePackage P k r)

theorem exists_canonicalSplitRealization_of_exactChainSourceGate_at
    (H : ExactChainFamilySourceGate) (k r : Nat) :
    ExistsCanonicalSplitRealization k r := by
  cases H with
  | intro P =>
      exact exists_canonicalSplitRealization_of_exactChainSourcePackage P k r

def exactChainSourcePackageOfExactClosedChainPackage
    (P : ExactClosedChainPackage) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfExactClosedChainPackage P

def sourceAtOfExactClosedChainPackage
    (P : ExactClosedChainPackage) (k r : Nat) :
    FarApartRemainderSourceAt k r :=
  sourceAtOfExactChainSourcePackage
    (exactChainSourcePackageOfExactClosedChainPackage P) k r

def canonicalSplitRealizationOfExactClosedChainPackage
    (P : ExactClosedChainPackage) (k r : Nat) :
    CanonicalSplitRealization k r :=
  (sourceAtOfExactClosedChainPackage P k r).realization

theorem exists_canonicalSplitRealization_of_exactClosedChainPackage
    (P : ExactClosedChainPackage) (k r : Nat) :
    ExistsCanonicalSplitRealization k r :=
  exists_canonicalSplitRealization_of_sourceAt
    (sourceAtOfExactClosedChainPackage P k r)

theorem exists_canonicalSplitRealization_of_exactClosedChainPackageGate
    (H : Nonempty ExactClosedChainPackage) (k r : Nat) :
    ExistsCanonicalSplitRealization k r := by
  cases H with
  | intro P =>
      exact exists_canonicalSplitRealization_of_exactClosedChainPackage P k r

def exactChainSourcePackageOfClosedPlacementFamily
    (P : ClosedPlacementFamily) :
    ExactChainFamilySourcePackage :=
  ExactChainFamilySourceW29.packageOfClosedPlacementFamily P

theorem exists_canonicalSplitRealization_of_closedPlacementFamily
    (P : ClosedPlacementFamily) (k r : Nat) :
    ExistsCanonicalSplitRealization k r :=
  exists_canonicalSplitRealization_of_exactChainSourcePackage
    (exactChainSourcePackageOfClosedPlacementFamily P) k r

theorem exists_canonicalSplitRealization_of_closedPlacementFamilyGate
    (H : Nonempty ClosedPlacementFamily) (k r : Nat) :
    ExistsCanonicalSplitRealization k r := by
  cases H with
  | intro P =>
      exact exists_canonicalSplitRealization_of_closedPlacementFamily P k r

/-! ## Compatibility with the W32 source-facing split package -/

/-- Rebuild the far-apart source from W32 pointwise source fields.  This
reconstructs the translated certificate from the exact chain and checked
remainder fields, rather than treating a downstream target as input. -/
def sourceAtOfW32SourceAt
    {P : ExactChainFamilySourcePackage} {n : Nat}
    (S : ExactRemainderSplitSourceAt P n) :
    FarApartRemainderSourceAt (n / 16) (n % 16) :=
  sourceAtOfExactChainRemainder S.exactChain S.checkedRemainder

theorem exists_canonicalSplitRealization_of_w32SourceAt
    {P : ExactChainFamilySourcePackage} {n : Nat}
    (S : ExactRemainderSplitSourceAt P n) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_sourceAt
    (sourceAtOfW32SourceAt S)

/-! ## Package and exact missing source theorem -/

/-- A full source package for the far-apart translated remainder certificates
at every div/mod split. -/
structure FarApartRemainderSourcePackage where
  exactChainSource : ExactChainFamilySourcePackage
  sourceAt : forall n : Nat,
    FarApartRemainderSourceAt (n / 16) (n % 16)

abbrev FarApartRemainderSourcePackageGate : Prop :=
  Nonempty FarApartRemainderSourcePackage

def packageOfExactChainSourcePackage
    (P : ExactChainFamilySourcePackage) :
    FarApartRemainderSourcePackage where
  exactChainSource := P
  sourceAt := fun n =>
    sourceAtOfW32SourceAt
      (RemainderSplitSourceClosureW32.sourceAtOfExactChainSourcePackage P n)

def packageOfW32Package
    (S : ExactRemainderSplitSourcePackage) :
    FarApartRemainderSourcePackage where
  exactChainSource := S.exactChainSource
  sourceAt := fun n => sourceAtOfW32SourceAt (S.sourceAt n)

theorem packageGate_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) :
    FarApartRemainderSourcePackageGate := by
  cases H with
  | intro P =>
      exact Nonempty.intro (packageOfExactChainSourcePackage P)

theorem exactChainFamilySourceGate_of_packageGate
    (H : FarApartRemainderSourcePackageGate) :
    ExactChainFamilySourceGate := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.exactChainSource

theorem packageGate_iff_exactChainFamilySourceGate :
    FarApartRemainderSourcePackageGate <-> ExactChainFamilySourceGate := by
  constructor
  case mp =>
    exact exactChainFamilySourceGate_of_packageGate
  case mpr =>
    exact packageGate_of_exactChainFamilySourceGate

/-- The exact remaining source theorem for this file: far-apart remainder
sources are equivalent to the W32 exact-chain source blocker. -/
theorem packageGate_iff_minimalBlocker :
    FarApartRemainderSourcePackageGate <->
      MinimalExactRemainderSplitSourceBlocker :=
  Iff.trans packageGate_iff_exactChainFamilySourceGate
    RemainderSplitSourceClosureW32.exactChainFamilySourceGate_iff_minimalBlocker

theorem packageGate_of_deformedSmallSource_and_largeTail
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeExactBlockTargetsFromSix) :
    FarApartRemainderSourcePackageGate :=
  packageGate_of_exactChainFamilySourceGate
    (Nonempty.intro
      (ExactChainFamilySourceW29.packageOfSmallBlocksAndLargeTail
        (SmallLengthExactTargetsConcreteW24.exactBlocksOneThroughFive_of_deformedLengthOneExactBlocksTwoThroughFiveSource
          small)
        large))

theorem packageGate_of_deformedSmallSourceGate_and_largeTail
    (Hsmall : Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeExactBlockTargetsFromSix) :
    FarApartRemainderSourcePackageGate := by
  cases Hsmall with
  | intro small =>
      exact packageGate_of_deformedSmallSource_and_largeTail small large

theorem largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsFromSix
    (large : LargeClosedPlacementFieldsFromSix) :
    LargeExactBlockTargetsFromSix :=
  RemainderSplitSourceClosureW32.largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsFromSix
    large

theorem minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeClosedPlacementFieldsFromSix) :
    MinimalExactRemainderSplitSourceBlocker :=
  RemainderSplitSourceClosureW32.minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
    small large

theorem packageGate_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
    (small : DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (large : LargeClosedPlacementFieldsFromSix) :
    FarApartRemainderSourcePackageGate :=
  packageGate_iff_minimalBlocker.mpr
    (minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
      small large)

theorem packageGate_of_deformedSmallSourceGate_and_largeClosedPlacementFieldsFromSixGate
    (Hsmall : Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource)
    (Hlarge : Nonempty LargeClosedPlacementFieldsFromSix) :
    FarApartRemainderSourcePackageGate := by
  cases Hsmall with
  | intro small =>
      cases Hlarge with
      | intro large =>
          exact
            packageGate_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
              small large

theorem exists_canonicalSplitRealization_of_package
    (S : FarApartRemainderSourcePackage) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_sourceAt (S.sourceAt n)

theorem exists_canonicalSplitRealization_of_packageGate
    (H : FarApartRemainderSourcePackageGate) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) := by
  cases H with
  | intro S =>
      exact exists_canonicalSplitRealization_of_package S n

theorem exists_canonicalSplitRealization_of_exactChainFamilySourceGate
    (H : ExactChainFamilySourceGate) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) :=
  exists_canonicalSplitRealization_of_packageGate
    (packageGate_of_exactChainFamilySourceGate H) n

/-- Summary certificate for the source-facing translated-remainder bridge. -/
structure FarApartRemainderSourceCertificate : Prop where
  sourceAtExists :
    forall {k r : Nat} (chain : ExactChainUpper k)
      (remainder : RemainderUpper r),
      Exists fun S : FarApartRemainderSourceAt k r =>
        S.chain = chain /\ S.checkedRemainder = remainder
  sourceAtFeedsCanonicalSplit :
    forall {k r : Nat},
      FarApartRemainderSourceAt k r ->
        ExistsCanonicalSplitRealization k r
  package_iff_sourceGate :
    FarApartRemainderSourcePackageGate <-> ExactChainFamilySourceGate
  package_iff_minimalBlocker :
    FarApartRemainderSourcePackageGate <->
      MinimalExactRemainderSplitSourceBlocker
  deformedSmallSourceAndLargeTailFeedsPackage :
    DeformedLengthOneExactBlocksTwoThroughFiveSource ->
      LargeExactBlockTargetsFromSix ->
        FarApartRemainderSourcePackageGate
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsPackage :
    DeformedLengthOneExactBlocksTwoThroughFiveSource ->
      LargeClosedPlacementFieldsFromSix ->
        FarApartRemainderSourcePackageGate
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsMinimalBlocker :
    DeformedLengthOneExactBlocksTwoThroughFiveSource ->
      LargeClosedPlacementFieldsFromSix ->
        MinimalExactRemainderSplitSourceBlocker
  packageFeedsCanonicalSplit :
    FarApartRemainderSourcePackageGate ->
      forall n : Nat,
        ExistsCanonicalSplitRealization (n / 16) (n % 16)
  sourceGateFeedsCanonicalSplit :
    ExactChainFamilySourceGate ->
      forall n : Nat,
        ExistsCanonicalSplitRealization (n / 16) (n % 16)

theorem farApartRemainderSourceCertificate :
    FarApartRemainderSourceCertificate where
  sourceAtExists := by
    intro _k _r chain remainder
    exact Exists.intro
      (sourceAtOfExactChainRemainder chain remainder)
      (And.intro rfl rfl)
  sourceAtFeedsCanonicalSplit := by
    intro _k _r S
    exact exists_canonicalSplitRealization_of_sourceAt S
  package_iff_sourceGate := packageGate_iff_exactChainFamilySourceGate
  package_iff_minimalBlocker := packageGate_iff_minimalBlocker
  deformedSmallSourceAndLargeTailFeedsPackage :=
    packageGate_of_deformedSmallSource_and_largeTail
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsPackage :=
    packageGate_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
  deformedSmallSourceAndLargeClosedPlacementFieldsFeedsMinimalBlocker :=
    minimalBlocker_of_deformedSmallSource_and_largeClosedPlacementFieldsFromSix
  packageFeedsCanonicalSplit := by
    intro H n
    exact exists_canonicalSplitRealization_of_packageGate H n
  sourceGateFeedsCanonicalSplit := by
    intro H n
    exact exists_canonicalSplitRealization_of_exactChainFamilySourceGate H n

end

end FarApartRemainderSourceW34
end PachToth

namespace Verified

abbrev PachTothW34FarApartRemainderSourcePackage : Type :=
  PachToth.FarApartRemainderSourceW34.FarApartRemainderSourcePackage

theorem pachtoth_w34_farApartRemainderSourcePackage_iff_minimalBlocker :
    Nonempty PachTothW34FarApartRemainderSourcePackage <->
      PachToth.FarApartRemainderSourceW34.MinimalExactRemainderSplitSourceBlocker :=
  PachToth.FarApartRemainderSourceW34.packageGate_iff_minimalBlocker

end Verified
end ErdosProblems1066
