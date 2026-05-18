import ErdosProblems1066.PachToth.PositiveExactChainPackageW26

set_option autoImplicit false

/-!
# W27 remainder/exact source construction

This file packages the concrete checked-remainder data that sits downstream
of an exact source package.  The translated-remainder bridge is not
duplicated here; instead, its actual data products are exposed at each
div/mod split:

* the exact chain at `n / 16`;
* the checked finite remainder at `n % 16`;
* the translated checked remainder;
* the W24 appended-separation fields;
* the far-apart split certificate;
* the canonical split realization consumed by split soundness.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainderExactSourceConstructionW27

open Arithmetic

noncomputable section

abbrev ExactSourcePackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ExactChainUpper (k : Nat) : Type :=
  SplitSoundness.ExactChainUpper k

abbrev RemainderUpper (r : Nat) : Type :=
  SplitSoundness.RemainderUpper r

abbrev AppendedRemainderSeparation {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Prop :=
  ConcreteRemainderSplitW24.AppendedRemainderSeparation chain remainder

abbrev FarApartRemainderCertificate {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Type :=
  SplitCertificateBridge.FarApartRemainderCertificate chain remainder

abbrev CanonicalSplitRealization (k r : Nat) : Type :=
  SplitSoundness.CanonicalSplitRealization k r

/-! ## Pointwise div/mod data after an exact source -/

def exactChainAt
    (P : ExactSourcePackage) (n : Nat) :
    ExactChainUpper (n / 16) :=
  PositiveExactChainPackageW26.exactChainUpperOfPackageDiv P n

def checkedRemainderAt
    (n : Nat) :
    RemainderUpper (n % 16) :=
  PositiveExactChainPackageW26.checkedRemainderUpperOfLtSixteen
    (Nat.mod_lt n (by norm_num))

def translatedRemainderAt
    (P : ExactSourcePackage) (n : Nat) :
    RemainderUpper (n % 16) :=
  RemainderPlacement.translatedRemainderUpper
    (exactChainAt P n).config
    (checkedRemainderAt n)

def translatedSeparationAt
    (P : ExactSourcePackage) (n : Nat) :
    AppendedRemainderSeparation
      (exactChainAt P n).config
      (translatedRemainderAt P n).config :=
  ConcreteRemainderSplitW24.appendedRemainderSeparationOfTranslatedRemainder
    (exactChainAt P n).config
    (checkedRemainderAt n).config

def farApartCertificateAt
    (P : ExactSourcePackage) (n : Nat) :
    FarApartRemainderCertificate
      (exactChainAt P n).config
      (translatedRemainderAt P n).config :=
  ConcreteRemainderSplitW24.farApartRemainderCertificateOfTranslatedRemainder
    (exactChainAt P n).config
    (checkedRemainderAt n).config

def canonicalSplitRealizationAt
    (P : ExactSourcePackage) (n : Nat) :
    CanonicalSplitRealization (n / 16) (n % 16) :=
  ConcreteRemainderSplitW24.canonicalSplitRealizationOfExactChainTranslatedSeparation
    (exactChainAt P n)
    (checkedRemainderAt n)

/-- Concrete remainder-plus-exact source data for one vertex count. -/
structure RemainderExactSourceAt
    (P : ExactSourcePackage) (n : Nat) where
  chain : ExactChainUpper (n / 16)
  chain_eq : chain = exactChainAt P n
  remainder : RemainderUpper (n % 16)
  remainder_eq : remainder = checkedRemainderAt n
  translatedRemainder : RemainderUpper (n % 16)
  translatedRemainder_eq :
    translatedRemainder = translatedRemainderAt P n
  separation :
    AppendedRemainderSeparation chain.config translatedRemainder.config
  farApart :
    FarApartRemainderCertificate chain.config translatedRemainder.config
  realization : CanonicalSplitRealization (n / 16) (n % 16)

def sourceAt
    (P : ExactSourcePackage) (n : Nat) :
    RemainderExactSourceAt P n where
  chain := exactChainAt P n
  chain_eq := rfl
  remainder := checkedRemainderAt n
  remainder_eq := rfl
  translatedRemainder := translatedRemainderAt P n
  translatedRemainder_eq := rfl
  separation := translatedSeparationAt P n
  farApart := farApartCertificateAt P n
  realization := canonicalSplitRealizationAt P n

@[simp]
theorem sourceAt_chain
    (P : ExactSourcePackage) (n : Nat) :
    (sourceAt P n).chain = exactChainAt P n :=
  rfl

@[simp]
theorem sourceAt_remainder
    (P : ExactSourcePackage) (n : Nat) :
    (sourceAt P n).remainder = checkedRemainderAt n :=
  rfl

@[simp]
theorem sourceAt_translatedRemainder
    (P : ExactSourcePackage) (n : Nat) :
    (sourceAt P n).translatedRemainder = translatedRemainderAt P n :=
  rfl

/-! ## Source package feeding arbitrary `n` -/

/-- The exact source together with concrete checked-remainder split data for
every div/mod vertex count. -/
structure RemainderExactSourcePackage where
  exact : ExactSourcePackage
  source : forall n : Nat, RemainderExactSourceAt exact n

def packageOfExactSource
    (P : ExactSourcePackage) :
    RemainderExactSourcePackage where
  exact := P
  source := fun n => sourceAt P n

def exactSourceOfPackage
    (S : RemainderExactSourcePackage) :
    ExactSourcePackage :=
  S.exact

theorem nonempty_package_iff_exactSource :
    Nonempty RemainderExactSourcePackage <-> Nonempty ExactSourcePackage := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S => exact Nonempty.intro S.exact
  case mpr =>
    intro h
    cases h with
    | intro P => exact Nonempty.intro (packageOfExactSource P)

theorem nonempty_package_iff_exactTarget :
    Nonempty RemainderExactSourcePackage <-> ExactTarget := by
  exact Iff.trans
    nonempty_package_iff_exactSource
    PositiveExactChainPackageW26.nonempty_package_iff_exactTarget

def packageOfExactTarget
    (H : ExactTarget) :
    RemainderExactSourcePackage :=
  packageOfExactSource
    (PositiveExactChainPackageW26.packageOfExactTarget H)

theorem fixedTarget_of_sourceAt
    {P : ExactSourcePackage} {n : Nat}
    (S : RemainderExactSourceAt P n) :
    FixedTarget n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    SplitSoundness.targetUpperConstructionFiveSixteenAt_of_canonicalSplitRealization
      hr S.realization

theorem fixedTarget_of_package
    (S : RemainderExactSourcePackage) (n : Nat) :
    FixedTarget n :=
  fixedTarget_of_sourceAt (S.source n)

theorem arbitraryTarget_of_package
    (S : RemainderExactSourcePackage) :
    ArbitraryTarget := by
  intro n
  exact fixedTarget_of_package S n

end

end RemainderExactSourceConstructionW27
end PachToth

namespace Verified

abbrev PachTothW27RemainderExactSourcePackage : Type :=
  PachToth.RemainderExactSourceConstructionW27.RemainderExactSourcePackage

theorem pachtoth_w27_remainderExactSourcePackage_iff_exactTarget :
    Nonempty PachTothW27RemainderExactSourcePackage <->
      PachToth.targetUpperConstructionFiveSixteen :=
  PachToth.RemainderExactSourceConstructionW27.nonempty_package_iff_exactTarget

end Verified
end ErdosProblems1066
