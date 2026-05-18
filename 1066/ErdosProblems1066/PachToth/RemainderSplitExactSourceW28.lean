import ErdosProblems1066.PachToth.RemainderExactSourceConstructionW27

set_option autoImplicit false

/-!
# W28 remainder split exact source

This file keeps the arbitrary-`n` Pach--Toth split route source-facing.
It packages the exact-chain block, the checked finite remainder block, and
the explicit appended-separation data before applying split soundness.

The main constructor uses an exact-chain source package together with the
finite checked remainders from `RemainderConstruction`, then translates the
remainder to produce the W24 separation certificate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainderSplitExactSourceW28

open Arithmetic

noncomputable section

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

abbrev ExactSourcePackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev ExactChainFamily : Type :=
  forall k : Nat, 0 < k -> ExactChainUpper k

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

/-! ## Explicit source data for one split -/

/-- Source data for one `16 * k + r` split before applying the counting
theorem.  The remainder is already the spatially placed remainder used by
the combined configuration. -/
structure SplitExactSourceAt (k r : Nat) where
  chain : ExactChainUpper k
  remainder : RemainderUpper r
  separation : AppendedRemainderSeparation chain.config remainder.config

def sourceAtOfExactChainRemainderSeparation
    {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r)
    (H : AppendedRemainderSeparation chain.config remainder.config) :
    SplitExactSourceAt k r where
  chain := chain
  remainder := remainder
  separation := H

def farApartCertificateOfSourceAt
    {k r : Nat} (S : SplitExactSourceAt k r) :
    FarApartRemainderCertificate S.chain.config S.remainder.config :=
  ConcreteRemainderSplitW24.farApartRemainderCertificateOfSeparation
    S.chain.config S.remainder.config S.separation

def canonicalSplitRealizationOfSourceAt
    {k r : Nat} (S : SplitExactSourceAt k r) :
    CanonicalSplitRealization k r :=
  ConcreteRemainderSplitW24.canonicalSplitRealizationOfExactChainRemainderSeparation
    S.chain S.remainder S.separation

theorem exists_canonicalSplitRealization_of_sourceAt
    {k r : Nat} (S : SplitExactSourceAt k r) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact Exists.intro (canonicalSplitRealizationOfSourceAt S) True.intro

theorem fixedTarget_of_sourceAt
    {k r : Nat} (hr : r < 16) (S : SplitExactSourceAt k r) :
    FixedTarget (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_sourceAt S)

/-! ## Checked finite remainders and translated separation -/

def checkedFiniteRemainderUpper {r : Nat} (hr : r < 16) :
    RemainderUpper r where
  config :=
    Classical.choose (RemainderConstruction.exists_remainder_config_mod_sixteen hr)
  independent_card_le_ceil_third :=
    Classical.choose_spec
      (RemainderConstruction.exists_remainder_config_mod_sixteen hr)

def sourceAtOfExactChainTranslatedRemainder
    {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    SplitExactSourceAt k r where
  chain := chain
  remainder := RemainderPlacement.translatedRemainderUpper chain.config remainder
  separation :=
    ConcreteRemainderSplitW24.appendedRemainderSeparationOfTranslatedRemainder
      chain.config remainder.config

@[simp]
theorem sourceAtOfExactChainTranslatedRemainder_chain
    {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    (sourceAtOfExactChainTranslatedRemainder chain remainder).chain = chain :=
  rfl

@[simp]
theorem sourceAtOfExactChainTranslatedRemainder_remainder
    {k r : Nat}
    (chain : ExactChainUpper k) (remainder : RemainderUpper r) :
    (sourceAtOfExactChainTranslatedRemainder chain remainder).remainder =
      RemainderPlacement.translatedRemainderUpper chain.config remainder :=
  rfl

def sourceAtOfExactChainCheckedFiniteRemainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    SplitExactSourceAt k r :=
  sourceAtOfExactChainTranslatedRemainder
    chain
    (checkedFiniteRemainderUpper hr)

theorem fixedTarget_of_exactChain_checkedFiniteRemainder
    {k r : Nat} (hr : r < 16) (chain : ExactChainUpper k) :
    FixedTarget (16 * k + r) :=
  fixedTarget_of_sourceAt hr
    (sourceAtOfExactChainCheckedFiniteRemainder chain hr)

/-! ## Div/mod source packages -/

structure DivModSplitExactSource (n : Nat) where
  source : SplitExactSourceAt (n / 16) (n % 16)

def divModSourceOfSourceAtFamily
    (H : forall n : Nat, SplitExactSourceAt (n / 16) (n % 16))
    (n : Nat) :
    DivModSplitExactSource n where
  source := H n

theorem fixedTarget_of_divModSource
    {n : Nat} (S : DivModSplitExactSource n) :
    FixedTarget n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact fixedTarget_of_sourceAt hr S.source

/-- A package of source-facing split data for every vertex count. -/
structure RemainderSplitExactSourcePackage where
  sourceAt : forall n : Nat, DivModSplitExactSource n

def packageOfDivModSources
    (H : forall n : Nat, DivModSplitExactSource n) :
    RemainderSplitExactSourcePackage where
  sourceAt := H

def packageOfSourceAtFamily
    (H : forall n : Nat, SplitExactSourceAt (n / 16) (n % 16)) :
    RemainderSplitExactSourcePackage :=
  packageOfDivModSources (divModSourceOfSourceAtFamily H)

theorem fixedTarget_of_package
    (P : RemainderSplitExactSourcePackage) (n : Nat) :
    FixedTarget n :=
  fixedTarget_of_divModSource (P.sourceAt n)

theorem arbitraryTarget_of_package
    (P : RemainderSplitExactSourcePackage) :
    ArbitraryTarget := by
  intro n
  exact fixedTarget_of_package P n

/-! ## Constructors from exact-chain sources plus checked remainders -/

def exactChainUpperOfExactSourcePackageDiv
    (P : ExactSourcePackage) (n : Nat) :
    ExactChainUpper (n / 16) :=
  PositiveExactChainPackageW26.exactChainUpperOfPackageDiv P n

def divModSourceOfExactSourcePackage
    (P : ExactSourcePackage) (n : Nat) :
    DivModSplitExactSource n where
  source :=
    sourceAtOfExactChainCheckedFiniteRemainder
      (exactChainUpperOfExactSourcePackageDiv P n)
      (Nat.mod_lt n (by norm_num))

def packageOfExactSourcePackage
    (P : ExactSourcePackage) :
    RemainderSplitExactSourcePackage :=
  packageOfDivModSources (divModSourceOfExactSourcePackage P)

def packageOfExactChainFamily
    (H : ExactChainFamily) :
    RemainderSplitExactSourcePackage :=
  packageOfExactSourcePackage
    (PositiveExactChainPackageW26.packageOfPositiveExactChains H)

theorem nonempty_package_of_exactSourcePackage :
    Nonempty ExactSourcePackage -> Nonempty RemainderSplitExactSourcePackage := by
  intro h
  cases h with
  | intro P => exact Nonempty.intro (packageOfExactSourcePackage P)

theorem arbitraryTarget_of_exactSourcePackage
    (P : ExactSourcePackage) :
    ArbitraryTarget :=
  arbitraryTarget_of_package (packageOfExactSourcePackage P)

theorem arbitraryTarget_of_exactChainFamily
    (H : ExactChainFamily) :
    ArbitraryTarget :=
  arbitraryTarget_of_package (packageOfExactChainFamily H)

/-- The remaining split blocker after this file: inhabit the exact-chain
source package.  The remainder and separation side is constructed here. -/
abbrev RemainingSplitBlocker : Prop :=
  Nonempty ExactSourcePackage

theorem arbitraryTarget_of_remainingSplitBlocker :
    RemainingSplitBlocker -> ArbitraryTarget := by
  intro h
  cases h with
  | intro P => exact arbitraryTarget_of_exactSourcePackage P

end

end RemainderSplitExactSourceW28
end PachToth

namespace Verified

abbrev PachTothW28RemainderSplitExactSourcePackage : Type :=
  PachToth.RemainderSplitExactSourceW28.RemainderSplitExactSourcePackage

theorem pachtoth_w28_arbitraryTarget_of_remainderSplitExactSourcePackage
    (P : PachTothW28RemainderSplitExactSourcePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.RemainderSplitExactSourceW28.arbitraryTarget_of_package P

theorem pachtoth_w28_arbitraryTarget_of_exactChainFamily
    (H : PachToth.RemainderSplitExactSourceW28.ExactChainFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.RemainderSplitExactSourceW28.arbitraryTarget_of_exactChainFamily H

theorem pachtoth_w28_arbitraryTarget_of_remainingSplitBlocker :
    PachToth.RemainderSplitExactSourceW28.RemainingSplitBlocker ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.RemainderSplitExactSourceW28.arbitraryTarget_of_remainingSplitBlocker

end Verified
end ErdosProblems1066
