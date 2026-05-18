import ErdosProblems1066.PachToth.RemainderSplitExactSourceW28
import ErdosProblems1066.PachToth.SplitRealizationClosure
import ErdosProblems1066.PachToth.SplitRealizationFinal

set_option autoImplicit false

/-!
# W29 remainder split closure

This leaf sharpens the W28 remainder split handoff.  It records that the
checked finite remainder construction, after the existing far-apart
translation, supplies the concrete W24 separation certificate, the
`FarApartRemainderCertificate`, the canonical split realization, and the W28
source package.

The exact-chain family remains an explicit dependency.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RemainderSplitClosureW29

open Arithmetic
open FiniteGraph

noncomputable section

abbrev ExactChainUpper (k : Nat) : Type :=
  RemainderSplitExactSourceW28.ExactChainUpper k

abbrev RemainderUpper (r : Nat) : Type :=
  RemainderSplitExactSourceW28.RemainderUpper r

abbrev AppendedRemainderSeparation {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Prop :=
  RemainderSplitExactSourceW28.AppendedRemainderSeparation chain remainder

abbrev FarApartRemainderCertificate {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) : Type :=
  RemainderSplitExactSourceW28.FarApartRemainderCertificate chain remainder

abbrev CanonicalSplitRealization (k r : Nat) : Type :=
  RemainderSplitExactSourceW28.CanonicalSplitRealization k r

abbrev SplitExactSourceAt (k r : Nat) : Type :=
  RemainderSplitExactSourceW28.SplitExactSourceAt k r

abbrev DivModSplitExactSource (n : Nat) : Type :=
  RemainderSplitExactSourceW28.DivModSplitExactSource n

abbrev RemainderSplitExactSourcePackage : Type :=
  RemainderSplitExactSourceW28.RemainderSplitExactSourcePackage

abbrev ExactChainFamily : Type :=
  RemainderSplitExactSourceW28.ExactChainFamily

abbrev ArbitraryTarget : Prop :=
  RemainderSplitExactSourceW28.ArbitraryTarget

/-! ## Concrete checked-remainder closure -/

def exactChainUpperOfFamily
    (H : ExactChainFamily) (k : Nat) :
    ExactChainUpper k := by
  by_cases hk : 0 < k
  case pos =>
    exact H k hk
  case neg =>
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    exact SplitSoundness.emptyExactChainUpper

def checkedFiniteRemainderUpper {r : Nat} (hr : r < 16) :
    RemainderUpper r :=
  RemainderSplitExactSourceW28.checkedFiniteRemainderUpper hr

def translatedCheckedRemainderUpper
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    RemainderUpper r :=
  RemainderPlacement.translatedRemainderUpper
    chain.config
    (checkedFiniteRemainderUpper hr)

def appendedSeparationOfTranslatedCheckedRemainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    AppendedRemainderSeparation
      chain.config
      (translatedCheckedRemainderUpper chain hr).config :=
  ConcreteRemainderSplitW24.appendedRemainderSeparationOfTranslatedRemainder
    chain.config
    (checkedFiniteRemainderUpper hr).config

def farApartCertificateOfTranslatedCheckedRemainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    FarApartRemainderCertificate
      chain.config
      (translatedCheckedRemainderUpper chain hr).config :=
  ConcreteRemainderSplitW24.farApartRemainderCertificateOfTranslatedRemainder
    chain.config
    (checkedFiniteRemainderUpper hr).config

def canonicalSplitRealizationOfTranslatedCheckedRemainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    CanonicalSplitRealization k r :=
  ConcreteRemainderSplitW24.canonicalSplitRealizationOfExactChainTranslatedSeparation
    chain
    (checkedFiniteRemainderUpper hr)

theorem exists_canonicalSplitRealization_of_translatedCheckedRemainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact Exists.intro
    (canonicalSplitRealizationOfTranslatedCheckedRemainder chain hr)
    True.intro

def splitExactSourceAtOfTranslatedCheckedRemainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    SplitExactSourceAt k r :=
  RemainderSplitExactSourceW28.sourceAtOfExactChainCheckedFiniteRemainder
    chain hr

@[simp]
theorem splitExactSourceAtOfTranslatedCheckedRemainder_chain
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    (splitExactSourceAtOfTranslatedCheckedRemainder chain hr).chain = chain :=
  rfl

@[simp]
theorem splitExactSourceAtOfTranslatedCheckedRemainder_remainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    (splitExactSourceAtOfTranslatedCheckedRemainder chain hr).remainder =
      translatedCheckedRemainderUpper chain hr :=
  rfl

@[simp]
theorem canonicalSplitRealizationOfSourceAt_translatedCheckedRemainder
    {k r : Nat} (chain : ExactChainUpper k) (hr : r < 16) :
    RemainderSplitExactSourceW28.canonicalSplitRealizationOfSourceAt
        (splitExactSourceAtOfTranslatedCheckedRemainder chain hr) =
      canonicalSplitRealizationOfTranslatedCheckedRemainder chain hr :=
  rfl

/-! ## Div/mod source package from an exact-chain family -/

def splitExactSourceAtOfExactChainFamily
    (H : ExactChainFamily) {k r : Nat} (hr : r < 16) :
    SplitExactSourceAt k r :=
  splitExactSourceAtOfTranslatedCheckedRemainder
    (exactChainUpperOfFamily H k)
    hr

def divModSourceOfExactChainFamily
    (H : ExactChainFamily) (n : Nat) :
    DivModSplitExactSource n where
  source :=
    splitExactSourceAtOfExactChainFamily
      H
      (Nat.mod_lt n (by norm_num))

def packageOfExactChainFamily
    (H : ExactChainFamily) :
    RemainderSplitExactSourcePackage :=
  RemainderSplitExactSourceW28.packageOfDivModSources
    (divModSourceOfExactChainFamily H)

theorem arbitraryTarget_of_exactChainFamily
    (H : ExactChainFamily) :
    ArbitraryTarget :=
  RemainderSplitExactSourceW28.arbitraryTarget_of_package
    (packageOfExactChainFamily H)

abbrev RemainingExactChainFamilyDependency : Prop :=
  Nonempty ExactChainFamily

theorem nonempty_package_of_exactChainFamilyDependency :
    RemainingExactChainFamilyDependency ->
      Nonempty RemainderSplitExactSourcePackage := by
  intro h
  cases h with
  | intro H =>
      exact Nonempty.intro (packageOfExactChainFamily H)

theorem arbitraryTarget_of_exactChainFamilyDependency :
    RemainingExactChainFamilyDependency -> ArbitraryTarget := by
  intro h
  cases h with
  | intro H =>
      exact arbitraryTarget_of_exactChainFamily H

/-! ## Compatibility facades for final split-realization modules -/

theorem final_exists_canonicalSplitRealization_of_exactChain
    {k r : Nat} (chain : ExactChainUpper k) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r :=
  SplitRealizationFinal.exists_canonicalSplitRealization_of_exactChain_translatedCheckedRemainder
    chain

theorem final_targetUpperConstructionFiveSixteenAt_of_exactChain
    {k r : Nat} (hr : r < 16) (chain : ExactChainUpper k) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) :=
  SplitRealizationFinal.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedCheckedRemainder
    hr chain

def closureCanonicalSplitRealizationOfGeneratedClosedChain
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k r : Nat} (hk : 0 < k) (hr : r < 16)
    (base : LocalVertex -> SplitRealizationClosure.R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (metric :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    CanonicalSplitRealization k r :=
  canonicalSplitRealizationOfTranslatedCheckedRemainder
    (SplitRealizationClosure.exactChainUpperOfGeneratedClosedChain
      O hk base orientation period metric)
    hr

end

end RemainderSplitClosureW29
end PachToth

namespace Verified

abbrev PachTothW29RemainderSplitExactSourcePackage : Type :=
  PachToth.RemainderSplitClosureW29.RemainderSplitExactSourcePackage

abbrev PachTothW29RemainderSplitExactChainFamily : Type :=
  PachToth.RemainderSplitClosureW29.ExactChainFamily

abbrev PachTothW29RemainderSplitRemainingDependency : Prop :=
  PachToth.RemainderSplitClosureW29.RemainingExactChainFamilyDependency

noncomputable def pachtoth_w29_remainderSplitPackage_of_exactChainFamily
    (H : PachTothW29RemainderSplitExactChainFamily) :
    PachTothW29RemainderSplitExactSourcePackage :=
  PachToth.RemainderSplitClosureW29.packageOfExactChainFamily H

theorem pachtoth_w29_arbitraryTarget_of_exactChainFamily
    (H : PachTothW29RemainderSplitExactChainFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamily H

theorem pachtoth_w29_arbitraryTarget_of_remainingDependency :
    PachTothW29RemainderSplitRemainingDependency ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.RemainderSplitClosureW29.arbitraryTarget_of_exactChainFamilyDependency

end Verified
end ErdosProblems1066
