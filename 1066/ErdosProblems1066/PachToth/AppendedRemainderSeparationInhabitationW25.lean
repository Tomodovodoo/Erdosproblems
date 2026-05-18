import ErdosProblems1066.PachToth.ConcreteRemainderSplitW24

set_option autoImplicit false

/-!
# W25 inhabited appended-remainder separation

This file closes the explicit W24 appended-remainder separation field for the
canonical translated remainder from `RemainderPlacement`, then routes that
field through the existing `ConcreteRemainderSplitW24` split bridges.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteRemainderSplitW24

open Arithmetic

noncomputable section

/-- The translated remainder supplied by `RemainderPlacement` satisfies the
minimal cross-block separation/no-unit-distance fields required by the W24
append bridge. -/
def appendedRemainderSeparationOfTranslatedRemainder {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) :
    AppendedRemainderSeparation
      chain
      (RemainderPlacement.translatedRemainder chain remainder) where
  cross_sep := by
    intro i j
    exact RemainderPlacement.chain_translatedRemainder_separated
      chain remainder i j
  cross_far := by
    intro i j
    exact RemainderPlacement.chain_translatedRemainder_ne_unit
      chain remainder i j

/-- Adapter from the translated-remainder machinery to the W24 explicit
far-apart certificate obtained via appended separation. -/
def farApartRemainderCertificateOfTranslatedRemainder {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) :
    SplitCertificateBridge.FarApartRemainderCertificate
      chain
      (RemainderPlacement.translatedRemainder chain remainder) :=
  farApartRemainderCertificateOfSeparation
    chain
    (RemainderPlacement.translatedRemainder chain remainder)
    (appendedRemainderSeparationOfTranslatedRemainder chain remainder)

/-- Exact-chain and remainder upper certificates give a canonical split
realization after translating the remainder and discharging the W24 appended
separation field. -/
def canonicalSplitRealizationOfExactChainTranslatedSeparation {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r) :
    SplitSoundness.CanonicalSplitRealization k r :=
  canonicalSplitRealizationOfExactChainRemainderSeparation
    chain
    (RemainderPlacement.translatedRemainderUpper chain.config remainder)
    (appendedRemainderSeparationOfTranslatedRemainder
      chain.config remainder.config)

/-- Existence form of the translated-remainder appended-separation bridge. -/
theorem exists_canonicalSplitRealization_of_exactChain_translatedSeparation
    {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact Exists.intro
    (canonicalSplitRealizationOfExactChainTranslatedSeparation
      chain remainder)
    True.intro

/-- Downstream split target from exact-chain data and a checked remainder,
with the W24 appended-separation field supplied by translation. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChain_translatedSeparation
    {k r : Nat} (hr : r < 16)
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_exactChain_translatedSeparation
        chain remainder)

/-- Exact target data and the checked finite remainder construction produce
the W24 appended-separation field by translating the checked remainder. -/
def checkedRemainderTranslatedSeparation
    (Hexact : targetUpperConstructionFiveSixteen)
    {k r : Nat} (hr : r < 16) :
    AppendedRemainderSeparation
      (SplitSoundness.exactChainUpperOfTarget Hexact k).config
      (RemainderPlacement.translatedRemainder
        (SplitSoundness.exactChainUpperOfTarget Hexact k).config
        (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
          hr).config) :=
  appendedRemainderSeparationOfTranslatedRemainder
    (SplitSoundness.exactChainUpperOfTarget Hexact k).config
    (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
      hr).config

/-- Exact target data plus checked finite remainders close the split count at
`16 * k + r`; the explicit W24 separation field is inhabited by the canonical
far-apart translation. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_translatedSeparation
    (Hexact : targetUpperConstructionFiveSixteen)
    {k r : Nat} (hr : r < 16) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_exactChain_translatedSeparation
      hr
      (SplitSoundness.exactChainUpperOfTarget Hexact k)
      (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen hr)

/-- Div/mod form of the translated appended-separation bridge. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_divMod_checkedRemainder_translatedSeparation
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_translatedSeparation
      Hexact hr

/-- Arbitrary-`n` form: the checked finite remainder is translated far away,
which inhabits the W24 appended-separation field for every div/mod split. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder_translatedSeparation
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_divMod_checkedRemainder_translatedSeparation
      Hexact n

end

end ConcreteRemainderSplitW24
end PachToth
end ErdosProblems1066
