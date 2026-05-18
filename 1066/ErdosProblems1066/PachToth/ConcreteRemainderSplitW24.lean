import ErdosProblems1066.PachToth.ArbitraryNExactRemainderClosure
import ErdosProblems1066.PachToth.SmallLengthExactTargetsInhabitationW23
import ErdosProblems1066.PachToth.SplitCertificateBridge

set_option autoImplicit false

/-!
# W24 concrete remainder/split bridges

This file adds a small, concrete bridge just upstream of
`SplitCertificateBridge.FarApartRemainderCertificate`.

For the split-counting theorem, callers do not need to supply an already
assembled combined configuration.  It is enough to supply the two checked
blocks plus the minimal cross-block facts:

* every chain/remainder pair is separated by distance at least one, so the
  appended point set is a `UDConfig`;
* every chain/remainder pair is not at distance exactly one, recording the
  far-apart/no-cross-unit-edge obligation.

The file then packages those facts into the existing canonical split
realization and downstream `5 / 16` target theorems.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteRemainderSplitW24

open Arithmetic

noncomputable section

/-- Minimal cross-block hypotheses for appending a checked chain block and a
checked remainder block without changing either internal configuration. -/
structure AppendedRemainderSeparation {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) where
  cross_sep :
    forall (i : Fin m) (j : Fin r),
      1 <= eucDist (chain.pts i) (remainder.pts j)
  cross_far :
    forall (i : Fin m) (j : Fin r),
      eucDist (chain.pts i) (remainder.pts j) ≠ 1

/-- The direct append of a chain configuration and a remainder configuration,
certified by explicit cross-block separation. -/
def appendedConfig {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (H : AppendedRemainderSeparation chain remainder) :
    _root_.UDConfig (m + r) where
  pts := Fin.append chain.pts remainder.pts
  sep := by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
        induction b using Fin.addCases with
        | left j =>
            have hij : i ≠ j := by
              intro h
              exact hab (by simp [h])
            simpa using chain.sep i j hij
        | right j =>
            simpa using H.cross_sep i j
    | right i =>
        induction b using Fin.addCases with
        | left j =>
            have hsep := H.cross_sep j i
            simpa [_root_.eucDist_comm] using hsep
        | right j =>
            have hij : i ≠ j := by
              intro h
              exact hab (by simp [h])
            simpa using remainder.sep i j hij

@[simp]
lemma appendedConfig_chain_pts {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (H : AppendedRemainderSeparation chain remainder)
    (i : Fin m) :
    (appendedConfig chain remainder H).pts (Fin.castAdd r i) =
      chain.pts i := by
  simp [appendedConfig]

@[simp]
lemma appendedConfig_remainder_pts {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (H : AppendedRemainderSeparation chain remainder)
    (j : Fin r) :
    (appendedConfig chain remainder H).pts (Fin.natAdd m j) =
      remainder.pts j := by
  simp [appendedConfig]

lemma appendedConfig_cross_far {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (H : AppendedRemainderSeparation chain remainder)
    (i : Fin m) (j : Fin r) :
    eucDist
        ((appendedConfig chain remainder H).pts (Fin.castAdd r i))
        ((appendedConfig chain remainder H).pts (Fin.natAdd m j)) ≠
      1 := by
  simpa using H.cross_far i j

/-- Turn the minimal cross-block hypotheses into the existing far-apart
certificate consumed by `SplitCertificateBridge`. -/
def farApartRemainderCertificateOfSeparation {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r)
    (H : AppendedRemainderSeparation chain remainder) :
    SplitCertificateBridge.FarApartRemainderCertificate chain remainder where
  config := appendedConfig chain remainder H
  chain_points := by
    intro i
    simp
  remainder_points := by
    intro j
    simp
  cross_far := by
    intro i j
    exact appendedConfig_cross_far chain remainder H i j

/-- Exact-chain and remainder upper certificates plus minimal cross-block
separation give the canonical split realization used by split soundness. -/
def canonicalSplitRealizationOfExactChainRemainderSeparation {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r)
    (H : AppendedRemainderSeparation chain.config remainder.config) :
    SplitSoundness.CanonicalSplitRealization k r :=
  SplitCertificateBridge.canonicalSplitRealizationOfExactChainFarApart
    chain
    remainder
    (farApartRemainderCertificateOfSeparation chain.config remainder.config H)

/-- Existence bridge for canonical split realizations from the sharpened
cross-block separation fields. -/
theorem exists_canonicalSplitRealization_of_exactChain_remainderSeparation
    {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r)
    (H : AppendedRemainderSeparation chain.config remainder.config) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact Exists.intro
    (canonicalSplitRealizationOfExactChainRemainderSeparation
      chain remainder H)
    True.intro

/-- Downstream split counting theorem from exact-chain data, remainder data,
and the sharpened cross-block separation fields. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChain_remainderSeparation
    {k r : Nat} (hr : r < 16)
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r)
    (H : AppendedRemainderSeparation chain.config remainder.config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_exactChain_remainderSeparation
        chain remainder H)

/-- Exact target data and the checked finite remainder construction give a
canonical split realization once the concrete cross-block separation fields
are supplied for that checked remainder. -/
theorem exists_canonicalSplitRealization_of_exactTarget_checkedRemainder_separation
    (Hexact : targetUpperConstructionFiveSixteen)
    {k r : Nat} (hr : r < 16)
    (H :
      AppendedRemainderSeparation
        (SplitSoundness.exactChainUpperOfTarget Hexact k).config
        (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
          hr).config) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact
    exists_canonicalSplitRealization_of_exactChain_remainderSeparation
      (SplitSoundness.exactChainUpperOfTarget Hexact k)
      (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen hr)
      H

/-- Exact target data plus checked finite remainders close the split count
at `16 * k + r` under explicit cross-block separation/no-unit hypotheses. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_separation
    (Hexact : targetUpperConstructionFiveSixteen)
    {k r : Nat} (hr : r < 16)
    (H :
      AppendedRemainderSeparation
        (SplitSoundness.exactChainUpperOfTarget Hexact k).config
        (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
          hr).config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_exactChain_remainderSeparation
      hr
      (SplitSoundness.exactChainUpperOfTarget Hexact k)
      (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen hr)
      H

/-- Div/mod version of the explicit-separation bridge. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_divMod_checkedRemainder_separation
    (Hexact : targetUpperConstructionFiveSixteen)
    (n : Nat) (hr : n % 16 < 16)
    (H :
      AppendedRemainderSeparation
        (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16)).config
        (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
          hr).config) :
    targetUpperConstructionFiveSixteenAt n := by
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_separation
      Hexact hr H

/-- Family form: exact target data plus explicit cross-block separation for
each div/mod checked remainder gives the full arbitrary-`n` target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder_separation
    (Hexact : targetUpperConstructionFiveSixteen)
    (H :
      forall n : Nat,
        AppendedRemainderSeparation
          (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16)).config
          (ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen
            (Nat.mod_lt n (by norm_num))).config) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_divMod_checkedRemainder_separation
      Hexact n (Nat.mod_lt n (by norm_num)) (H n)

/-- W23 small-length exact targets still discharge the finite small-case
complement below the six-block threshold; this wrapper keeps that side
visible next to the W24 split bridge. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo_ninetySix_of_smallLengthExactBlockTargets
    (C :
      SmallLengthExactTargetsInhabitationW23.SmallLengthExactBlockTargets) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * 6) := by
  exact
    SmallLengthExactTargetsInhabitationW23.exactVertexTargetsBelow_ninetySix_of_exactFiniteTargets
      (SmallLengthExactTargetsInhabitationW23.exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
        C)

end

end ConcreteRemainderSplitW24
end PachToth
end ErdosProblems1066
