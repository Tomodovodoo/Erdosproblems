import ErdosProblems1066.PachToth.FiniteCertificateObligationsW12
import ErdosProblems1066.PachToth.LargeClosedPlacementW12
import ErdosProblems1066.PachToth.NonConnectorSeparationW12
import ErdosProblems1066.PachToth.OrbitSqDistancesW12
import ErdosProblems1066.PachToth.RemainderPlacement
import ErdosProblems1066.PachToth.SplitCertificateBridge

set_option autoImplicit false

/-!
# W13 split-soundness instantiation

This file instantiates the checked split-soundness interface from exact-chain
data, checked remainder data, and either explicit or translated far-separation
data.  It deliberately contains only packaging theorems: the finite search and
large closed-placement obligations remain explicit inputs in their W12 modules.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SplitSoundnessInstantiationW13

open Arithmetic

noncomputable section

abbrev ExistsCanonicalSplitRealization (k r : Nat) : Prop :=
  SplitCertificateBridge.exists_canonicalSplitRealization k r

abbrev checkedRemainderUpper (r : Nat) : SplitSoundness.RemainderUpper r :=
  SplitSoundness.remainderUpperOfConstruction r

/-- Minimal explicit fields for the conditional far-apart bridge. -/
structure ExactChainRemainderFarApartFields (k r : Nat) where
  chain : SplitSoundness.ExactChainUpper k
  remainder : SplitSoundness.RemainderUpper r
  farApart :
    SplitCertificateBridge.FarApartRemainderCertificate
      chain.config remainder.config

namespace ExactChainRemainderFarApartFields

def canonicalSplitRealization {k r : Nat}
    (D : ExactChainRemainderFarApartFields k r) :
    SplitSoundness.CanonicalSplitRealization k r :=
  SplitCertificateBridge.canonicalSplitRealizationOfExactChainFarApart
    D.chain D.remainder D.farApart

theorem exists_canonicalSplitRealization {k r : Nat}
    (D : ExactChainRemainderFarApartFields k r) :
    ExistsCanonicalSplitRealization k r := by
  exact Exists.intro D.canonicalSplitRealization True.intro

theorem targetUpperConstructionFiveSixteenAt {k r : Nat}
    (hr : r < 16) (D : ExactChainRemainderFarApartFields k r) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr D.exists_canonicalSplitRealization

end ExactChainRemainderFarApartFields

/-- Exact-chain data and any checked remainder instantiate the named canonical
split-realization existence proposition by translating the remainder far away. -/
theorem exists_canonicalSplitRealization_of_exactChain_translatedRemainder
    {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r) :
    ExistsCanonicalSplitRealization k r := by
  exact Exists.intro
    (RemainderPlacement.canonicalSplitRealizationOfExactChainTranslatedRemainder
      chain remainder)
    True.intro

/-- Exact-chain data plus the checked finite remainder construction instantiate
the named canonical split-realization existence proposition. -/
theorem exists_canonicalSplitRealization_of_exactChain_checkedRemainder
    {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k) :
    ExistsCanonicalSplitRealization k r := by
  exact
    exists_canonicalSplitRealization_of_exactChain_translatedRemainder
      chain (checkedRemainderUpper r)

/-- The same instantiation followed by split soundness. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChain_checkedRemainder
    {k r : Nat} (hr : r < 16)
    (chain : SplitSoundness.ExactChainUpper k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_exactChain_checkedRemainder
        (k := k) (r := r) chain)

/-- Exact `16 * k` target data supplies the div/mod exact-chain block, while
the remainder and far-separation are instantiated by the checked translated
remainder construction. -/
theorem exists_canonicalSplitRealization_divMod_of_exactTarget
    (Hexact : PachToth.targetUpperConstructionFiveSixteen) (n : Nat) :
    ExistsCanonicalSplitRealization (n / 16) (n % 16) := by
  exact
    exists_canonicalSplitRealization_of_exactChain_checkedRemainder
      (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16))

/-- A div/mod canonical split realization gives the target at the original
vertex count. -/
theorem targetUpperConstructionFiveSixteenAt_of_divMod_canonicalSplitRealization
    (n : Nat)
    (H : ExistsCanonicalSplitRealization (n / 16) (n % 16)) :
    PachToth.targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr H

/-- Exact-target data extends to a fixed arbitrary vertex count via the W13
split instantiation. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget
    (Hexact : PachToth.targetUpperConstructionFiveSixteen) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n := by
  exact
    targetUpperConstructionFiveSixteenAt_of_divMod_canonicalSplitRealization
      n
      (exists_canonicalSplitRealization_divMod_of_exactTarget Hexact n)

/-- Exact-target data extends to the proposition-valued arbitrary-`n` target
via the W13 split instantiation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (Hexact : PachToth.targetUpperConstructionFiveSixteen) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact targetUpperConstructionFiveSixteenAt_of_exactTarget Hexact n

/-- W12 raw all-positive finite-certificate fields routed through the W13
split instantiation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_rawFields
    (C : FiniteCertificateObligationsW12.AllPositiveNonConnectorFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteen_of_rawFields C)

/-- W12 native table-family package routed through the W13 split
instantiation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_tableFamilyPackage
    (P : FiniteCertificateObligationsW12.TableFamilyPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteen_of_tableFamilyPackage P)

/-- W12 vector-table package routed through the W13 split instantiation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_vectorPackage
    (P : FiniteCertificateObligationsW12.VectorPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteen_of_vectorPackage P)

/-- W12 list-table package routed through the W13 split instantiation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_listPackage
    (P : FiniteCertificateObligationsW12.ListPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteen_of_listPackage P)

/-- W12 generated local-vertex non-connector separation data routed through
the W13 split instantiation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_W12_generatedNonConnectorFamily
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      T.targetUpperConstructionFiveSixteen

/-- A W12 sufficiently-large explicit closed-placement certificate supplies
canonical split realizations for every large exact-chain block after adding
the checked translated remainder. -/
theorem exists_canonicalSplitRealization_of_W12_largeClosedPlacement
    {K0 k r : Nat}
    (C : LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0)
    (hK : K0 <= k) (hk : 0 < k) :
    ExistsCanonicalSplitRealization k r := by
  exact
    exists_canonicalSplitRealization_of_exactChain_checkedRemainder
      (C.exactChainUpper k hK hk)

/-- The W12 sufficiently-large explicit closed-placement certificate followed
by checked translated remainders and split soundness. -/
theorem targetUpperConstructionFiveSixteenAt_of_W12_largeClosedPlacement
    {K0 k r : Nat}
    (C : LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0)
    (hK : K0 <= k) (hk : 0 < k) (hr : r < 16) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_W12_largeClosedPlacement
        (K0 := K0) (k := k) (r := r) C hK hk)

/-- Convert any exact-block target-at statement into the exact-chain upper
certificate expected by split soundness. -/
def exactChainUpperOfExactBlockTarget {k : Nat}
    (H : PachToth.targetUpperConstructionFiveSixteenAt (16 * k)) :
    SplitSoundness.ExactChainUpper k where
  config := Classical.choose H
  independent_card_le_five_mul := by
    intro s hs
    have hbound := Classical.choose_spec H s hs
    have hceil : ceilDiv (5 * (16 * k)) 16 = 5 * k := by
      unfold ceilDiv
      omega
    simpa [hceil] using hbound

/-- The W12 orbit-square-distance bridge supplies an exact block target; this
adapter exposes the corresponding checked exact-chain upper certificate. -/
def exactChainUpperOfW12OrbitSqDistances
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        OrbitSqDistancesW12.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        OrbitSqDistancesW12.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (horbit :
      RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
        OrbitSqDistancesW12.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    SplitSoundness.ExactChainUpper k :=
  exactChainUpperOfExactBlockTarget
    (OrbitSqDistancesW12.exactBlockTarget_of_concreteTransitionObligations_orbitSqDistances
      hk orientation closure separated horbit)

/-- The W12 orbit-square-distance bridge followed by checked translated
remainders gives the named canonical split-realization proposition. -/
theorem exists_canonicalSplitRealization_of_W12_orbitSqDistances
    {k r : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        OrbitSqDistancesW12.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        OrbitSqDistancesW12.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (horbit :
      RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
        OrbitSqDistancesW12.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    ExistsCanonicalSplitRealization k r := by
  exact
    exists_canonicalSplitRealization_of_exactChain_checkedRemainder
      (exactChainUpperOfW12OrbitSqDistances
        hk orientation closure separated horbit)

end

end SplitSoundnessInstantiationW13
end PachToth
end ErdosProblems1066
