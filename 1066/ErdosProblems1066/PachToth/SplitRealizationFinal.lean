import ErdosProblems1066.PachToth.SplitSoundness
import ErdosProblems1066.PachToth.RemainderConstruction
import ErdosProblems1066.PachToth.RemainderPlacement
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart
import ErdosProblems1066.PachToth.FinalConditional

set_option autoImplicit false

/-!
# Final split-realization closure for arbitrary `n`

This module closes the conditional arbitrary-`n` route from:

* exact `16 * k` closed placements or exact-target data,
* the checked finite remainder construction, and
* the far-apart translated remainder placement.

All statements are conditional facades over explicit data supplied by earlier
interfaces.  No period certificate, lower-bound table, or closed placement is
asserted here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SplitRealizationFinal

open Arithmetic
open FiniteGraph
open GeneratedSeparationFarApart

noncomputable section

abbrev R2 := Prod Real Real

/-- The checked remainder construction packaged as the split-soundness
remainder upper certificate. -/
def checkedRemainderUpper (r : Nat) : SplitSoundness.RemainderUpper r where
  config := Classical.choose (RemainderConstruction.exists_remainder_config r)
  independent_card_le_ceil_third :=
    Classical.choose_spec (RemainderConstruction.exists_remainder_config r)

/-- Exact-chain data plus the checked remainder and an explicit far-apart
combined placement give the named canonical split-realization existence
proposition. -/
theorem exists_canonicalSplitRealization_of_exactChain_checkedRemainder_farApart
    {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        chain.config
        (checkedRemainderUpper r).config) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact
    SplitCertificateBridge.exists_canonicalSplitRealization_of_exactChain_farApart
      chain
      (checkedRemainderUpper r)
      F

/-- Exact-chain data plus the checked remainder and an explicit far-apart
combined placement route through split soundness to the target at
`16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChain_checkedRemainder_farApart
    {k r : Nat} (hr : r < 16)
    (chain : SplitSoundness.ExactChainUpper k)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        chain.config
        (checkedRemainderUpper r).config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_exactChain_checkedRemainder_farApart
        chain F)

/-- Exact-chain data and the checked remainder give the named canonical
split-realization existence proposition after translating the remainder far
away from the chain. -/
theorem exists_canonicalSplitRealization_of_exactChain_translatedCheckedRemainder
    {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k) :
    SplitCertificateBridge.exists_canonicalSplitRealization k r := by
  exact
    Exists.intro
      (RemainderPlacement.canonicalSplitRealizationOfExactChainTranslatedRemainder
        chain
        (checkedRemainderUpper r))
      True.intro

/-- Exact-chain data and the checked translated remainder route through
split soundness to the target at `16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChain_translatedCheckedRemainder
    {k r : Nat} (hr : r < 16)
    (chain : SplitSoundness.ExactChainUpper k) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      chain
      (checkedRemainderUpper r)

/-- Exact `16 * k` target data supplies the div/mod exact-chain block, and
an explicit far-apart placement of the checked remainder gives the named
canonical split-realization existence proposition. -/
theorem exists_canonicalSplitRealization_divMod_of_exactTarget_checkedRemainder_farApart
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16)).config
        (checkedRemainderUpper (n % 16)).config) :
    SplitCertificateBridge.exists_canonicalSplitRealization (n / 16) (n % 16) := by
  exact
    exists_canonicalSplitRealization_of_exactChain_checkedRemainder_farApart
      (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16))
      F

/-- Exact `16 * k` target data supplies the div/mod exact-chain block, and
the translated checked remainder gives the named canonical split-realization
existence proposition. -/
theorem exists_canonicalSplitRealization_divMod_of_exactTarget_translatedCheckedRemainder
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    SplitCertificateBridge.exists_canonicalSplitRealization (n / 16) (n % 16) := by
  exact
    exists_canonicalSplitRealization_of_exactChain_translatedCheckedRemainder
      (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16))

/-- Exact `16 * k` target data extends to `n` when the div/mod checked
remainder is supplied with an explicit far-apart placement. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_farApart
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16)).config
        (checkedRemainderUpper (n % 16)).config) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_divMod_of_exactTarget_checkedRemainder_farApart
        Hexact n F)

/-- Exact `16 * k` target data extends to every vertex count by appending the
checked remainder block and translating it far away from the exact chain. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_remainderFarApart
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16))
      (checkedRemainderUpper (n % 16))

/-- Exact `16 * k` target data gives the full arbitrary-`n` target using the
checked remainder construction and far-apart translated placement. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_remainderFarApart
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_remainderFarApart
      Hexact n

/-- A family of exact closed placements gives the arbitrary-`n` target after
adding the checked far-apart remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements_remainderFarApart
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_remainderFarApart
      (DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
        H)

/-- Generated period equations and cross-block lower bounds imply the full
arbitrary-`n` target once routed through the exact target and the split
remainder/far-apart construction. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_period_crossBlockDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
          (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let exactTarget :=
    targetUpperConstructionFiveSixteen_of_period_crossBlockDistanceLowerBounds_reduced
      O base orientation period base_same_block_isometry
      transition_preserves_same_block_distances lower hge_one hlower
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_remainderFarApart
      exactTarget

/-- Final conditional period-search/equation-transition/cross-block data imply
the full arbitrary-`n` target through the split realization closure. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finalConditionalFamily
    (F : FinalConditional.EquationPeriodSearchCrossBlockFamily) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_remainderFarApart
      (FinalConditional.exactTarget_of_periodSearch_equationTransitions_crossBlock
        F)

end

end SplitRealizationFinal
end PachToth
end ErdosProblems1066
