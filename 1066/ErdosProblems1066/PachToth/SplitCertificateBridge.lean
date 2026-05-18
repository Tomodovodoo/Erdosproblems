import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.SplitSoundness

set_option autoImplicit false

/-!
# Pach--Toth split certificate bridge

This module packages the remaining arbitrary-`n` split geometry as explicit
certificate data.  It does not assert that the remainder has been placed far
from the exact chain; instead, a caller must supply the combined
configuration and the no-cross-unit-distance fact.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SplitCertificateBridge

open Arithmetic

noncomputable section

/-- A concrete combined configuration preserving a chain block and a
remainder block.

The `cross_far` field is the explicit geometric obligation needed to certify
that no chain vertex and remainder vertex form a unit edge in the combined
configuration. -/
structure FarApartRemainderCertificate {m r : Nat}
    (chain : _root_.UDConfig m) (remainder : _root_.UDConfig r) where
  config : _root_.UDConfig (m + r)
  chain_points :
    forall i : Fin m,
      config.pts (Fin.castAdd r i) = chain.pts i
  remainder_points :
    forall j : Fin r,
      config.pts (Fin.natAdd m j) = remainder.pts j
  cross_far :
    forall (i : Fin m) (j : Fin r),
      Ne
        (eucDist (config.pts (Fin.castAdd r i))
          (config.pts (Fin.natAdd m j)))
        1

/-- Existence of the split-soundness canonical realization, named for
downstream reduction lemmas. -/
def exists_canonicalSplitRealization (k r : Nat) : Prop :=
  Exists fun _S : SplitSoundness.CanonicalSplitRealization k r => True

/-- Repackage exact chain and remainder upper certificates plus an explicit
far-apart combined configuration as the canonical split realization consumed
by `SplitSoundness`. -/
def canonicalSplitRealizationOfExactChainFarApart {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r)
    (F : FarApartRemainderCertificate chain.config remainder.config) :
    SplitSoundness.CanonicalSplitRealization k r where
  chain := chain
  remainder := remainder
  config := F.config
  chain_points := F.chain_points
  remainder_points := F.remainder_points
  cross_far := F.cross_far

/-- The named existence reduction for canonical split realizations.  The
theorem only packages supplied data; it constructs no far-apart placement. -/
theorem exists_canonicalSplitRealization_of_exactChain_farApart {k r : Nat}
    (chain : SplitSoundness.ExactChainUpper k)
    (remainder : SplitSoundness.RemainderUpper r)
    (F : FarApartRemainderCertificate chain.config remainder.config) :
    exists_canonicalSplitRealization k r := by
  exact Exists.intro
    (canonicalSplitRealizationOfExactChainFarApart chain remainder F)
    True.intro

/-- A deformed closed placement supplies the exact-chain upper certificate
through the existing indexed-chain counting theorem. -/
def exactChainUpperOfClosedPlacement {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    SplitSoundness.ExactChainUpper k where
  config := P.config
  independent_card_le_five_mul := by
    intro s hs
    exact IndexedChain.independent_card_le_five_mul hk
      P.toIndexedChainRealization s hs

/-- Specialize the canonical split bridge to a deformed closed placement and
the checked remainder construction.  The far-apart combined configuration is
still an explicit input. -/
def canonicalSplitRealizationOfClosedPlacementFarApart {k r : Nat}
    {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk)
    (F :
      FarApartRemainderCertificate
        P.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    SplitSoundness.CanonicalSplitRealization k r :=
  canonicalSplitRealizationOfExactChainFarApart
    (exactChainUpperOfClosedPlacement P)
    (SplitSoundness.remainderUpperOfConstruction r)
    F

/-- A deformed closed placement plus an explicit far-apart remainder
certificate yields the named canonical split existence proposition. -/
theorem exists_canonicalSplitRealization_of_closedPlacement_farApart
    {k r : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk)
    (F :
      FarApartRemainderCertificate
        P.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    exists_canonicalSplitRealization k r := by
  exact Exists.intro
    (canonicalSplitRealizationOfClosedPlacementFarApart P F)
    True.intro

/-- Any supplied canonical split realization routes through the checked split
counting theorem to the arbitrary-`n` target at `16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
    {k r : Nat} (hr : r < 16)
    (H : exists_canonicalSplitRealization k r) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  rcases H with ⟨S, _⟩
  exact
    SplitSoundness.targetUpperConstructionFiveSixteenAt_of_canonicalSplitRealization
      hr S

/-- The closed-placement bridge followed by the existing split counting
theorem. -/
theorem targetUpperConstructionFiveSixteenAt_of_closedPlacement_farApart
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (P : DeformedPlacement.ClosedPlacement k hk)
    (F :
      FarApartRemainderCertificate
        P.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      hr
      (exists_canonicalSplitRealization_of_closedPlacement_farApart P F)

end

end SplitCertificateBridge
end PachToth
end ErdosProblems1066
