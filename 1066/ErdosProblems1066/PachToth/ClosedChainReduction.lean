import ErdosProblems1066.PachToth.ClosedPlacementInterface
import ErdosProblems1066.PachToth.RemainderPlacement
import ErdosProblems1066.PachToth.SplitCertificateBridge
import ErdosProblems1066.PachToth.TargetReduction

set_option autoImplicit false

/-!
# Closed-chain final reductions

This module is a disjoint final-spine route for the Pach--Toth closed-chain
construction.  It proves only conditional statements from explicit
certificates already named in the interface modules.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedChainReduction

open Arithmetic
open SplitCertificateBridge

noncomputable section

/-- Repackage an explicit closed-placement certificate as the exact-chain
upper certificate used by the split bridge. -/
def exactChainUpperOfExplicitClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    SplitSoundness.ExactChainUpper k :=
  SplitCertificateBridge.exactChainUpperOfClosedPlacement C.toClosedPlacement

/-- A single explicit closed-placement certificate gives the arbitrary-target
form at the exact block count.  The bound comes from the stronger exact
`5 * k` indexed-chain theorem. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  refine Exists.intro C.toClosedPlacement.config ?_
  intro s hs
  have hfive :
      s.card <= 5 * k :=
    IndexedChain.independent_card_le_five_mul hk
      C.toIndexedChainRealization s hs
  have harith : 5 * k <= ceilDiv (5 * (16 * k)) 16 := by
    unfold ceilDiv
    omega
  exact le_trans hfive harith

/-- Explicit closed-placement certificates for every positive block count
imply the exact block Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
    (H :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteen := by
  exact targetUpperConstructionFiveSixteen_of_indexedChainRealizations
    (fun k hk => (H k hk).toIndexedChainRealization)

/-- The transition-certificate variant routed through the closed-placement
interface. -/
theorem targetUpperConstructionFiveSixteen_of_explicitTransitionClosedPlacementCertificates
    (H :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteen := by
  exact targetUpperConstructionFiveSixteen_of_indexedChainRealizations
    (fun k hk => (H k hk).toIndexedChainRealization)

/-- A positive exact chain, supplied by an explicit closed-placement
certificate, plus an explicit far-apart remainder certificate gives the
target at `16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_explicitClosedPlacementCertificate_farApart
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (C : ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        C.toClosedPlacement.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_closedPlacement_farApart
      hr C.toClosedPlacement F

/-- Explicit closed-placement certificates for all positive exact chains imply
the full arbitrary-`n` Pach--Toth target.  The remainder block is placed far
away by the universal translation construction in `RemainderPlacement`, so no
additional far-apart hypothesis is needed. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
    (Hclosed :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  have hr : n % 16 < 16 := by
    exact Nat.mod_lt n (by norm_num)
  have hn : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have hAt :
      targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) := by
    by_cases hk : 0 < n / 16
    · exact
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          (exactChainUpperOfExplicitClosedPlacementCertificate (Hclosed (n / 16) hk))
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
    · have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
      have hzero :
          targetUpperConstructionFiveSixteenAt (16 * 0 + n % 16) :=
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          SplitSoundness.emptyExactChainUpper
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
      simpa [hk0] using hzero
  rw [hn]
  exact hAt

/-- Eventual explicit closed-placement certificates imply the source-faithful
eventual arbitrary-`n` Pach--Toth target.  Remainder vertices are supplied by
the checked finite remainder construction and placed far away by
`RemainderPlacement`. -/
theorem targetUpperConstructionFiveSixteenEventually_of_eventualExplicitClosedPlacementCertificates
    (K0 : Nat)
    (Hclosed :
      forall (k : Nat), K0 <= k -> forall hk : 0 < k,
        ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro (16 * K0) ?_
  intro n hn
  have hr : n % 16 < 16 := by
    exact Nat.mod_lt n (by norm_num)
  have hn_split : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have hAt :
      targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) := by
    by_cases hk : 0 < n / 16
    case pos =>
      have hK : K0 <= n / 16 := by
        omega
      exact
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          (exactChainUpperOfExplicitClosedPlacementCertificate
            (Hclosed (n / 16) hK hk))
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
    case neg =>
      have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
      have hzero :
          targetUpperConstructionFiveSixteenAt (16 * 0 + n % 16) :=
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          SplitSoundness.emptyExactChainUpper
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
      simpa [hk0] using hzero
  rw [hn_split]
  exact hAt

end

end ClosedChainReduction
end PachToth
end ErdosProblems1066
