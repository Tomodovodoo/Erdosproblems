import ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface
import ErdosProblems1066.PachToth.ClosedPlacementNonRigidComponents
import ErdosProblems1066.PachToth.RemainderPlacement

set_option autoImplicit false

/-!
# Arbitrary-`n` non-rigid split bridge

This module is a small wrapper from the non-rigid closed-placement interfaces
to the checked arbitrary-`n` split machinery.  It exposes both forms of the
split route:

* callers may supply an explicit far-apart chain/remainder certificate, or
* use the canonical translated remainder constructed in `RemainderPlacement`.

No closed-placement data or far-apart geometry is asserted here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SplitArbitraryNNonRigidBridge

open Arithmetic

noncomputable section

/-- A checked closed placement supplies the exact-chain upper certificate
used by the split construction. -/
def exactChainUpperOfClosedPlacement {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    SplitSoundness.ExactChainUpper k :=
  SplitCertificateBridge.exactChainUpperOfClosedPlacement P

/-- Direct cyclic point/edge data supplies the exact-chain upper certificate
used by the split construction. -/
def exactChainUpperOfExplicitCyclicPointEdgeData {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk) :
    SplitSoundness.ExactChainUpper k :=
  exactChainUpperOfClosedPlacement D.toClosedPlacement

/-- Concrete non-rigid components supply the exact-chain upper certificate
used by the split construction. -/
def exactChainUpperOfComponents {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk) :
    SplitSoundness.ExactChainUpper k :=
  exactChainUpperOfClosedPlacement C.toClosedPlacement

/-- A checked closed placement plus an explicit far-apart remainder certificate
gives the fixed split target at `16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_closedPlacement_farApart
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (P : DeformedPlacement.ClosedPlacement k hk)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        P.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_closedPlacement_farApart
      hr P F

/-- Direct cyclic point/edge data plus an explicit far-apart remainder
certificate gives the fixed split target at `16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_explicitCyclicPointEdgeData_farApart
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        D.toClosedPlacement.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement_farApart
      hr D.toClosedPlacement F

/-- Concrete non-rigid components plus an explicit far-apart remainder
certificate give the fixed split target at `16 * k + r`. -/
theorem targetUpperConstructionFiveSixteenAt_of_components_farApart
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (C : ClosedPlacementNonRigidComponents.Components k hk)
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        C.toClosedPlacement.config
        (SplitSoundness.remainderUpperOfConstruction r).config) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement_farApart
      hr C.toClosedPlacement F

/-- A checked closed placement gives the fixed split target at `16 * k + r`
using the canonical translated remainder construction. -/
theorem targetUpperConstructionFiveSixteenAt_of_closedPlacement_translatedRemainder
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (P : DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (exactChainUpperOfClosedPlacement P)
      (SplitSoundness.remainderUpperOfConstruction r)

/-- Direct cyclic point/edge data gives the fixed split target at
`16 * k + r` using the canonical translated remainder construction. -/
theorem targetUpperConstructionFiveSixteenAt_of_explicitCyclicPointEdgeData_translatedRemainder
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement_translatedRemainder
      hr D.toClosedPlacement

/-- Concrete non-rigid components give the fixed split target at
`16 * k + r` using the canonical translated remainder construction. -/
theorem targetUpperConstructionFiveSixteenAt_of_components_translatedRemainder
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (C : ClosedPlacementNonRigidComponents.Components k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_closedPlacement_translatedRemainder
      hr C.toClosedPlacement

/-- A family of checked non-rigid closed placements gives the full arbitrary
vertex-count target.  For `k = n / 16 = 0`, the exact chain is empty and the
checked remainder construction handles all vertices. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  by_cases hk : 0 < n / 16
  case pos =>
    exact
      targetUpperConstructionFiveSixteenAt_of_closedPlacement_translatedRemainder
        hr (H (n / 16) hk)
  case neg =>
    have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
    have htarget :
        targetUpperConstructionFiveSixteenAt (16 * 0 + n % 16) := by
      exact
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          SplitSoundness.emptyExactChainUpper
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
    simpa [hk0] using htarget

/-- A family of direct cyclic point/edge data gives the full arbitrary
vertex-count target via the checked translated remainder split. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitCyclicPointEdgeData
    (H :
      forall (k : Nat) (hk : 0 < k),
        NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
      (fun k hk => (H k hk).toClosedPlacement)

/-- A family of concrete non-rigid components gives the full arbitrary
vertex-count target via the checked translated remainder split. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_components
    (H :
      forall (k : Nat) (hk : 0 < k),
        ClosedPlacementNonRigidComponents.Components k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
      (fun k hk => (H k hk).toClosedPlacement)

end

end SplitArbitraryNNonRigidBridge
end PachToth
end ErdosProblems1066
