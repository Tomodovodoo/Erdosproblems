import ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface
import ErdosProblems1066.PachToth.ClosedPlacementNonRigidComponents
import ErdosProblems1066.PachToth.RemainderPlacement
import ErdosProblems1066.PachToth.SplitRealizationClosure

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

/-- Successor-orbit non-rigid data supplies the exact-chain upper certificate
used by the split construction. -/
def exactChainUpperOfExplicitCyclicOrbitEdgeData {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk) :
    SplitSoundness.ExactChainUpper k :=
  NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData.exactChainUpper D

/-- Same/opposite cyclic-orbit data supplies the exact-chain upper certificate
used by the split construction. -/
def exactChainUpperOfSameOppositeCyclicOrbitData
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData O k hk) :
    SplitSoundness.ExactChainUpper k :=
  NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData.exactChainUpper D

/-- Generated closed-chain data supplies the exact-chain upper certificate
used by the split construction. -/
def exactChainUpperOfExactGeneratedClosedChainData {k : Nat} {hk : 0 < k}
    (G : SplitRealizationClosure.ExactGeneratedClosedChainData k hk) :
    SplitSoundness.ExactChainUpper k :=
  G.exactChainUpper

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

/-- Successor-orbit non-rigid data gives the fixed split target at
`16 * k + r` using the canonical translated remainder construction. -/
theorem targetUpperConstructionFiveSixteenAt_of_explicitCyclicOrbitEdgeData_translatedRemainder
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (exactChainUpperOfExplicitCyclicOrbitEdgeData D)
      (SplitSoundness.remainderUpperOfConstruction r)

/-- Same/opposite cyclic-orbit data gives the fixed split target at
`16 * k + r` using the canonical translated remainder construction. -/
theorem targetUpperConstructionFiveSixteenAt_of_sameOppositeCyclicOrbitData_translatedRemainder
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (D : NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData O k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (exactChainUpperOfSameOppositeCyclicOrbitData D)
      (SplitSoundness.remainderUpperOfConstruction r)

/-- Generated closed-chain data gives the fixed split target at
`16 * k + r` using the canonical translated remainder construction. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactGeneratedClosedChainData_translatedRemainder
    {k r : Nat} {hk : 0 < k} (hr : r < 16)
    (G : SplitRealizationClosure.ExactGeneratedClosedChainData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k + r) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (exactChainUpperOfExactGeneratedClosedChainData G)
      (SplitSoundness.remainderUpperOfConstruction r)

/-- Select a supplied positive exact-chain certificate at the quotient
`n / 16`, using the empty exact chain when the quotient is zero. -/
def exactChainUpperOfPositiveExactChainsDiv
    (H :
      forall (k : Nat), 0 < k -> SplitSoundness.ExactChainUpper k)
    (n : Nat) :
    SplitSoundness.ExactChainUpper (n / 16) := by
  by_cases hk : 0 < n / 16
  case pos =>
    exact H (n / 16) hk
  case neg =>
    have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
    rw [hk0]
    exact SplitSoundness.emptyExactChainUpper

/-- Exact-chain certificates for all positive quotient blocks give the split
target for the canonical `div`/`mod` decomposition of `n`. -/
theorem targetUpperConstructionFiveSixteenAt_divMod_of_positiveExactChains
    (H :
      forall (k : Nat), 0 < k -> SplitSoundness.ExactChainUpper k)
    (n : Nat) :
    targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      (Nat.mod_lt n (by norm_num))
      (exactChainUpperOfPositiveExactChainsDiv H n)
      (SplitSoundness.remainderUpperOfConstruction (n % 16))

/-- A supplied exact-chain certificate for the quotient block, plus an
explicit far-apart certificate for the checked remainder, gives the split
target for the canonical `div`/`mod` decomposition of `n`. -/
theorem targetUpperConstructionFiveSixteenAt_divMod_of_exactChain_farApart
    (n : Nat)
    (chain : SplitSoundness.ExactChainUpper (n / 16))
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        chain.config
        (SplitSoundness.remainderUpperOfConstruction (n % 16)).config) :
    targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) := by
  exact
    SplitCertificateBridge.targetUpperConstructionFiveSixteenAt_of_exists_canonicalSplitRealization
      (Nat.mod_lt n (by norm_num))
      (SplitCertificateBridge.exists_canonicalSplitRealization_of_exactChain_farApart
        chain
        (SplitSoundness.remainderUpperOfConstruction (n % 16))
        F)

/-- A supplied exact-chain certificate for the quotient block, plus an
explicit far-apart certificate for the checked remainder, gives the target at
`n`. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChainDivMod_farApart
    (n : Nat)
    (chain : SplitSoundness.ExactChainUpper (n / 16))
    (F :
      SplitCertificateBridge.FarApartRemainderCertificate
        chain.config
        (SplitSoundness.remainderUpperOfConstruction (n % 16)).config) :
    targetUpperConstructionFiveSixteenAt n := by
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact targetUpperConstructionFiveSixteenAt_divMod_of_exactChain_farApart
    n chain F

/-- A family of quotient exact-chain certificates and explicit far-apart
remainder certificates gives the full arbitrary vertex-count target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactChainDivMod_farApart
    (chain : forall n : Nat, SplitSoundness.ExactChainUpper (n / 16))
    (F :
      forall n : Nat,
        SplitCertificateBridge.FarApartRemainderCertificate
          (chain n).config
          (SplitSoundness.remainderUpperOfConstruction (n % 16)).config) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact targetUpperConstructionFiveSixteenAt_of_exactChainDivMod_farApart
    n (chain n) (F n)

/-- Exact-chain certificates for all positive quotient blocks give the full
arbitrary vertex-count target.  The remainder block is supplied by the checked
finite construction and translated far away from the chain. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_positiveExactChains
    (H :
      forall (k : Nat), 0 < k -> SplitSoundness.ExactChainUpper k) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact targetUpperConstructionFiveSixteenAt_divMod_of_positiveExactChains H n

/-- Select the exact-chain certificate at the quotient `n / 16`, using the
empty exact chain when the quotient is zero. -/
def exactChainUpperOfClosedPlacementsDiv
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk)
    (n : Nat) :
    SplitSoundness.ExactChainUpper (n / 16) := by
  by_cases hk : 0 < n / 16
  case pos =>
    exact exactChainUpperOfClosedPlacement (H (n / 16) hk)
  case neg =>
    have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
    rw [hk0]
    exact SplitSoundness.emptyExactChainUpper

/-- A family of checked non-rigid closed placements gives the split target for
the canonical `div`/`mod` decomposition of `n`. -/
theorem targetUpperConstructionFiveSixteenAt_divMod_of_closedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk)
    (n : Nat) :
    targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) := by
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      (Nat.mod_lt n (by norm_num))
      (exactChainUpperOfClosedPlacementsDiv H n)
      (SplitSoundness.remainderUpperOfConstruction (n % 16))

/-- A family of checked non-rigid closed placements gives the full arbitrary
vertex-count target.  For `k = n / 16 = 0`, the exact chain is empty and the
checked remainder construction handles all vertices. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact targetUpperConstructionFiveSixteenAt_divMod_of_closedPlacements H n

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

/-- A family of successor-orbit non-rigid data gives the full arbitrary
vertex-count target via the exact-chain split route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitCyclicOrbitEdgeData
    (H :
      forall (k : Nat) (hk : 0 < k),
        NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_positiveExactChains
      (fun k hk => exactChainUpperOfExplicitCyclicOrbitEdgeData (H k hk))

/-- A family of same/opposite cyclic-orbit data gives the full arbitrary
vertex-count target via the exact-chain split route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_sameOppositeCyclicOrbitData
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    (H :
      forall (k : Nat) (hk : 0 < k),
        NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData O k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_positiveExactChains
      (fun k hk => exactChainUpperOfSameOppositeCyclicOrbitData (H k hk))

/-- A family of generated closed-chain data gives the full arbitrary
vertex-count target via the exact-chain split route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactGeneratedClosedChainData
    (H :
      forall (k : Nat) (hk : 0 < k),
        SplitRealizationClosure.ExactGeneratedClosedChainData k hk) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_positiveExactChains
      (fun k hk => exactChainUpperOfExactGeneratedClosedChainData (H k hk))

end

end SplitArbitraryNNonRigidBridge
end PachToth
end ErdosProblems1066
