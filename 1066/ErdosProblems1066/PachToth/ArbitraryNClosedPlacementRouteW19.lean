import ErdosProblems1066.PachToth.ClosedChainReduction
import ErdosProblems1066.PachToth.SplitArbitraryNNonRigidBridge

set_option autoImplicit false

/-!
# W19 arbitrary-n route from explicit closed placements

This file is a thin W19 facade for the source-faithful closed-placement route.
It does not assert any closed-placement data.  Instead, the public wrappers
are conditional on an explicit certificate family, and the arbitrary vertex
count target is routed through the checked closed-chain/split reductions.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNClosedPlacementRouteW19

open ClosedChainReduction

noncomputable section

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitTransitionClosedPlacementCertificateFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk

abbrev ClosedPlacementFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    DeformedPlacement.ClosedPlacement k hk

abbrev ExactChainUpper (k : Nat) : Type :=
  SplitSoundness.ExactChainUpper k

/-! ## Repackaging explicit certificates -/

def closedPlacementFamilyOfExplicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateFamily) :
    ClosedPlacementFamily :=
  fun k hk => (H k hk).toClosedPlacement

def explicitClosedPlacementCertificateFamilyOfTransition
    (H : ExplicitTransitionClosedPlacementCertificateFamily) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => (H k hk).toExplicitClosedPlacementCertificate

def closedPlacementFamilyOfExplicitTransitionClosedPlacementCertificates
    (H : ExplicitTransitionClosedPlacementCertificateFamily) :
    ClosedPlacementFamily :=
  fun k hk => (H k hk).toClosedPlacement

def exactChainFamilyOfExplicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateFamily) :
    forall k : Nat, 0 < k -> ExactChainUpper k :=
  fun k hk =>
    SplitArbitraryNNonRigidBridge.exactChainUpperOfClosedPlacement
      ((H k hk).toClosedPlacement)

/-! ## Arbitrary-n targets -/

private theorem closedChainArbitraryTarget
    (H : ExplicitClosedPlacementCertificateFamily) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
    H

theorem targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateFamily) :
    ExactTarget :=
  ClosedChainReduction.targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
    H

/-- Arbitrary-`n` target from a family of explicit closed-placement
certificates, routed through the checked closed-chain reduction. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateFamily) :
    ArbitraryTarget :=
  closedChainArbitraryTarget H

/-- The same arbitrary-`n` wrapper, exposed through the non-rigid split
bridge after forgetting the explicit certificate family to checked closed
placements. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates_split
    (H : ExplicitClosedPlacementCertificateFamily) :
    ArbitraryTarget :=
  SplitArbitraryNNonRigidBridge.targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (closedPlacementFamilyOfExplicitClosedPlacementCertificates H)

theorem targetUpperConstructionFiveSixteenAt_of_explicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateFamily) (n : Nat) :
    FixedTarget n :=
  (targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
    H) n

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitTransitionClosedPlacementCertificates
    (H : ExplicitTransitionClosedPlacementCertificateFamily) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
    (explicitClosedPlacementCertificateFamilyOfTransition H)

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitTransitionCertificates_split
    (H : ExplicitTransitionClosedPlacementCertificateFamily) :
    ArbitraryTarget :=
  SplitArbitraryNNonRigidBridge.targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (closedPlacementFamilyOfExplicitTransitionClosedPlacementCertificates H)

theorem targetUpperConstructionFiveSixteenAt_of_explicitTransitionClosedPlacementCertificates
    (H : ExplicitTransitionClosedPlacementCertificateFamily) (n : Nat) :
    FixedTarget n :=
  (targetUpperConstructionFiveSixteenArbitrary_of_explicitTransitionClosedPlacementCertificates
    H) n

/-! ## Public upper-bound wrappers -/

theorem upper_bound_five_sixteen_arbitrary_of_explicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenAt_of_explicitClosedPlacementCertificates
    H n

theorem upper_bound_five_sixteen_arbitrary_of_explicitTransitionClosedPlacementCertificates
    (H : ExplicitTransitionClosedPlacementCertificateFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenAt_of_explicitTransitionClosedPlacementCertificates
    H n

end

end ArbitraryNClosedPlacementRouteW19

open ArbitraryNClosedPlacementRouteW19

theorem upper_bound_five_sixteen_arbitrary_of_w19_explicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_explicitClosedPlacementCertificates
    H n

theorem upper_bound_five_sixteen_arbitrary_of_w19_explicitTransitionClosedPlacementCertificates
    (H : ExplicitTransitionClosedPlacementCertificateFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_explicitTransitionClosedPlacementCertificates
    H n

end PachToth

namespace Verified

abbrev PachTothW19ExplicitClosedPlacementCertificateFamily :=
  PachToth.ArbitraryNClosedPlacementRouteW19.ExplicitClosedPlacementCertificateFamily

abbrev PachTothW19ExplicitTransitionClosedPlacementCertificateFamily :=
  PachToth.ArbitraryNClosedPlacementRouteW19.ExplicitTransitionClosedPlacementCertificateFamily

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w19_explicitClosedPlacementCertificates
    (H : PachTothW19ExplicitClosedPlacementCertificateFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w19_explicitClosedPlacementCertificates
    H n

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w19_explicitTransitionCertificates
    (H : PachTothW19ExplicitTransitionClosedPlacementCertificateFamily)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w19_explicitTransitionClosedPlacementCertificates
    H n

end Verified
end ErdosProblems1066
