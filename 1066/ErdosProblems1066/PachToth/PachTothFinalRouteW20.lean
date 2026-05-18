import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19

set_option autoImplicit false

/-!
# W20 final Pach-Toth closed-placement route

This module is intentionally conditional.  The workspace does not contain an
unconditional producer for
`ExplicitClosedPlacementProducerW19.InputPackage`, so the final route and the
public-style wrappers below all take that package as an explicit input.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothFinalRouteW20

noncomputable section

abbrev InputPackage :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily

abbrev ExactTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ExactTarget

abbrev ArbitraryTarget : Prop :=
  ExplicitClosedPlacementProducerW19.ArbitraryTarget

abbrev FixedTarget (n : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.FixedTarget n

abbrev ExactBlockTarget (k : Nat) : Prop :=
  ExplicitClosedPlacementProducerW19.ExactBlockTarget k

/-! ## Final route package -/

/-- The shortest W20 final route surface: the exact and arbitrary Pach-Toth
targets obtained from one W19 explicit closed-placement input package. -/
structure FinalRoute where
  exactTarget : ExactTarget
  arbitraryTarget : ArbitraryTarget

namespace FinalRoute

theorem targetUpperConstructionFiveSixteen
    (R : FinalRoute) :
    ExactTarget :=
  R.exactTarget

theorem targetUpperConstructionFiveSixteenArbitrary
    (R : FinalRoute) :
    ArbitraryTarget :=
  R.arbitraryTarget

theorem targetUpperConstructionFiveSixteenAt
    (R : FinalRoute) (n : Nat) :
    FixedTarget n :=
  R.arbitraryTarget n

theorem upper_bound_five_sixteen_exact
    (R : FinalRoute) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  R.exactTarget k hk

theorem upper_bound_five_sixteen_arbitrary
    (R : FinalRoute) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  R.arbitraryTarget n

end FinalRoute

/-! ## Route from the W19 input package -/

def explicitClosedPlacementCertificateFamily
    (P : InputPackage) :
    ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate P

def finalRoute
    (P : InputPackage) :
    FinalRoute where
  exactTarget :=
    ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteen_of_inputPackage
      P
  arbitraryTarget :=
    ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
      P

theorem targetUpperConstructionFiveSixteen_of_inputPackage
    (P : InputPackage) :
    ExactTarget :=
  (finalRoute P).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    (P : InputPackage) :
    ArbitraryTarget :=
  (finalRoute P).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_inputPackage
    (P : InputPackage) (n : Nat) :
    FixedTarget n :=
  (finalRoute P).targetUpperConstructionFiveSixteenAt n

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_inputPackage
    (P : InputPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  ExplicitClosedPlacementProducerW19.InputPackage.targetUpperConstructionFiveSixteenAt_exactBlock
    P k hk

/-! ## Public-style upper-bound wrappers -/

theorem upper_bound_five_sixteen_exact_of_inputPackage
    (P : InputPackage) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  (finalRoute P).upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary_of_inputPackage
    (P : InputPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  (finalRoute P).upper_bound_five_sixteen_arbitrary n

end

end PachTothFinalRouteW20

/-! ## Source-specific public aliases -/

theorem targetUpperConstructionFiveSixteen_of_w20_inputPackage
    (P : PachTothFinalRouteW20.InputPackage) :
    PachTothFinalRouteW20.ExactTarget :=
  PachTothFinalRouteW20.targetUpperConstructionFiveSixteen_of_inputPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_w20_inputPackage
    (P : PachTothFinalRouteW20.InputPackage) :
    PachTothFinalRouteW20.ArbitraryTarget :=
  PachTothFinalRouteW20.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage
    P

theorem upper_bound_five_sixteen_exact_of_w20_inputPackage
    (P : PachTothFinalRouteW20.InputPackage)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothFinalRouteW20.upper_bound_five_sixteen_exact_of_inputPackage
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_w20_inputPackage
    (P : PachTothFinalRouteW20.InputPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  PachTothFinalRouteW20.upper_bound_five_sixteen_arbitrary_of_inputPackage
    P n

end PachToth

namespace Verified

abbrev PachTothW20InputPackage :=
  PachToth.PachTothFinalRouteW20.InputPackage

abbrev PachTothW20FinalRoute :=
  PachToth.PachTothFinalRouteW20.FinalRoute

theorem upper_bound_five_sixteen_exact_of_pachtoth_w20_inputPackage
    (P : PachTothW20InputPackage) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w20_inputPackage P k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w20_inputPackage
    (P : PachTothW20InputPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w20_inputPackage P n

theorem upper_bound_five_sixteen_exact_of_pachtoth_w20_finalRoute
    (R : PachTothW20FinalRoute) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  R.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w20_finalRoute
    (R : PachTothW20FinalRoute) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  R.upper_bound_five_sixteen_arbitrary n

end Verified
end ErdosProblems1066
