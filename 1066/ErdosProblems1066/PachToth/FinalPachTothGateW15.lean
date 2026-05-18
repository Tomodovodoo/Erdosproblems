import ErdosProblems1066.PachToth.PachTothKnownBoundsSpineW14
import ErdosProblems1066.PachToth.ExactToArbitraryNCombinationW14
import ErdosProblems1066.PachToth.ClosedPlacementExactRouteW14
import ErdosProblems1066.PachToth.LargeThresholdSmallCasesW15

set_option autoImplicit false

/-!
# W15 final Pach--Toth gate

This module is the smallest current final gate for the checked `5 / 16`
Pach--Toth surfaces: an exact-block target and an arbitrary-`n` target.
Every public wrapper below is conditional on an explicit gate/package input.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FinalPachTothGateW15

noncomputable section

open _root_.ErdosProblems1066.PachToth.ExactToArbitraryNCombinationW14
open _root_.ErdosProblems1066.PachToth.ClosedPlacementExactRouteW14

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeThresholdSmallCasesW15.LargeClosedPlacementFields K0

abbrev SmallComplement (K0 : Nat) : Prop :=
  LargeThresholdSmallCasesW15.SmallComplement K0

abbrev LargeWithThresholdSmallCases (K0 : Nat) :=
  LargeThresholdSmallCasesW15.LargeWithThresholdSmallCases K0

abbrev ExplicitAllPositiveCertificate :=
  ClosedPlacementExactRouteW14.ExplicitAllPositiveCertificate

abbrev TableFamilyPackage :=
  ClosedPlacementExactRouteW14.TableFamilyPackage

abbrev VectorPackage :=
  ClosedPlacementExactRouteW14.VectorPackage

abbrev ListPackage :=
  ClosedPlacementExactRouteW14.ListPackage

/-! ## Gate record -/

/-- The final gate stores only the two public `5 / 16` target surfaces that
are currently closed by explicit data. -/
structure FinalGate where
  exactTarget : ExactTarget
  arbitraryTarget : ArbitraryTarget

namespace FinalGate

theorem targetUpperConstructionFiveSixteen
    (G : FinalGate) :
    ExactTarget :=
  G.exactTarget

theorem targetUpperConstructionFiveSixteenAt
    (G : FinalGate) (n : Nat) :
    FixedTarget n :=
  G.arbitraryTarget n

theorem targetUpperConstructionFiveSixteenArbitrary
    (G : FinalGate) :
    ArbitraryTarget :=
  G.arbitraryTarget

/-- Exact-block public-style upper-bound wrapper from a final gate. -/
theorem upper_bound_five_sixteen_exact
    (G : FinalGate) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  G.exactTarget k hk

/-- Arbitrary-`n` public-style upper-bound wrapper from a final gate. -/
theorem upper_bound_five_sixteen_arbitrary
    (G : FinalGate) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  G.arbitraryTarget n

end FinalGate

/-! ## Gate constructors from current checked routes -/

def of_exact_arbitrary
    (Hexact : ExactTarget) (Harbitrary : ArbitraryTarget) :
    FinalGate where
  exactTarget := Hexact
  arbitraryTarget := Harbitrary

/-- An exact target closes the gate through the checked W14 exact-to-arbitrary
route. -/
def of_exactTarget
    (Hexact : ExactTarget) :
    FinalGate :=
  of_exact_arbitrary
    Hexact
    (targetUpperConstructionFiveSixteenArbitrary_of_exactTarget Hexact)

def of_explicitAllPositiveCertificate
    (C : ExplicitAllPositiveCertificate) :
    FinalGate :=
  of_exact_arbitrary
    (targetUpperConstructionFiveSixteen_of_explicitAllPositiveCertificate C)
    (targetUpperConstructionFiveSixteenArbitrary_of_explicitAllPositiveCertificate
      C)

def of_tableFamilyPackage
    (P : TableFamilyPackage) :
    FinalGate :=
  of_exact_arbitrary
    (targetUpperConstructionFiveSixteen_of_tableFamilyPackage P)
    (targetUpperConstructionFiveSixteenArbitrary_of_W12_tableFamilyPackage P)

def of_vectorPackage
    (P : VectorPackage) :
    FinalGate :=
  of_exact_arbitrary
    (targetUpperConstructionFiveSixteen_of_vectorPackage P)
    (targetUpperConstructionFiveSixteenArbitrary_of_W12_vectorPackage P)

def of_listPackage
    (P : ListPackage) :
    FinalGate :=
  of_exact_arbitrary
    (targetUpperConstructionFiveSixteen_of_listPackage P)
    (targetUpperConstructionFiveSixteenArbitrary_of_W12_listPackage P)

def of_largeWithThresholdSmallCases
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) :
    FinalGate :=
  of_exact_arbitrary
    P.targetUpperConstructionFiveSixteen
    P.targetUpperConstructionFiveSixteenArbitrary

def of_largeClosedPlacementFields_smallComplement
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (small : SmallComplement K0) :
    FinalGate :=
  of_largeWithThresholdSmallCases
    { large := L, small := small }

def of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    FinalGate :=
  of_largeWithThresholdSmallCases
    (LargeThresholdSmallCasesW15.largeWithThresholdSmallCases_atMostOne
      L hK0)

/-! ## Local public-style wrappers -/

theorem upper_bound_five_sixteen_exact_of_finalGate
    (G : FinalGate) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  G.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary_of_finalGate
    (G : FinalGate) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  G.upper_bound_five_sixteen_arbitrary n

theorem upper_bound_five_sixteen_exact_of_largeWithThresholdSmallCases
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  (of_largeWithThresholdSmallCases P).upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary_of_largeWithThresholdSmallCases
    {K0 : Nat} (P : LargeWithThresholdSmallCases K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  (of_largeWithThresholdSmallCases P).upper_bound_five_sixteen_arbitrary n

theorem upper_bound_five_sixteen_exact_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  (of_largeClosedPlacementFields_atMostOne L hK0)
    |>.upper_bound_five_sixteen_exact k hk

theorem upper_bound_five_sixteen_arbitrary_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  (of_largeClosedPlacementFields_atMostOne L hK0)
    |>.upper_bound_five_sixteen_arbitrary n

end

end FinalPachTothGateW15

/-! ## Source-specific public aliases -/

theorem upper_bound_five_sixteen_exact_of_w15_finalGate
    (G : FinalPachTothGateW15.FinalGate)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  FinalPachTothGateW15.upper_bound_five_sixteen_exact_of_finalGate G k hk

theorem upper_bound_five_sixteen_arbitrary_of_w15_finalGate
    (G : FinalPachTothGateW15.FinalGate) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  FinalPachTothGateW15.upper_bound_five_sixteen_arbitrary_of_finalGate G n

theorem upper_bound_five_sixteen_exact_of_w15_largeWithThresholdSmallCases
    {K0 : Nat}
    (P : FinalPachTothGateW15.LargeWithThresholdSmallCases K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  FinalPachTothGateW15.upper_bound_five_sixteen_exact_of_largeWithThresholdSmallCases
    P k hk

theorem upper_bound_five_sixteen_arbitrary_of_w15_largeWithThresholdSmallCases
    {K0 : Nat}
    (P : FinalPachTothGateW15.LargeWithThresholdSmallCases K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  FinalPachTothGateW15.upper_bound_five_sixteen_arbitrary_of_largeWithThresholdSmallCases
    P n

theorem upper_bound_five_sixteen_exact_of_w15_largeClosedPlacementFields_atMostOne
    {K0 : Nat}
    (L : FinalPachTothGateW15.LargeClosedPlacementFields K0)
    (hK0 : K0 <= 1) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  FinalPachTothGateW15.upper_bound_five_sixteen_exact_of_largeClosedPlacementFields_atMostOne
      L hK0 k hk

theorem upper_bound_five_sixteen_arbitrary_of_w15_largeClosedPlacementFields_atMostOne
    {K0 : Nat}
    (L : FinalPachTothGateW15.LargeClosedPlacementFields K0)
    (hK0 : K0 <= 1) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  FinalPachTothGateW15.upper_bound_five_sixteen_arbitrary_of_largeClosedPlacementFields_atMostOne
      L hK0 n

end PachToth

namespace Verified

abbrev PachTothW15FinalGate :=
  PachToth.FinalPachTothGateW15.FinalGate

abbrev PachTothW15LargeWithThresholdSmallCases (K0 : Nat) :=
  PachToth.FinalPachTothGateW15.LargeWithThresholdSmallCases K0

abbrev PachTothW15LargeClosedPlacementFields (K0 : Nat) :=
  PachToth.FinalPachTothGateW15.LargeClosedPlacementFields K0

/-- Public-facade-shaped conditional exact-block upper bound from the W15
final gate. -/
theorem upper_bound_five_sixteen_exact_of_pachtoth_w15_finalGate
    (G : PachTothW15FinalGate) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w15_finalGate G k hk

/-- Public-facade-shaped conditional arbitrary-`n` upper bound from the W15
final gate. -/
theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w15_finalGate
    (G : PachTothW15FinalGate) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w15_finalGate G n

/-- Public-facade-shaped conditional exact-block upper bound from the W15
large-threshold package with finite small cases. -/
theorem upper_bound_five_sixteen_exact_of_pachtoth_w15_largeWithThresholdSmallCases
    {K0 : Nat} (P : PachTothW15LargeWithThresholdSmallCases K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w15_largeWithThresholdSmallCases
    P k hk

/-- Public-facade-shaped conditional arbitrary-`n` upper bound from the W15
large-threshold package with finite small cases. -/
theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w15_largeWithThresholdSmallCases
    {K0 : Nat} (P : PachTothW15LargeWithThresholdSmallCases K0) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w15_largeWithThresholdSmallCases
    P n

/-- Public-facade-shaped conditional exact-block upper bound from large
closed-placement fields when the threshold is at most one block. -/
theorem upper_bound_five_sixteen_exact_of_pachtoth_w15_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : PachTothW15LargeClosedPlacementFields K0)
    (hK0 : K0 <= 1) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w15_largeClosedPlacementFields_atMostOne
      L hK0 k hk

/-- Public-facade-shaped conditional arbitrary-`n` upper bound from large
closed-placement fields when the threshold is at most one block. -/
theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w15_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : PachTothW15LargeClosedPlacementFields K0)
    (hK0 : K0 <= 1) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w15_largeClosedPlacementFields_atMostOne
      L hK0 n

end Verified
end ErdosProblems1066
