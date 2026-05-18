import ErdosProblems1066.KnownBounds
import ErdosProblems1066.PachToth.TargetReduction
import ErdosProblems1066.PachToth.SplitSoundnessInstantiationW13
import ErdosProblems1066.PachToth.LargeClosedPlacementInstantiationW13

set_option autoImplicit false

/-!
# W14 Pach--Toth known-bounds spine

This standalone module keeps the Pach--Toth `5 / 16` upper-bound facade
conditional.  It exposes `KnownBounds`-shaped wrappers only from explicit
certificate families or from an already supplied exact-block target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothKnownBoundsSpineW14

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

abbrev IndexedChainRealizationFamily :=
  forall (k : Nat) (hk : 0 < k),
    IndexedChain.IndexedChainRealization k hk

abbrev ExplicitEdgeSoundnessFamily :=
  forall (k : Nat) (hk : 0 < k),
    GeometricSoundness.ExplicitEdgeSoundness k hk

abbrev AllPositiveFiniteFields :=
  LargeClosedPlacementInstantiationW13.AllPositiveFiniteFields

abbrev TableFamilyPackage :=
  FiniteCertificateObligationsW12.TableFamilyPackage

abbrev VectorPackage :=
  FiniteCertificateObligationsW12.VectorPackage

abbrev ListPackage :=
  FiniteCertificateObligationsW12.ListPackage

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields K0

abbrev LargeClosedPlacementWithFiniteComplementFields (K0 : Nat) :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementWithFiniteComplementFields
    K0

/-! ## Target-proposition wrappers -/

/-- Exact-block target from a supplied indexed-chain realization family. -/
theorem targetUpperConstructionFiveSixteen_of_indexedChainRealizationFamily
    (H : IndexedChainRealizationFamily) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_indexedChainRealizations H

/-- Exact-block target from a supplied explicit edge-soundness family. -/
theorem targetUpperConstructionFiveSixteen_of_explicitEdgeSoundnessFamily
    (H : ExplicitEdgeSoundnessFamily) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_explicitEdgeSoundness H

/-- Arbitrary-`n` target from an exact-block target, using checked remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (Hexact : ExactTarget) :
    ArbitraryTarget :=
  SplitSoundnessInstantiationW13.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    Hexact

/-- Arbitrary-`n` target from a supplied indexed-chain realization family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_indexedChainRealizationFamily
    (H : IndexedChainRealizationFamily) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_indexedChainRealizationFamily H)

/-- Arbitrary-`n` target from a supplied explicit edge-soundness family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitEdgeSoundnessFamily
    (H : ExplicitEdgeSoundnessFamily) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_explicitEdgeSoundnessFamily H)

/-- Exact-block target from W12 all-positive finite fields. -/
theorem targetUpperConstructionFiveSixteen_of_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) :
    ExactTarget :=
  LargeClosedPlacementInstantiationW13.targetUpperConstructionFiveSixteen_of_allPositiveFiniteFields
    F

/-- Arbitrary-`n` target from W12 all-positive finite fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) :
    ArbitraryTarget :=
  F.targetUpperConstructionFiveSixteenArbitrary

/-- Exact-block target from a W12 native table-family package. -/
theorem targetUpperConstructionFiveSixteen_of_tableFamilyPackage
    (P : TableFamilyPackage) :
    ExactTarget :=
  FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteen_of_tableFamilyPackage
    P

/-- Arbitrary-`n` target from a W12 native table-family package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_tableFamilyPackage
    (P : TableFamilyPackage) :
    ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

/-- Exact-block target from a W12 vector-table package. -/
theorem targetUpperConstructionFiveSixteen_of_vectorPackage
    (P : VectorPackage) :
    ExactTarget :=
  FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteen_of_vectorPackage
    P

/-- Arbitrary-`n` target from a W12 vector-table package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_vectorPackage
    (P : VectorPackage) :
    ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

/-- Exact-block target from a W12 list-table package. -/
theorem targetUpperConstructionFiveSixteen_of_listPackage
    (P : ListPackage) :
    ExactTarget :=
  FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteen_of_listPackage
    P

/-- Arbitrary-`n` target from a W12 list-table package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_listPackage
    (P : ListPackage) :
    ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

/-- Eventual target from sufficiently large closed-placement fields. -/
theorem targetUpperConstructionFiveSixteenEventually_of_w13_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  open LargeClosedPlacementInstantiationW13 in
    targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields L

/-- Exact-block target from large closed-placement fields when the threshold
is at most one block. -/
theorem targetUpperConstructionFiveSixteen_of_w13_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ExactTarget :=
  open LargeClosedPlacementInstantiationW13 in
    targetUpperConstructionFiveSixteen_of_largeClosedPlacementFields_atMostOne
      L hK0

/-- Arbitrary-`n` target from large closed-placement fields when the threshold
is at most one block. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_w13_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ArbitraryTarget :=
  open LargeClosedPlacementInstantiationW13 in
    targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacementFields_atMostOne
      L hK0

/-- Arbitrary-`n` target from large closed-placement fields plus finite
exact-block data below the threshold. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacementFiniteComplement
    {K0 : Nat} (P : LargeClosedPlacementWithFiniteComplementFields K0) :
    ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

/-! ## KnownBounds-shaped upper-bound wrappers -/

/-- Exact-block `5 / 16` upper-bound statement from an exact-block target. -/
theorem upper_bound_five_sixteen_exact_of_exactTarget
    (Hexact : ExactTarget) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  Hexact k hk

/-- Fixed-`n` `5 / 16` upper-bound statement from an exact-block target and
checked remainders. -/
theorem upper_bound_five_sixteen_arbitrary_of_exactTarget
    (Hexact : ExactTarget) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_exactTarget Hexact n

/-- Exact-block public-style wrapper from indexed-chain realizations. -/
theorem upper_bound_five_sixteen_exact_of_indexedChainRealizationFamily
    (H : IndexedChainRealizationFamily) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_indexedChainRealizationFamily H)
    k hk

/-- Arbitrary-`n` public-style wrapper from indexed-chain realizations. -/
theorem upper_bound_five_sixteen_arbitrary_of_indexedChainRealizationFamily
    (H : IndexedChainRealizationFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_indexedChainRealizationFamily
    H n

/-- Exact-block public-style wrapper from explicit edge-soundness data. -/
theorem upper_bound_five_sixteen_exact_of_explicitEdgeSoundnessFamily
    (H : ExplicitEdgeSoundnessFamily) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_explicitEdgeSoundnessFamily H)
    k hk

/-- Arbitrary-`n` public-style wrapper from explicit edge-soundness data. -/
theorem upper_bound_five_sixteen_arbitrary_of_explicitEdgeSoundnessFamily
    (H : ExplicitEdgeSoundnessFamily) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_explicitEdgeSoundnessFamily
    H n

/-- Exact-block public-style wrapper from W12 all-positive finite fields. -/
theorem upper_bound_five_sixteen_exact_of_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_allPositiveFiniteFields F) k hk

/-- Arbitrary-`n` public-style wrapper from W12 all-positive finite fields. -/
theorem upper_bound_five_sixteen_arbitrary_of_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_allPositiveFiniteFields F n

/-- Exact-block public-style wrapper from a W12 native table-family package. -/
theorem upper_bound_five_sixteen_exact_of_tableFamilyPackage
    (P : TableFamilyPackage) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_tableFamilyPackage P) k hk

/-- Arbitrary-`n` public-style wrapper from a W12 native table-family package. -/
theorem upper_bound_five_sixteen_arbitrary_of_tableFamilyPackage
    (P : TableFamilyPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_tableFamilyPackage P n

/-- Exact-block public-style wrapper from a W12 vector-table package. -/
theorem upper_bound_five_sixteen_exact_of_vectorPackage
    (P : VectorPackage) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_vectorPackage P) k hk

/-- Arbitrary-`n` public-style wrapper from a W12 vector-table package. -/
theorem upper_bound_five_sixteen_arbitrary_of_vectorPackage
    (P : VectorPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_vectorPackage P n

/-- Exact-block public-style wrapper from a W12 list-table package. -/
theorem upper_bound_five_sixteen_exact_of_listPackage
    (P : ListPackage) (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_listPackage P) k hk

/-- Arbitrary-`n` public-style wrapper from a W12 list-table package. -/
theorem upper_bound_five_sixteen_arbitrary_of_listPackage
    (P : ListPackage) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_listPackage P n

/-- Exact-block public-style wrapper from large closed-placement data whose
threshold is at most one block. -/
theorem upper_bound_five_sixteen_exact_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_exactTarget
    (targetUpperConstructionFiveSixteen_of_w13_largeClosedPlacementFields_atMostOne
      L hK0)
    k hk

/-- Arbitrary-`n` public-style wrapper from large closed-placement data whose
threshold is at most one block. -/
theorem upper_bound_five_sixteen_arbitrary_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_w13_largeClosedPlacementFields_atMostOne
    L hK0 n

/-- Arbitrary-`n` public-style wrapper from large closed-placement data plus
finite exact-block data below the threshold. -/
theorem upper_bound_five_sixteen_arbitrary_of_largeClosedPlacementComplement
    {K0 : Nat} (P : LargeClosedPlacementWithFiniteComplementFields K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacementFiniteComplement
    P n

end

end PachTothKnownBoundsSpineW14

/-! ## Source-specific public-style aliases -/

/-- Source-specific conditional exact-block alias for W12 all-positive finite
fields. -/
theorem upper_bound_five_sixteen_exact_of_w14_allPositiveFiniteFields
    (F : PachTothKnownBoundsSpineW14.AllPositiveFiniteFields)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothKnownBoundsSpineW14.upper_bound_five_sixteen_exact_of_allPositiveFiniteFields
    F k hk

/-- Source-specific conditional arbitrary-`n` alias for W12 all-positive
finite fields. -/
theorem upper_bound_five_sixteen_arbitrary_of_w14_allPositiveFiniteFields
    (F : PachTothKnownBoundsSpineW14.AllPositiveFiniteFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  PachTothKnownBoundsSpineW14.upper_bound_five_sixteen_arbitrary_of_allPositiveFiniteFields
    F n

/-- Source-specific conditional arbitrary-`n` alias for large closed-placement
fields with finite exact-block complement. -/
theorem upper_bound_five_sixteen_arbitrary_of_w14_largeClosedPlacementFiniteComplement
    {K0 : Nat}
    (P : PachTothKnownBoundsSpineW14.LargeClosedPlacementWithFiniteComplementFields K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  PachTothKnownBoundsSpineW14.upper_bound_five_sixteen_arbitrary_of_largeClosedPlacementComplement
    P n

end PachToth

namespace Verified

abbrev PachTothW14FiniteComplementFields (K0 : Nat) :=
  PachToth.PachTothKnownBoundsSpineW14.LargeClosedPlacementWithFiniteComplementFields
    K0

/-- Public-facade-shaped conditional Pach--Toth exact-block upper bound from
W12 all-positive finite fields. -/
theorem upper_bound_five_sixteen_exact_of_pachtoth_w14_allPositiveFiniteFields
    (F : PachToth.PachTothKnownBoundsSpineW14.AllPositiveFiniteFields)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachToth.upper_bound_five_sixteen_exact_of_w14_allPositiveFiniteFields
    F k hk

/-- Public-facade-shaped conditional Pach--Toth arbitrary-`n` upper bound from
W12 all-positive finite fields. -/
theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w14_allPositiveFiniteFields
    (F : PachToth.PachTothKnownBoundsSpineW14.AllPositiveFiniteFields)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w14_allPositiveFiniteFields
    F n

/-- Public-facade-shaped conditional Pach--Toth arbitrary-`n` upper bound from
large closed-placement fields plus finite exact-block complement data. -/
theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w14_largeClosedPlacementFiniteComplement
    {K0 : Nat}
    (P : PachTothW14FiniteComplementFields K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.upper_bound_five_sixteen_arbitrary_of_w14_largeClosedPlacementFiniteComplement
    P n

end Verified
end ErdosProblems1066
