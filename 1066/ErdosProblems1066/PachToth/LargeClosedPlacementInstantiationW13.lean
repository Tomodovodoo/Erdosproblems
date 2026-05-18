import ErdosProblems1066.PachToth.LargeClosedPlacementW12
import ErdosProblems1066.PachToth.FiniteCertificateObligationsW12

set_option autoImplicit false

/-!
# W13 large closed-placement instantiation

This module keeps the W13 target bridge deliberately threshold-aware.  Large
closed-placement certificates prove the eventual target from the induced
vertex threshold `16 * K0`; finite exact-block certificates below `K0` close
the finite complement.  Exact all-positive target statements are exposed only
from all-positive finite fields, or from large fields whose threshold is at
most one block.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeClosedPlacementInstantiationW13

open Arithmetic
open ClosedChainReduction
open SmallCaseCertificates

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt (16 * k)

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0

abbrev AllPositiveFiniteFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

/-- A large closed-placement field gives the exact-block target precisely in
the block range where its certificate field is available. -/
theorem exactBlockTarget_of_largeClosedPlacementFields
    {K0 k : Nat} (L : LargeClosedPlacementFields K0)
    (hK : K0 <= k) (hk : 0 < k) :
    ExactBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificate
      (L.certificate k hK hk)

/-- Large closed-placement fields give every vertex target from the explicit
threshold `16 * K0` onward. -/
theorem targetUpperConstructionFiveSixteenAt_of_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    PachToth.targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have htarget :
      PachToth.targetUpperConstructionFiveSixteenAt
        (16 * (n / 16) + n % 16) := by
    by_cases hk : 0 < n / 16
    case pos =>
      have hK : K0 <= n / 16 := by
        omega
      exact
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          (L.exactChainUpper (n / 16) hK hk)
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
    case neg =>
      have hdiv : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
      have hzero :
          PachToth.targetUpperConstructionFiveSixteenAt (16 * 0 + n % 16) :=
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          SplitSoundness.emptyExactChainUpper
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
      simpa [hdiv] using hzero
  rw [hsplit]
  exact htarget

/-- Large closed-placement fields give the source-faithful eventual target
with the concrete threshold `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    EventualTarget := by
  exact
    Exists.intro (16 * K0)
      (fun _n hn =>
        targetUpperConstructionFiveSixteenAt_of_largeClosedPlacementFields
          L hn)

/-- If the large threshold is at most one block, the large field actually
covers every positive exact block count. -/
theorem targetUpperConstructionFiveSixteen_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ExactTarget := by
  exact
    targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
      (fun k hk =>
        L.certificate k
          (EventualRoleHingeClosure.threshold_le_of_atMostOne hK0 hk)
          hk)

/-- If the large threshold is at most one block, checked remainders turn the
exact block-form target into the arbitrary-`n` target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ArbitraryTarget := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (targetUpperConstructionFiveSixteen_of_largeClosedPlacementFields_atMostOne
        L hK0)

/-- Large closed-placement fields plus exact-chain certificates for the
positive block counts below `K0` close the finite complement. -/
theorem arbitraryTarget_of_largeClosedPlacementFields_blockSmallChains
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (smallChains :
      forall k : Nat, k < K0 -> 0 < k -> SplitSoundness.ExactChainUpper k) :
    ArbitraryTarget := by
  exact
    PachToth.targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * K0)
      (fun _n hn =>
        targetUpperConstructionFiveSixteenAt_of_largeClosedPlacementFields
          L hn)
      (targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold
        K0 smallChains)

/-- The same finite-complement closure, with small data supplied as
exact-block target proofs below `K0`. -/
theorem arbitraryTarget_of_largeClosedPlacementFields_exactBlockSmallTargets
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (smallBlocks :
      forall k : Nat, k < K0 -> 0 < k -> ExactBlockTarget k) :
    ArbitraryTarget := by
  exact
    PachToth.targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * K0)
      (fun _n hn =>
        targetUpperConstructionFiveSixteenAt_of_largeClosedPlacementFields
          L hn)
      (targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
        K0 smallBlocks)

/-- A compact W13 package: large closed-placement data for the eventual range,
and finite exact-block data for the block complement. -/
structure LargeClosedPlacementWithFiniteComplementFields (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  exactBlockSmall :
    forall k : Nat, k < K0 -> 0 < k -> ExactBlockTarget k

namespace LargeClosedPlacementWithFiniteComplementFields

theorem exactBlockTarget_large
    {K0 k : Nat} (P : LargeClosedPlacementWithFiniteComplementFields K0)
    (hK : K0 <= k) (hk : 0 < k) :
    ExactBlockTarget k :=
  exactBlockTarget_of_largeClosedPlacementFields P.large hK hk

theorem targetUpperConstructionFiveSixteenAt_large
    {K0 : Nat} (P : LargeClosedPlacementWithFiniteComplementFields K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  targetUpperConstructionFiveSixteenAt_of_largeClosedPlacementFields
    P.large hn

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : LargeClosedPlacementWithFiniteComplementFields K0) :
    EventualTarget :=
  targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields
    P.large

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : LargeClosedPlacementWithFiniteComplementFields K0) :
    ArbitraryTarget :=
  arbitraryTarget_of_largeClosedPlacementFields_exactBlockSmallTargets
    P.large P.exactBlockSmall

theorem targetUpperConstructionFiveSixteen_atMostOne
    {K0 : Nat} (P : LargeClosedPlacementWithFiniteComplementFields K0)
    (hK0 : K0 <= 1) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_largeClosedPlacementFields_atMostOne
    P.large hK0

end LargeClosedPlacementWithFiniteComplementFields

/-! ## All-positive finite fields -/

theorem exactBlockTarget_of_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  F.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem targetUpperConstructionFiveSixteen_of_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) :
    ExactTarget :=
  F.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) :
    ArbitraryTarget :=
  F.targetUpperConstructionFiveSixteenArbitrary

/-- All-positive finite fields can be viewed as large closed-placement fields
from any chosen threshold. -/
def largeClosedPlacementFieldsOfAllPositiveFiniteFields
    (K0 : Nat) (F : AllPositiveFiniteFields) :
    LargeClosedPlacementFields K0 :=
  LargeClosedPlacementW12.largeExplicitClosedPlacementCertificatesOfRoleHinged
    K0
    F.transitions
    (fun k _hK hk => F.orientation k hk)
    (fun k _hK hk => F.period.generatedPeriod k hk)
    (fun k _hK hk => F.separated k hk)

/-- All-positive finite fields also give the source-faithful eventual target
through the large closed-placement route. -/
theorem targetUpperConstructionFiveSixteenEventually_of_allPositiveFiniteFields_as_large
    (K0 : Nat) (F : AllPositiveFiniteFields) :
    EventualTarget :=
  targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields
    (largeClosedPlacementFieldsOfAllPositiveFiniteFields K0 F)

/-- Large closed-placement fields close arbitrary `n` once all-positive finite
fields supply the finite exact-block complement below the large threshold. -/
theorem arbitraryTarget_of_largeClosedPlacementFields_allPositiveFiniteFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (F : AllPositiveFiniteFields) :
    ArbitraryTarget :=
  arbitraryTarget_of_largeClosedPlacementFields_exactBlockSmallTargets
    L
    (fun k _hklt hk => exactBlockTarget_of_allPositiveFiniteFields F k hk)

/-- The strongest combined W13 projection when all-positive finite fields and
large closed-placement fields are both supplied: exact from the all-positive
finite fields, eventual from the large fields, and arbitrary from the exact
finite route. -/
theorem exact_eventual_arbitrary_of_allPositiveFiniteFields_and_largeClosedPlacementFields
    {K0 : Nat} (F : AllPositiveFiniteFields)
    (L : LargeClosedPlacementFields K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget := by
  exact
    And.intro
      (targetUpperConstructionFiveSixteen_of_allPositiveFiniteFields F)
      (And.intro
        (targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields
          L)
        (targetUpperConstructionFiveSixteenArbitrary_of_allPositiveFiniteFields
          F))

end

end LargeClosedPlacementInstantiationW13
end PachToth
end ErdosProblems1066
