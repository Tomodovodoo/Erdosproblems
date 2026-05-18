import ErdosProblems1066.PachToth.LargeClosedPlacementInstantiationW13

set_option autoImplicit false

/-!
# W14 large/small Pach--Toth closure

This module is the threshold-aware splice between the W13 large
closed-placement route and finite complement data. Bare large fields only give
the explicit threshold and eventual targets. The all-vertex target is exposed
only from packages that also carry exact finite complement evidence.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeSmallCaseClosureW14

open Arithmetic
open LargeClosedPlacementInstantiationW13
open LargeClosedPlacementW12
open SmallCaseCertificates
open RemainderPlacement

noncomputable section

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  LargeExplicitClosedPlacementCertificates K0

abbrev AllPositiveFiniteFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

/-! ## Bare large fields -/

/-- Bare large closed-placement fields give the fixed-`n` target only from
their explicit vertex threshold onward. -/
theorem targetAt_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n :=
  targetUpperConstructionFiveSixteenAt_of_largeClosedPlacementFields L hn

/-- Bare large closed-placement fields give the source-faithful eventual
target with the concrete threshold `16 * K0`. -/
theorem eventualTarget_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    EventualTarget :=
  targetUpperConstructionFiveSixteenEventually_of_largeClosedPlacementFields L

/-- Bare large closed-placement fields give exact block targets at and above
their block threshold. -/
theorem exactBlockTarget_largeClosedPlacementFields
    {K0 k : Nat} (L : LargeClosedPlacementFields K0)
    (hK : K0 <= k) (hk : 0 < k) :
    ExactBlockTarget k :=
  exactBlockTarget_of_largeClosedPlacementFields L hK hk

/-! ## Exact finite complement evidence -/

/-- Exact-chain evidence for all positive quotient blocks below a block
threshold. -/
structure ExactChainThresholdEvidence (K0 : Nat) where
  chain :
    forall k : Nat, k < K0 -> 0 < k -> SplitSoundness.ExactChainUpper k

namespace ExactChainThresholdEvidence

/-- Exact-chain threshold evidence supplies the small side below `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo
    {K0 : Nat} (E : ExactChainThresholdEvidence K0) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * K0) :=
  targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold K0 E.chain

/-- Exact-chain threshold evidence gives exact block targets below the block
threshold. -/
theorem exactBlockTarget
    {K0 k : Nat} (E : ExactChainThresholdEvidence K0)
    (hklt : k < K0) (hk : 0 < k) :
    ExactBlockTarget k := by
  have htarget :
      targetUpperConstructionFiveSixteenAt (16 * k + 0) :=
    targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      (k := k)
      (r := 0)
      (by norm_num)
      (E.chain k hklt hk)
      (SplitSoundness.remainderUpperOfConstruction 0)
  change targetUpperConstructionFiveSixteenAt (16 * k)
  simpa using htarget

end ExactChainThresholdEvidence

/-- Exact-block evidence for all positive quotient blocks below a block
threshold. -/
structure ExactBlockThresholdEvidence (K0 : Nat) where
  exactBlock : forall k : Nat, k < K0 -> 0 < k -> ExactBlockTarget k

namespace ExactBlockThresholdEvidence

/-- Exact-block threshold evidence supplies the small side below `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenSmallUpTo
    {K0 : Nat} (E : ExactBlockThresholdEvidence K0) :
    targetUpperConstructionFiveSixteenSmallUpTo (16 * K0) :=
  targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
    K0 E.exactBlock

/-- Exact-block threshold evidence can be viewed as exact-chain evidence. -/
noncomputable def toExactChainThresholdEvidence
    {K0 : Nat} (E : ExactBlockThresholdEvidence K0) :
    ExactChainThresholdEvidence K0 where
  chain := fun k hklt hk =>
    exactChainUpperOfExactBlockTarget (E.exactBlock k hklt hk)

end ExactBlockThresholdEvidence

/-! ## Exact targets from exact evidence -/

/-- Exact-chain data for every positive block count gives the exact block-form
Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_exactChainUpper
    (chain : forall k : Nat, 0 < k -> SplitSoundness.ExactChainUpper k) :
    ExactTarget := by
  intro k hk
  let C := chain k hk
  exact Exists.intro C.config C.independent_card_le_five_mul

/-- Exact-block `At (16 * k)` data for every positive block count gives the
exact block-form Pach--Toth target after simplifying the exact ceiling. -/
theorem targetUpperConstructionFiveSixteen_of_exactBlockTargets
    (exactBlock : forall k : Nat, 0 < k -> ExactBlockTarget k) :
    ExactTarget := by
  intro k hk
  let C := Classical.choose (exactBlock k hk)
  have hC := Classical.choose_spec (exactBlock k hk)
  refine Exists.intro C ?_
  intro s hs
  have hbound := hC s hs
  have hceil : ceilDiv (5 * (16 * k)) 16 = 5 * k := by
    unfold ceilDiv
    omega
  simpa [targetUpperConstructionFiveSixteenAt, hceil] using hbound

/-! ## Large fields plus a proved small complement -/

/-- The generic large/small package: large closed-placement fields from block
threshold `K0`, plus the finite small complement below `16 * K0`. -/
structure LargeWithSmallComplementFields (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  small : targetUpperConstructionFiveSixteenSmallUpTo (16 * K0)

namespace LargeWithSmallComplementFields

theorem targetUpperConstructionFiveSixteenAt_large
    {K0 : Nat} (P : LargeWithSmallComplementFields K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n :=
  targetAt_largeClosedPlacementFields P.large hn

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : LargeWithSmallComplementFields K0) :
    EventualTarget :=
  eventualTarget_largeClosedPlacementFields (K0 := K0) P.large

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : LargeWithSmallComplementFields K0) :
    ArbitraryTarget :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
    (16 * K0)
    (fun n hn =>
      targetUpperConstructionFiveSixteenAt_large P (n := n) hn)
    P.small

end LargeWithSmallComplementFields

/-! ## Large fields plus exact-chain finite evidence -/

/-- Large closed-placement fields together with exact-chain evidence for the
finite complement below the large threshold. -/
structure LargeWithExactChainComplementFields (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  exactChainBelowThreshold : ExactChainThresholdEvidence K0

namespace LargeWithExactChainComplementFields

def toSmallComplementFields
    {K0 : Nat} (P : LargeWithExactChainComplementFields K0) :
    LargeWithSmallComplementFields K0 where
  large := P.large
  small :=
    ExactChainThresholdEvidence.targetUpperConstructionFiveSixteenSmallUpTo
      P.exactChainBelowThreshold

def exactChainUpper
    {K0 k : Nat} (P : LargeWithExactChainComplementFields K0)
    (hk : 0 < k) :
    SplitSoundness.ExactChainUpper k := by
  by_cases hK : K0 <= k
  case pos =>
    exact LargeExplicitClosedPlacementCertificates.exactChainUpper
      P.large k hK hk
  case neg =>
    exact P.exactChainBelowThreshold.chain k (Nat.lt_of_not_ge hK) hk

theorem exactBlockTarget
    {K0 k : Nat} (P : LargeWithExactChainComplementFields K0)
    (hk : 0 < k) :
    ExactBlockTarget k := by
  by_cases hK : K0 <= k
  case pos =>
    exact exactBlockTarget_largeClosedPlacementFields P.large hK hk
  case neg =>
    exact
      ExactChainThresholdEvidence.exactBlockTarget
        P.exactChainBelowThreshold (Nat.lt_of_not_ge hK) hk

theorem targetUpperConstructionFiveSixteenAt_large
    {K0 : Nat} (P : LargeWithExactChainComplementFields K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n :=
  targetAt_largeClosedPlacementFields P.large hn

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : LargeWithExactChainComplementFields K0) :
    EventualTarget :=
  eventualTarget_largeClosedPlacementFields (K0 := K0) P.large

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : LargeWithExactChainComplementFields K0) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_exactChainUpper
    (fun _k hk => P.exactChainUpper hk)

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : LargeWithExactChainComplementFields K0) :
    ArbitraryTarget :=
  LargeWithSmallComplementFields.targetUpperConstructionFiveSixteenArbitrary
    P.toSmallComplementFields

end LargeWithExactChainComplementFields

/-! ## Large fields plus exact-block finite evidence -/

/-- Large closed-placement fields together with exact-block evidence for the
finite complement below the large threshold. -/
structure LargeWithExactBlockComplementFields (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  exactBlockBelowThreshold : ExactBlockThresholdEvidence K0

namespace LargeWithExactBlockComplementFields

noncomputable def toExactChainComplementFields
    {K0 : Nat} (P : LargeWithExactBlockComplementFields K0) :
    LargeWithExactChainComplementFields K0 where
  large := P.large
  exactChainBelowThreshold :=
    P.exactBlockBelowThreshold.toExactChainThresholdEvidence

def toSmallComplementFields
    {K0 : Nat} (P : LargeWithExactBlockComplementFields K0) :
    LargeWithSmallComplementFields K0 where
  large := P.large
  small :=
    ExactBlockThresholdEvidence.targetUpperConstructionFiveSixteenSmallUpTo
      P.exactBlockBelowThreshold

theorem exactBlockTarget
    {K0 k : Nat} (P : LargeWithExactBlockComplementFields K0)
    (hk : 0 < k) :
    ExactBlockTarget k := by
  by_cases hK : K0 <= k
  case pos =>
    exact exactBlockTarget_largeClosedPlacementFields P.large hK hk
  case neg =>
    exact P.exactBlockBelowThreshold.exactBlock
      k (Nat.lt_of_not_ge hK) hk

theorem targetUpperConstructionFiveSixteenAt_large
    {K0 : Nat} (P : LargeWithExactBlockComplementFields K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n :=
  targetAt_largeClosedPlacementFields P.large hn

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : LargeWithExactBlockComplementFields K0) :
    EventualTarget :=
  eventualTarget_largeClosedPlacementFields (K0 := K0) P.large

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : LargeWithExactBlockComplementFields K0) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_exactBlockTargets
    (fun _k hk => P.exactBlockTarget hk)

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : LargeWithExactBlockComplementFields K0) :
    ArbitraryTarget :=
  LargeWithSmallComplementFields.targetUpperConstructionFiveSixteenArbitrary
    P.toSmallComplementFields

end LargeWithExactBlockComplementFields

/-! ## All-positive finite fields -/

theorem exactBlockTarget_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  exactBlockTarget_of_allPositiveFiniteFields F k hk

theorem exactTarget_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_allPositiveFiniteFields F

theorem arbitraryTarget_allPositiveFiniteFields
    (F : AllPositiveFiniteFields) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_allPositiveFiniteFields F

/-- All-positive finite fields provide exact evidence for every block, while
large fields still record the source-faithful eventual threshold. -/
structure LargeWithAllPositiveFiniteFields (K0 : Nat) where
  large : LargeClosedPlacementFields K0
  finite : AllPositiveFiniteFields

namespace LargeWithAllPositiveFiniteFields

def toExactBlockComplementFields
    {K0 : Nat} (P : LargeWithAllPositiveFiniteFields K0) :
    LargeWithExactBlockComplementFields K0 where
  large := P.large
  exactBlockBelowThreshold := {
    exactBlock := fun k _hklt hk =>
      exactBlockTarget_allPositiveFiniteFields P.finite k hk }

theorem targetUpperConstructionFiveSixteenAt_large
    {K0 : Nat} (P : LargeWithAllPositiveFiniteFields K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n :=
  targetAt_largeClosedPlacementFields P.large hn

theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (P : LargeWithAllPositiveFiniteFields K0) :
    EventualTarget :=
  eventualTarget_largeClosedPlacementFields (K0 := K0) P.large

theorem targetUpperConstructionFiveSixteen
    {K0 : Nat} (P : LargeWithAllPositiveFiniteFields K0) :
    ExactTarget :=
  exactTarget_allPositiveFiniteFields P.finite

theorem targetUpperConstructionFiveSixteenArbitrary
    {K0 : Nat} (P : LargeWithAllPositiveFiniteFields K0) :
    ArbitraryTarget :=
  arbitraryTarget_allPositiveFiniteFields P.finite

theorem exact_eventual_arbitrary
    {K0 : Nat} (P : LargeWithAllPositiveFiniteFields K0) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget := by
  exact
    And.intro
      P.targetUpperConstructionFiveSixteen
      (And.intro
        P.targetUpperConstructionFiveSixteenEventually
        P.targetUpperConstructionFiveSixteenArbitrary)

end LargeWithAllPositiveFiniteFields

/-! ## Threshold-at-most-one endpoint -/

/-- If the large threshold is at most one block, large fields alone cover
every positive exact block count. -/
theorem exactTarget_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ExactTarget :=
  targetUpperConstructionFiveSixteen_of_largeClosedPlacementFields_atMostOne
    L hK0

/-- If the large threshold is at most one block, checked remainders turn the
exact block-form target into the arbitrary-`n` target. -/
theorem arbitraryTarget_largeClosedPlacementFields_atMostOne
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (hK0 : K0 <= 1) :
    ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_largeClosedPlacementFields_atMostOne
    L hK0

end

end LargeSmallCaseClosureW14
end PachToth
end ErdosProblems1066
