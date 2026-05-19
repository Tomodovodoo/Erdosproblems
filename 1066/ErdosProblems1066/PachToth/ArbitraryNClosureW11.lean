import ErdosProblems1066.PachToth.ArbitraryNBridgeW10
import ErdosProblems1066.PachToth.ArbitraryNExactRemainderClosure
import ErdosProblems1066.PachToth.SplitArbitraryNNonRigidBridge
import ErdosProblems1066.PachToth.SplitRealizationFinal
import ErdosProblems1066.PachToth.RemainderConstruction

set_option autoImplicit false

/-!
# W11 arbitrary-`n` closure adapters

This module is a checked adapter layer over the W10 exact/remainder bridge.
It keeps the finite remainder input, the eventual vertex threshold, and the
finite small-case input visible in the types.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNClosureW11

noncomputable section

/-- Finite remainder certificates for the only remainder range used by the
`n = 16 * (n / 16) + n % 16` split. -/
structure FiniteRemainderPackage where
  upper : forall r : Nat, r < 16 -> SplitSoundness.RemainderUpper r

/-- The checked finite remainder package built from `RemainderConstruction`. -/
def checkedRemainderUpperOfLtSixteen {r : Nat} (hr : r < 16) :
    SplitSoundness.RemainderUpper r where
  config :=
    Classical.choose (RemainderConstruction.exists_remainder_config_mod_sixteen hr)
  independent_card_le_ceil_third :=
    Classical.choose_spec
      (RemainderConstruction.exists_remainder_config_mod_sixteen hr)

/-- The canonical checked finite remainder package. -/
def checkedFiniteRemainders : FiniteRemainderPackage where
  upper := fun r hr => checkedRemainderUpperOfLtSixteen (r := r) hr

/-- A fixed and arbitrary target facade. -/
structure ArbitraryNTargetFacade where
  fixedTarget : forall n : Nat, targetUpperConstructionFiveSixteenAt n
  arbitraryTarget : targetUpperConstructionFiveSixteenArbitrary

namespace ArbitraryNTargetFacade

/-- Build a facade from fixed-`n` targets for every `n`. -/
def ofFixed
    (H : forall n : Nat, targetUpperConstructionFiveSixteenAt n) :
    ArbitraryNTargetFacade where
  fixedTarget := H
  arbitraryTarget := fun n => H n

end ArbitraryNTargetFacade

/-- A threshold facade which records the large-case and small-case sides
before exposing the arbitrary target. -/
structure ThresholdTargetFacade where
  vertexThreshold : Nat
  largeTarget :
    forall n : Nat, vertexThreshold <= n ->
      targetUpperConstructionFiveSixteenAt n
  smallTarget : targetUpperConstructionFiveSixteenSmallUpTo vertexThreshold
  arbitraryTarget : targetUpperConstructionFiveSixteenArbitrary

namespace ThresholdTargetFacade

/-- Forget the threshold bookkeeping after the arbitrary target has been
assembled. -/
def toArbitraryNTargetFacade
    (F : ThresholdTargetFacade) :
    ArbitraryNTargetFacade where
  fixedTarget := fun n => F.arbitraryTarget n
  arbitraryTarget := F.arbitraryTarget

end ThresholdTargetFacade

/-- A quotient exact chain and an explicit finite remainder package close the
target at the original vertex count. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChainDivMod_finiteRemainders
    (R : FiniteRemainderPackage) (n : Nat)
    (chain : SplitSoundness.ExactChainUpper (n / 16)) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  rw [hsplit]
  exact
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      chain
      (R.upper (n % 16) hr)

/-- Checked-remainder specialization of the quotient exact-chain adapter. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactChainDivMod_checkedRemainders
    (n : Nat) (chain : SplitSoundness.ExactChainUpper (n / 16)) :
    targetUpperConstructionFiveSixteenAt n :=
  targetUpperConstructionFiveSixteenAt_of_exactChainDivMod_finiteRemainders
    checkedFiniteRemainders n chain

/-- Exact closed-chain data for every positive block count. -/
structure ExactClosedChainPackage where
  chain : forall k : Nat, 0 < k -> SplitSoundness.ExactChainUpper k

namespace ExactClosedChainPackage

/-- Repackage as the W10 positive exact-chain package. -/
def toW10PositiveExactChainPackage
    (P : ExactClosedChainPackage) :
    ArbitraryNBridgeW10.PositiveExactChainPackage where
  exactChain := P.chain

/-- Exact closed chains supply the exact block Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (P : ExactClosedChainPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  P.toW10PositiveExactChainPackage.targetUpperConstructionFiveSixteen

/-- Select the quotient exact chain, using the empty chain at quotient zero. -/
def chainAtDiv
    (P : ExactClosedChainPackage) (n : Nat) :
    SplitSoundness.ExactChainUpper (n / 16) := by
  by_cases hk : 0 < n / 16
  case pos =>
    exact P.chain (n / 16) hk
  case neg =>
    have hdiv : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
    rw [hdiv]
    exact SplitSoundness.emptyExactChainUpper

/-- Fixed-`n` target from exact closed chains and an explicit finite remainder
package. -/
theorem fixedTarget
    (P : ExactClosedChainPackage) (R : FiniteRemainderPackage) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n :=
  targetUpperConstructionFiveSixteenAt_of_exactChainDivMod_finiteRemainders
    R n (P.chainAtDiv n)

/-- Arbitrary target from exact closed chains and an explicit finite remainder
package. -/
theorem arbitraryTarget
    (P : ExactClosedChainPackage) (R : FiniteRemainderPackage) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact P.fixedTarget R n

/-- Facade from exact closed chains and an explicit finite remainder package. -/
def targetFacade
    (P : ExactClosedChainPackage) (R : FiniteRemainderPackage) :
    ArbitraryNTargetFacade :=
  ArbitraryNTargetFacade.ofFixed (fun n => P.fixedTarget R n)

/-- Checked-remainder facade from exact closed chains. -/
def checkedTargetFacade
    (P : ExactClosedChainPackage) :
    ArbitraryNTargetFacade :=
  P.targetFacade checkedFiniteRemainders

/-- W10 checked-remainder arbitrary target from the same exact closed-chain
package. -/
theorem arbitraryTarget_viaW10
    (P : ExactClosedChainPackage) :
    targetUpperConstructionFiveSixteenArbitrary :=
  P.toW10PositiveExactChainPackage
    |>.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders

/-- Split-bridge checked-remainder arbitrary target from the same exact
closed-chain package. -/
theorem arbitraryTarget_splitBridge
    (P : ExactClosedChainPackage) :
    targetUpperConstructionFiveSixteenArbitrary :=
  P.toW10PositiveExactChainPackage
    |>.targetUpperConstructionFiveSixteenArbitrary_splitBridge

end ExactClosedChainPackage

/-- Exact generated closed-chain data for every positive block count. -/
structure ExactGeneratedClosedChainPackage where
  data :
    forall (k : Nat) (hk : 0 < k),
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk

namespace ExactGeneratedClosedChainPackage

/-- Generated closed-chain data supplies exact closed-chain certificates. -/
def toExactClosedChainPackage
    (P : ExactGeneratedClosedChainPackage) :
    ExactClosedChainPackage where
  chain := fun k hk =>
    SplitArbitraryNNonRigidBridge.exactChainUpperOfExactGeneratedClosedChainData
      (P.data k hk)

/-- Facade from exact generated closed chains and an explicit finite remainder
package. -/
def targetFacade
    (P : ExactGeneratedClosedChainPackage) (R : FiniteRemainderPackage) :
    ArbitraryNTargetFacade :=
  P.toExactClosedChainPackage.targetFacade R

/-- Checked-remainder facade from exact generated closed chains. -/
def checkedTargetFacade
    (P : ExactGeneratedClosedChainPackage) :
    ArbitraryNTargetFacade :=
  P.targetFacade checkedFiniteRemainders

/-- Split-bridge arbitrary target from exact generated closed chains. -/
theorem arbitraryTarget_splitBridge
    (P : ExactGeneratedClosedChainPackage) :
    targetUpperConstructionFiveSixteenArbitrary :=
  open SplitArbitraryNNonRigidBridge in
  targetUpperConstructionFiveSixteenArbitrary_of_exactGeneratedClosedChainData
    P.data

end ExactGeneratedClosedChainPackage

/-- Eventual exact closed-chain data together with its finite small-case
complement.  The vertex threshold is `16 * threshold`. -/
structure EventualClosedChainPackage where
  threshold : Nat
  largeChain :
    forall k : Nat, threshold <= k -> 0 < k ->
      SplitSoundness.ExactChainUpper k
  smallCases : targetUpperConstructionFiveSixteenSmallUpTo (16 * threshold)

namespace EventualClosedChainPackage

/-- Select the quotient exact chain in the large range.  Quotient zero is
handled by the empty chain. -/
def chainAtLargeDiv
    (P : EventualClosedChainPackage) (n : Nat)
    (hn : 16 * P.threshold <= n) :
    SplitSoundness.ExactChainUpper (n / 16) := by
  by_cases hk : 0 < n / 16
  case pos =>
    exact P.largeChain (n / 16) (by omega) hk
  case neg =>
    have hdiv : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
    rw [hdiv]
    exact SplitSoundness.emptyExactChainUpper

/-- Large-case target from eventual closed chains and an explicit finite
remainder package. -/
theorem largeTarget
    (P : EventualClosedChainPackage) (R : FiniteRemainderPackage)
    (n : Nat) (hn : 16 * P.threshold <= n) :
    targetUpperConstructionFiveSixteenAt n :=
  targetUpperConstructionFiveSixteenAt_of_exactChainDivMod_finiteRemainders
    R n (P.chainAtLargeDiv n hn)

/-- Threshold facade from eventual closed chains, with the finite small cases
kept as a field. -/
def thresholdFacade
    (P : EventualClosedChainPackage) (R : FiniteRemainderPackage) :
    ThresholdTargetFacade where
  vertexThreshold := 16 * P.threshold
  largeTarget := fun n hn => P.largeTarget R n hn
  smallTarget := P.smallCases
  arbitraryTarget :=
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * P.threshold)
      (fun n hn => P.largeTarget R n hn)
      P.smallCases

/-- Arbitrary facade from eventual closed chains and explicit finite
remainders. -/
def targetFacade
    (P : EventualClosedChainPackage) (R : FiniteRemainderPackage) :
    ArbitraryNTargetFacade :=
  (P.thresholdFacade R).toArbitraryNTargetFacade

/-- Arbitrary target from eventual closed chains and explicit finite
remainders. -/
theorem arbitraryTarget
    (P : EventualClosedChainPackage) (R : FiniteRemainderPackage) :
    targetUpperConstructionFiveSixteenArbitrary :=
  (P.thresholdFacade R).arbitraryTarget

/-- Checked-remainder facade from eventual closed chains. -/
def checkedTargetFacade
    (P : EventualClosedChainPackage) :
    ArbitraryNTargetFacade :=
  P.targetFacade checkedFiniteRemainders

/-- Build an eventual package when the finite complement is supplied as
exact chains below the block threshold. -/
def ofLargeAndSmallChains
    (K0 : Nat)
    (largeChain :
      forall k : Nat, K0 <= k -> 0 < k ->
        SplitSoundness.ExactChainUpper k)
    (smallChain :
      forall k : Nat, k < K0 -> 0 < k ->
        SplitSoundness.ExactChainUpper k) :
    EventualClosedChainPackage where
  threshold := K0
  largeChain := largeChain
  smallCases :=
    SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold
      K0 smallChain

/-- Build an eventual package when the finite complement is supplied as exact
block targets below the block threshold. -/
def ofLargeChainsAndExactBlockSmallCases
    (K0 : Nat)
    (largeChain :
      forall k : Nat, K0 <= k -> 0 < k ->
        SplitSoundness.ExactChainUpper k)
    (exactBlock :
      forall k : Nat, k < K0 -> 0 < k ->
        targetUpperConstructionFiveSixteenAt (16 * k)) :
    EventualClosedChainPackage where
  threshold := K0
  largeChain := largeChain
  smallCases :=
    open SmallCaseCertificates in
    targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
      K0 exactBlock

/-- Build an eventual package when a full exact target supplies the finite
small-case complement. -/
def ofLargeChainsAndExactTargetSmallCases
    (K0 : Nat)
    (largeChain :
      forall k : Nat, K0 <= k -> 0 < k ->
        SplitSoundness.ExactChainUpper k)
    (Hexact : targetUpperConstructionFiveSixteen) :
    EventualClosedChainPackage where
  threshold := K0
  largeChain := largeChain
  smallCases :=
    SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactTarget
      Hexact K0

end EventualClosedChainPackage

/-- Eventual generated closed-chain data together with the finite small-case
complement. -/
structure EventualGeneratedClosedChainPackage where
  threshold : Nat
  largeData :
    forall k : Nat, threshold <= k -> forall hk : 0 < k,
      SplitRealizationClosure.ExactGeneratedClosedChainData k hk
  smallCases : targetUpperConstructionFiveSixteenSmallUpTo (16 * threshold)

namespace EventualGeneratedClosedChainPackage

/-- Generated eventual data supplies eventual exact closed-chain data. -/
def toEventualClosedChainPackage
    (P : EventualGeneratedClosedChainPackage) :
    EventualClosedChainPackage where
  threshold := P.threshold
  largeChain := fun k hK hk =>
    SplitArbitraryNNonRigidBridge.exactChainUpperOfExactGeneratedClosedChainData
      (P.largeData k hK hk)
  smallCases := P.smallCases

/-- Threshold facade from eventual generated closed chains and explicit finite
remainders. -/
def thresholdFacade
    (P : EventualGeneratedClosedChainPackage) (R : FiniteRemainderPackage) :
    ThresholdTargetFacade :=
  P.toEventualClosedChainPackage.thresholdFacade R

/-- Arbitrary facade from eventual generated closed chains and explicit finite
remainders. -/
def targetFacade
    (P : EventualGeneratedClosedChainPackage) (R : FiniteRemainderPackage) :
    ArbitraryNTargetFacade :=
  P.toEventualClosedChainPackage.targetFacade R

/-- Checked-remainder facade from eventual generated closed chains. -/
def checkedTargetFacade
    (P : EventualGeneratedClosedChainPackage) :
    ArbitraryNTargetFacade :=
  P.targetFacade checkedFiniteRemainders

/-- Arbitrary target from eventual generated closed chains and explicit finite
remainders. -/
theorem arbitraryTarget
    (P : EventualGeneratedClosedChainPackage) (R : FiniteRemainderPackage) :
    targetUpperConstructionFiveSixteenArbitrary :=
  P.toEventualClosedChainPackage.arbitraryTarget R

end EventualGeneratedClosedChainPackage

/-- W10 exact-target packages as W11 target facades. -/
def targetFacadeOfW10ExactTargetPackage
    (P : ArbitraryNBridgeW10.ExactTargetPackage) :
    ArbitraryNTargetFacade where
  fixedTarget :=
    fun n =>
      ArbitraryNBridgeW10.ExactTargetPackage.targetUpperConstructionFiveSixteenAt_checkedRemainders
        P n
  arbitraryTarget :=
    open ArbitraryNBridgeW10.ExactTargetPackage in
    targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
      P

/-- W10 positive exact-chain packages as W11 target facades. -/
def targetFacadeOfW10PositiveExactChainPackage
    (P : ArbitraryNBridgeW10.PositiveExactChainPackage) :
    ArbitraryNTargetFacade where
  fixedTarget :=
    fun n =>
      open ArbitraryNBridgeW10.PositiveExactChainPackage in
      targetUpperConstructionFiveSixteenAt_checkedRemainders
        P n
  arbitraryTarget :=
    open ArbitraryNBridgeW10.PositiveExactChainPackage in
    targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
      P

end

end ArbitraryNClosureW11
end PachToth
end ErdosProblems1066
