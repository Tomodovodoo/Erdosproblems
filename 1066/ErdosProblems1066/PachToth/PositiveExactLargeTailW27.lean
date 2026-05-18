import ErdosProblems1066.PachToth.PositiveExactChainPackageW26
import ErdosProblems1066.PachToth.ClosedPlacementConcreteConstructionW26
import ErdosProblems1066.PachToth.ConcreteReducedMetricCertificatesW26
import ErdosProblems1066.PachToth.FullToReducedMetricClosureW26
import ErdosProblems1066.PachToth.LargeKClosedPlacementSourceW20

set_option autoImplicit false

/-!
# W27 positive exact large-tail worker

This file attacks
`PositiveExactChainPackageW26.RemainingPositiveExactChainBlocker` directly:
the blocker is the exact block target for every `k >= 6`, after the exact
small blocks one through five have been split off in W26.

The route below is pointwise.  It uses exact-chain, closed-placement,
generated-chain, reduced-metric, and large closed-placement packages to prove
the block `16 * k` target at each `k >= 6`; it does not derive the tail from
the global exact target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PositiveExactLargeTailW27

open Arithmetic

noncomputable section

abbrev ExactChainUpper (k : Nat) : Type :=
  PositiveExactChainPackageW26.ExactChainUpper k

abbrev ExactBlockTarget (k : Nat) : Prop :=
  PositiveExactChainPackageW26.ExactBlockTarget k

abbrev ExactBlocksOneThroughFive : Prop :=
  PositiveExactChainPackageW26.ExactBlocksOneThroughFive

abbrev RemainingPositiveExactChainBlocker : Prop :=
  PositiveExactChainPackageW26.RemainingPositiveExactChainBlocker

abbrev PositiveExactChainPackage : Type :=
  PositiveExactChainPackageW26.PositiveExactChainPackage

abbrev SmallAndLargeExactBlockTargets : Prop :=
  PositiveExactChainPackageW26.SmallAndLargeExactBlockTargets

abbrev ClosedPlacementFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ClosedPlacementFamily

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedPlacementConcreteConstructionW26.ConcreteClosedOrbitFamily

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedPlacementConcreteConstructionW26.MinimalFieldsWithOrbitClosure

abbrev LargeClosedPlacementFieldsFromSix : Type :=
  LargeClosedPlacementInstantiationW13.LargeClosedPlacementFields 6

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedClosureMetricRowPackage

abbrev ReducedMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness

abbrev FullMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteReducedMetricCertificate : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteReducedMetricCertificate

/-! ## Tail from exact-chain and closed-placement sources -/

theorem exactBlockTarget_of_exactChainUpper
    {k : Nat} (chain : ExactChainUpper k) :
    ExactBlockTarget k :=
  SmallLengthExactTargetsConcreteW24.exactBlockTarget_of_exactChainUpper
    chain

theorem remainingBlocker_of_exactChainTailFromSix
    (H : forall k : Nat, 6 <= k -> ExactChainUpper k) :
    RemainingPositiveExactChainBlocker := by
  intro k hk
  exact exactBlockTarget_of_exactChainUpper (H k hk)

theorem exactBlockTarget_of_closedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    ExactBlockTarget k :=
  exactBlockTarget_of_exactChainUpper
    (SplitArbitraryNNonRigidBridge.exactChainUpperOfClosedPlacement P)

theorem remainingBlocker_of_closedPlacementFamily
    (H : ClosedPlacementFamily) :
    RemainingPositiveExactChainBlocker := by
  intro k hk
  have hkpos : 0 < k := by omega
  exact exactBlockTarget_of_closedPlacement (H k hkpos)

theorem remainingBlocker_of_nonempty_closedPlacementFamily :
    Nonempty ClosedPlacementFamily -> RemainingPositiveExactChainBlocker := by
  intro h
  rcases h with ⟨H⟩
  exact remainingBlocker_of_closedPlacementFamily H

theorem remainingBlocker_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    RemainingPositiveExactChainBlocker :=
  remainingBlocker_of_closedPlacementFamily F.toClosedPlacementFamily

theorem remainingBlocker_of_minimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    RemainingPositiveExactChainBlocker :=
  remainingBlocker_of_concreteClosedOrbitFamily
    M.toConcreteClosedOrbitFamily

/-! ## Tail from generated-chain and reduced-metric packages -/

theorem exactBlockTarget_of_w19InputPackage
    (P : W19InputPackage) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  P.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem remainingBlocker_of_w19InputPackage
    (P : W19InputPackage) :
    RemainingPositiveExactChainBlocker := by
  intro k hk
  exact exactBlockTarget_of_w19InputPackage P k (by omega)

theorem remainingBlocker_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    RemainingPositiveExactChainBlocker :=
  remainingBlocker_of_w19InputPackage P.toInputPackage

theorem exactBlockTarget_of_reducedMetricClosedPlacementWitness
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  W.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem remainingBlocker_of_reducedMetricClosedPlacementWitness
    (W : ReducedMetricClosedPlacementWitness) :
    RemainingPositiveExactChainBlocker := by
  intro k hk
  exact exactBlockTarget_of_reducedMetricClosedPlacementWitness W k (by omega)

theorem exactBlockTarget_of_fullMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k :=
  W.targetUpperConstructionFiveSixteenAt_exactBlock k hk

theorem remainingBlocker_of_fullMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementWitness) :
    RemainingPositiveExactChainBlocker := by
  intro k hk
  exact exactBlockTarget_of_fullMetricClosedPlacementWitness W k (by omega)

/-! ## Tail from the W26 concrete reduced-metric route -/

theorem remainingBlocker_of_concreteReducedMetricCertificate
    (P : ConcreteReducedMetricCertificate) :
    RemainingPositiveExactChainBlocker :=
  remainingBlocker_of_generatedClosureMetricRowPackage
    P.generatedClosureMetricRowPackage

theorem remainingBlocker_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    RemainingPositiveExactChainBlocker :=
  remainingBlocker_of_concreteReducedMetricCertificate
    (ConcreteReducedMetricCertificatesW26.concreteReducedMetricCertificateOfLowerTables
      C)

theorem remainingBlocker_of_concreteLowerTables_reducedWitness
    (C : ConcreteNonConnectorLowerTableFamily) :
    RemainingPositiveExactChainBlocker :=
  remainingBlocker_of_reducedMetricClosedPlacementWitness
    (FullToReducedMetricClosureW26.reducedMetricClosedPlacementWitnessOfConcreteLowerTables
      C)

/-! ## Tail from threshold-six large closed placements -/

theorem remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (L : LargeClosedPlacementFieldsFromSix) :
    RemainingPositiveExactChainBlocker := by
  intro k hk
  have hkpos : 0 < k := by omega
  exact
    LargeClosedPlacementInstantiationW13.exactBlockTarget_of_largeClosedPlacementFields
      L hk hkpos

theorem remainingBlocker_of_w19InputPackage_as_largeFromSix
    (P : W19InputPackage) :
    RemainingPositiveExactChainBlocker :=
  remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (LargeKClosedPlacementSourceW20.largeClosedPlacementFieldsOfInputPackage
      6 P)

/-! ## Reattaching the W26 small block package -/

def smallAndLargeExactBlockTargets
    (small : ExactBlocksOneThroughFive)
    (large : RemainingPositiveExactChainBlocker) :
    SmallAndLargeExactBlockTargets where
  small := small
  large := large

def positiveExactChainPackageOfSmallBlocksAndLargeTail
    (small : ExactBlocksOneThroughFive)
    (large : RemainingPositiveExactChainBlocker) :
    PositiveExactChainPackage :=
  PositiveExactChainPackageW26.packageOfSmallAndLargeExactBlockTargets
    (smallAndLargeExactBlockTargets small large)

def positiveExactChainPackageOfSmallBlocksAndLargeClosedPlacements
    (small : ExactBlocksOneThroughFive)
    (L : LargeClosedPlacementFieldsFromSix) :
    PositiveExactChainPackage :=
  positiveExactChainPackageOfSmallBlocksAndLargeTail small
    (remainingBlocker_of_largeClosedPlacementFieldsFromSix L)

theorem nonempty_positiveExactChainPackage_of_smallBlocks_and_largeTail
    (small : ExactBlocksOneThroughFive)
    (large : RemainingPositiveExactChainBlocker) :
    Nonempty PositiveExactChainPackage :=
  Nonempty.intro
    (positiveExactChainPackageOfSmallBlocksAndLargeTail small large)

theorem nonempty_positiveExactChainPackage_of_smallBlocks_and_largeClosedPlacements
    (small : ExactBlocksOneThroughFive)
    (L : LargeClosedPlacementFieldsFromSix) :
    Nonempty PositiveExactChainPackage :=
  Nonempty.intro
    (positiveExactChainPackageOfSmallBlocksAndLargeClosedPlacements small L)

end

end PositiveExactLargeTailW27
end PachToth

namespace Verified

abbrev PachTothW27RemainingPositiveExactChainBlocker : Prop :=
  PachToth.PositiveExactLargeTailW27.RemainingPositiveExactChainBlocker

abbrev PachTothW27LargeClosedPlacementFieldsFromSix : Type :=
  PachToth.PositiveExactLargeTailW27.LargeClosedPlacementFieldsFromSix

theorem pachtoth_w27_remainingBlocker_of_largeClosedPlacementFieldsFromSix
    (L : PachTothW27LargeClosedPlacementFieldsFromSix) :
    PachTothW27RemainingPositiveExactChainBlocker :=
  PachToth.PositiveExactLargeTailW27.remainingBlocker_of_largeClosedPlacementFieldsFromSix
    L

end Verified
end ErdosProblems1066
