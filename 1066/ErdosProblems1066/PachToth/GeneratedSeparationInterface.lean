import ErdosProblems1066.PachToth.GeneratedClosedChainEventualReduction

set_option autoImplicit false

/-!
# Generated separation interface

This module names the global metric hypotheses used by generated closed
chains, then gives small conditional wrappers into the generated closed-chain
reduction layers.  The wrappers do not add geometry; they keep the repeated
separation and same-block hypotheses explicit while making theorem statements
shorter at call sites.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedSeparationInterface

open ClosedChainReduction
open FiniteGraph
open GeneratedClosedChainEventualReduction
open GeneratedClosedChainReduction

noncomputable section

abbrev R2 := Prod Real Real

/-- The final generated block returns to the base block. -/
def GeneratedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  GeneratedClosedChain.generatedBlock O hk base orientation k = base

/-- Global separation for all distinct generated vertices in a closed chain. -/
def GeneratedGlobalSeparation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) ->
      1 <=
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- Every generated block has the same internal metric as the checked block. -/
def GeneratedSameBlockIsometry
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  forall (i : Fin k) (u v : LocalVertex),
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint O hk base orientation i u)
      (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
        _root_.eucDist
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 u))
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 v))

/-- The base block has the checked one-block metric. -/
def GeneratedBaseSameBlockIsometry
    (base : LocalVertex -> R2) : Prop :=
  forall u v : LocalVertex,
    _root_.eucDist (base u) (base v) =
      _root_.eucDist
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 u))
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 v))

/-- All selected same/opposite transitions preserve same-block distances. -/
def GeneratedTransitionsPreserveSameBlockDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  forall (o : OrientationData.BlockOrientation)
      (source : LocalVertex -> R2) (u v : LocalVertex),
    _root_.eucDist
      ((O.transitionFor o).placeNext source u)
      ((O.transitionFor o).placeNext source v) =
        _root_.eucDist (source u) (source v)

/-- Metric hypotheses for one generated closed chain, using full same-block
isometry on every generated block. -/
structure GeneratedMetricHypotheses
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) where
  separated : GeneratedGlobalSeparation O hk base orientation
  same_block_isometry : GeneratedSameBlockIsometry O hk base orientation

/-- Reduced metric hypotheses for one generated closed chain: global separation
plus base-block isometry and transition preservation. -/
structure GeneratedReducedMetricHypotheses
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (_orientation : Fin k -> OrientationData.BlockOrientation) where
  separated : GeneratedGlobalSeparation O hk base _orientation
  base_same_block_isometry : GeneratedBaseSameBlockIsometry base
  transition_preserves_same_block_distances :
    GeneratedTransitionsPreserveSameBlockDistances O

/-- The reduced same-block hypotheses imply same-block isometry for every
generated block. -/
theorem same_block_isometry_of_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (H : GeneratedReducedMetricHypotheses O hk base orientation) :
    GeneratedSameBlockIsometry O hk base orientation :=
  GeneratedClosedChain.generatedPoint_same_block_isometry
    O hk base orientation H.base_same_block_isometry
    H.transition_preserves_same_block_distances

/-- A generated chain with named metric hypotheses packages into the explicit
transition closed-placement certificate. -/
def explicitTransitionClosedPlacementCertificate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedPeriod O hk base orientation)
    (H : GeneratedMetricHypotheses O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  GeneratedClosedChainReduction.explicitTransitionClosedPlacementCertificateOfGenerated
    O hk base orientation period H.separated H.same_block_isometry

/-- A generated chain with reduced named metric hypotheses packages into the
explicit transition closed-placement certificate. -/
def explicitTransitionClosedPlacementCertificate_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedPeriod O hk base orientation)
    (H : GeneratedReducedMetricHypotheses O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionClosedPlacementCertificateOfGenerated_reducedSameBlock
    O hk base orientation period H.separated H.base_same_block_isometry
    H.transition_preserves_same_block_distances

/-- Exact-block reduction from one generated closed chain with named metric
hypotheses. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedPeriod O hk base orientation)
    (H : GeneratedMetricHypotheses O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generated_closed_chain
      O hk base orientation period H.separated H.same_block_isometry

/-- Exact-block reduction from one generated closed chain with reduced named
metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : GeneratedPeriod O hk base orientation)
    (H : GeneratedReducedMetricHypotheses O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generated_closed_chain_reducedSameBlock
      O hk base orientation period H.separated H.base_same_block_isometry
      H.transition_preserves_same_block_distances

/-- Named generated-chain data for every positive block count. -/
structure GeneratedChainFamily where
  O :
    forall (k : Nat), 0 < k ->
      Figure2Certificate.SameOppositeTransitionObligations
  base : forall (k : Nat), 0 < k -> LocalVertex -> R2
  orientation :
    forall (k : Nat) (_hk : 0 < k),
      Fin k -> OrientationData.BlockOrientation

/-- Period hypotheses for a generated-chain family. -/
def GeneratedChainFamily.Periods (F : GeneratedChainFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    GeneratedPeriod (F.O k hk) hk (F.base k hk) (F.orientation k hk)

/-- Full metric hypotheses for a generated-chain family. -/
structure GeneratedChainFamily.MetricHypotheses (F : GeneratedChainFamily) where
  metric :
    forall (k : Nat) (hk : 0 < k),
      GeneratedMetricHypotheses (F.O k hk) hk (F.base k hk)
        (F.orientation k hk)

/-- Reduced metric hypotheses for a generated-chain family. -/
structure GeneratedChainFamily.ReducedMetricHypotheses
    (F : GeneratedChainFamily) where
  metric :
    forall (k : Nat) (hk : 0 < k),
      GeneratedReducedMetricHypotheses (F.O k hk) hk (F.base k hk)
        (F.orientation k hk)

/-- Generated closed-chain certificates for every positive block count imply
the exact-block target, using named family hypotheses. -/
theorem targetUpperConstructionFiveSixteen_of_family
    (F : GeneratedChainFamily)
    (period : F.Periods)
    (H : F.MetricHypotheses) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedClosedChainReduction.targetUpperConstructionFiveSixteen_of_generated_closed_chains
      F.O F.base F.orientation period
      (fun k hk => (H.metric k hk).separated)
      (fun k hk => (H.metric k hk).same_block_isometry)

/-- Generated closed-chain certificates for every positive block count imply
the exact-block target, using reduced named family hypotheses. -/
theorem targetUpperConstructionFiveSixteen_of_family_reduced
    (F : GeneratedChainFamily)
    (period : F.Periods)
    (H : F.ReducedMetricHypotheses) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_generated_closed_chains_reducedSameBlock
      F.O F.base F.orientation period
      (fun k hk => (H.metric k hk).separated)
      (fun k hk => (H.metric k hk).base_same_block_isometry)
      (fun k hk => (H.metric k hk).transition_preserves_same_block_distances)

/-- Named eventual generated-chain data for all block counts from `K0` onward. -/
structure EventualGeneratedChainFamily (K0 : Nat) where
  O :
    forall (k : Nat), K0 <= k -> 0 < k ->
      Figure2Certificate.SameOppositeTransitionObligations
  base :
    forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
      LocalVertex -> R2
  orientation :
    forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
      Fin k -> OrientationData.BlockOrientation

/-- Period hypotheses for an eventual generated-chain family. -/
def EventualGeneratedChainFamily.Periods {K0 : Nat}
    (F : EventualGeneratedChainFamily K0) : Prop :=
  forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
    GeneratedPeriod (F.O k hK hk) hk (F.base k hK hk)
      (F.orientation k hK hk)

/-- Full metric hypotheses for an eventual generated-chain family. -/
structure EventualGeneratedChainFamily.MetricHypotheses {K0 : Nat}
    (F : EventualGeneratedChainFamily K0) where
  metric :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedMetricHypotheses (F.O k hK hk) hk (F.base k hK hk)
        (F.orientation k hK hk)

/-- Reduced metric hypotheses for an eventual generated-chain family. -/
structure EventualGeneratedChainFamily.ReducedMetricHypotheses {K0 : Nat}
    (F : EventualGeneratedChainFamily K0) where
  metric :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedReducedMetricHypotheses (F.O k hK hk) hk (F.base k hK hk)
        (F.orientation k hK hk)

/-- Eventual generated closed-chain data and small cases imply the arbitrary
Pach--Toth target, using named metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
    {K0 : Nat} (F : EventualGeneratedChainFamily K0)
    (period : F.Periods)
    (H : F.MetricHypotheses)
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_generated_closed_chains_and_small
      K0 F.O F.base F.orientation period
      (fun k hK hk => (H.metric k hK hk).separated)
      (fun k hK hk => (H.metric k hK hk).same_block_isometry)
      Hsmall

/-- Eventual generated closed-chain data and small cases imply the arbitrary
Pach--Toth target, using reduced named metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
    {K0 : Nat} (F : EventualGeneratedChainFamily K0)
    (period : F.Periods)
    (H : F.ReducedMetricHypotheses)
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_generated_chains_base_transitions
      K0 F.O F.base F.orientation period
      (fun k hK hk => (H.metric k hK hk).separated)
      (fun k hK hk => (H.metric k hK hk).base_same_block_isometry)
      (fun k hK hk => (H.metric k hK hk).transition_preserves_same_block_distances)
      Hsmall

end

end GeneratedSeparationInterface
end PachToth
end ErdosProblems1066
