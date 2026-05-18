import ErdosProblems1066.PachToth.GeneratedPeriodClosure

set_option autoImplicit false

/-!
# Generated far-apart separation wrappers

This module turns quantitative lower-bound checks for generated point pairs
into the named `GeneratedGlobalSeparation` hypothesis, then routes those
checks through the exact-block and arbitrary-`n` generated-chain closures.

The cross-block wrappers discharge same-block separation from the checked
one-block certificate and a supplied same-block isometry, so only genuinely
cross-block distance lower bounds remain.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedSeparationFarApart

open FiniteGraph
open GeneratedPeriodClosure
open GeneratedSeparationInterface

noncomputable section

abbrev R2 := Prod Real Real

/-- A per-pair quantitative lower bound for distinct generated vertices. -/
def GeneratedPairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) ->
      lower i u j v <=
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A per-pair lower-bound table is strong enough for separation. -/
def GeneratedPairLowerBoundsAtLeastOne
    {k : Nat}
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) -> 1 <= lower i u j v

/-- A cross-block-only quantitative lower bound.  Same-block pairs can often
be discharged from the finite one-block data instead. -/
def GeneratedCrossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j ->
      lower i u j v <=
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A cross-block lower-bound table is strong enough for separation on every
cross-block pair. -/
def GeneratedCrossBlockLowerBoundsAtLeastOne
    {k : Nat}
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j -> 1 <= lower i u j v

/-- Quantitative pairwise lower bounds imply generated global separation. -/
theorem generatedGlobalSeparation_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  exact le_trans (hge_one i u j v hne) (hlower i u j v hne)

/-- Uniform quantitative lower bounds imply generated global separation. -/
theorem generatedGlobalSeparation_of_uniformDistanceLowerBound
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    {delta : Real}
    (hdelta : 1 <= delta)
    (hlower :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          delta <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  exact le_trans hdelta (hlower i u j v hne)

/-- Same-block generated separation follows from the checked one-block finite
separation data and a same-block isometry. -/
theorem generatedSameBlockSeparation_of_sameBlockIsometry
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation) :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
        1 <=
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation i v) := by
  intro i u v huv
  have hfin :
      Ne (BlockPartition.localVertexEquivFin16 u)
        (BlockPartition.localVertexEquivFin16 v) := by
    intro h
    exact huv (BlockPartition.localVertexEquivFin16.injective h)
  have hsep :=
    OneBlockSoundness.oneBlockCertificate.separated
      (BlockPartition.localVertexEquivFin16 u)
      (BlockPartition.localVertexEquivFin16 v) hfin
  rw [same_block_isometry i u v]
  exact hsep

/-- Cross-block quantitative lower bounds, plus finite same-block separation,
imply generated global separation. -/
theorem generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  by_cases hij : i = j
  case pos =>
    subst j
    have huv : Ne u v := by
      intro huv
      exact hne (Prod.ext rfl huv)
    exact
      generatedSameBlockSeparation_of_sameBlockIsometry
        O hk base orientation same_block_isometry i u v huv
  case neg =>
    exact le_trans (hge_one i u j v hij) (hlower i u j v hij)

/-- Uniform cross-block lower bounds, plus finite same-block separation, imply
generated global separation. -/
theorem generatedGlobalSeparation_of_uniformCrossBlockDistanceLowerBound
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    {delta : Real}
    (hdelta : 1 <= delta)
    (hlower :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          delta <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation same_block_isometry
      (fun _i _u _j _v => delta)
      (fun i u j v hij => hdelta)
      (fun i u j v hij => hlower i u j v hij)

/-- Cross-block lower bounds with reduced same-block hypotheses. -/
theorem generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)
      lower hge_one hlower

/-- Uniform cross-block lower bounds with reduced same-block hypotheses. -/
theorem generatedGlobalSeparation_of_uniformCrossBlockDistanceLowerBound_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    {delta : Real}
    (hdelta : 1 <= delta)
    (hlower :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          delta <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_uniformCrossBlockDistanceLowerBound
      O hk base orientation
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)
      hdelta hlower

/-- Package full generated metric hypotheses from per-pair lower bounds. -/
def generatedMetricHypotheses_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_pairDistanceLowerBounds
      O hk base orientation lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package reduced generated metric hypotheses from per-pair lower bounds. -/
def generatedReducedMetricHypotheses_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_pairDistanceLowerBounds
      O hk base orientation lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Package full generated metric hypotheses from cross-block lower bounds,
using finite same-block separation for pairs in the same block. -/
def generatedMetricHypotheses_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation same_block_isometry lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package reduced generated metric hypotheses from cross-block lower bounds,
using finite same-block separation for pairs in the same block. -/
def generatedReducedMetricHypotheses_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
      O hk base orientation base_same_block_isometry
      transition_preserves_same_block_distances lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Exact-block target from one period equation, same-block isometry, and
per-pair lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_pairDistanceLowerBounds
        O hk base orientation same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data, and
per-pair lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_pairDistanceLowerBounds_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_pairDistanceLowerBounds
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact-block target from one period equation and cross-block lower bounds.
Same-block separation is obtained from the checked finite block. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_crossBlockDistanceLowerBounds
        O hk base orientation same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data, and
cross-block lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockDistanceLowerBounds_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_crossBlockDistanceLowerBounds
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact Pach--Toth target from generated period equations and per-pair lower
bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_pairDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_pairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, and per-pair lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_pairDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_pairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Exact Pach--Toth target from generated period equations and cross-block
lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_crossBlockDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk)
          (same_block_isometry k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, and cross-block lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_crossBlockDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
          (O k hk) hk (base k hk) (orientation k hk)
          (base_same_block_isometry k hk)
          (transition_preserves_same_block_distances k hk)
          (lower k hk) (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, per-pair lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_pairDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_pairDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, per-pair lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_pairDistanceLowerBounds_and_small_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_pairDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, cross-block lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_crossBlockDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (same_block_isometry k hK hk) (lower k hK hk)
                (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, cross-block lower bounds, and the supplied small
cases. -/
theorem targetArbitrary_of_eventual_period_crossBlockDistanceLowerBounds_and_small_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (base_same_block_isometry k hK hk)
                (transition_preserves_same_block_distances k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

end

end GeneratedSeparationFarApart
end PachToth
end ErdosProblems1066
