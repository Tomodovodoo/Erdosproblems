import ErdosProblems1066.PachToth.PeriodInterface
import ErdosProblems1066.PachToth.GeneratedSeparationInterface
import ErdosProblems1066.PachToth.ClosedPlacementClosure
import ErdosProblems1066.PachToth.RoleHingeInterfaceRefinement

set_option autoImplicit false

/-!
# Generated period closure wrappers

This module connects the finite generated period equation named in
`PeriodInterface` with the generated separation interface used by the exact
Pach--Toth target reduction.

No period, separation, or isometry fact is asserted here.  The theorems below
only convert explicitly supplied generated period equations into the closure
and exact-target wrappers already proved downstream.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPeriodClosure

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Local facade for the orbit-level exact-local squared-distance invariant. -/
abbrev GeneratedOrbitMatchesExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
    O hk base orientation

/-- Local facade for one-chain metric data whose same-block control is
supplied by orbit-level exact-local squared distances. -/
abbrev GeneratedOrbitSqDistanceMetricHypotheses
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  RoleHingeInterfaceRefinement.GeneratedOrbitSqDistanceMetricHypotheses
    O hk base orientation

namespace GeneratedOrbitSqDistanceMetricHypotheses

/-- Convert the orbit-square-distance facade to the full generated metric
hypotheses consumed by the existing generated-period closure route. -/
def toMetricHypotheses
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    {base : LocalVertex -> R2}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    (H : GeneratedOrbitSqDistanceMetricHypotheses O hk base orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation :=
  RoleHingeInterfaceRefinement.GeneratedOrbitSqDistanceMetricHypotheses.toMetricHypotheses
    H

end GeneratedOrbitSqDistanceMetricHypotheses

/-- Package global separation and orbit-level exact-local squared distances
as the full generated metric facade. -/
def generatedMetricHypotheses_of_orbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (horbit :
      GeneratedOrbitMatchesExactLocalSqDistances O hk base orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation :=
  RoleHingeInterfaceRefinement.generatedMetricHypotheses_of_orbitSqDistances
    O hk base orientation separated horbit

/-- Promote reduced generated metric data to the full metric facade by
deriving same-block isometry along the generated orbit. -/
def generatedMetricHypotheses_of_reducedMetricHypotheses
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated := H.separated
  same_block_isometry :=
    GeneratedSeparationInterface.same_block_isometry_of_reduced
      O hk base orientation H

/-- The period equation named by `PeriodInterface` is the period hypothesis
used by `GeneratedSeparationInterface`. -/
theorem generatedPeriod_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base orientation := by
  exact hperiod

/-- The finite generated period equation gives the algebraic closure equation
from cyclic index `0`. -/
theorem generatedClosureEquation_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation) :
    PeriodInterface.GeneratedClosureEquation O hk base orientation := by
  exact
    PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
      O hk base orientation hperiod

/-- Package a generated chain closed by a generated period equation as an
explicit transition closed-placement certificate. -/
def explicitTransitionClosedPlacementCertificate_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedPeriod
    O hk base orientation
    (generatedPeriod_of_generatedPeriodEquation
      O hk base orientation hperiod)
    H

/-- Reduced metric data also packages into an explicit transition
closed-placement certificate once the generated period equation is known. -/
def explicitTransitionClosedPlacementCertificate_of_generatedPeriodEquation_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedPeriod_reduced
    O hk base orientation
    (generatedPeriod_of_generatedPeriodEquation
      O hk base orientation hperiod)
    H

/-- Build the deformed closed placement carried by a generated period
equation and full generated metric data. -/
def closedPlacement_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (explicitTransitionClosedPlacementCertificate_of_generatedPeriodEquation
    O hk base orientation hperiod H).toClosedPlacement

/-- Build the deformed closed placement carried by a generated period
equation and reduced generated metric data. -/
def closedPlacement_of_generatedPeriodEquation_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  (explicitTransitionClosedPlacementCertificate_of_generatedPeriodEquation_reduced
    O hk base orientation hperiod H).toClosedPlacement

/-- A generated period equation and full metric data produce the downstream
closed-placement existence statement with the generated point map. -/
theorem exists_closedPlacement_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    Exists.intro
      (closedPlacement_of_generatedPeriodEquation
        O hk base orientation hperiod H)
      rfl

/-- A generated period equation and reduced metric data produce the downstream
closed-placement existence statement with the generated point map. -/
theorem exists_closedPlacement_of_generatedPeriodEquation_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    Exists.intro
      (closedPlacement_of_generatedPeriodEquation_reduced
        O hk base orientation hperiod H)
      rfl

/-- One generated period equation plus full generated metric hypotheses gives
the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock
      O hk base orientation
      (generatedPeriod_of_generatedPeriodEquation
        O hk base orientation hperiod)
      H

/-- One generated period equation plus reduced generated metric hypotheses
gives the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
      O hk base orientation
      (generatedPeriod_of_generatedPeriodEquation
        O hk base orientation hperiod)
      H

/-- Period equations for every positive member of a generated-chain family,
using the period equation named in `PeriodInterface`. -/
def FamilyPeriodEquations
    (F : GeneratedSeparationInterface.GeneratedChainFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    PeriodInterface.GeneratedPeriodEquation
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)

/-- Convert family period equations into the period hypotheses consumed by the
generated separation interface. -/
theorem familyPeriods_of_periodEquations
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F) :
    GeneratedSeparationInterface.GeneratedChainFamily.Periods F := by
  intro k hk
  exact
    generatedPeriod_of_generatedPeriodEquation
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (hperiod k hk)

/-- Family period equations converted to the algebraic closure equations used
by the closed-placement closure interface. -/
theorem familyClosures_of_periodEquations
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures F := by
  intro k hk
  exact
    generatedClosureEquation_of_generatedPeriodEquation
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (hperiod k hk)

/-- Promote family-level reduced generated metric data to the full metric
facade. -/
def familyMetricHypotheses_of_reducedMetricHypotheses
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F where
  metric := fun k hk =>
    generatedMetricHypotheses_of_reducedMetricHypotheses
      (F.O k hk) hk (F.base k hk) (F.orientation k hk) (H.metric k hk)

/-- A family of generated period equations plus full generated metric
hypotheses gives the exact Pach--Toth `5 / 16` target. -/
theorem targetUpperConstructionFiveSixteen_of_family_periodEquations
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteen_of_family
      F (familyPeriods_of_periodEquations F hperiod) H

/-- A family of generated period equations plus reduced generated metric
hypotheses gives the exact Pach--Toth `5 / 16` target. -/
theorem targetUpperConstructionFiveSixteen_of_family_periodEquations_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteen_of_family_reduced
      F (familyPeriods_of_periodEquations F hperiod) H

/-- Generated period equations and full metric hypotheses give closed
placements for every positive block count in the family. -/
def closedPlacementFamily_of_periodEquations
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedPeriodEquation
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (hperiod k hk) (H.metric k hk)

/-- Generated period equations and reduced metric hypotheses give closed
placements for every positive block count in the family. -/
def closedPlacementFamily_of_periodEquations_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedPeriodEquation_reduced
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (hperiod k hk) (H.metric k hk)

/-- Combined family period-equation theorem: full generated metric
hypotheses give closed placements at every positive block count and the exact
target. -/
theorem exists_closedPlacement_and_target_of_family_periodEquations
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
              (F.orientation k hk))
      targetUpperConstructionFiveSixteen := by
  exact
    And.intro
      (fun k hk =>
        exists_closedPlacement_of_generatedPeriodEquation
          (F.O k hk) hk (F.base k hk) (F.orientation k hk)
          (hperiod k hk) (H.metric k hk))
      (targetUpperConstructionFiveSixteen_of_family_periodEquations
        F hperiod H)

/-- Combined family period-equation theorem: reduced generated metric
hypotheses give closed placements at every positive block count and the exact
target. -/
theorem exists_closedPlacement_and_target_of_family_periodEquations_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
              (F.orientation k hk))
      targetUpperConstructionFiveSixteen := by
  exact
    And.intro
      (fun k hk =>
        exists_closedPlacement_of_generatedPeriodEquation_reduced
          (F.O k hk) hk (F.base k hk) (F.orientation k hk)
          (hperiod k hk) (H.metric k hk))
      (targetUpperConstructionFiveSixteen_of_family_periodEquations_reduced
        F hperiod H)

/-- Raw-function wrapper with already packaged full generated metric
hypotheses for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_metricHypotheses
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
    (H :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedMetricHypotheses
          (O k hk) hk (base k hk) (orientation k hk)) :
    targetUpperConstructionFiveSixteen := by
  let F : GeneratedSeparationInterface.GeneratedChainFamily :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteen_of_family_periodEquations
      F (fun k hk => period k hk)
      { metric := fun k hk => H k hk }

/-- Raw-function wrapper with already packaged reduced generated metric
hypotheses for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_reducedMetricHypotheses
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
    (H :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
          (O k hk) hk (base k hk) (orientation k hk)) :
    targetUpperConstructionFiveSixteen := by
  let F : GeneratedSeparationInterface.GeneratedChainFamily :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteen_of_family_periodEquations_reduced
      F (fun k hk => period k hk)
      { metric := fun k hk => H k hk }

/-- Raw-function closed-placement family wrapper with packaged full generated
metric hypotheses for every positive block count. -/
def closedPlacementFamily_of_period_metricHypotheses
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
    (H :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedMetricHypotheses
          (O k hk) hk (base k hk) (orientation k hk)) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedPeriodEquation
      (O k hk) hk (base k hk) (orientation k hk)
      (period k hk) (H k hk)

/-- Raw-function closed-placement family wrapper with packaged reduced
generated metric hypotheses for every positive block count. -/
def closedPlacementFamily_of_period_reducedMetricHypotheses
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
    (H :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
          (O k hk) hk (base k hk) (orientation k hk)) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk =>
    closedPlacement_of_generatedPeriodEquation_reduced
      (O k hk) hk (base k hk) (orientation k hk)
      (period k hk) (H k hk)

/-- Raw-function wrapper: packaged full generated metric hypotheses give both
closed placements and the exact target. -/
theorem exists_closedPlacement_and_target_of_period_metricHypotheses
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
    (H :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedMetricHypotheses
          (O k hk) hk (base k hk) (orientation k hk)) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
              (orientation k hk))
      targetUpperConstructionFiveSixteen := by
  let F : GeneratedSeparationInterface.GeneratedChainFamily :=
    { O := O
      base := base
      orientation := orientation }
  exact
    exists_closedPlacement_and_target_of_family_periodEquations
      F (fun k hk => period k hk)
      { metric := fun k hk => H k hk }

/-- Raw-function wrapper: packaged reduced generated metric hypotheses give
both closed placements and the exact target. -/
theorem exists_closedPlacement_and_target_of_period_reducedMetricHypotheses
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
    (H :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
          (O k hk) hk (base k hk) (orientation k hk)) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint (O k hk) hk (base k hk)
              (orientation k hk))
      targetUpperConstructionFiveSixteen := by
  let F : GeneratedSeparationInterface.GeneratedChainFamily :=
    { O := O
      base := base
      orientation := orientation }
  exact
    exists_closedPlacement_and_target_of_family_periodEquations_reduced
      F (fun k hk => period k hk)
      { metric := fun k hk => H k hk }

/-- Raw-function wrapper: finite generated period equations, global generated
separation, and same-block isometry for every positive block count imply the
exact Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
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
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk)) :
    targetUpperConstructionFiveSixteen := by
  let F : GeneratedSeparationInterface.GeneratedChainFamily :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteen_of_family_periodEquations F
      (fun k hk => period k hk)
      { metric := fun k hk =>
          { separated := separated k hk
            same_block_isometry := same_block_isometry k hk } }

/-- Raw-function wrapper with same-block isometry reduced to base-block
isometry and transition preservation. -/
theorem targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
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
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk)) :
    targetUpperConstructionFiveSixteen := by
  let F : GeneratedSeparationInterface.GeneratedChainFamily :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteen_of_family_periodEquations_reduced F
      (fun k hk => period k hk)
      { metric := fun k hk =>
          { separated := separated k hk
            base_same_block_isometry := base_same_block_isometry k hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hk } }

/-- One generated period equation plus orbit-square-distance metric
hypotheses gives the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_orbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedOrbitSqDistanceMetricHypotheses O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation hperiod H.toMetricHypotheses

/-- Raw one-chain wrapper: a generated period equation, global separation,
and orbit-level exact-local squared distances give the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_period_separation_orbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (horbit :
      GeneratedOrbitMatchesExactLocalSqDistances O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_orbitSqDistances
      O hk base orientation hperiod
      { separated := separated
        orbit_sq_distances := horbit }

/-- Local facade for family-level orbit-square-distance metric hypotheses. -/
abbrev GeneratedChainFamilyOrbitSqDistanceHypotheses
    (F : GeneratedSeparationInterface.GeneratedChainFamily) : Prop :=
  RoleHingeInterfaceRefinement.GeneratedChainFamilyOrbitSqDistanceHypotheses F

namespace GeneratedChainFamilyOrbitSqDistanceHypotheses

/-- Convert family-level orbit-square-distance metric data to the full metric
hypotheses consumed by the generated-period closure family route. -/
def toMetricHypotheses
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (H : GeneratedChainFamilyOrbitSqDistanceHypotheses F) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F :=
  RoleHingeInterfaceRefinement.GeneratedChainFamilyOrbitSqDistanceHypotheses.toMetricHypotheses
    H

end GeneratedChainFamilyOrbitSqDistanceHypotheses

/-- A family of generated period equations plus orbit-square-distance metric
hypotheses gives the exact Pach--Toth `5 / 16` target. -/
theorem targetUpperConstructionFiveSixteen_of_family_periodEquations_orbitSqDistances
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (hperiod : FamilyPeriodEquations F)
    (H : GeneratedChainFamilyOrbitSqDistanceHypotheses F) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_family_periodEquations F hperiod
      H.toMetricHypotheses

/-- Raw-function wrapper: finite generated period equations, global generated
separation, and orbit-level exact-local squared distances for every positive
block count imply the exact Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_period_separation_orbitSqDistances
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
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          (O k hk) hk (base k hk) (orientation k hk))
    (orbit_sq_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedOrbitMatchesExactLocalSqDistances
          (O k hk) hk (base k hk) (orientation k hk)) :
    targetUpperConstructionFiveSixteen := by
  let F : GeneratedSeparationInterface.GeneratedChainFamily :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteen_of_family_periodEquations_orbitSqDistances
      F (fun k hk => period k hk)
      { separated := fun k hk => separated k hk
        orbit_sq_distances := fun k hk => orbit_sq_distances k hk }

end

end GeneratedPeriodClosure
end PachToth
end ErdosProblems1066
