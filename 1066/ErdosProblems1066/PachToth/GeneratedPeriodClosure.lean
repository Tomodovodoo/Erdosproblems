import ErdosProblems1066.PachToth.PeriodInterface
import ErdosProblems1066.PachToth.GeneratedSeparationInterface

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

end

end GeneratedPeriodClosure
end PachToth
end ErdosProblems1066
