import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.ClosedPlacementClosure

set_option autoImplicit false

/-!
# Generated metric closure from role-hinged transitions

This module packages the metric part of a generated closed chain when the
base block is the checked exact block and the same/opposite transitions are
supplied by `BaseTransitionRealization`.

The orientation word, generated closure equation, and global separation are
still explicit inputs.  The only facts discharged here are the reduced
same-block metric hypotheses: exact base isometry and preservation of
same-block distances by the role-hinged same/opposite transition maps.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedMetricClosure

open ClosedPlacementClosure
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The role-hinged same/opposite transition package built on the exact base. -/
abbrev RoleHingeTransitions :=
  BaseTransitionRealization.BaseSameOppositeTransitionRealization

/-- The checked exact base block is a generated base same-block isometry. -/
theorem exactBase_generatedBaseSameBlockIsometry :
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
      BaseTransitionRealization.exactBase := by
  intro u v
  simpa [HingedTransitionInterface.referenceDistance] using
    BaseTransitionRealization.exactBase_same_block_isometry u v

/-- Role-hinged same/opposite transitions preserve same-block distances after
forgetting to the generated-chain Figure 2 transition interface. -/
theorem roleHingeTransitions_preserveSameBlockDistances
    (T : RoleHingeTransitions) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      T.toFigure2TransitionObligations := by
  intro orientation source u v
  cases orientation
  case same =>
    exact T.same.preserves_same_block_distances source u v
  case opposite =>
    exact T.opposite.preserves_same_block_distances source u v

/-- Reduced generated metric hypotheses for the exact base and role-hinged
transitions.  Global generated separation remains the explicit geometric
input. -/
def generatedReducedMetricHypotheses
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation where
  separated := separated
  base_same_block_isometry := exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    roleHingeTransitions_preserveSameBlockDistances T

@[simp]
theorem generatedReducedMetricHypotheses_separated
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    (generatedReducedMetricHypotheses T hk orientation separated).separated =
      separated :=
  rfl

@[simp]
theorem generatedReducedMetricHypotheses_baseSameBlock
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    (generatedReducedMetricHypotheses T hk orientation separated).base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

theorem generatedReducedMetricHypotheses_transitionPreserves
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      T.toFigure2TransitionObligations := by
  let H := generatedReducedMetricHypotheses T hk orientation separated
  exact H.transition_preserves_same_block_distances

/-- The explicit transition closed-placement certificate obtained from a
role-hinged generated closure. -/
def explicitTransitionClosedPlacementCertificate
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure_reduced
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation closure
      (generatedReducedMetricHypotheses T hk orientation separated)

/-- The closed placement obtained from a role-hinged generated closure. -/
def closedPlacement
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacement_of_generatedClosure_reduced
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation closure
    (generatedReducedMetricHypotheses T hk orientation separated)

/-- Existence form of the closed placement produced by role-hinged generated
closure and explicit generated separation. -/
theorem exists_closedPlacement
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint T.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase orientation := by
  exact
    ClosedPlacementClosure.exists_closedPlacement_of_generatedClosure_reduced
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation closure
      (generatedReducedMetricHypotheses T hk orientation separated)

/-- Exact-block target from role-hinged generated closure and explicit
generated separation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure_reduced
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation closure
        (generatedReducedMetricHypotheses T hk orientation separated)

/-- Bundled one-chain version of role-hinged generated closure data. -/
structure RoleHingedGeneratedClosureData (k : Nat) (hk : 0 < k) where
  transitions : RoleHingeTransitions
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  separated :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation

namespace RoleHingedGeneratedClosureData

/-- Project bundled role-hinged closure data to reduced generated metric
hypotheses. -/
def toGeneratedReducedMetricHypotheses
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase G.orientation :=
  generatedReducedMetricHypotheses G.transitions hk G.orientation G.separated

@[simp]
theorem toGeneratedReducedMetricHypotheses_separated
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.separated = G.separated :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_baseSameBlock
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_transitionPreserves
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.transition_preserves_same_block_distances =
      roleHingeTransitions_preserveSameBlockDistances G.transitions :=
  rfl

/-- Project bundled data to the explicit transition closed-placement
certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionClosedPlacementCertificate G.transitions hk G.orientation
    G.closure G.separated

/-- Project bundled data to the closed placement. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacement G.transitions hk G.orientation G.closure G.separated

/-- Bundled role-hinged generated closure data gives the closed-placement
existence theorem. -/
theorem exists_closedPlacement
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint
          G.transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase G.orientation := by
  exact
    GeneratedMetricClosure.exists_closedPlacement G.transitions hk
      G.orientation G.closure G.separated

/-- Bundled role-hinged generated closure data gives the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedMetricClosure.targetUpperConstructionFiveSixteenAt_exactBlock
      G.transitions hk G.orientation G.closure G.separated

end RoleHingedGeneratedClosureData

/-- Family version with one role-hinged transition package and explicit
orientation, closure, and separation data for every positive block count. -/
structure RoleHingedGeneratedClosureFamily where
  transitions : RoleHingeTransitions
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)

namespace RoleHingedGeneratedClosureFamily

/-- Forget the role-hinged construction to the generated-chain family
interface. -/
def toGeneratedChainFamily
    (F : RoleHingedGeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

@[simp]
theorem toGeneratedChainFamily_O
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.O k hk =
      F.transitions.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem toGeneratedChainFamily_base
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toGeneratedChainFamily_orientation
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.orientation k hk = F.orientation k hk :=
  rfl

/-- Project family closure equations to the closed-placement closure
interface. -/
def toGeneratedChainFamilyClosures
    (F : RoleHingedGeneratedClosureFamily) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures
      F.toGeneratedChainFamily :=
  fun k hk => F.closure k hk

/-- Project family separation and role-hinged metric data to reduced
generated metric hypotheses. -/
def toReducedMetricHypotheses
    (F : RoleHingedGeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      F.toGeneratedChainFamily where
  metric := fun k hk =>
    generatedReducedMetricHypotheses F.transitions hk (F.orientation k hk)
      (F.separated k hk)

@[simp]
theorem toReducedMetricHypotheses_metric_separated
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).separated =
      F.separated k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_baseSameBlock
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_transitionPreserves
    (F : RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).transition_preserves_same_block_distances =
      roleHingeTransitions_preserveSameBlockDistances F.transitions :=
  rfl

/-- Closed placements for every positive block count in the role-hinged
generated-closure family. -/
def closedPlacementFamily
    (F : RoleHingedGeneratedClosureFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacementFamily_of_generatedClosure_reduced
    F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
    F.toReducedMetricHypotheses

/-- Family target theorem obtained by projecting to `ClosedPlacementClosure`. -/
theorem targetUpperConstructionFiveSixteen
    (F : RoleHingedGeneratedClosureFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
        F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
        F.toReducedMetricHypotheses

/-- Combined closed-placement existence and exact-block target for the
role-hinged generated-closure family. -/
theorem exists_closedPlacement_and_target
    (F : RoleHingedGeneratedClosureFamily) :
    And
      (forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point =
            GeneratedClosedChain.generatedPoint
              F.transitions.toFigure2TransitionObligations hk
              BaseTransitionRealization.exactBase (F.orientation k hk))
      PachToth.targetUpperConstructionFiveSixteen := by
  simpa [toGeneratedChainFamily] using
    ClosedPlacementClosure.exists_closedPlacement_and_target_of_generatedClosure_family_reduced
        F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
        F.toReducedMetricHypotheses

end RoleHingedGeneratedClosureFamily

/-- Raw-function family wrapper keeping all orientation-dependent closure and
separation hypotheses explicit. -/
theorem targetUpperConstructionFiveSixteen_of_roleHingeTransitions
    (T : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (orientation k hk))
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (orientation k hk)) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    RoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      { transitions := T
        orientation := orientation
        closure := closure
        separated := separated }

end

end GeneratedMetricClosure
end PachToth
end ErdosProblems1066
