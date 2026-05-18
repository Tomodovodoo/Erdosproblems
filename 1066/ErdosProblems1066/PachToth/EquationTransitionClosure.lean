import ErdosProblems1066.PachToth.ConnectorEquationClosure
import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.HingeAlgebra
import ErdosProblems1066.PachToth.GeneratedMetricClosure

set_option autoImplicit false

/-!
# Equation transition closure

This module packages same/opposite transition metric data directly from the
explicit connector equations of `ConnectorEquationClosure`.

The connector equations and same-block preservation hypotheses remain explicit
inputs.  The only work done here is routing those inputs through the strongest
same/opposite metric interfaces and the generated reduced-metric closure
pipeline.
-/

namespace ErdosProblems1066
namespace PachToth
namespace EquationTransitionClosure

open FiniteGraph
open ClosedPlacementClosure

noncomputable section

abbrev R2 := Prod Real Real

/-- One equation-carried transition with explicit connector equations and
same-block preservation. -/
abbrev EquationTransitionData :=
  ConnectorEquationClosure.EquationTransition

/-- Same/opposite equation-carried transitions based at the checked exact
local block. -/
abbrev SameOppositeEquationTransitionData :=
  ConnectorEquationClosure.SameOppositeEquationTransition

/-- Build one equation-carried transition from fully explicit equation and
same-block preservation inputs. -/
def equationTransitionOfEquations
    (offset : R2)
    (eq211 :
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h)
    (eq212 :
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h)
    (eq400 :
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h)
    (eq402 :
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h)
    (preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext offset)) :
    EquationTransitionData where
  offset := offset
  eq211 := eq211
  eq212 := eq212
  eq400 := eq400
  eq402 := eq402
  preserves_same_block_distances := preserves_same_block_distances

@[simp]
theorem equationTransitionOfEquations_offset
    (offset : R2)
    (eq211 :
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h)
    (eq212 :
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h)
    (eq400 :
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h)
    (eq402 :
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h)
    (preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext offset)) :
    (equationTransitionOfEquations offset eq211 eq212 eq400 eq402
        preserves_same_block_distances).offset = offset :=
  rfl

/-- Build one transition metric package directly from explicit connector
equations and same-block preservation. -/
def transitionMetricObligationsOfEquations
    (offset : R2)
    (eq211 :
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h)
    (eq212 :
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h)
    (eq400 :
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h)
    (eq402 :
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h)
    (preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext offset)) :
    HingedTransitionInterface.TransitionMetricObligations :=
  (equationTransitionOfEquations offset eq211 eq212 eq400 eq402
      preserves_same_block_distances).toTransitionMetricObligations

@[simp]
theorem transitionMetricObligationsOfEquations_placeNext
    (offset : R2)
    (eq211 :
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h)
    (eq212 :
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h)
    (eq400 :
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h)
    (eq402 :
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h)
    (preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext offset)) :
    (transitionMetricObligationsOfEquations offset eq211 eq212 eq400 eq402
        preserves_same_block_distances).placeNext =
      ConnectorEquationClosure.equationPlaceNext offset :=
  rfl

/-- Build the same/opposite equation-transition data from explicit equations
for each orientation and explicit same-block preservation for each transition. -/
def sameOppositeEquationTransitionOfEquations
    (sameOffset oppositeOffset : R2)
    (same_eq211 :
      ConnectorEquationFacts.eq211 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq212 :
      ConnectorEquationFacts.eq212 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq400 :
      ConnectorEquationFacts.eq400 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq402 :
      ConnectorEquationFacts.eq402 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext sameOffset))
    (opposite_eq211 :
      ConnectorEquationFacts.eq211 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq212 :
      ConnectorEquationFacts.eq212 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq400 :
      ConnectorEquationFacts.eq400 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq402 :
      ConnectorEquationFacts.eq402 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext oppositeOffset)) :
    SameOppositeEquationTransitionData where
  same :=
    equationTransitionOfEquations sameOffset
      same_eq211 same_eq212 same_eq400 same_eq402
      same_preserves_same_block_distances
  opposite :=
    equationTransitionOfEquations oppositeOffset
      opposite_eq211 opposite_eq212 opposite_eq400 opposite_eq402
      opposite_preserves_same_block_distances

/-- The strongest same/opposite transition metric package obtained from
explicit connector equations and same-block preservation. -/
def sameOppositeTransitionMetricObligationsOfEquations
    (sameOffset oppositeOffset : R2)
    (same_eq211 :
      ConnectorEquationFacts.eq211 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq212 :
      ConnectorEquationFacts.eq212 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq400 :
      ConnectorEquationFacts.eq400 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq402 :
      ConnectorEquationFacts.eq402 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext sameOffset))
    (opposite_eq211 :
      ConnectorEquationFacts.eq211 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq212 :
      ConnectorEquationFacts.eq212 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq400 :
      ConnectorEquationFacts.eq400 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq402 :
      ConnectorEquationFacts.eq402 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext oppositeOffset)) :
    HingedTransitionInterface.SameOppositeTransitionMetricObligations :=
  (sameOppositeEquationTransitionOfEquations sameOffset oppositeOffset
      same_eq211 same_eq212 same_eq400 same_eq402
      same_preserves_same_block_distances
      opposite_eq211 opposite_eq212 opposite_eq400 opposite_eq402
      opposite_preserves_same_block_distances).toMetricObligations

@[simp]
theorem sameOppositeTransitionMetricObligationsOfEquations_base
    (sameOffset oppositeOffset : R2)
    (same_eq211 :
      ConnectorEquationFacts.eq211 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq212 :
      ConnectorEquationFacts.eq212 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq400 :
      ConnectorEquationFacts.eq400 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_eq402 :
      ConnectorEquationFacts.eq402 sameOffset.1 sameOffset.2
        ExactLocalGeometry.h)
    (same_preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext sameOffset))
    (opposite_eq211 :
      ConnectorEquationFacts.eq211 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq212 :
      ConnectorEquationFacts.eq212 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq400 :
      ConnectorEquationFacts.eq400 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_eq402 :
      ConnectorEquationFacts.eq402 oppositeOffset.1 oppositeOffset.2
        ExactLocalGeometry.h)
    (opposite_preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances
        (ConnectorEquationClosure.equationPlaceNext oppositeOffset)) :
    (sameOppositeTransitionMetricObligationsOfEquations sameOffset
        oppositeOffset same_eq211 same_eq212 same_eq400 same_eq402
        same_preserves_same_block_distances opposite_eq211 opposite_eq212
        opposite_eq400 opposite_eq402
        opposite_preserves_same_block_distances).base =
      BaseTransitionRealization.exactBase :=
  rfl

/-- Equation-carried same/opposite transitions preserve generated same-block
distances after forgetting to the Figure 2 transition interface. -/
theorem equationTransitions_preserveSameBlockDistances
    (T : SameOppositeEquationTransitionData) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      T.toFigure2TransitionObligations := by
  intro orientation source u v
  cases orientation
  case same =>
    exact T.same.preserves_same_block_distances source u v
  case opposite =>
    exact T.opposite.preserves_same_block_distances source u v

/-- The checked exact base block is the generated base same-block isometry used
by equation-carried transitions. -/
theorem exactBase_generatedBaseSameBlockIsometry :
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
      BaseTransitionRealization.exactBase :=
  GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry

/-- Reduced generated metric hypotheses for exact-base equation-carried
same/opposite transitions.  Global separation remains explicit. -/
def generatedReducedMetricHypotheses
    (T : SameOppositeEquationTransitionData)
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
    equationTransitions_preserveSameBlockDistances T

@[simp]
theorem generatedReducedMetricHypotheses_separated
    (T : SameOppositeEquationTransitionData)
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
    (T : SameOppositeEquationTransitionData)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    (generatedReducedMetricHypotheses T hk orientation
        separated).base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem generatedReducedMetricHypotheses_transitionPreserves
    (T : SameOppositeEquationTransitionData)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    (generatedReducedMetricHypotheses T hk orientation
        separated).transition_preserves_same_block_distances =
      equationTransitions_preserveSameBlockDistances T :=
  rfl

/-- Same-block isometry on every generated block follows from the exact base
and explicit same-block preservation of the equation transitions. -/
theorem generatedSameBlockIsometry
    (T : SameOppositeEquationTransitionData)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation := by
  exact
    GeneratedSeparationInterface.same_block_isometry_of_reduced
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
      (generatedReducedMetricHypotheses T hk orientation separated)

/-- The explicit transition closed-placement certificate obtained from an
equation-carried generated closure. -/
def explicitTransitionClosedPlacementCertificate
    (T : SameOppositeEquationTransitionData)
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
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure_reduced
    T.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase orientation closure
    (generatedReducedMetricHypotheses T hk orientation separated)

/-- The closed placement obtained from an equation-carried generated closure. -/
def closedPlacement
    (T : SameOppositeEquationTransitionData)
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

/-- Existence form of the closed placement produced by equation-carried
generated closure and explicit generated separation. -/
theorem exists_closedPlacement
    (T : SameOppositeEquationTransitionData)
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
        GeneratedClosedChain.generatedPoint
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase orientation := by
  exact
    ClosedPlacementClosure.exists_closedPlacement_of_generatedClosure_reduced
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation closure
      (generatedReducedMetricHypotheses T hk orientation separated)

/-- Exact-block target from equation-carried generated closure and explicit
generated separation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (T : SameOppositeEquationTransitionData)
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

/-- Bundled one-chain version of equation-carried generated closure data. -/
structure EquationGeneratedClosureData (k : Nat) (hk : 0 < k) where
  transitions : SameOppositeEquationTransitionData
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  separated :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation

namespace EquationGeneratedClosureData

/-- Project bundled equation-carried closure data to reduced generated metric
hypotheses. -/
def toGeneratedReducedMetricHypotheses
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase G.orientation :=
  generatedReducedMetricHypotheses G.transitions hk G.orientation G.separated

@[simp]
theorem toGeneratedReducedMetricHypotheses_separated
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.separated = G.separated :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_baseSameBlock
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    G.toGeneratedReducedMetricHypotheses.base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_transitionPreserves
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    (G.toGeneratedReducedMetricHypotheses).transition_preserves_same_block_distances =
      equationTransitions_preserveSameBlockDistances G.transitions :=
  rfl

/-- Project bundled data to the explicit transition closed-placement
certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  explicitTransitionClosedPlacementCertificate G.transitions hk G.orientation
    G.closure G.separated

/-- Project bundled data to the closed placement. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  closedPlacement G.transitions hk G.orientation G.closure G.separated

/-- Bundled equation-carried generated closure data gives the closed-placement
existence theorem. -/
theorem exists_closedPlacement
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint
          G.transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase G.orientation := by
  exact
    EquationTransitionClosure.exists_closedPlacement G.transitions hk
      G.orientation G.closure G.separated

/-- Bundled equation-carried generated closure data gives the exact-block
target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {k : Nat} {hk : 0 < k}
    (G : EquationGeneratedClosureData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    EquationTransitionClosure.targetUpperConstructionFiveSixteenAt_exactBlock
      G.transitions hk G.orientation G.closure G.separated

end EquationGeneratedClosureData

/-- Family version with one equation-carried transition package and explicit
orientation, closure, and separation data for every positive block count. -/
structure EquationGeneratedClosureFamily where
  transitions : SameOppositeEquationTransitionData
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

namespace EquationGeneratedClosureFamily

/-- Forget the equation-carried construction to the generated-chain family
interface. -/
def toGeneratedChainFamily
    (F : EquationGeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

@[simp]
theorem toGeneratedChainFamily_O
    (F : EquationGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.O k hk =
      F.transitions.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem toGeneratedChainFamily_base
    (F : EquationGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toGeneratedChainFamily_orientation
    (F : EquationGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.orientation k hk = F.orientation k hk :=
  rfl

/-- Project family closure equations to the closed-placement closure
interface. -/
def toGeneratedChainFamilyClosures
    (F : EquationGeneratedClosureFamily) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures
      F.toGeneratedChainFamily :=
  fun k hk => F.closure k hk

/-- Project family separation and equation-transition metric data to reduced
generated metric hypotheses. -/
def toReducedMetricHypotheses
    (F : EquationGeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      F.toGeneratedChainFamily where
  metric := fun k hk =>
    generatedReducedMetricHypotheses F.transitions hk (F.orientation k hk)
      (F.separated k hk)

@[simp]
theorem toReducedMetricHypotheses_metric_separated
    (F : EquationGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).separated =
      F.separated k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_baseSameBlock
    (F : EquationGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ((F.toReducedMetricHypotheses).metric k hk).base_same_block_isometry =
      exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_transitionPreserves
    (F : EquationGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    (((F.toReducedMetricHypotheses).metric k hk).transition_preserves_same_block_distances) =
      equationTransitions_preserveSameBlockDistances F.transitions :=
  rfl

/-- Closed placements for every positive block count in the equation-carried
generated-closure family. -/
def closedPlacementFamily
    (F : EquationGeneratedClosureFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacementFamily_of_generatedClosure_reduced
    F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
    F.toReducedMetricHypotheses

/-- Family target theorem obtained by projecting to `ClosedPlacementClosure`. -/
theorem targetUpperConstructionFiveSixteen
    (F : EquationGeneratedClosureFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
      F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
      F.toReducedMetricHypotheses

/-- Combined closed-placement existence and exact-block target for the
equation-carried generated-closure family. -/
theorem exists_closedPlacement_and_target
    (F : EquationGeneratedClosureFamily) :
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

end EquationGeneratedClosureFamily

/-- Raw-function family wrapper keeping all orientation-dependent closure and
separation hypotheses explicit. -/
theorem targetUpperConstructionFiveSixteen_of_equationTransitions
    (T : SameOppositeEquationTransitionData)
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
    EquationGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      { transitions := T
        orientation := orientation
        closure := closure
        separated := separated }

end

end EquationTransitionClosure
end PachToth
end ErdosProblems1066
