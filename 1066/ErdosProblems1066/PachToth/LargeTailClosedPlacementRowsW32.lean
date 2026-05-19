import ErdosProblems1066.PachToth.LargeTailRowsRealizationW31
import ErdosProblems1066.PachToth.ClosedPlacementSeparationW19
import ErdosProblems1066.PachToth.ClosedPlacementSameBlockEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementCrossConnectorEdgesW19
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.NonRigidPeriodCandidateW10
import ErdosProblems1066.PachToth.PachTothFinalDataAssembly
import ErdosProblems1066.PachToth.GeneratedMetricClosure

set_option autoImplicit false

/-!
# W32 large-tail closed-placement row bridge

W31 records the remaining large-tail blocker as checked
`DeformedPlacement.ClosedPlacement` rows for every block count `k >= 6`.
This file sharpens that blocker by exposing the concrete row fields that are
enough to build those checked placements:

* a threshold-six point map;
* global separation for that point map;
* same-block unit-edge certificates;
* the four named successor connector unit equations from W19.

The generated role-hinge closure route is then repackaged into those rows.
The conditional theorem names the fields still missing on that route:
threshold-six orientations, generated closure equations, and generated global
separation.  No theorem below constructs a closed placement from an assumed
closed placement.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeTailClosedPlacementRowsW32

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev ClosedPlacement (k : Nat) (hk : 0 < k) : Type :=
  DeformedPlacement.ClosedPlacement k hk

abbrev LargeTailClosedPlacementRows : Type :=
  LargeTailRowsRealizationW31.LargeTailClosedPlacementRows

abbrev LargeTailCertificateRows : Type :=
  LargeTailRowsRealizationW31.LargeTailCertificateRows

abbrev LargeClosedPlacementFamilyFromSix : Type :=
  LargeTailRowsRealizationW31.LargeClosedPlacementFamilyFromSix

abbrev RemainingLargeTailExactSourceBlocker : Prop :=
  LargeTailRowsRealizationW31.RemainingLargeTailExactSourceBlocker

abbrev RemainingPositiveExactChainBlocker : Prop :=
  LargeTailRowsRealizationW31.RemainingPositiveExactChainBlocker

abbrev Separated {k : Nat} (point : Fin k -> LocalVertex -> R2) : Prop :=
  ClosedPlacementSeparationW19.Separated point

abbrev SameBlockUnitEdgeCertificate {k : Nat}
    (point : Fin k -> LocalVertex -> R2) : Prop :=
  ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdgeCertificate point

abbrev ExactCrossConnectorUnitCertificate
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2) : Prop :=
  ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate
    hk point

abbrev RoleHingeTransitions : Type :=
  GeneratedMetricClosure.RoleHingeTransitions

abbrev FlexibleGeneratedClosureFamily : Type :=
  FlexibleExactLocalTransition.GeneratedClosureFamily

abbrev W10Candidate : Type :=
  NonRigidPeriodCandidateW10.Candidate

abbrev W10FlexibleFamilyFields (T : W10Candidate) : Type :=
  NonRigidPeriodCandidateW10.FlexibleFamilyFields T

abbrev FlexiblePeriodLowerTableFamily : Type :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily

abbrev FlexiblePeriodValueMatrixFamily : Type :=
  PachTothFinalDataAssembly.FlexiblePeriodValueMatrixFamily

/-! ## Concrete threshold-six row fields -/

/-- The concrete row fields sufficient to build W31 closed-placement rows for
every tail block count.  Connector data is deliberately stored as the four W19
named equations, rather than as the already-quantified closed-placement field. -/
structure LargeTailConcreteRowFields where
  point :
    forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
      Fin k -> LocalVertex -> R2
  separated :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
      Separated (point k hkSix hk)
  same_block_edges_unit :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
      SameBlockUnitEdgeCertificate (point k hkSix hk)
  cross_connector_named_units :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
      ExactCrossConnectorUnitCertificate hk (point k hkSix hk)

namespace LargeTailConcreteRowFields

def closedPlacement
    (R : LargeTailConcreteRowFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    ClosedPlacement k hk :=
  ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate.toClosedPlacement
    (R.cross_connector_named_units k hkSix hk)
    (R.separated k hkSix hk)
    (R.same_block_edges_unit k hkSix hk).unit_edges

@[simp]
theorem closedPlacement_point
    (R : LargeTailConcreteRowFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (R.closedPlacement k hkSix hk).point i v =
      R.point k hkSix hk i v := by
  rfl

def closedPlacementRows
    (R : LargeTailConcreteRowFields) :
    LargeTailClosedPlacementRows where
  placement := R.closedPlacement

@[simp]
theorem closedPlacementRows_placement_point
    (R : LargeTailConcreteRowFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    ((R.closedPlacementRows).placement k hkSix hk).point i v =
      R.point k hkSix hk i v := by
  rfl

def certificateRows
    (R : LargeTailConcreteRowFields) :
    LargeTailCertificateRows :=
  LargeTailRowsRealizationW31.certificateRowsOfClosedPlacementRows
    R.closedPlacementRows

theorem remainingLargeTailExactSourceBlocker
    (R : LargeTailConcreteRowFields) :
    RemainingLargeTailExactSourceBlocker :=
  LargeTailRowsRealizationW31.remainingLargeTailExactSourceBlocker_of_closedPlacementRows
    R.closedPlacementRows

theorem remainingPositiveExactChainBlocker
    (R : LargeTailConcreteRowFields) :
    RemainingPositiveExactChainBlocker :=
  LargeTailRowsRealizationW31.remainingPositiveExactChainBlocker_of_closedPlacementRows
    R.closedPlacementRows

end LargeTailConcreteRowFields

def concreteRowFieldsOfPointSeparatedSameBlockNamedConnectors
    (point :
      forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
        Fin k -> LocalVertex -> R2)
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        Separated (point k hkSix hk))
    (same_block_edges_unit :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        SameBlockUnitEdgeCertificate (point k hkSix hk))
    (cross_connector_named_units :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        ExactCrossConnectorUnitCertificate hk (point k hkSix hk)) :
    LargeTailConcreteRowFields where
  point := point
  separated := separated
  same_block_edges_unit := same_block_edges_unit
  cross_connector_named_units := cross_connector_named_units

theorem nonempty_closedPlacementRows_of_point_separated_sameBlock_namedConnectors
    (point :
      forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
        Fin k -> LocalVertex -> R2)
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        Separated (point k hkSix hk))
    (same_block_edges_unit :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        SameBlockUnitEdgeCertificate (point k hkSix hk))
    (cross_connector_named_units :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        ExactCrossConnectorUnitCertificate hk (point k hkSix hk)) :
    Nonempty LargeTailClosedPlacementRows :=
  Nonempty.intro
    (concreteRowFieldsOfPointSeparatedSameBlockNamedConnectors
      point separated same_block_edges_unit cross_connector_named_units
      |>.closedPlacementRows)

theorem nonempty_certificateRows_of_point_separated_sameBlock_namedConnectors
    (point :
      forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
        Fin k -> LocalVertex -> R2)
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        Separated (point k hkSix hk))
    (same_block_edges_unit :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        SameBlockUnitEdgeCertificate (point k hkSix hk))
    (cross_connector_named_units :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        ExactCrossConnectorUnitCertificate hk (point k hkSix hk)) :
    Nonempty LargeTailCertificateRows :=
  Nonempty.intro
    ((concreteRowFieldsOfPointSeparatedSameBlockNamedConnectors
      point separated same_block_edges_unit cross_connector_named_units)
      |>.certificateRows)

theorem remainingLargeTailExactSourceBlocker_of_point_separated_sameBlock_namedConnectors
    (point :
      forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
        Fin k -> LocalVertex -> R2)
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        Separated (point k hkSix hk))
    (same_block_edges_unit :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        SameBlockUnitEdgeCertificate (point k hkSix hk))
    (cross_connector_named_units :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        ExactCrossConnectorUnitCertificate hk (point k hkSix hk)) :
    RemainingLargeTailExactSourceBlocker :=
  (concreteRowFieldsOfPointSeparatedSameBlockNamedConnectors
    point separated same_block_edges_unit cross_connector_named_units)
    |>.remainingLargeTailExactSourceBlocker

theorem remainingPositiveExactChainBlocker_of_point_separated_sameBlock_namedConnectors
    (point :
      forall (k : Nat), 6 <= k -> forall _hk : 0 < k,
        Fin k -> LocalVertex -> R2)
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        Separated (point k hkSix hk))
    (same_block_edges_unit :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        SameBlockUnitEdgeCertificate (point k hkSix hk))
    (cross_connector_named_units :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        ExactCrossConnectorUnitCertificate hk (point k hkSix hk)) :
    RemainingPositiveExactChainBlocker :=
  (concreteRowFieldsOfPointSeparatedSameBlockNamedConnectors
    point separated same_block_edges_unit cross_connector_named_units)
    |>.remainingPositiveExactChainBlocker

/-! ## Generated closure and separation route -/

/-- Threshold-six role-hinged generated data.  The same-block metric facts are
already supplied by `GeneratedMetricClosure`; after that reduction, the exact
missing row-level inputs are `orientation`, `closure`, and `separated`. -/
structure LargeTailGeneratedClosureSeparationFields where
  transitions : RoleHingeTransitions
  orientation :
    forall (k : Nat), 6 <= k -> 0 < k ->
      Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (orientation k hkSix hk)
  separated :
    forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (orientation k hkSix hk)

namespace LargeTailGeneratedClosureSeparationFields

def point
    (G : LargeTailGeneratedClosureSeparationFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    Fin k -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedPoint
    G.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (G.orientation k hkSix hk)

def reducedMetricHypotheses
    (G : LargeTailGeneratedClosureSeparationFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (G.orientation k hkSix hk) :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    G.transitions hk (G.orientation k hkSix hk)
    (G.separated k hkSix hk)

def generatedPeriod
    (G : LargeTailGeneratedClosureSeparationFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (G.orientation k hkSix hk) :=
  ClosedPlacementClosure.generatedPeriod_of_generatedClosure
    G.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (G.orientation k hkSix hk)
    (G.closure k hkSix hk)

def explicitCyclicPointEdgeData
    (G : LargeTailGeneratedClosureSeparationFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k) :
    NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk :=
  NonRigidClosedPlacementInterface.explicitCyclicPointEdgeData_of_generatedPeriod_reduced
    G.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase
    (G.orientation k hkSix hk)
    (G.generatedPeriod k hkSix hk)
    (G.reducedMetricHypotheses k hkSix hk)

@[simp]
theorem explicitCyclicPointEdgeData_point
    (G : LargeTailGeneratedClosureSeparationFields)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (G.explicitCyclicPointEdgeData k hkSix hk).point i v =
      G.point k hkSix hk i v := by
  rfl

def concreteRowFields
    (G : LargeTailGeneratedClosureSeparationFields) :
    LargeTailConcreteRowFields where
  point := G.point
  separated := fun k hkSix hk => G.separated k hkSix hk
  same_block_edges_unit := fun k hkSix hk =>
    { unit_edges :=
        (G.explicitCyclicPointEdgeData k hkSix hk).same_block_edges_unit }
  cross_connector_named_units := fun k hkSix hk =>
    ClosedPlacementCrossConnectorEdgesW19.ofExplicitCyclicPointEdgeData
      (G.explicitCyclicPointEdgeData k hkSix hk)

def closedPlacementRows
    (G : LargeTailGeneratedClosureSeparationFields) :
    LargeTailClosedPlacementRows :=
  G.concreteRowFields.closedPlacementRows

def certificateRows
    (G : LargeTailGeneratedClosureSeparationFields) :
    LargeTailCertificateRows :=
  G.concreteRowFields.certificateRows

theorem remainingLargeTailExactSourceBlocker
    (G : LargeTailGeneratedClosureSeparationFields) :
    RemainingLargeTailExactSourceBlocker :=
  G.concreteRowFields.remainingLargeTailExactSourceBlocker

theorem remainingPositiveExactChainBlocker
    (G : LargeTailGeneratedClosureSeparationFields) :
    RemainingPositiveExactChainBlocker :=
  G.concreteRowFields.remainingPositiveExactChainBlocker

end LargeTailGeneratedClosureSeparationFields

def generatedClosureSeparationFields
    (transitions : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), 6 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk))
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk)) :
    LargeTailGeneratedClosureSeparationFields where
  transitions := transitions
  orientation := orientation
  closure := closure
  separated := separated

/-! ## Period-search/cross-block source route -/

def generatedClosureSeparationFieldsOfPeriodSearchCrossBlockSource
    (F : ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily) :
    LargeTailGeneratedClosureSeparationFields where
  transitions := F.transitions
  orientation := fun k _hkSix hk => F.orientation k hk
  closure := fun k _hkSix hk => F.closure k hk
  separated := fun k _hkSix hk => F.separated k hk

def generatedClosureSeparationFieldsOfConcretePeriodSearchCrossBlockFamily
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    LargeTailGeneratedClosureSeparationFields :=
  generatedClosureSeparationFieldsOfPeriodSearchCrossBlockSource
    F.toCrossBlockLowerBounds.toExactFamilyClosure

theorem nonempty_generatedClosureSeparationFields_of_periodSearch_crossBlockSource
    (H : Nonempty ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily) :
    Nonempty LargeTailGeneratedClosureSeparationFields := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (generatedClosureSeparationFieldsOfPeriodSearchCrossBlockSource F)

theorem nonempty_generatedClosureSeparationFields_of_concretePeriodSearchCrossBlockFamily
    (H : Nonempty ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    Nonempty LargeTailGeneratedClosureSeparationFields := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (generatedClosureSeparationFieldsOfConcretePeriodSearchCrossBlockFamily F)

theorem nonempty_closedPlacementRows_of_periodSearch_crossBlockSource
    (H : Nonempty ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily) :
    Nonempty LargeTailClosedPlacementRows := by
  cases nonempty_generatedClosureSeparationFields_of_periodSearch_crossBlockSource H with
  | intro G =>
      exact Nonempty.intro G.closedPlacementRows

theorem nonempty_closedPlacementRows_of_concretePeriodSearchCrossBlockFamily
    (H : Nonempty ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    Nonempty LargeTailClosedPlacementRows := by
  cases
      nonempty_generatedClosureSeparationFields_of_concretePeriodSearchCrossBlockFamily
        H with
  | intro G =>
      exact Nonempty.intro G.closedPlacementRows

theorem remainingLargeTailExactSourceBlocker_of_periodSearch_crossBlockSource
    (H : Nonempty ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily) :
    RemainingLargeTailExactSourceBlocker := by
  cases nonempty_generatedClosureSeparationFields_of_periodSearch_crossBlockSource H with
  | intro G =>
      exact G.remainingLargeTailExactSourceBlocker

theorem remainingLargeTailExactSourceBlocker_of_concretePeriodSearchCrossBlockFamily
    (H : Nonempty ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    RemainingLargeTailExactSourceBlocker := by
  cases
      nonempty_generatedClosureSeparationFields_of_concretePeriodSearchCrossBlockFamily
        H with
  | intro G =>
      exact G.remainingLargeTailExactSourceBlocker

theorem nonempty_closedPlacementRows_of_roleHinged_generatedClosure_globalSeparation
    (transitions : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), 6 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk))
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk)) :
    Nonempty LargeTailClosedPlacementRows :=
  Nonempty.intro
    ((generatedClosureSeparationFields
      transitions orientation closure separated).closedPlacementRows)

theorem nonempty_certificateRows_of_roleHinged_generatedClosure_globalSeparation
    (transitions : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), 6 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk))
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk)) :
    Nonempty LargeTailCertificateRows :=
  Nonempty.intro
    ((generatedClosureSeparationFields
      transitions orientation closure separated).certificateRows)

theorem remainingLargeTailExactSourceBlocker_of_roleHinged_generatedClosure_globalSeparation
    (transitions : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), 6 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk))
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk)) :
    RemainingLargeTailExactSourceBlocker :=
  (generatedClosureSeparationFields
    transitions orientation closure separated)
    |>.remainingLargeTailExactSourceBlocker

theorem remainingPositiveExactChainBlocker_of_roleHinged_generatedClosure_globalSeparation
    (transitions : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), 6 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk))
    (separated :
      forall (k : Nat) (hkSix : 6 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hkSix hk)) :
    RemainingPositiveExactChainBlocker :=
  (generatedClosureSeparationFields
    transitions orientation closure separated)
    |>.remainingPositiveExactChainBlocker

/-! ## Flexible exact-local generated-closure route -/

/-- The generated point map carried by a flexible exact-local
generated-closure family. -/
def pointOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedPoint
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)

/-- The full generated metric hypotheses from the flexible exact-local
same-block fields and the stored global separation. -/
def generatedMetricHypothesesOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  F.transitions.generatedMetricHypotheses
    hk (F.orientation k hk) (F.separated k hk)

/-- The generated period equation obtained from the stored closure equation. -/
def generatedPeriodOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  ClosedPlacementClosure.generatedPeriod_of_generatedClosure
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)
    (F.closure k hk)

/-- Direct non-rigid point/edge data from flexible generated closure data.
This is the source-level row object used below; it is not extracted from a
pre-existing closed placement. -/
def explicitCyclicPointEdgeDataOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk :=
  NonRigidClosedPlacementInterface.explicitCyclicPointEdgeData_of_generatedPeriod
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)
    (generatedPeriodOfFlexibleGeneratedClosureFamily F k hk)
    (generatedMetricHypothesesOfFlexibleGeneratedClosureFamily F k hk)

@[simp]
theorem explicitCyclicPointEdgeDataOfFlexibleGeneratedClosureFamily_point
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (explicitCyclicPointEdgeDataOfFlexibleGeneratedClosureFamily F k hk).point
        i v =
      pointOfFlexibleGeneratedClosureFamily F k hk i v := by
  rfl

/-- The flexible generated-closure family gives row-level global separation
for its generated point map. -/
def separatedOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    Separated (pointOfFlexibleGeneratedClosureFamily F k hk) :=
  F.separated k hk

/-- The flexible exact-local same-block data gives the same-block unit row
certificate for the generated point map. -/
def sameBlockUnitEdgeCertificateOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    SameBlockUnitEdgeCertificate
      (pointOfFlexibleGeneratedClosureFamily F k hk) where
  unit_edges :=
    (explicitCyclicPointEdgeDataOfFlexibleGeneratedClosureFamily F k hk)
      |>.same_block_edges_unit

/-- The exact four W19 successor-connector unit equations for the flexible
generated point map. -/
def crossConnectorNamedUnitsOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ExactCrossConnectorUnitCertificate hk
      (pointOfFlexibleGeneratedClosureFamily F k hk) :=
  ClosedPlacementCrossConnectorEdgesW19.ofExplicitCyclicPointEdgeData
    (explicitCyclicPointEdgeDataOfFlexibleGeneratedClosureFamily F k hk)

/-- A checked closed placement built from the explicit separation row, the
same-block unit row, and the four named cross-connector unit equations. -/
def closedPlacementOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacement k hk :=
  ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate.toClosedPlacement
    (crossConnectorNamedUnitsOfFlexibleGeneratedClosureFamily F k hk)
    (separatedOfFlexibleGeneratedClosureFamily F k hk)
    (sameBlockUnitEdgeCertificateOfFlexibleGeneratedClosureFamily F k hk).unit_edges

@[simp]
theorem closedPlacementOfFlexibleGeneratedClosureFamily_point
    (F : FlexibleGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfFlexibleGeneratedClosureFamily F k hk).point i v =
      pointOfFlexibleGeneratedClosureFamily F k hk i v := by
  rfl

/-- A flexible exact-local generated-closure family supplies checked
closed placements for every positive block count by first checking the
separation row, same-block unit row, and four W19 named connector equations. -/
def largeClosedPlacementFamilyFromSixOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    LargeClosedPlacementFamilyFromSix :=
  fun k _hkSix hk => closedPlacementOfFlexibleGeneratedClosureFamily F k hk

/-- The same flexible family materializes the concrete W32 row fields. -/
def concreteRowFieldsOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    LargeTailConcreteRowFields where
  point := fun k _hkSix hk =>
    pointOfFlexibleGeneratedClosureFamily F k hk
  separated := fun k _hkSix hk =>
    separatedOfFlexibleGeneratedClosureFamily F k hk
  same_block_edges_unit := fun k _hkSix hk =>
    sameBlockUnitEdgeCertificateOfFlexibleGeneratedClosureFamily F k hk
  cross_connector_named_units := fun k _hkSix hk =>
    crossConnectorNamedUnitsOfFlexibleGeneratedClosureFamily F k hk

def closedPlacementRowsOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    LargeTailClosedPlacementRows :=
  (concreteRowFieldsOfFlexibleGeneratedClosureFamily F).closedPlacementRows

theorem nonempty_largeClosedPlacementFamilyFromSix_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    Nonempty LargeClosedPlacementFamilyFromSix :=
  Nonempty.intro
    (largeClosedPlacementFamilyFromSixOfFlexibleGeneratedClosureFamily F)

theorem nonempty_concreteRowFields_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    Nonempty LargeTailConcreteRowFields :=
  Nonempty.intro (concreteRowFieldsOfFlexibleGeneratedClosureFamily F)

theorem nonempty_closedPlacementRows_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    Nonempty LargeTailClosedPlacementRows :=
  Nonempty.intro (closedPlacementRowsOfFlexibleGeneratedClosureFamily F)

theorem remainingLargeTailExactSourceBlocker_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    RemainingLargeTailExactSourceBlocker :=
  (concreteRowFieldsOfFlexibleGeneratedClosureFamily F)
    |>.remainingLargeTailExactSourceBlocker

theorem remainingPositiveExactChainBlocker_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    RemainingPositiveExactChainBlocker :=
  (concreteRowFieldsOfFlexibleGeneratedClosureFamily F)
    |>.remainingPositiveExactChainBlocker

def concreteRowFieldsOfW10FlexibleFamilyFields
    {T : W10Candidate} (F : W10FlexibleFamilyFields T) :
    LargeTailConcreteRowFields :=
  concreteRowFieldsOfFlexibleGeneratedClosureFamily
    F.toFlexibleGeneratedClosureFamily

theorem nonempty_closedPlacementRows_of_w10FlexibleFamilyFields
    {T : W10Candidate} (F : W10FlexibleFamilyFields T) :
    Nonempty LargeTailClosedPlacementRows :=
  nonempty_closedPlacementRows_of_flexibleGeneratedClosureFamily
    F.toFlexibleGeneratedClosureFamily

theorem remainingLargeTailExactSourceBlocker_of_w10FlexibleFamilyFields
    {T : W10Candidate} (F : W10FlexibleFamilyFields T) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_flexibleGeneratedClosureFamily
    F.toFlexibleGeneratedClosureFamily

/-! ### Flexible lower-table source route -/

def pointOfFlexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> LocalVertex -> R2 :=
  pointOfFlexibleGeneratedClosureFamily F.toGeneratedClosureFamily k hk

def separatedOfFlexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    Separated (pointOfFlexiblePeriodLowerTableFamily F k hk) :=
  separatedOfFlexibleGeneratedClosureFamily F.toGeneratedClosureFamily k hk

def sameBlockUnitEdgeCertificateOfFlexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    SameBlockUnitEdgeCertificate
      (pointOfFlexiblePeriodLowerTableFamily F k hk) :=
  sameBlockUnitEdgeCertificateOfFlexibleGeneratedClosureFamily
    F.toGeneratedClosureFamily k hk

def crossConnectorNamedUnitsOfFlexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    ExactCrossConnectorUnitCertificate hk
      (pointOfFlexiblePeriodLowerTableFamily F k hk) :=
  crossConnectorNamedUnitsOfFlexibleGeneratedClosureFamily
    F.toGeneratedClosureFamily k hk

def concreteRowFieldsOfFlexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily) :
    LargeTailConcreteRowFields where
  point := fun k _hkSix hk =>
    pointOfFlexiblePeriodLowerTableFamily F k hk
  separated := fun k _hkSix hk =>
    separatedOfFlexiblePeriodLowerTableFamily F k hk
  same_block_edges_unit := fun k _hkSix hk =>
    sameBlockUnitEdgeCertificateOfFlexiblePeriodLowerTableFamily F k hk
  cross_connector_named_units := fun k _hkSix hk =>
    crossConnectorNamedUnitsOfFlexiblePeriodLowerTableFamily F k hk

def closedPlacementRowsOfFlexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily) :
    LargeTailClosedPlacementRows :=
  (concreteRowFieldsOfFlexiblePeriodLowerTableFamily F).closedPlacementRows

@[simp]
theorem closedPlacementRowsOfFlexiblePeriodLowerTableFamily_placement_point
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hkSix : 6 <= k) (hk : 0 < k)
    (i : Fin k) (v : LocalVertex) :
    ((closedPlacementRowsOfFlexiblePeriodLowerTableFamily F).placement
      k hkSix hk).point i v =
      pointOfFlexiblePeriodLowerTableFamily F k hk i v := by
  rfl

theorem nonempty_closedPlacementRows_of_flexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily) :
    Nonempty LargeTailClosedPlacementRows :=
  Nonempty.intro (closedPlacementRowsOfFlexiblePeriodLowerTableFamily F)

theorem remainingLargeTailExactSourceBlocker_of_flexiblePeriodLowerTableFamily
    (F : FlexiblePeriodLowerTableFamily) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_flexibleGeneratedClosureFamily
    F.toGeneratedClosureFamily

def concreteRowFieldsOfFlexiblePeriodValueMatrixFamily
    (F : FlexiblePeriodValueMatrixFamily) :
    LargeTailConcreteRowFields :=
  concreteRowFieldsOfFlexiblePeriodLowerTableFamily
    F.toLowerTableFamily

theorem nonempty_closedPlacementRows_of_flexiblePeriodValueMatrixFamily
    (F : FlexiblePeriodValueMatrixFamily) :
    Nonempty LargeTailClosedPlacementRows :=
  nonempty_closedPlacementRows_of_flexiblePeriodLowerTableFamily
    F.toLowerTableFamily

theorem remainingLargeTailExactSourceBlocker_of_flexiblePeriodValueMatrixFamily
    (F : FlexiblePeriodValueMatrixFamily) :
    RemainingLargeTailExactSourceBlocker :=
  remainingLargeTailExactSourceBlocker_of_flexiblePeriodLowerTableFamily
    F.toLowerTableFamily

end

end LargeTailClosedPlacementRowsW32
end PachToth

namespace Verified

abbrev PachTothW32LargeTailConcreteRowFields : Type :=
  PachToth.LargeTailClosedPlacementRowsW32.LargeTailConcreteRowFields

abbrev PachTothW32LargeTailGeneratedClosureSeparationFields : Type :=
  PachToth.LargeTailClosedPlacementRowsW32.LargeTailGeneratedClosureSeparationFields

abbrev PachTothW32LargeTailClosedPlacementRows : Type :=
  PachToth.LargeTailClosedPlacementRowsW32.LargeTailClosedPlacementRows

abbrev PachTothW32FlexibleGeneratedClosureFamily : Type :=
  PachToth.LargeTailClosedPlacementRowsW32.FlexibleGeneratedClosureFamily

abbrev PachTothW32FlexiblePeriodLowerTableFamily : Type :=
  PachToth.LargeTailClosedPlacementRowsW32.FlexiblePeriodLowerTableFamily

theorem pachtoth_w32_closedPlacementRows_of_concreteRowFields
    (R : PachTothW32LargeTailConcreteRowFields) :
    Nonempty PachTothW32LargeTailClosedPlacementRows :=
  Nonempty.intro R.closedPlacementRows

theorem pachtoth_w32_closedPlacementRows_of_generatedClosureSeparationFields
    (G : PachTothW32LargeTailGeneratedClosureSeparationFields) :
    Nonempty PachTothW32LargeTailClosedPlacementRows :=
  Nonempty.intro G.closedPlacementRows

theorem pachtoth_w32_closedPlacementRows_of_flexibleGeneratedClosureFamily
    (F : PachTothW32FlexibleGeneratedClosureFamily) :
    Nonempty PachTothW32LargeTailClosedPlacementRows :=
  PachToth.LargeTailClosedPlacementRowsW32.nonempty_closedPlacementRows_of_flexibleGeneratedClosureFamily
    F

theorem pachtoth_w32_closedPlacementRows_of_flexiblePeriodLowerTableFamily
    (F : PachTothW32FlexiblePeriodLowerTableFamily) :
    Nonempty PachTothW32LargeTailClosedPlacementRows :=
  PachToth.LargeTailClosedPlacementRowsW32.nonempty_closedPlacementRows_of_flexiblePeriodLowerTableFamily
    F

end Verified
end ErdosProblems1066
