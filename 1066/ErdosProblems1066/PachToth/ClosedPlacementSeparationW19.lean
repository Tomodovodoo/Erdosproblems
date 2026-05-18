import ErdosProblems1066.PachToth.ClosedPlacementNonRigidComponents
import ErdosProblems1066.PachToth.GeneratedSeparationInterface
import ErdosProblems1066.PachToth.LargeKGlobalSeparationW16
import ErdosProblems1066.PachToth.NonConnectorSeparationW12

set_option autoImplicit false

/-!
# W19 closed-placement separation adapters

This module isolates the separated field for non-rigid closed placements and
connects it to the generated-chain separation interfaces and existing
non-connector lower-table routes.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementSeparationW19

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The separated field of a non-rigid block placement, stated directly for
its point map. -/
def Separated {k : Nat} (point : Fin k -> LocalVertex -> R2) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)

/-- A sharp one-block-count certificate for the separated field only. -/
structure SeparationCertificate (k : Nat) (_hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  separated : Separated point

namespace SeparationCertificate

/-- Forget all non-rigid component fields except pointwise separation. -/
def ofComponents {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk) :
    SeparationCertificate k hk where
  point := C.point
  separated := C.separated

@[simp]
theorem ofComponents_point {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk) :
    (ofComponents C).point = C.point :=
  rfl

@[simp]
theorem ofComponents_separated {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk) :
    (ofComponents C).separated = C.separated :=
  rfl

/-- Add the two unit-edge fields to a separation certificate to recover the
full non-rigid component package. -/
def toComponents {k : Nat} {hk : 0 < k}
    (S : SeparationCertificate k hk)
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (S.point i u) (S.point i v) = 1)
    (successor_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (S.point i u)
            (S.point (Arithmetic.cyclicSucc hk i) v) = 1) :
    ClosedPlacementNonRigidComponents.Components k hk where
  point := S.point
  separated := S.separated
  same_block_edges_unit := same_block_edges_unit
  successor_connector_edges_unit := successor_connector_edges_unit

@[simp]
theorem toComponents_point {k : Nat} {hk : 0 < k}
    (S : SeparationCertificate k hk)
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (S.point i u) (S.point i v) = 1)
    (successor_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (S.point i u)
            (S.point (Arithmetic.cyclicSucc hk i) v) = 1) :
    (S.toComponents same_block_edges_unit
      successor_connector_edges_unit).point = S.point :=
  rfl

@[simp]
theorem toComponents_separated {k : Nat} {hk : 0 < k}
    (S : SeparationCertificate k hk)
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (S.point i u) (S.point i v) = 1)
    (successor_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (S.point i u)
            (S.point (Arithmetic.cyclicSucc hk i) v) = 1) :
    (S.toComponents same_block_edges_unit
      successor_connector_edges_unit).separated = S.separated :=
  rfl

/-- Transport a separation certificate across definitional or proved equality
of point maps. -/
def congrPoint {k : Nat} {hk : 0 < k}
    (S : SeparationCertificate k hk)
    (point' : Fin k -> LocalVertex -> R2)
    (hpoint : point' = S.point) :
    SeparationCertificate k hk where
  point := point'
  separated := by
    intro i u j v hne
    simpa [hpoint] using S.separated i u j v hne

end SeparationCertificate

/-- Point-map equality transports the separated proposition itself. -/
theorem separated_of_point_eq {k : Nat}
    {point point' : Fin k -> LocalVertex -> R2}
    (hpoint : point = point')
    (hsep : Separated point') :
    Separated point := by
  intro i u j v hne
  simpa [hpoint] using hsep i u j v hne

/-- Generated global separation is exactly the separated field for the
generated point map. -/
def ofGeneratedGlobalSeparation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation) :
    SeparationCertificate k hk where
  point := GeneratedClosedChain.generatedPoint O hk base orientation
  separated := separated

@[simp]
theorem ofGeneratedGlobalSeparation_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation) :
    (ofGeneratedGlobalSeparation O hk base orientation separated).point =
      GeneratedClosedChain.generatedPoint O hk base orientation :=
  rfl

@[simp]
theorem ofGeneratedGlobalSeparation_separated
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation) :
    (ofGeneratedGlobalSeparation O hk base orientation separated).separated =
      separated :=
  rfl

/-- Full generated metric hypotheses expose the separated field. -/
def ofGeneratedMetricHypotheses
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    SeparationCertificate k hk :=
  ofGeneratedGlobalSeparation O hk base orientation H.separated

/-- Reduced generated metric hypotheses expose the separated field. -/
def ofGeneratedReducedMetricHypotheses
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    SeparationCertificate k hk :=
  ofGeneratedGlobalSeparation O hk base orientation H.separated

/-- A generated non-connector square-distance table supplies the separated
field for its generated point map. -/
def ofGeneratedNonConnectorSqDistanceTable
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTable
      F k hk) :
    SeparationCertificate k hk :=
  ofGeneratedGlobalSeparation
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)
    T.generatedGlobalSeparation

/-- An existing indexed non-connector square-distance table supplies the
separated field after the W12 finite-index conversion. -/
def ofIndexedNonConnectorCrossBlockSqDistanceTable
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T :
      NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTable
        F k hk) :
    SeparationCertificate k hk :=
  ofGeneratedGlobalSeparation
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)
    T.generatedGlobalSeparation

/-- A family-level separated-field certificate. -/
structure SeparationFamilyCertificate where
  point : forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2
  separated :
    forall (k : Nat) (hk : 0 < k), Separated (point k hk)

namespace SeparationFamilyCertificate

/-- Extract the one-block-count certificate from a family certificate. -/
def certificate (S : SeparationFamilyCertificate)
    (k : Nat) (hk : 0 < k) :
    SeparationCertificate k hk where
  point := S.point k hk
  separated := S.separated k hk

/-- Add unit-edge fields to a family separation certificate to get the full
non-rigid component family. -/
def components
    (S : SeparationFamilyCertificate)
    (same_block_edges_unit :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (S.point k hk i u) (S.point k hk i v) = 1)
    (successor_connector_edges_unit :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (S.point k hk i u)
            (S.point k hk (Arithmetic.cyclicSucc hk i) v) = 1)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementNonRigidComponents.Components k hk where
  point := S.point k hk
  separated := S.separated k hk
  same_block_edges_unit := same_block_edges_unit k hk
  successor_connector_edges_unit := successor_connector_edges_unit k hk

/-- Full generated-family metric hypotheses supply family separation. -/
def ofGeneratedFamily
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (H : F.MetricHypotheses) :
    SeparationFamilyCertificate where
  point := fun k hk =>
    GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
      (F.orientation k hk)
  separated := fun k hk => (H.metric k hk).separated

/-- Reduced generated-family metric hypotheses supply family separation. -/
def ofGeneratedFamilyReduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (H : F.ReducedMetricHypotheses) :
    SeparationFamilyCertificate where
  point := fun k hk =>
    GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
      (F.orientation k hk)
  separated := fun k hk => (H.metric k hk).separated

/-- Generated non-connector table families supply family separation. -/
def ofGeneratedNonConnectorSqDistanceTableFamily
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T :
      NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily
        F) :
    SeparationFamilyCertificate where
  point := fun k hk =>
    GeneratedClosedChain.generatedPoint
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
  separated := fun k hk => T.separated k hk

/-- Existing indexed non-connector table families supply family separation. -/
def ofIndexedNonConnectorCrossBlockSqDistanceTableFamily
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T :
      NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily
        F) :
    SeparationFamilyCertificate where
  point := fun k hk =>
    GeneratedClosedChain.generatedPoint
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
  separated := fun k hk => T.separated k hk

/-- Existing cross-block lower-bound facades supply family separation. -/
def ofCrossBlockLowerBounds
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (H : NonConnectorSeparationW12.CrossBlockLowerBounds F) :
    SeparationFamilyCertificate where
  point := fun k hk =>
    GeneratedClosedChain.generatedPoint
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
  separated := fun k hk => H.separated k hk

end SeparationFamilyCertificate

/-- A thresholded separated-field certificate for large block counts. -/
structure EventualSeparationFamilyCertificate (K0 : Nat) where
  point :
    forall (k : Nat), K0 <= k -> 0 < k ->
      Fin k -> LocalVertex -> R2
  separated :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      Separated (point k hK hk)

namespace EventualSeparationFamilyCertificate

/-- Extract the one-block-count certificate in the threshold range. -/
def certificate {K0 : Nat}
    (S : EventualSeparationFamilyCertificate K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    SeparationCertificate k hk where
  point := S.point k hK hk
  separated := S.separated k hK hk

/-- Large-k cross-block distance fields expose thresholded family
separation. -/
def ofLargeKCrossBlockDistanceFields {K0 : Nat}
    (F : LargeKGlobalSeparationW16.LargeKCrossBlockDistanceFields K0) :
    EventualSeparationFamilyCertificate K0 where
  point := fun k hK hk =>
    GeneratedClosedChain.generatedPoint
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hK hk)
  separated := fun k hK hk => F.separated k hK hk

/-- Large-k non-connector square-distance fields expose thresholded family
separation. -/
def ofLargeKNonConnectorSqDistanceFields {K0 : Nat}
    (F : LargeKGlobalSeparationW16.LargeKNonConnectorSqDistanceFields K0) :
    EventualSeparationFamilyCertificate K0 where
  point := fun k hK hk =>
    GeneratedClosedChain.generatedPoint
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hK hk)
  separated := fun k hK hk => F.separated k hK hk

end EventualSeparationFamilyCertificate

end

end ClosedPlacementSeparationW19
end PachToth
end ErdosProblems1066
