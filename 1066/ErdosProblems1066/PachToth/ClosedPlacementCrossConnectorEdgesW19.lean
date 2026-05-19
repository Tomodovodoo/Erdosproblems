import ErdosProblems1066.PachToth.CrossBlock
import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.ExactLocalGeometry
import ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface
import ErdosProblems1066.PachToth.GeneratedPeriodClosure
import ErdosProblems1066.PachToth.OrbitSqDistancesW12
import ErdosProblems1066.PachToth.PeriodCandidateCompatibilityW18

set_option autoImplicit false

/-!
# W19 cross-connector unit edges for non-rigid closed placements

This file isolates the four finite cross-block connector equations used by
the non-rigid closed-placement route.  The data below is deliberately minimal:
it stores exactly the four successor-block unit distances and converts them
to the quantified `cross_connector_edges_unit` field used by
`DeformedPlacement.ClosedPlacement` and
`NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementCrossConnectorEdgesW19

open Arithmetic
open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real

/-- Local facade for the exact one-block coordinate model used by the
surrounding generated/orbit routes. -/
abbrev exactLocalPoint : LocalVertex -> R2 :=
  ExactLocalGeometry.localPoint

/-- Local facade for the concrete orbit transition package from W12. -/
abbrev concreteOrbitTransitionObligations :
    Figure2Certificate.SameOppositeTransitionObligations :=
  OrbitSqDistancesW12.ConcreteTransitionObligations

/-- Local facade for the W18 period-candidate family type. -/
abbrev periodCandidateFamily :=
  PeriodCandidateCompatibilityW18.PeriodCandidateFamily

/-- The finite next-block connector relation is exactly the four directed
edges named in `CrossBlock.nextConnectorEdges`. -/
theorem nextConnector_iff_four (u v : LocalVertex) :
    CrossBlock.NextConnector u v <->
      (u = T2_2 /\ v = T1_1) \/
      (u = T2_2 /\ v = T1_2) \/
      (u = T4_0 /\ v = T0_0) \/
      (u = T4_0 /\ v = T0_2) := by
  revert u v
  decide

theorem nextConnector_cases {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v) :
      (u = T2_2 /\ v = T1_1) \/
      (u = T2_2 /\ v = T1_2) \/
      (u = T4_0 /\ v = T0_0) \/
      (u = T4_0 /\ v = T0_2) :=
  (nextConnector_iff_four u v).1 hconn

theorem nextConnector_T2_2_T1_1 :
    CrossBlock.NextConnector T2_2 T1_1 := by
  decide

theorem nextConnector_T2_2_T1_2 :
    CrossBlock.NextConnector T2_2 T1_2 := by
  decide

theorem nextConnector_T4_0_T0_0 :
    CrossBlock.NextConnector T4_0 T0_0 := by
  decide

theorem nextConnector_T4_0_T0_2 :
    CrossBlock.NextConnector T4_0 T0_2 := by
  decide

/-- Minimal exact certificate for the four successor cross-block unit
distances.  The `point` map is the blockwise non-rigid placement map. -/
structure ExactCrossConnectorUnitCertificate
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2) where
  t2_2_t1_1 :
    forall i : Fin k,
      _root_.eucDist (point i T2_2)
        (point (cyclicSucc hk i) T1_1) = 1
  t2_2_t1_2 :
    forall i : Fin k,
      _root_.eucDist (point i T2_2)
        (point (cyclicSucc hk i) T1_2) = 1
  t4_0_t0_0 :
    forall i : Fin k,
      _root_.eucDist (point i T4_0)
        (point (cyclicSucc hk i) T0_0) = 1
  t4_0_t0_2 :
    forall i : Fin k,
      _root_.eucDist (point i T4_0)
        (point (cyclicSucc hk i) T0_2) = 1

namespace ExactCrossConnectorUnitCertificate

/-- Convert the four named unit equations into the quantified
`cross_connector_edges_unit` field. -/
def crossConnectorEdgesUnit
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (C : ExactCrossConnectorUnitCertificate hk point) :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u)
          (point (cyclicSucc hk i) v) = 1 := by
  intro i u v hconn
  cases nextConnector_cases hconn with
  | inl h211 =>
      cases h211 with
      | intro hu hv =>
          simpa [hu, hv] using C.t2_2_t1_1 i
  | inr hrest =>
      cases hrest with
      | inl h212 =>
          cases h212 with
          | intro hu hv =>
              simpa [hu, hv] using C.t2_2_t1_2 i
      | inr hrest2 =>
          cases hrest2 with
          | inl h400 =>
              cases h400 with
              | intro hu hv =>
                  simpa [hu, hv] using C.t4_0_t0_0 i
          | inr h402 =>
              cases h402 with
              | intro hu hv =>
                  simpa [hu, hv] using C.t4_0_t0_2 i

/-- Package the four-edge certificate with the remaining non-rigid metric
fields as the existing explicit point/edge data interface. -/
def toExplicitCyclicPointEdgeData
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (C : ExactCrossConnectorUnitCertificate hk point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1) :
    NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk where
  point := point
  separated := separated
  same_block_edges_unit := same_block_edges_unit
  cross_connector_edges_unit := C.crossConnectorEdgesUnit

/-- Package the four-edge certificate directly as a checked deformed closed
placement once the separation and same-block unit fields are supplied. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (C : ExactCrossConnectorUnitCertificate hk point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1) :
    DeformedPlacement.ClosedPlacement k hk :=
  (C.toExplicitCyclicPointEdgeData separated
    same_block_edges_unit).toClosedPlacement

@[simp]
theorem toClosedPlacement_point
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (C : ExactCrossConnectorUnitCertificate hk point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (i : Fin k) (v : LocalVertex) :
    (C.toClosedPlacement separated same_block_edges_unit).point i v =
      point i v :=
  rfl

end ExactCrossConnectorUnitCertificate

/-- Extract the four named connector equations from an already checked
deformed closed placement. -/
def ofClosedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    ExactCrossConnectorUnitCertificate hk P.point where
  t2_2_t1_1 := fun i =>
    P.cross_connector_edges_unit i T2_2 T1_1
      nextConnector_T2_2_T1_1
  t2_2_t1_2 := fun i =>
    P.cross_connector_edges_unit i T2_2 T1_2
      nextConnector_T2_2_T1_2
  t4_0_t0_0 := fun i =>
    P.cross_connector_edges_unit i T4_0 T0_0
      nextConnector_T4_0_T0_0
  t4_0_t0_2 := fun i =>
    P.cross_connector_edges_unit i T4_0 T0_2
      nextConnector_T4_0_T0_2

/-- Extract the four named connector equations from the non-rigid explicit
point/edge interface. -/
def ofExplicitCyclicPointEdgeData
    {k : Nat} {hk : 0 < k}
    (D :
      NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk) :
    ExactCrossConnectorUnitCertificate hk D.point where
  t2_2_t1_1 := fun i =>
    D.cross_connector_edges_unit i T2_2 T1_1
      nextConnector_T2_2_T1_1
  t2_2_t1_2 := fun i =>
    D.cross_connector_edges_unit i T2_2 T1_2
      nextConnector_T2_2_T1_2
  t4_0_t0_0 := fun i =>
    D.cross_connector_edges_unit i T4_0 T0_0
      nextConnector_T4_0_T0_0
  t4_0_t0_2 := fun i =>
    D.cross_connector_edges_unit i T4_0 T0_2
      nextConnector_T4_0_T0_2

/-- Extract the four named connector equations from explicit successor-orbit
data, after forgetting the transition structure to point/edge data. -/
def ofExplicitCyclicOrbitEdgeData
    {k : Nat} {hk : 0 < k}
    (D :
      NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk) :
    ExactCrossConnectorUnitCertificate hk D.point :=
  ofExplicitCyclicPointEdgeData D.toExplicitCyclicPointEdgeData

/-- The four connector unit equations carried by a generated period and full
generated metric data. -/
def ofGeneratedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ExactCrossConnectorUnitCertificate hk
      (GeneratedClosedChain.generatedPoint O hk base orientation) :=
  ofExplicitCyclicPointEdgeData
    (NonRigidClosedPlacementInterface.explicitCyclicPointEdgeData_of_generatedPeriod
      O hk base orientation period H)

/-- The four connector unit equations carried by a generated period and
reduced generated metric data. -/
def ofGeneratedPeriodReduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ExactCrossConnectorUnitCertificate hk
      (GeneratedClosedChain.generatedPoint O hk base orientation) :=
  ofExplicitCyclicPointEdgeData
    (NonRigidClosedPlacementInterface.explicitCyclicPointEdgeData_of_generatedPeriod_reduced
      O hk base orientation period H)

/-- The four connector unit equations carried by a generated period equation
from the period interface. -/
def ofGeneratedPeriodEquation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ExactCrossConnectorUnitCertificate hk
      (GeneratedClosedChain.generatedPoint O hk base orientation) :=
  ofGeneratedPeriod O hk base orientation
    (GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
      O hk base orientation period)
    H

/-- The four connector unit equations carried by a generated period equation
and reduced generated metric data. -/
def ofGeneratedPeriodEquationReduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ExactCrossConnectorUnitCertificate hk
      (GeneratedClosedChain.generatedPoint O hk base orientation) :=
  ofGeneratedPeriodReduced O hk base orientation
    (GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
      O hk base orientation period)
    H

/-- The orbit-square-distance period route also supplies the four connector
unit equations after converting its metric facade to full generated metric
hypotheses. -/
def ofGeneratedPeriodEquationOrbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (H :
      GeneratedPeriodClosure.GeneratedOrbitSqDistanceMetricHypotheses
        O hk base orientation) :
    ExactCrossConnectorUnitCertificate hk
      (GeneratedClosedChain.generatedPoint O hk base orientation) :=
  ofGeneratedPeriodEquation O hk base orientation period H.toMetricHypotheses

/-- The concrete W12 orbit package, with a period equation, global separation,
and orbit-level exact-local squared distances, gives the four connector unit
equations for the generated non-rigid chain. -/
def ofConcreteOrbitPeriodEquation
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      PeriodInterface.GeneratedPeriodEquation
        concreteOrbitTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        concreteOrbitTransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (orbit_sq_distances :
      GeneratedPeriodClosure.GeneratedOrbitMatchesExactLocalSqDistances
        concreteOrbitTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    ExactCrossConnectorUnitCertificate hk
      (GeneratedClosedChain.generatedPoint
        concreteOrbitTransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :=
  ofGeneratedPeriodEquationOrbitSqDistances
    concreteOrbitTransitionObligations hk
    BaseTransitionRealization.exactBase orientation period
    { separated := separated
      orbit_sq_distances := orbit_sq_distances }

/-! ## Named unit edges from transition and closure certificates -/

/-- A transition certificate supplies the named `T2_2 -> T1_1` connector
unit edge on its stored target block. -/
theorem transitionCertificate_t2_2_t1_1
    {source target : LocalVertex -> R2}
    (C : OrientationData.TransitionCertificate source target) :
    _root_.eucDist (source T2_2) (target T1_1) = 1 :=
  C.connector_unit_target nextConnector_T2_2_T1_1

/-- A transition certificate supplies the named `T2_2 -> T1_2` connector
unit edge on its stored target block. -/
theorem transitionCertificate_t2_2_t1_2
    {source target : LocalVertex -> R2}
    (C : OrientationData.TransitionCertificate source target) :
    _root_.eucDist (source T2_2) (target T1_2) = 1 :=
  C.connector_unit_target nextConnector_T2_2_T1_2

/-- A transition certificate supplies the named `T4_0 -> T0_0` connector
unit edge on its stored target block. -/
theorem transitionCertificate_t4_0_t0_0
    {source target : LocalVertex -> R2}
    (C : OrientationData.TransitionCertificate source target) :
    _root_.eucDist (source T4_0) (target T0_0) = 1 :=
  C.connector_unit_target nextConnector_T4_0_T0_0

/-- A transition certificate supplies the named `T4_0 -> T0_2` connector
unit edge on its stored target block. -/
theorem transitionCertificate_t4_0_t0_2
    {source target : LocalVertex -> R2}
    (C : OrientationData.TransitionCertificate source target) :
    _root_.eucDist (source T4_0) (target T0_2) = 1 :=
  C.connector_unit_target nextConnector_T4_0_T0_2

/-- Same/opposite transition obligations supply the named `T2_2 -> T1_1`
connector unit edge for any selected orientation. -/
theorem sameOppositeTransition_t2_2_t1_1
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (orientation : OrientationData.BlockOrientation)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T2_2)
      ((O.transitionFor orientation).placeNext source T1_1) = 1 :=
  O.transitionFor_connector_unit_edges orientation source
    T2_2 T1_1 nextConnector_T2_2_T1_1

/-- Same/opposite transition obligations supply the named `T2_2 -> T1_2`
connector unit edge for any selected orientation. -/
theorem sameOppositeTransition_t2_2_t1_2
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (orientation : OrientationData.BlockOrientation)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T2_2)
      ((O.transitionFor orientation).placeNext source T1_2) = 1 :=
  O.transitionFor_connector_unit_edges orientation source
    T2_2 T1_2 nextConnector_T2_2_T1_2

/-- Same/opposite transition obligations supply the named `T4_0 -> T0_0`
connector unit edge for any selected orientation. -/
theorem sameOppositeTransition_t4_0_t0_0
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (orientation : OrientationData.BlockOrientation)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T4_0)
      ((O.transitionFor orientation).placeNext source T0_0) = 1 :=
  O.transitionFor_connector_unit_edges orientation source
    T4_0 T0_0 nextConnector_T4_0_T0_0

/-- Same/opposite transition obligations supply the named `T4_0 -> T0_2`
connector unit edge for any selected orientation. -/
theorem sameOppositeTransition_t4_0_t0_2
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (orientation : OrientationData.BlockOrientation)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T4_0)
      ((O.transitionFor orientation).placeNext source T0_2) = 1 :=
  O.transitionFor_connector_unit_edges orientation source
    T4_0 T0_2 nextConnector_T4_0_T0_2

/-- Algebraic generated closure plus reduced metric data carries the four
named successor connector unit equations for the generated non-rigid chain. -/
def ofGeneratedClosureReduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ExactCrossConnectorUnitCertificate hk
      (GeneratedClosedChain.generatedPoint O hk base orientation) :=
  ofGeneratedPeriodReduced O hk base orientation
    (GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
      O hk base orientation
      (PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
        O hk base orientation closure))
    H

/-- Named `T2_2 -> next T1_1` unit edge from generated closure and reduced
metric data. -/
theorem generatedClosureReduced_t2_2_t1_1
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) :
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint O hk base orientation i T2_2)
      (GeneratedClosedChain.generatedPoint O hk base orientation
        (cyclicSucc hk i) T1_1) = 1 :=
  (ofGeneratedClosureReduced O hk base orientation closure H).t2_2_t1_1 i

/-- Named `T2_2 -> next T1_2` unit edge from generated closure and reduced
metric data. -/
theorem generatedClosureReduced_t2_2_t1_2
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) :
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint O hk base orientation i T2_2)
      (GeneratedClosedChain.generatedPoint O hk base orientation
        (cyclicSucc hk i) T1_2) = 1 :=
  (ofGeneratedClosureReduced O hk base orientation closure H).t2_2_t1_2 i

/-- Named `T4_0 -> next T0_0` unit edge from generated closure and reduced
metric data. -/
theorem generatedClosureReduced_t4_0_t0_0
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) :
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint O hk base orientation i T4_0)
      (GeneratedClosedChain.generatedPoint O hk base orientation
        (cyclicSucc hk i) T0_0) = 1 :=
  (ofGeneratedClosureReduced O hk base orientation closure H).t4_0_t0_0 i

/-- Named `T4_0 -> next T0_2` unit edge from generated closure and reduced
metric data. -/
theorem generatedClosureReduced_t4_0_t0_2
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) :
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint O hk base orientation i T4_0)
      (GeneratedClosedChain.generatedPoint O hk base orientation
        (cyclicSucc hk i) T0_2) = 1 :=
  (ofGeneratedClosureReduced O hk base orientation closure H).t4_0_t0_2 i

/-- Named T2_2 -> next T1_1 unit edge from any checked closed placement. -/
theorem closedPlacement_t2_2_t1_1
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) (i : Fin k) :
    _root_.eucDist (P.point i T2_2)
      (P.point (cyclicSucc hk i) T1_1) = 1 :=
  (ofClosedPlacement P).t2_2_t1_1 i

/-- Named T2_2 -> next T1_2 unit edge from any checked closed placement. -/
theorem closedPlacement_t2_2_t1_2
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) (i : Fin k) :
    _root_.eucDist (P.point i T2_2)
      (P.point (cyclicSucc hk i) T1_2) = 1 :=
  (ofClosedPlacement P).t2_2_t1_2 i

/-- Named T4_0 -> next T0_0 unit edge from any checked closed placement. -/
theorem closedPlacement_t4_0_t0_0
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) (i : Fin k) :
    _root_.eucDist (P.point i T4_0)
      (P.point (cyclicSucc hk i) T0_0) = 1 :=
  (ofClosedPlacement P).t4_0_t0_0 i

/-- Named T4_0 -> next T0_2 unit edge from any checked closed placement. -/
theorem closedPlacement_t4_0_t0_2
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) (i : Fin k) :
    _root_.eucDist (P.point i T4_0)
      (P.point (cyclicSucc hk i) T0_2) = 1 :=
  (ofClosedPlacement P).t4_0_t0_2 i

end

end ClosedPlacementCrossConnectorEdgesW19
end PachToth
end ErdosProblems1066
