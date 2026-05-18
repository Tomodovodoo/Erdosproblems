import ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface
import ErdosProblems1066.PachToth.ClosedPlacementNonRigidComponents

set_option autoImplicit false

/-!
# W19 non-rigid closed-placement data

This file is a data-layer bridge to the downstream closed-placement
certificate family

`forall k hk, ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk`.

It does not assert any geometric existence.  The remaining geometric work is
carried as named structures whose fields are the exact period, separation,
same-block, and connector facts consumed by the existing non-rigid records.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonRigidClosedPlacementDataW19

open Arithmetic
open ClosedPlacementInterface
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The downstream family object requested by the closed-placement interface. -/
abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    ExplicitClosedPlacementCertificate k hk

/-- Forget a certificate family to the checked closed placements it carries. -/
def closedPlacementFamilyOfCertificates
    (C : ExplicitClosedPlacementCertificateFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk => (C k hk).toClosedPlacement

@[simp]
theorem closedPlacementFamilyOfCertificates_point
    (C : ExplicitClosedPlacementCertificateFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamilyOfCertificates C k hk).point i v =
      (C k hk).point i v :=
  rfl

/-- A certificate family gives pointwise checked closed placements. -/
theorem exists_closedPlacement_of_certificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    forall (k : Nat) (hk : 0 < k),
      exists P : DeformedPlacement.ClosedPlacement k hk,
        P.point = (C k hk).point := by
  intro k hk
  exact Exists.intro ((C k hk).toClosedPlacement) rfl

/-- Exact-block target wrapper from the requested certificate family. -/
theorem targetUpperConstructionFiveSixteen_of_certificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    targetUpperConstructionFiveSixteen :=
  NonRigidClosedPlacementInterface.targetUpperConstructionFiveSixteen_of_closedPlacements
    (closedPlacementFamilyOfCertificates C)

/-- Arbitrary-vertex target wrapper from the requested certificate family. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_certificateFamily
    (C : ExplicitClosedPlacementCertificateFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  NonRigidClosedPlacementInterface.targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (closedPlacementFamilyOfCertificates C)

/-- Repackage the direct non-rigid component record as the explicit
closed-placement certificate. -/
def certificateOfComponents
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk) :
    ExplicitClosedPlacementCertificate k hk where
  point := C.point
  separated := C.separated
  same_block_edges_unit := C.same_block_edges_unit
  cross_connector_edges_unit := C.successor_connector_edges_unit

@[simp]
theorem certificateOfComponents_point
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfComponents C).point i v = C.point i v :=
  rfl

/-- Direct non-rigid components also give the point/edge data interface. -/
def explicitCyclicPointEdgeDataOfComponents
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk) :
    NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk where
  point := C.point
  separated := C.separated
  same_block_edges_unit := C.same_block_edges_unit
  cross_connector_edges_unit := C.successor_connector_edges_unit

@[simp]
theorem explicitCyclicPointEdgeDataOfComponents_point
    {k : Nat} {hk : 0 < k}
    (C : ClosedPlacementNonRigidComponents.Components k hk)
    (i : Fin k) (v : LocalVertex) :
    (explicitCyclicPointEdgeDataOfComponents C).point i v = C.point i v :=
  rfl

/-- Repackage point/edge data as direct non-rigid components. -/
def componentsOfExplicitCyclicPointEdgeData
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk) :
    ClosedPlacementNonRigidComponents.Components k hk where
  point := D.point
  separated := D.separated
  same_block_edges_unit := D.same_block_edges_unit
  successor_connector_edges_unit := D.cross_connector_edges_unit

@[simp]
theorem componentsOfExplicitCyclicPointEdgeData_point
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk)
    (i : Fin k) (v : LocalVertex) :
    (componentsOfExplicitCyclicPointEdgeData D).point i v = D.point i v :=
  rfl

/-- Direct point/edge data gives the requested explicit certificate. -/
def certificateOfExplicitCyclicPointEdgeData
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  D.toExplicitClosedPlacementCertificate

@[simp]
theorem certificateOfExplicitCyclicPointEdgeData_point
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfExplicitCyclicPointEdgeData D).point i v = D.point i v :=
  rfl

/-- Successor-orbit data gives the requested explicit certificate. -/
def certificateOfExplicitCyclicOrbitEdgeData
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  D.toExplicitTransitionClosedPlacementCertificate
    |>.toExplicitClosedPlacementCertificate

@[simp]
theorem certificateOfExplicitCyclicOrbitEdgeData_point
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfExplicitCyclicOrbitEdgeData D).point i v = D.point i v :=
  rfl

/-- Same/opposite orbit data gives the requested explicit certificate. -/
def certificateOfSameOppositeCyclicOrbitData
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData
      O k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  D.toExplicitTransitionClosedPlacementCertificate
    |>.toExplicitClosedPlacementCertificate

@[simp]
theorem certificateOfSameOppositeCyclicOrbitData_point
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    {k : Nat} {hk : 0 < k}
    (D : NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData
      O k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfSameOppositeCyclicOrbitData D).point i v =
      D.point i v :=
  rfl

/-- A successor-compatible closed-chain orbit gives the requested explicit
certificate. -/
def certificateOfSuccessorCompatibleCyclicPointOrbit
    {k : Nat} {hk : 0 < k}
    (O : ClosedChainExistence.SuccessorCompatibleCyclicPointOrbit k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  O.toExplicitTransitionClosedPlacementCertificate
    |>.toExplicitClosedPlacementCertificate

@[simp]
theorem certificateOfSuccessorCompatibleCyclicPointOrbit_point
    {k : Nat} {hk : 0 < k}
    (O : ClosedChainExistence.SuccessorCompatibleCyclicPointOrbit k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfSuccessorCompatibleCyclicPointOrbit O).point i v =
      O.point i v :=
  rfl

/-- An isometric successor-compatible closed-chain orbit gives the requested
explicit certificate. -/
def certificateOfIsometricSuccessorCompatibleCyclicPointOrbit
    {k : Nat} {hk : 0 < k}
    (O :
      ClosedChainExistence.IsometricSuccessorCompatibleCyclicPointOrbit
        k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  O.toExplicitTransitionClosedPlacementCertificate
    |>.toExplicitClosedPlacementCertificate

@[simp]
theorem certificateOfIsometricSuccessorCompatibleCyclicPointOrbit_point
    {k : Nat} {hk : 0 < k}
    (O :
      ClosedChainExistence.IsometricSuccessorCompatibleCyclicPointOrbit
        k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfIsometricSuccessorCompatibleCyclicPointOrbit O).point i v =
      O.point i v :=
  rfl

/-- The older closed-chain placement record gives the requested explicit
certificate through `ClosedChainConstruction`. -/
def certificateOfClosedChainPlacement
    {k : Nat} {hk : 0 < k}
    (P : PlacementBridge.ClosedChainPlacement k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  ClosedChainConstruction.explicitCertificateOfClosedChainPlacement P

@[simp]
theorem certificateOfClosedChainPlacement_point
    {k : Nat} {hk : 0 < k}
    (P : PlacementBridge.ClosedChainPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfClosedChainPlacement P).point i v = P.point i v :=
  rfl

/-- The oriented closed-chain placement record gives the requested explicit
certificate through `ClosedChainConstruction`. -/
def certificateOfOrientedClosedChainPlacement
    {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  ClosedChainConstruction.explicitCertificateOfOrientedClosedChainPlacement P

@[simp]
theorem certificateOfOrientedClosedChainPlacement_point
    {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfOrientedClosedChainPlacement P).point i v = P.point i v :=
  rfl

/-- Generated period data plus full generated metric hypotheses gives the
requested explicit certificate. -/
def certificateOfGeneratedPeriod
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation) :
    ExplicitClosedPlacementCertificate k hk :=
  (NonRigidClosedPlacementInterface.explicitCyclicPointEdgeData_of_generatedPeriod
      O hk base orientation period H)
    |>.toExplicitClosedPlacementCertificate

@[simp]
theorem certificateOfGeneratedPeriod_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfGeneratedPeriod O hk base orientation period H).point i v =
      GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- Generated period data plus reduced same-block metric hypotheses gives the
requested explicit certificate. -/
def certificateOfGeneratedPeriod_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    ExplicitClosedPlacementCertificate k hk :=
  (NonRigidClosedPlacementInterface.explicitCyclicPointEdgeData_of_generatedPeriod_reduced
      O hk base orientation period H)
    |>.toExplicitClosedPlacementCertificate

@[simp]
theorem certificateOfGeneratedPeriod_reduced_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod O hk base orientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation)
    (i : Fin k) (v : LocalVertex) :
    (certificateOfGeneratedPeriod_reduced
      O hk base orientation period H).point i v =
      GeneratedClosedChain.generatedPoint O hk base orientation i v :=
  rfl

/-- The exact raw fields needed to produce a certificate family directly. -/
structure RawClosedPlacementFamilyFields where
  point : forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2
  separated :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) ->
        1 <= _root_.eucDist (point k hk i u) (point k hk j v)
  same_block_edges_unit :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point k hk i u) (point k hk i v) = 1
  successor_connector_edges_unit :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point k hk i u)
          (point k hk (cyclicSucc hk i) v) = 1

namespace RawClosedPlacementFamilyFields

/-- Raw family fields as the existing direct component record at a fixed
block count. -/
def toComponents
    (F : RawClosedPlacementFamilyFields)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementNonRigidComponents.Components k hk where
  point := F.point k hk
  separated := F.separated k hk
  same_block_edges_unit := F.same_block_edges_unit k hk
  successor_connector_edges_unit :=
    F.successor_connector_edges_unit k hk

@[simp]
theorem toComponents_point
    (F : RawClosedPlacementFamilyFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (F.toComponents k hk).point i v = F.point k hk i v :=
  rfl

/-- Raw family fields as the requested explicit certificate family. -/
def toCertificateFamily
    (F : RawClosedPlacementFamilyFields) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => certificateOfComponents (F.toComponents k hk)

@[simp]
theorem toCertificateFamily_point
    (F : RawClosedPlacementFamilyFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (F.toCertificateFamily k hk).point i v = F.point k hk i v :=
  rfl

end RawClosedPlacementFamilyFields

/-- A family wrapper around the direct non-rigid component records. -/
structure ComponentFamily where
  components :
    forall (k : Nat) (hk : 0 < k),
      ClosedPlacementNonRigidComponents.Components k hk

namespace ComponentFamily

/-- Direct component records as the requested explicit certificate family. -/
def toCertificateFamily
    (F : ComponentFamily) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => certificateOfComponents (F.components k hk)

@[simp]
theorem toCertificateFamily_point
    (F : ComponentFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (F.toCertificateFamily k hk).point i v =
      (F.components k hk).point i v :=
  rfl

/-- Direct component records also provide checked closed placements. -/
def toClosedPlacements
    (F : ComponentFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementFamilyOfCertificates F.toCertificateFamily

@[simp]
theorem toClosedPlacements_point
    (F : ComponentFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (F.toClosedPlacements k hk).point i v =
      (F.components k hk).point i v :=
  rfl

end ComponentFamily

/-- Point/edge records for every positive block count as a certificate
family. -/
def certificateFamilyOfExplicitCyclicPointEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => certificateOfExplicitCyclicPointEdgeData (H k hk)

/-- Successor-orbit records for every positive block count as a certificate
family. -/
def certificateFamilyOfExplicitCyclicOrbitEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => certificateOfExplicitCyclicOrbitEdgeData (H k hk)

/-- Same/opposite orbit records for every positive block count as a
certificate family. -/
def certificateFamilyOfSameOppositeCyclicOrbitData
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    (H : forall (k : Nat) (hk : 0 < k),
      NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData O k hk) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => certificateOfSameOppositeCyclicOrbitData (H k hk)

/-- Successor-compatible closed-chain orbit records for every positive block
count as a certificate family. -/
def certificateFamilyOfSuccessorCompatibleCyclicPointOrbit
    (H : forall (k : Nat) (hk : 0 < k),
      ClosedChainExistence.SuccessorCompatibleCyclicPointOrbit k hk) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => certificateOfSuccessorCompatibleCyclicPointOrbit (H k hk)

/-- Isometric successor-compatible closed-chain orbit records for every
positive block count as a certificate family. -/
def certificateFamilyOfIsometricSuccessorCompatibleCyclicPointOrbit
    (H : forall (k : Nat) (hk : 0 < k),
      ClosedChainExistence.IsometricSuccessorCompatibleCyclicPointOrbit k hk) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => certificateOfIsometricSuccessorCompatibleCyclicPointOrbit
    (H k hk)

/-- Generated-chain family plus full metric data as a certificate family. -/
def certificateFamilyOfGeneratedPeriodFamily
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (periods : F.Periods)
    (H : F.MetricHypotheses) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk =>
    certificateOfGeneratedPeriod
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (periods k hk) (H.metric k hk)

/-- Generated-chain family plus reduced metric data as a certificate family. -/
def certificateFamilyOfGeneratedPeriodFamily_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (periods : F.Periods)
    (H : F.ReducedMetricHypotheses) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk =>
    certificateOfGeneratedPeriod_reduced
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (periods k hk) (H.metric k hk)

/-- Combined full generated-family obligations.  The fields are exactly the
generated final-period equation and the full generated metric hypotheses. -/
structure GeneratedClosedPlacementFamilyObligations
    (F : GeneratedSeparationInterface.GeneratedChainFamily) where
  periods : F.Periods
  fullMetric : F.MetricHypotheses

namespace GeneratedClosedPlacementFamilyObligations

/-- Full generated-family obligations as the requested certificate family. -/
def toCertificateFamily
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B : GeneratedClosedPlacementFamilyObligations F) :
    ExplicitClosedPlacementCertificateFamily :=
  certificateFamilyOfGeneratedPeriodFamily F B.periods B.fullMetric

@[simp]
theorem toCertificateFamily_point
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B : GeneratedClosedPlacementFamilyObligations F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (B.toCertificateFamily k hk).point i v =
      GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i v :=
  rfl

end GeneratedClosedPlacementFamilyObligations

/-- Combined reduced generated-family obligations.  For each positive block
count these expose exactly:
period, global separation, base same-block isometry, and transition
same-block distance preservation. -/
structure GeneratedReducedClosedPlacementFamilyObligations
    (F : GeneratedSeparationInterface.GeneratedChainFamily) where
  periods : F.Periods
  reducedMetric : F.ReducedMetricHypotheses

namespace GeneratedReducedClosedPlacementFamilyObligations

/-- Reduced family obligations as the existing one-chain obligation record at
a fixed block count. -/
def toOneChainObligations
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B : GeneratedReducedClosedPlacementFamilyObligations F)
    (k : Nat) (hk : 0 < k) :
    NonRigidClosedPlacementInterface.GeneratedReducedClosedPlacementObligations
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) where
  period := B.periods k hk
  separated := (B.reducedMetric.metric k hk).separated
  base_same_block_isometry :=
    (B.reducedMetric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances :=
    (B.reducedMetric.metric k hk).transition_preserves_same_block_distances

/-- Reduced generated-family obligations as the requested certificate
family. -/
def toCertificateFamily
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B : GeneratedReducedClosedPlacementFamilyObligations F) :
    ExplicitClosedPlacementCertificateFamily :=
  certificateFamilyOfGeneratedPeriodFamily_reduced
    F B.periods B.reducedMetric

@[simp]
theorem toCertificateFamily_point
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B : GeneratedReducedClosedPlacementFamilyObligations F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (B.toCertificateFamily k hk).point i v =
      GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i v :=
  rfl

/-- Reduced generated-family obligations produce checked closed placements. -/
def toClosedPlacements
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B : GeneratedReducedClosedPlacementFamilyObligations F) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  closedPlacementFamilyOfCertificates B.toCertificateFamily

@[simp]
theorem toClosedPlacements_point
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B : GeneratedReducedClosedPlacementFamilyObligations F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (B.toClosedPlacements k hk).point i v =
      GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i v :=
  rfl

end GeneratedReducedClosedPlacementFamilyObligations

end

end NonRigidClosedPlacementDataW19
end PachToth
end ErdosProblems1066
