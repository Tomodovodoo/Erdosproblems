import ErdosProblems1066.Swanepoel.BoundaryAngleTurnW11
import ErdosProblems1066.Swanepoel.SubpolygonFamilyW11
import ErdosProblems1066.Swanepoel.TopologyInstantiationW11
import ErdosProblems1066.Swanepoel.BoundaryCountingInstantiationW10
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Boundary-angle closure layer, W11

This file closes the boundary angle/turn packages over the current topology,
subpolygon, W10 component, and W11 geometry-row facades.

The concrete outer-boundary topology, boundary classification, face-subpolygon
family, long-arc count-gap data, labels, windows, and no-early alternatives
remain explicit input fields.  The layer only proves checked projections among
the existing rows; it does not state an unconditional final lower-bound target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleClosureW11

open BoundaryCountingInstantiationW10
open BoundaryWalkClassificationConcrete
open GeometryRemainingFieldsW10
open MinimalGraphFacts
open NoEarlyTripleObstructionConcrete

universe u

noncomputable section

variable {n : Nat}

/-- Canonical graph used by the Swanepoel boundary stack. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanTopologyFactsConcrete.canonicalGraph C

/-! ## Boundary angle data with explicit topology and subpolygons -/

/-- Boundary-angle bookkeeping obtained directly from the concrete W10
unit-separated witness family. -/
def outerAngleBoundsOfWitness
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {P : OuterBoundaryCore G}
    (D : OuterBoundaryClassificationInputs P)
    (W : ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} where
  countsRealization := D.countsRealizationLift
  geometricAngleSum := W.geometricAngleSum
  forced_le_geometric := W.forced_le_geometricAngleSum
  geometric_le_polygon := W.geometric_le_polygon

@[simp]
theorem outerAngleBoundsOfWitness_counts
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {P : OuterBoundaryCore G}
    (D : OuterBoundaryClassificationInputs P)
    (W : ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    (outerAngleBoundsOfWitness D W).counts = D.counts :=
  rfl

/-- Explicit selected-face/enclosure data plus the boundary-angle row produced
from the concrete unit-separated angle witnesses. -/
def explicitFaceDataOfTopologyAngle
    {C : _root_.UDConfig n}
    (T : JordanTopologyFactsConcrete.TopologyFacts C)
    (D : OuterBoundaryClassificationInputs T.toCore)
    (W : ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    SubpolygonInstantiation.ExplicitOuterBoundaryFaceData.{u}
      (CanonicalGraph C) where
  outerFaceData := T.outerFaceData
  enclosureData := T.enclosureData
  outerAngleBounds := outerAngleBoundsOfWitness D W

@[simp]
theorem explicitFaceDataOfTopologyAngle_core
    {C : _root_.UDConfig n}
    (T : JordanTopologyFactsConcrete.TopologyFacts C)
    (D : OuterBoundaryClassificationInputs T.toCore)
    (W : ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    (explicitFaceDataOfTopologyAngle T D W).core = T.toCore :=
  rfl

@[simp]
theorem explicitFaceDataOfTopologyAngle_outerAngleBounds
    {C : _root_.UDConfig n}
    (T : JordanTopologyFactsConcrete.TopologyFacts C)
    (D : OuterBoundaryClassificationInputs T.toCore)
    (W : ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    (explicitFaceDataOfTopologyAngle T D W).outerAngleBounds =
      outerAngleBoundsOfWitness D W :=
  rfl

/--
The explicit boundary-angle closure input for one configuration.

The subpolygon family is indexed by the selected face/enclosure data and by
the angle row computed from `angleWitness`.  The long-arc field is then tied to
the same subpolygon data, so the count-gap route and the topology/subpolygon
rows share the same concrete inputs.
-/
structure BoundaryAngleClosureInput (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts C
  classification : OuterBoundaryClassificationInputs topology.toCore
  angleWitness :
    ClassifiedBoundary.UnitSeparatedAngleFamilies classification
  subpolygons :
    SubpolygonFamilyW11.SubpolygonFamilyPackage
      (explicitFaceDataOfTopologyAngle topology classification angleWitness)
  longArcFields :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      classification angleWitness.geometricAngleSum
      angleWitness.forced_le_geometricAngleSum
      angleWitness.geometric_le_polygon
      subpolygons.Subpolygon
      (fun S => subpolygons.toPlanarBoundaryData.subpolygonData S)

namespace BoundaryAngleClosureInput

variable {C : _root_.UDConfig n}

/-- The W11 compact topology package associated to the explicit topology row. -/
def checkedTopology
    (I : BoundaryAngleClosureInput.{0} C) :
    TopologyInstantiationW11.CheckedTopologyPackage C :=
  TopologyInstantiationW11.ofTopologyFacts I.topology

/-- The explicit face/enclosure and angle data used by the subpolygon family. -/
def explicitFaceData
    (I : BoundaryAngleClosureInput.{u} C) :
    SubpolygonInstantiation.ExplicitOuterBoundaryFaceData.{u}
      (CanonicalGraph C) :=
  explicitFaceDataOfTopologyAngle
    I.topology I.classification I.angleWitness

@[simp]
theorem explicitFaceData_core
    (I : BoundaryAngleClosureInput.{u} C) :
    I.explicitFaceData.core = I.topology.toCore :=
  rfl

@[simp]
theorem explicitFaceData_outerAngleBounds
    (I : BoundaryAngleClosureInput.{u} C) :
    I.explicitFaceData.outerAngleBounds =
      outerAngleBoundsOfWitness I.classification I.angleWitness :=
  rfl

/-- The exact subpolygon data consumed by the boundary-count and long-arc
route. -/
def subpolygonData
    (I : BoundaryAngleClosureInput.{u} C)
    (S : I.subpolygons.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C) :=
  I.subpolygons.toPlanarBoundaryData.subpolygonData S

@[simp]
theorem subpolygonData_counts
    (I : BoundaryAngleClosureInput.{u} C)
    (S : I.subpolygons.Subpolygon) :
    (I.subpolygonData S).counts =
      I.subpolygons.subpolygonCounts S :=
  rfl

/-- The W10 count/turn input assembled from the explicit W11 fields. -/
def countTurnInput
    (I : BoundaryAngleClosureInput.{u} C) :
    ClassifiedBoundary.CountTurnInput
      I.classification I.subpolygons.Subpolygon I.subpolygonData where
  angleWitness := I.angleWitness
  longArcFields := I.longArcFields

/-- The boundary angle/turn package from `BoundaryAngleTurnW11`. -/
def boundaryAngleTurnPackage
    (I : BoundaryAngleClosureInput.{u} C) :
    BoundaryAngleTurnW11.ClassifiedBoundary.BoundaryAngleTurnPackage
      I.classification I.subpolygons.Subpolygon I.subpolygonData where
  countTurn := I.countTurnInput

@[simp]
theorem boundaryAngleTurnPackage_outerAngleBounds
    (I : BoundaryAngleClosureInput.{u} C) :
    I.boundaryAngleTurnPackage.outerAngleBounds =
      outerAngleBoundsOfWitness I.classification I.angleWitness :=
  rfl

/-- Boundary angle/turn data in the topology-indexed W11 route shape. -/
def toBoundaryAngleTurnTopologyPackage
    (I : BoundaryAngleClosureInput.{u} C) :
    BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.{u}
      C where
  topology := I.topology
  classification := I.classification
  Subpolygon := I.subpolygons.Subpolygon
  subpolygonData := I.subpolygonData
  boundary := I.boundaryAngleTurnPackage

/-- The checked W9 topology/angle/subpolygon row. -/
def toTopologyAngleSubpolygonRow
    (I : BoundaryAngleClosureInput.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  I.toBoundaryAngleTurnTopologyPackage.toW9TopologyAngleSubpolygonRow

@[simp]
theorem toTopologyAngleSubpolygonRow_topology
    (I : BoundaryAngleClosureInput.{u} C) :
    I.toTopologyAngleSubpolygonRow.topology = I.topology :=
  rfl

@[simp]
theorem toTopologyAngleSubpolygonRow_Subpolygon
    (I : BoundaryAngleClosureInput.{u} C) :
    I.toTopologyAngleSubpolygonRow.Subpolygon =
      I.subpolygons.Subpolygon :=
  rfl

/-- The checked outer-boundary E12 inequality in concrete boundary counts. -/
theorem boundaryAngleCountInequality
    (I : BoundaryAngleClosureInput.{u} C) :
    I.classification.counts.d5 + 2 * I.classification.counts.d6 +
        I.classification.counts.b + I.classification.counts.B + 6 <=
      I.classification.counts.d3 :=
  I.boundaryAngleTurnPackage.boundaryAngleCountInequality

/-- The checked negative-element E12 inequality in concrete boundary counts. -/
theorem boundaryNegativeCountInequality
    (I : BoundaryAngleClosureInput.{u} C) :
    I.classification.counts.negativeCount +
        I.classification.counts.B + 6 <=
      I.classification.counts.d3 :=
  I.boundaryAngleTurnPackage.boundaryNegativeCountInequality

/-- The checked E13 low-degree conclusion for every explicit W11 subpolygon. -/
theorem subpolygonLowDegree
    (I : BoundaryAngleClosureInput.{u} C)
    (S : I.subpolygons.Subpolygon) :
    6 <= 2 * (I.subpolygonData S).counts.D2 +
      (I.subpolygonData S).counts.D3 := by
  exact I.subpolygons.lowDegree S

/-- The selected long-arc turn bound is carried through the boundary package. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three
    (I : BoundaryAngleClosureInput.{u} C) :
    Lemma10Inequalities.totalTurn
        I.boundaryAngleTurnPackage.m8TurnBounds.turn <
      Real.pi / 3 :=
  I.boundaryAngleTurnPackage.m8TurnBounds_totalTurn_lt_pi_div_three

/-! ## W10 topology and component rows -/

/-- W10 topology/enclosure source fields projected from the explicit topology
row. -/
def toGeometryTopologyEnclosureFields
    (I : BoundaryAngleClosureInput.{u} C) :
    GeometryRemainingFieldsW10.TopologyEnclosureFields C where
  outerFaceData := I.topology.outerFaceData
  enclosureData := I.topology.enclosureData

/-- W10 topology/angle/long-arc source fields. -/
def toGeometryTopologyAngleLongArcFields
    (I : BoundaryAngleClosureInput.{u} C) :
    GeometryRemainingFieldsW10.TopologyAngleLongArcFields.{u} C where
  topology := I.toGeometryTopologyEnclosureFields
  outerAngleBounds := I.boundaryAngleTurnPackage.outerAngleBounds
  Subpolygon := I.subpolygons.Subpolygon
  subpolygonData := I.subpolygonData
  longArc := I.toBoundaryAngleTurnTopologyPackage.w9LongArc

/-- Minimal-failure W10 topology component fields. -/
def toW10TopologyComponentFields
    (I : BoundaryAngleClosureInput.{u} C) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C where
  topology := I.topology

/-- Minimal-failure W10 partition/angle component fields. -/
def toW10PartitionAngleComponentFields
    (I : BoundaryAngleClosureInput.{u} C) :
    MinimalFailureDirectMatrixW10.PartitionAngleComponentFields.{u}
      C I.toW10TopologyComponentFields where
  outerAngleBounds := I.boundaryAngleTurnPackage.outerAngleBounds
  Subpolygon := I.subpolygons.Subpolygon
  subpolygonData := I.subpolygonData
  longArc := I.toBoundaryAngleTurnTopologyPackage.w9LongArc

/-- Direct W10 component row once the label, no-early, and window rows are
supplied for the same boundary angle/turn source. -/
def toW10DirectComponentPackageRow
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin I.toTopologyAngleSubpolygonRow)
    (noEarlyTriples :
      M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples
        (I.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (I.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels
        (I.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).turnBounds) :
    SwanepoelW10ClosureMatrix.DirectComponentPackageRow.{u}
      C hmin :=
  I.toBoundaryAngleTurnTopologyPackage.toW10DirectComponentPackageRow
    boundaryLabels noEarlyTriples windowContainment

/-- K23 W10 component row once the label, K23, and window rows are supplied
for the same boundary angle/turn source. -/
def toW10K23ComponentPackageRow
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin I.toTopologyAngleSubpolygonRow)
    (k23Obstruction :
      NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
        (I.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels.predicates.data)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (I.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels
        (I.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).turnBounds) :
    SwanepoelW10ClosureMatrix.K23ComponentPackageRow.{u}
      C hmin :=
  I.toBoundaryAngleTurnTopologyPackage.toW10K23ComponentPackageRow
    boundaryLabels k23Obstruction windowContainment

/-! ## W11 geometry-row source projections -/

/-- Geometry source fields after adding boundary labels to the boundary
angle/turn source. -/
def toGeometrySourceFields
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
        C hmin I.toGeometryTopologyAngleLongArcFields) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin where
  geometry := I.toGeometryTopologyAngleLongArcFields
  boundaryLabels := labels

/-- Direct W10 geometry package from the boundary angle/turn source plus the
remaining label, containment, and no-start/no-early rows. -/
def toDirectGeometryPackage
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
        C hmin I.toGeometryTopologyAngleLongArcFields)
    (containment :
      GeometryRemainingFieldsW10.ContainmentFields
        (I.toGeometrySourceFields labels))
    (noStartNoEarly :
      GeometryRemainingFieldsW10.NoStartNoEarlyFields
        (I.toGeometrySourceFields labels)) :
    GeometryRemainingFieldsW10.DirectGeometryPackage.{u} C hmin where
  source := I.toGeometrySourceFields labels
  containment := containment
  noStartNoEarly := noStartNoEarly

/-- K23 W10 geometry package from the boundary angle/turn source plus the
remaining label, containment, and K23 rows. -/
def toK23GeometryPackage
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
        C hmin I.toGeometryTopologyAngleLongArcFields)
    (containment :
      GeometryRemainingFieldsW10.ContainmentFields
        (I.toGeometrySourceFields labels))
    (k23NoEarly :
      GeometryRemainingFieldsW10.K23NoEarlyFields
        (I.toGeometrySourceFields labels)) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin where
  source := I.toGeometrySourceFields labels
  containment := containment
  k23NoEarly := k23NoEarly

/-- Common-neighbor W10 geometry package from the boundary angle/turn source
plus the remaining label, containment, and common-neighbor rows. -/
def toCommonNeighborGeometryPackage
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
        C hmin I.toGeometryTopologyAngleLongArcFields)
    (containment :
      GeometryRemainingFieldsW10.ContainmentFields
        (I.toGeometrySourceFields labels))
    (commonNeighborNoEarly :
      GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
        (I.toGeometrySourceFields labels)) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin where
  source := I.toGeometrySourceFields labels
  containment := containment
  commonNeighborNoEarly := commonNeighborNoEarly

/-- Direct route into the W11 minimal-failure geometry closure row. -/
def toDirectGeometryClosureRow
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
        C hmin I.toGeometryTopologyAngleLongArcFields)
    (containment :
      GeometryRemainingFieldsW10.ContainmentFields
        (I.toGeometrySourceFields labels))
    (noStartNoEarly :
      GeometryRemainingFieldsW10.NoStartNoEarlyFields
        (I.toGeometrySourceFields labels)) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofDirectGeometryPackage
    (I.toDirectGeometryPackage labels containment noStartNoEarly)

/-- K23 route into the W11 minimal-failure geometry closure row. -/
def toK23GeometryClosureRow
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
        C hmin I.toGeometryTopologyAngleLongArcFields)
    (containment :
      GeometryRemainingFieldsW10.ContainmentFields
        (I.toGeometrySourceFields labels))
    (k23NoEarly :
      GeometryRemainingFieldsW10.K23NoEarlyFields
        (I.toGeometrySourceFields labels)) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
    (I.toK23GeometryPackage labels containment k23NoEarly)

/-- Common-neighbor route into the W11 minimal-failure geometry closure row. -/
def toCommonNeighborGeometryClosureRow
    (I : BoundaryAngleClosureInput.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
        C hmin I.toGeometryTopologyAngleLongArcFields)
    (containment :
      GeometryRemainingFieldsW10.ContainmentFields
        (I.toGeometrySourceFields labels))
    (commonNeighborNoEarly :
      GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
        (I.toGeometrySourceFields labels)) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
    (I.toCommonNeighborGeometryPackage
      labels containment commonNeighborNoEarly)

end BoundaryAngleClosureInput

/-! ## Row and matrix wrappers into the W11 geometry matrix -/

/-- Direct geometry row sourced from explicit boundary angle/turn data. -/
structure BoundaryDirectGeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryAngleClosureInput.{u} C
  labels :
    GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
      C hmin boundary.toGeometryTopologyAngleLongArcFields
  containment :
    GeometryRemainingFieldsW10.ContainmentFields
      (boundary.toGeometrySourceFields labels)
  noStartNoEarly :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      (boundary.toGeometrySourceFields labels)

namespace BoundaryDirectGeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the boundary-sourced direct row to the W10 direct geometry package. -/
def toDirectGeometryPackage
    (R : BoundaryDirectGeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.DirectGeometryPackage.{u} C hmin :=
  R.boundary.toDirectGeometryPackage
    R.labels R.containment R.noStartNoEarly

/-- Convert the boundary-sourced direct row to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : BoundaryDirectGeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.boundary.toDirectGeometryClosureRow
    R.labels R.containment R.noStartNoEarly

/-- A fixed direct row closes the corresponding minimal cleared failure. -/
theorem contradiction
    (R : BoundaryDirectGeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end BoundaryDirectGeometryRow

/-- K23 geometry row sourced from explicit boundary angle/turn data. -/
structure BoundaryK23GeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryAngleClosureInput.{u} C
  labels :
    GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
      C hmin boundary.toGeometryTopologyAngleLongArcFields
  containment :
    GeometryRemainingFieldsW10.ContainmentFields
      (boundary.toGeometrySourceFields labels)
  k23NoEarly :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      (boundary.toGeometrySourceFields labels)

namespace BoundaryK23GeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the boundary-sourced K23 row to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (R : BoundaryK23GeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin :=
  R.boundary.toK23GeometryPackage
    R.labels R.containment R.k23NoEarly

/-- Convert the boundary-sourced K23 row to the W11 geometry closure row. -/
def toGeometryClosureRow
    (R : BoundaryK23GeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.boundary.toK23GeometryClosureRow
    R.labels R.containment R.k23NoEarly

/-- A fixed K23 row closes the corresponding minimal cleared failure. -/
theorem contradiction
    (R : BoundaryK23GeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end BoundaryK23GeometryRow

/-- Common-neighbor geometry row sourced from explicit boundary angle/turn
data. -/
structure BoundaryCommonNeighborGeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryAngleClosureInput.{u} C
  labels :
    GeometryRemainingFieldsW10.BoundaryLabelFields.{u}
      C hmin boundary.toGeometryTopologyAngleLongArcFields
  containment :
    GeometryRemainingFieldsW10.ContainmentFields
      (boundary.toGeometrySourceFields labels)
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      (boundary.toGeometrySourceFields labels)

namespace BoundaryCommonNeighborGeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Forget the boundary-sourced common-neighbor row to the W10
common-neighbor geometry package. -/
def toCommonNeighborGeometryPackage
    (R : BoundaryCommonNeighborGeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin :=
  R.boundary.toCommonNeighborGeometryPackage
    R.labels R.containment R.commonNeighborNoEarly

/-- Convert the boundary-sourced common-neighbor row to the W11 geometry
closure row. -/
def toGeometryClosureRow
    (R : BoundaryCommonNeighborGeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  R.boundary.toCommonNeighborGeometryClosureRow
    R.labels R.containment R.commonNeighborNoEarly

/-- A fixed common-neighbor row closes the corresponding minimal cleared
failure. -/
theorem contradiction
    (R : BoundaryCommonNeighborGeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end BoundaryCommonNeighborGeometryRow

/-- Uniform direct geometry rows sourced from boundary angle/turn data. -/
structure BoundaryDirectGeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryDirectGeometryRow.{u} C hmin

namespace BoundaryDirectGeometryMatrix

/-- Forget to the W10 direct geometry matrix. -/
def toW10DirectGeometryMatrix
    (M : BoundaryDirectGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

/-- Convert to the W11 geometry closure matrix. -/
def toW11GeometryClosureMatrix
    (M : BoundaryDirectGeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Boundary-sourced direct rows rule out every minimal cleared failure once
the explicit row family is supplied. -/
theorem no_minimalClearedFailure
    (M : BoundaryDirectGeometryMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toW11GeometryClosureMatrix.no_minimalClearedFailure

end BoundaryDirectGeometryMatrix

/-- Uniform K23 geometry rows sourced from boundary angle/turn data. -/
structure BoundaryK23GeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryK23GeometryRow.{u} C hmin

namespace BoundaryK23GeometryMatrix

/-- Forget to the W10 K23 geometry matrix. -/
def toW10K23GeometryMatrix
    (M : BoundaryK23GeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

/-- Convert to the W11 geometry closure matrix. -/
def toW11GeometryClosureMatrix
    (M : BoundaryK23GeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Boundary-sourced K23 rows rule out every minimal cleared failure once the
explicit row family is supplied. -/
theorem no_minimalClearedFailure
    (M : BoundaryK23GeometryMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toW11GeometryClosureMatrix.no_minimalClearedFailure

end BoundaryK23GeometryMatrix

/-- Uniform common-neighbor geometry rows sourced from boundary angle/turn
data. -/
structure BoundaryCommonNeighborGeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryCommonNeighborGeometryRow.{u} C hmin

namespace BoundaryCommonNeighborGeometryMatrix

/-- Forget to the W10 common-neighbor geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : BoundaryCommonNeighborGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

/-- Convert to the W11 geometry closure matrix. -/
def toW11GeometryClosureMatrix
    (M : BoundaryCommonNeighborGeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Boundary-sourced common-neighbor rows rule out every minimal cleared
failure once the explicit row family is supplied. -/
theorem no_minimalClearedFailure
    (M : BoundaryCommonNeighborGeometryMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toW11GeometryClosureMatrix.no_minimalClearedFailure

end BoundaryCommonNeighborGeometryMatrix

end

end BoundaryAngleClosureW11
end Swanepoel
end ErdosProblems1066
