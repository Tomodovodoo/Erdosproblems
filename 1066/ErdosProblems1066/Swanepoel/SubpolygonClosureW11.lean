import ErdosProblems1066.Swanepoel.SubpolygonFamilyW11
import ErdosProblems1066.Swanepoel.BoundaryAngleTurnW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 subpolygon closure package

This module is a checked facade over the W11 concrete subpolygon family and
the W10/W11 boundary count and turn rows.

The file does not create cycle, face, enclosure, classification, long-arc,
label, window, or no-early data.  Those inputs stay visible.  Once such data
are supplied, the declarations below show that the concrete subpolygon family
feeds:

* the E13 angle lower-bound package;
* the E13 low-degree count obligations;
* the planar face-counting bridge;
* the W9/W10 minimal-failure route prefixes built by `BoundaryAngleTurnW11`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonClosureW11

open BoundaryCounting
open SubpolygonFamilyW11

universe u

noncomputable section

variable {n : Nat}

/-! ## Face-data level closure -/

namespace FaceData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {D : SubpolygonInstantiation.ExplicitOuterBoundaryFaceData.{u} G}

/-- The concrete W11 subpolygon family over fixed outer-face data. -/
abbrev ConcreteFamily :=
  SubpolygonFamilyPackage.{u} D

namespace ConcreteFamily

/-- The planar-boundary-facing cycle/count/angle data carried by one member. -/
def subpolygonData
    (F : ConcreteFamily.{u} (D := D)) (S : F.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData G :=
  F.toPlanarBoundaryData.subpolygonData S

@[simp]
theorem subpolygonData_counts
    (F : ConcreteFamily.{u} (D := D)) (S : F.Subpolygon) :
    (F.subpolygonData S).counts = F.subpolygonCounts S :=
  rfl

/-- The checked angle lower bound for the cycle/count/angle data. -/
theorem subpolygonData_angleLowerBound
    (F : ConcreteFamily.{u} (D := D)) (S : F.Subpolygon) :
    (F.subpolygonData S).counts.AngleLowerBound := by
  simpa using F.subpolygonAngleLowerBound S

/-- The count bridge package for one concrete subpolygon. -/
def canonicalCountHypotheses
    (F : ConcreteFamily.{u} (D := D)) (S : F.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  F.canonicalSubpolygonCountHypotheses S

@[simp]
theorem canonicalCountHypotheses_counts
    (F : ConcreteFamily.{u} (D := D)) (S : F.Subpolygon) :
    (F.canonicalCountHypotheses S).counts = F.subpolygonCounts S :=
  rfl

/-- E13 with high-degree slack, routed through the concrete count bridge. -/
theorem lowDegreeWithHighDegreeSlack
    (F : ConcreteFamily.{u} (D := D)) (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 :=
  F.lowDegreeWithHighDegreeSlack_viaBridge S

/-- The E13 low-degree obligation used downstream. -/
theorem lowDegree
    (F : ConcreteFamily.{u} (D := D)) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 :=
  F.lowDegree_viaBridge S

/-- The planar-boundary package assembled from the concrete family. -/
def planarBoundary
    (F : ConcreteFamily.{u} (D := D)) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  F.toPlanarBoundaryData

/-- The face-counting bridge assembled from the concrete family. -/
def faceCountingBridge
    (F : ConcreteFamily.{u} (D := D)) :
    PlanarBoundaryClosure.FaceCountingBridgeData.{u} G :=
  F.toFaceCountingBridgeData

/-- Checked face-counting conclusions supplied by the concrete family. -/
theorem faceCountingTheorems
    (F : ConcreteFamily.{u} (D := D)) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      F.planarBoundary :=
  SubpolygonFamilyPackage.faceCountingTheorems F

/-- The same conclusions in the bridge shape used by later rows. -/
theorem bridgeCountingTheorems
    (F : ConcreteFamily.{u} (D := D)) :
    PlanarBoundaryClosure.FaceCountingBridgeData.CountingTheorems
      F.faceCountingBridge :=
  SubpolygonFamilyPackage.bridgeCountingTheorems F

/-- Compact proposition-valued summary of all checked subpolygon obligations. -/
structure ObligationSummary
    (F : ConcreteFamily.{u} (D := D)) : Prop where
  angleLowerBound :
    forall S : F.Subpolygon, (F.subpolygonData S).counts.AngleLowerBound
  lowDegreeWithHighDegreeSlack :
    forall S : F.Subpolygon,
      (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
        2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3
  lowDegree :
    forall S : F.Subpolygon,
      6 <= 2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3
  faceCounting :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      F.planarBoundary
  bridgeCounting :
    PlanarBoundaryClosure.FaceCountingBridgeData.CountingTheorems
      F.faceCountingBridge

/-- The concrete W11 family closes the subpolygon count and angle side. -/
theorem obligationSummary
    (F : ConcreteFamily.{u} (D := D)) :
    ObligationSummary F where
  angleLowerBound := F.subpolygonData_angleLowerBound
  lowDegreeWithHighDegreeSlack := F.lowDegreeWithHighDegreeSlack
  lowDegree := F.lowDegree
  faceCounting := F.faceCountingTheorems
  bridgeCounting := F.bridgeCountingTheorems

end ConcreteFamily

end FaceData

/-! ## Topology-facing closure -/

/-- Build the subpolygon-instantiation face data from supplied topology and
outer-angle rows.  The topology data remains an input. -/
def explicitFaceDataOfTopology
    {C : _root_.UDConfig n}
    (topology : JordanTopologyFactsConcrete.TopologyFacts.{u} C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}) :
    SubpolygonInstantiation.ExplicitOuterBoundaryFaceData.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C) where
  outerFaceData := topology.outerFaceData
  enclosureData := topology.enclosureData
  outerAngleBounds := outerAngleBounds

namespace Topology

variable {C : _root_.UDConfig n}

/--
Concrete subpolygon family attached to a supplied topology row.

The `outerAngleBounds` field is part of the planar-boundary package in which
the concrete family is first assembled; a later classified boundary row may
provide its own outer-angle package while reusing the same subpolygon data.
-/
structure ConcreteFamilyPackage (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts.{u} C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  family :
    SubpolygonFamilyPackage.{u}
      (explicitFaceDataOfTopology topology outerAngleBounds)

namespace ConcreteFamilyPackage

/-- The family index type. -/
def Subpolygon (P : ConcreteFamilyPackage.{u} C) : Type u :=
  P.family.Subpolygon

/-- Computed E13 counts for one concrete subpolygon. -/
def subpolygonCounts
    (P : ConcreteFamilyPackage.{u} C) (S : P.Subpolygon) :
    SubpolygonDegreeCounts :=
  P.family.subpolygonCounts S

/-- Cycle/count/angle data in the shape expected by the boundary route. -/
def subpolygonData
    (P : ConcreteFamilyPackage.{u} C) (S : P.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  P.family.toPlanarBoundaryData.subpolygonData S

@[simp]
theorem subpolygonData_counts
    (P : ConcreteFamilyPackage.{u} C) (S : P.Subpolygon) :
    (P.subpolygonData S).counts = P.subpolygonCounts S :=
  rfl

/-- Planar-boundary data obtained from the supplied topology and family. -/
def planarBoundary
    (P : ConcreteFamilyPackage.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds
    P.Subpolygon P.subpolygonData

@[simp]
theorem planarBoundary_core
    (P : ConcreteFamilyPackage.{u} C) :
    P.planarBoundary.core = P.topology.toCore :=
  rfl

@[simp]
theorem planarBoundary_Subpolygon
    (P : ConcreteFamilyPackage.{u} C) :
    P.planarBoundary.Subpolygon = P.Subpolygon :=
  rfl

@[simp]
theorem planarBoundary_subpolygonData_counts
    (P : ConcreteFamilyPackage.{u} C) (S : P.Subpolygon) :
    (P.planarBoundary.subpolygonData S).counts =
      P.subpolygonCounts S :=
  rfl

/-- Face-count bridge package for the topology-facing planar boundary. -/
def faceCountingBridge
    (P : ConcreteFamilyPackage.{u} C) :
    PlanarBoundaryClosure.FaceCountingBridgeData.{u}
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  P.planarBoundary.toFaceCountingBridgeData

/-- The concrete family proves the subpolygon angle obligation. -/
theorem subpolygonAngleLowerBound
    (P : ConcreteFamilyPackage.{u} C) (S : P.Subpolygon) :
    (P.subpolygonData S).counts.AngleLowerBound := by
  simpa using P.family.subpolygonAngleLowerBound S

/-- E13 with high-degree slack for the topology-facing package. -/
theorem lowDegreeWithHighDegreeSlack
    (P : ConcreteFamilyPackage.{u} C) (S : P.Subpolygon) :
    (P.subpolygonCounts S).D5 + 2 * (P.subpolygonCounts S).D6 + 6 <=
      2 * (P.subpolygonCounts S).D2 + (P.subpolygonCounts S).D3 :=
  P.family.lowDegreeWithHighDegreeSlack_viaBridge S

/-- The E13 low-degree conclusion for the topology-facing package. -/
theorem lowDegree
    (P : ConcreteFamilyPackage.{u} C) (S : P.Subpolygon) :
    6 <= 2 * (P.subpolygonCounts S).D2 + (P.subpolygonCounts S).D3 :=
  P.family.lowDegree_viaBridge S

/-- Checked count conclusions for the topology-facing package. -/
theorem faceCountingTheorems
    (P : ConcreteFamilyPackage.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      P.planarBoundary :=
  P.planarBoundary.faceCountingTheorems

/-- Build the W9 topology/angle/subpolygon row when long-arc data is supplied. -/
def toW9TopologyAngleSubpolygonRow
    (P : ConcreteFamilyPackage.{u} C)
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        P.planarBoundary) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := longArc

@[simp]
theorem toW9TopologyAngleSubpolygonRow_planarBoundary
    (P : ConcreteFamilyPackage.{u} C)
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        P.planarBoundary) :
    (P.toW9TopologyAngleSubpolygonRow longArc).planarBoundary =
      P.planarBoundary :=
  rfl

end ConcreteFamilyPackage

end Topology

/-! ## Boundary angle and minimal-failure route prefix -/

namespace ClassifiedRoute

variable {C : _root_.UDConfig n}

/--
Concrete subpolygon data plugged into the W11 classified-boundary angle and
turn package.

The topology, boundary classification, concrete subpolygon family, and
boundary angle/turn data are all still supplied fields.  This record only
checks their projections to the minimal-failure route prefixes.
-/
structure SubpolygonBoundaryPackage (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts.{u} C
  outerAngleBoundsForFamily :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  family :
    SubpolygonFamilyPackage.{u}
      (explicitFaceDataOfTopology topology outerAngleBoundsForFamily)
  classification :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toCore
  boundary :
    BoundaryAngleTurnW11.ClassifiedBoundary.BoundaryAngleTurnPackage
      classification family.Subpolygon
        (fun S => family.toPlanarBoundaryData.subpolygonData S)

namespace SubpolygonBoundaryPackage

/-- The subpolygon index type carried into the classified boundary route. -/
def Subpolygon (P : SubpolygonBoundaryPackage.{u} C) : Type u :=
  P.family.Subpolygon

/-- Computed subpolygon counts from the concrete family. -/
def subpolygonCounts
    (P : SubpolygonBoundaryPackage.{u} C) (S : P.Subpolygon) :
    SubpolygonDegreeCounts :=
  P.family.subpolygonCounts S

/-- The subpolygon cycle/count/angle data consumed by `BoundaryAngleTurnW11`. -/
def subpolygonData
    (P : SubpolygonBoundaryPackage.{u} C) (S : P.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  P.family.toPlanarBoundaryData.subpolygonData S

@[simp]
theorem subpolygonData_counts
    (P : SubpolygonBoundaryPackage.{u} C) (S : P.Subpolygon) :
    (P.subpolygonData S).counts = P.subpolygonCounts S :=
  rfl

/-- The W11 topology/angle/subpolygon package supplied by the boundary route. -/
def toBoundaryAngleTurnTopologyPackage
    (P : SubpolygonBoundaryPackage.{u} C) :
    BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.{u}
      C where
  topology := P.topology
  classification := P.classification
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  boundary := P.boundary

/-- The W9 topology/angle/subpolygon row obtained from the boundary package. -/
def toW9TopologyAngleSubpolygonRow
    (P : SubpolygonBoundaryPackage.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  P.toBoundaryAngleTurnTopologyPackage.toW9TopologyAngleSubpolygonRow

@[simp]
theorem toW9TopologyAngleSubpolygonRow_Subpolygon
    (P : SubpolygonBoundaryPackage.{u} C) :
    P.toW9TopologyAngleSubpolygonRow.Subpolygon = P.Subpolygon :=
  rfl

@[simp]
theorem toW9TopologyAngleSubpolygonRow_subpolygonData_counts
    (P : SubpolygonBoundaryPackage.{u} C) (S : P.Subpolygon) :
    (P.toW9TopologyAngleSubpolygonRow.subpolygonData S).counts =
      P.subpolygonCounts S :=
  rfl

/-- The boundary-angle lower bound for the classified outer boundary. -/
theorem boundaryAngleLowerBound
    (P : SubpolygonBoundaryPackage.{u} C) :
    P.classification.counts.AngleLowerBound :=
  P.boundary.angleLowerBound

/-- The E12 boundary count obligation from the classified boundary route. -/
theorem boundaryAngleCount
    (P : SubpolygonBoundaryPackage.{u} C) :
    P.classification.counts.d5 + 2 * P.classification.counts.d6 +
        P.classification.counts.b + P.classification.counts.B + 6 <=
      P.classification.counts.d3 :=
  P.boundary.boundaryAngleCountInequality

/-- The negative-count E12 form from the classified boundary route. -/
theorem boundaryNegativeCount
    (P : SubpolygonBoundaryPackage.{u} C) :
    P.classification.counts.negativeCount + P.classification.counts.B + 6 <=
      P.classification.counts.d3 :=
  P.boundary.boundaryNegativeCountInequality

/-- The concrete subpolygon family gives the E13 angle obligation. -/
theorem subpolygonAngleLowerBound
    (P : SubpolygonBoundaryPackage.{u} C) (S : P.Subpolygon) :
    (P.subpolygonData S).counts.AngleLowerBound := by
  simpa using P.family.subpolygonAngleLowerBound S

/-- The concrete subpolygon family gives E13 with high-degree slack. -/
theorem lowDegreeWithHighDegreeSlack
    (P : SubpolygonBoundaryPackage.{u} C) (S : P.Subpolygon) :
    (P.subpolygonCounts S).D5 + 2 * (P.subpolygonCounts S).D6 + 6 <=
      2 * (P.subpolygonCounts S).D2 + (P.subpolygonCounts S).D3 :=
  P.family.lowDegreeWithHighDegreeSlack_viaBridge S

/-- The concrete subpolygon family gives the E13 low-degree obligation. -/
theorem lowDegree
    (P : SubpolygonBoundaryPackage.{u} C) (S : P.Subpolygon) :
    6 <= 2 * (P.subpolygonCounts S).D2 + (P.subpolygonCounts S).D3 :=
  P.family.lowDegree_viaBridge S

/-- The selected nonconcave long arc has the needed turn bound. -/
theorem selectedLongArc_totalTurn_lt_pi_div_three
    (P : SubpolygonBoundaryPackage.{u} C) :
    Lemma10Inequalities.totalTurn
        (P.boundary.countTurn.longArcFields.rawTurn
          P.boundary.selectedLongArc) <
      Real.pi / 3 :=
  P.boundary.selectedLongArc_totalTurn_lt_pi_div_three

/-- The M8 construction-level turn bounds produced by the route. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three
    (P : SubpolygonBoundaryPackage.{u} C) :
    Lemma10Inequalities.totalTurn P.boundary.m8TurnBounds.turn <
      Real.pi / 3 :=
  P.boundary.m8TurnBounds_totalTurn_lt_pi_div_three

/-- Convert the prefix to a W10 direct component row after the later fields
are supplied. -/
def toW10DirectComponentPackageRow
    (P : SubpolygonBoundaryPackage.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin P.toW9TopologyAngleSubpolygonRow)
    (noEarlyTriples :
      M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).turnBounds) :
    SwanepoelW10ClosureMatrix.DirectComponentPackageRow.{u} C hmin :=
  P.toBoundaryAngleTurnTopologyPackage.toW10DirectComponentPackageRow
    boundaryLabels noEarlyTriples windowContainment

/-- Convert the prefix to a W10 K23 component row after the later fields are
supplied. -/
def toW10K23ComponentPackageRow
    (P : SubpolygonBoundaryPackage.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin P.toW9TopologyAngleSubpolygonRow)
    (k23Obstruction :
      NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels.predicates.data)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).turnBounds) :
    SwanepoelW10ClosureMatrix.K23ComponentPackageRow.{u} C hmin :=
  P.toBoundaryAngleTurnTopologyPackage.toW10K23ComponentPackageRow
    boundaryLabels k23Obstruction windowContainment

/-- A direct W10 completion of this prefix closes the fixed minimal failure. -/
theorem contradiction_of_direct_completion
    (P : SubpolygonBoundaryPackage.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin P.toW9TopologyAngleSubpolygonRow)
    (noEarlyTriples :
      M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).turnBounds) :
    False :=
  (P.toW10DirectComponentPackageRow
    boundaryLabels noEarlyTriples windowContainment).contradiction

/-- A K23 W10 completion of this prefix closes the fixed minimal failure. -/
theorem contradiction_of_k23_completion
    (P : SubpolygonBoundaryPackage.{u} C)
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (boundaryLabels :
      SwanepoelRemainingObligationsW9.BoundaryLabelRow.{u}
        C hmin P.toW9TopologyAngleSubpolygonRow)
    (k23Obstruction :
      NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels.predicates.data)
    (windowContainment :
      M8WindowGeometryFromContainment.M8WindowContainment
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).localLabels
        (P.toBoundaryAngleTurnTopologyPackage.toW9BaseRow
          boundaryLabels).turnBounds) :
    False :=
  (P.toW10K23ComponentPackageRow
    boundaryLabels k23Obstruction windowContainment).contradiction

end SubpolygonBoundaryPackage

end ClassifiedRoute

end

end SubpolygonClosureW11
end Swanepoel
end ErdosProblems1066
