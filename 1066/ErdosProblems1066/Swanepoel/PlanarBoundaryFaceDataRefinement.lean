import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete
import ErdosProblems1066.Swanepoel.BoundaryFaceCountingToM8

set_option autoImplicit false

/-!
# Refined planar face data for the M8 boundary route

This module keeps the remaining face and boundary inputs in one visible
package.  The Jordan-style topology fields are supplied through
`JordanBoundaryConcrete.MissingTopologyFacts`; the angle and subpolygon count
data are the fields already consumed by `PlanarBoundaryClosure`.

The checked content here is deterministic projection: from this refined
package to `PlanarBoundaryData`, then onward to the face-counting facade and
the `m = 8` boundary route.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarBoundaryFaceDataRefinement

open BoundaryFaceCountingToM8
open CutVertexClosure
open JordanBoundaryConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a
configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryConcrete.canonicalGraph C

/-! ## Refined face and boundary package -/

/--
Refined planar face data for a concrete configuration.

Compared with `PlanarBoundaryClosure.PlanarBoundaryData`, this record keeps
the source of the outer-boundary core visible as the concrete Jordan/topology
package for the canonical graph of `C`.
-/
structure PlanarBoundaryFaceData (C : _root_.UDConfig n) where
  topology : MissingTopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)

namespace PlanarBoundaryFaceData

variable {C : _root_.UDConfig n}

/-- The outer-boundary core obtained from the concrete Jordan/topology data. -/
def core (D : PlanarBoundaryFaceData.{u} C) :
    OuterBoundaryCore (CanonicalGraph C) :=
  D.topology.toCore

/-- The supplied canonical face-boundary witness. -/
def faceBoundary (D : PlanarBoundaryFaceData.{u} C) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (CanonicalGraph C) :=
  D.topology.faceBoundary

/-- The selected outer face in the supplied face data. -/
def outerFace (D : PlanarBoundaryFaceData.{u} C) :
    D.faceBoundary.Face :=
  D.topology.outerFace

/-- The selected outer face is marked outer. -/
theorem outerFace_isOuter (D : PlanarBoundaryFaceData.{u} C) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.topology.outerFace_isOuter

/-- The old planar face-boundary interface attached to the supplied faces. -/
def planarFaceBoundary (D : PlanarBoundaryFaceData.{u} C) :
    PlanarInterface.FaceBoundaryHypotheses (CanonicalGraph C).toStraightLine :=
  D.topology.planarFaceBoundary

/-- The canonical noncrossing fact for the selected unit-distance graph. -/
theorem pairwiseNoncrossing (D : PlanarBoundaryFaceData.{u} C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  D.topology.pairwiseNoncrossing

/-- The selected outer boundary cycle. -/
def outerCycle (D : PlanarBoundaryFaceData.{u} C) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  D.topology.outerCycle

/-- The selected outer boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective (D : PlanarBoundaryFaceData.{u} C) :
    Function.Injective D.outerCycle.vertex :=
  D.topology.outerCycle_vertex_injective

/-- Boundary vertices of the selected outer face satisfy the supplied boundary
predicate. -/
theorem boundary_vertex_onBoundary
    (D : PlanarBoundaryFaceData.{u} C)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    D.topology.outerEnclosure.onBoundary
      (D.faceBoundary.boundaryVertex D.outerFace k) :=
  D.topology.boundary_vertex_onBoundary k

/-- Every ambient vertex lies inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn
    (D : PlanarBoundaryFaceData.{u} C) (v : Fin n) :
    D.topology.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  D.topology.all_vertices_insideOrOn v

/-- Forget the refined source fields to the existing planar-boundary package. -/
def toPlanarBoundaryData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) where
  core := D.core
  outerAngleBounds := D.outerAngleBounds
  Subpolygon := D.Subpolygon
  subpolygonData := D.subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.core = D.core :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_planarFaceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.planarFaceBoundary = D.planarFaceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.outerFace = D.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.toPlanarBoundaryData.subpolygonData S = D.subpolygonData S :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.outerBoundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

/-! ### Boundary bookkeeping and realized count projections -/

/-- The finite boundary classification bookkeeping whose cardinalities realize
the outer-boundary count fields. -/
def boundaryBookkeeping
    (D : PlanarBoundaryFaceData.{u} C) :
    BoundaryClassification.BoundaryBookkeeping.{u} :=
  D.outerAngleBounds.countsRealization.bookkeeping

/-- The realization tying the finite boundary classification bookkeeping to
the `BoundaryCounts` used by the angle-counting layer. -/
def boundaryCountsRealization
    (D : PlanarBoundaryFaceData.{u} C) :
    BoundaryClassification.BoundaryCountsRealization.{u} :=
  D.outerAngleBounds.countsRealization

@[simp]
theorem boundaryCountsRealization_toBoundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryCountsRealization.toBoundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

/-- The finite boundary bookkeeping projects to the same `BoundaryCounts`
record supplied to the planar-boundary closure. -/
@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.toBoundaryCounts =
      D.outerAngleBounds.counts :=
  D.boundaryCountsRealization.realizes

@[simp]
theorem outerBoundaryCounts_d3
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d3 = D.boundaryBookkeeping.d3 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d4
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d4 = D.boundaryBookkeeping.d4 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d5
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d5 = D.boundaryBookkeeping.d5 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d6
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d6 = D.boundaryBookkeeping.d6 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_b
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.b = D.boundaryBookkeeping.b := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_B
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.B =
      D.boundaryBookkeeping.longArcCount := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_negativeCount
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.negativeCount =
      D.boundaryBookkeeping.negativeElementCount := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

/-- The checked angle lower bound on the refined outer-boundary counts. -/
theorem boundaryAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.AngleLowerBound :=
  D.outerAngleBounds.angleLowerBound

/-- The same angle lower bound, pulled back to the finite bookkeeping
projection. -/
theorem boundaryBookkeepingAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.toBoundaryCounts.AngleLowerBound :=
  D.outerAngleBounds.projected_angleLowerBound

/-- E12 stated directly in the finite boundary-classification cardinalities. -/
theorem boundaryAngleCount_bookkeeping
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.d5 + 2 * D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.b + D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounting.BoundaryCounts.boundary_angle_count_inequality
      D.boundaryBookkeeping.toBoundaryCounts
      D.boundaryBookkeepingAngleLowerBound

/-- Negative-element E12 stated directly in finite boundary-classification
cardinalities. -/
theorem boundaryNegativeCount_bookkeeping
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.negativeElementCount +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounting.BoundaryCounts.boundary_negative_count_inequality
      D.boundaryBookkeeping.toBoundaryCounts
      D.boundaryBookkeepingAngleLowerBound

/-- Expanded negative-element E12 in the bookkeeping field names. -/
theorem boundaryNegativeCount_bookkeeping_expanded
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.b + D.boundaryBookkeeping.d5 +
        D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.negativeElementCount]
    using D.boundaryNegativeCount_bookkeeping

/-- The canonical outer-boundary count package extracted from the refined
face data. -/
def canonicalBoundaryCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses (CanonicalGraph C) :=
  D.toPlanarBoundaryData.canonicalBoundaryCountHypotheses

@[simp]
theorem canonicalBoundaryCountHypotheses_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.canonicalBoundaryCountHypotheses.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem canonicalBoundaryCountHypotheses_counts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.canonicalBoundaryCountHypotheses.counts =
      D.outerAngleBounds.counts :=
  rfl

/-- The canonical subpolygon count package extracted from the refined face
data. -/
def canonicalSubpolygonCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses (CanonicalGraph C) :=
  D.toPlanarBoundaryData.canonicalSubpolygonCountHypotheses S

@[simp]
theorem canonicalSubpolygonCountHypotheses_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.canonicalSubpolygonCountHypotheses S).faceBoundary =
      D.faceBoundary :=
  rfl

@[simp]
theorem canonicalSubpolygonCountHypotheses_counts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.canonicalSubpolygonCountHypotheses S).counts =
      (D.subpolygonData S).counts :=
  rfl

/-- The existing combined face-counting bridge interface obtained from the
refined face data. -/
def toFaceCountingBridgeData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.FaceCountingBridgeData.{u} (CanonicalGraph C) :=
  D.toPlanarBoundaryData.toFaceCountingBridgeData

@[simp]
theorem toFaceCountingBridgeData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_planarFaceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.planarFaceBoundary =
      D.planarFaceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_boundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.boundaryCounts =
      D.canonicalBoundaryCountHypotheses :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_outerCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.outerCounts =
      D.outerAngleBounds.counts :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_Subpolygon
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonCounts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.toFaceCountingBridgeData.subpolygonCounts S =
      D.canonicalSubpolygonCountHypotheses S :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonDegreeCounts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.toFaceCountingBridgeData.subpolygonDegreeCounts S =
      (D.subpolygonData S).counts :=
  rfl

theorem toFaceCountingBridgeData_countingTheorems
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.FaceCountingBridgeData.CountingTheorems
      D.toFaceCountingBridgeData :=
  D.toFaceCountingBridgeData.countingTheorems

/-- Concrete face-counting data extracted from the refined package. -/
def concreteFaceCountingData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      D.toPlanarBoundaryData :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    D.toPlanarBoundaryData

@[simp]
theorem concreteFaceCountingData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_planarFaceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.planarFaceBoundary =
      D.planarFaceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_pairwiseNoncrossing
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.pairwiseNoncrossing =
      D.pairwiseNoncrossing :=
  rfl

@[simp]
theorem concreteFaceCountingData_outerFace
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.outerFace = D.outerFace :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.boundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.boundaryCountHypotheses =
      D.canonicalBoundaryCountHypotheses :=
  rfl

/-- The concrete face-counting package retains the checked boundary angle
lower bound on the refined outer counts. -/
theorem concreteFaceCountingData_boundaryAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.boundaryCounts.AngleLowerBound :=
  D.concreteFaceCountingData.boundaryAngleLowerBound

@[simp]
theorem concreteFaceCountingData_Subpolygon
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.concreteFaceCountingData.subpolygonCounts S =
      (D.subpolygonData S).counts :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.concreteFaceCountingData.subpolygonCountHypotheses S =
      D.canonicalSubpolygonCountHypotheses S :=
  rfl

/-- The checked subpolygon angle lower bound carried by the refined package. -/
theorem subpolygonAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.AngleLowerBound :=
  (D.subpolygonData S).angleLowerBound

/-- The concrete face-counting package retains every checked subpolygon angle
lower bound. -/
theorem concreteFaceCountingData_subpolygonAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.concreteFaceCountingData.subpolygonCounts S).AngleLowerBound :=
  D.concreteFaceCountingData.subpolygonAngleLowerBound S

/-- The E12 count conclusion from the refined face data. -/
theorem boundaryAngleCount
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d5 + 2 * D.outerAngleBounds.counts.d6 +
        D.outerAngleBounds.counts.b + D.outerAngleBounds.counts.B + 6 <=
      D.outerAngleBounds.counts.d3 :=
  D.concreteFaceCountingData.boundaryAngleCount

/-- The negative-element E12 count conclusion from the refined face data. -/
theorem boundaryNegativeCount
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.negativeCount +
        D.outerAngleBounds.counts.B + 6 <=
      D.outerAngleBounds.counts.d3 :=
  D.concreteFaceCountingData.boundaryNegativeCount

/-- The E13 high-degree-slack conclusion for each supplied subpolygon. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.D5 +
        2 * (D.subpolygonData S).counts.D6 + 6 <=
      2 * (D.subpolygonData S).counts.D2 +
        (D.subpolygonData S).counts.D3 :=
  D.concreteFaceCountingData.subpolygonLowDegreeWithHighDegreeSlack S

/-- The Lemma 4 low-degree conclusion for each supplied subpolygon. -/
theorem subpolygonLowDegree
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    6 <= 2 * (D.subpolygonData S).counts.D2 +
      (D.subpolygonData S).counts.D3 :=
  D.concreteFaceCountingData.subpolygonLowDegree S

/-- Proposition-valued face-counting conclusions for the refined package. -/
theorem faceCountingTheorems
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.toPlanarBoundaryData :=
  PlanarBoundaryFinal.PlanarBoundaryData.faceCountingTheorems_of_concreteData
    D.toPlanarBoundaryData

end PlanarBoundaryFaceData

/-! ## Projection into the M8 boundary route -/

/--
Refined face/boundary data plus the still-explicit boundary-label inputs
needed by the `m = 8` route.
-/
structure M8RefinedBoundaryRouteData
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  faceData : PlanarBoundaryFaceData.{u} C
  connectedNoCut : PreconnectedNoCutVertexCertificate C
  spine :
    M8BoundarySpine
      (boundaryCutDegreeContextOfPlanarBoundary
        faceData.toPlanarBoundaryData connectedNoCut hmin)
  lemma8 : M8Lemma8Combinatorics spine

namespace M8RefinedBoundaryRouteData

variable {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The planar-boundary package obtained from the refined face data. -/
def planarBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  D.faceData.toPlanarBoundaryData

@[simp]
theorem planarBoundary_eq_faceData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.planarBoundary = D.faceData.toPlanarBoundaryData :=
  rfl

/-- The structural M8 context determined by the refined face data. -/
def context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryCutDegreeContext C :=
  boundaryCutDegreeContextOfPlanarBoundary
    D.planarBoundary D.connectedNoCut hmin

@[simp]
theorem context_outerBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary = D.faceData.core :=
  rfl

@[simp]
theorem context_faceBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary.faceBoundary = D.faceData.faceBoundary :=
  rfl

@[simp]
theorem context_outerFace
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary.outerFace = D.faceData.outerFace :=
  rfl

/-- The checked face-counting fields determined by the refined face data. -/
def faceCounting
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryFaceCountingFields D.planarBoundary D.context :=
  planarBoundaryFaceCountingFields
    D.planarBoundary D.connectedNoCut hmin

@[simp]
theorem faceCounting_concrete
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete = D.faceData.concreteFaceCountingData :=
  rfl

@[simp]
theorem faceCounting_concrete_faceBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.faceBoundary = D.faceData.faceBoundary :=
  rfl

@[simp]
theorem faceCounting_concrete_boundaryCounts
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCounts =
      D.faceData.outerAngleBounds.counts :=
  rfl

@[simp]
theorem faceCounting_concrete_boundaryCountHypotheses
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCountHypotheses =
      D.faceData.canonicalBoundaryCountHypotheses :=
  rfl

/-- Forget the refined wrapper to the existing M8 boundary route data. -/
def toM8BoundaryRouteData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryRouteData.{u} C hmin where
  planarBoundary := D.planarBoundary
  connectedNoCut := D.connectedNoCut
  spine := D.spine
  lemma8 := D.lemma8

@[simp]
theorem toM8BoundaryRouteData_planarBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.planarBoundary = D.planarBoundary :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_connectedNoCut
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.connectedNoCut = D.connectedNoCut :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_spine
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.spine = D.spine :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_lemma8
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.lemma8 = D.lemma8 :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context = D.context :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_faceBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context.outerBoundary.faceBoundary =
      D.faceData.faceBoundary :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_outerFace
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context.outerBoundary.outerFace =
      D.faceData.outerFace :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_faceCounting_concrete
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete =
      D.faceData.concreteFaceCountingData :=
  rfl

/-! ### Boundary bookkeeping and count projections along the route -/

/-- The finite boundary classification bookkeeping carried by the refined M8
route. -/
def boundaryBookkeeping
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    BoundaryClassification.BoundaryBookkeeping.{u} :=
  D.faceData.boundaryBookkeeping

/-- The realization tying the route's boundary classifications to the concrete
outer-boundary counts. -/
def boundaryCountsRealization
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    BoundaryClassification.BoundaryCountsRealization.{u} :=
  D.faceData.boundaryCountsRealization

@[simp]
theorem boundaryBookkeeping_eq_faceData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping = D.faceData.boundaryBookkeeping :=
  rfl

@[simp]
theorem boundaryCountsRealization_eq_faceData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryCountsRealization = D.faceData.boundaryCountsRealization :=
  rfl

@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.toBoundaryCounts =
      D.faceData.outerAngleBounds.counts :=
  D.faceData.boundaryBookkeeping_toBoundaryCounts

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d3
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 =
      D.boundaryBookkeeping.d3 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d4
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d4 =
      D.boundaryBookkeeping.d4 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d5
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d5 =
      D.boundaryBookkeeping.d5 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d6
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d6 =
      D.boundaryBookkeeping.d6 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_b
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.b =
      D.boundaryBookkeeping.b := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_B
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B =
      D.boundaryBookkeeping.longArcCount := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_negativeCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.negativeCount =
      D.boundaryBookkeeping.negativeElementCount := by
  simp

/-- The checked outer-boundary angle lower bound survives projection into the
M8 route's concrete face-counting package. -/
theorem boundaryAngleLowerBound
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.AngleLowerBound :=
  D.faceData.boundaryAngleLowerBound

/-- The route's finite bookkeeping carries the same checked angle lower
bound. -/
theorem boundaryBookkeepingAngleLowerBound
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.toBoundaryCounts.AngleLowerBound :=
  D.faceData.boundaryBookkeepingAngleLowerBound

/-- E12 on the refined M8 route, stated in finite boundary-classification
cardinalities. -/
theorem boundaryAngleCount_bookkeeping
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.d5 + 2 * D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.b + D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 :=
  D.faceData.boundaryAngleCount_bookkeeping

/-- Negative-element E12 on the refined M8 route, stated in finite
boundary-classification cardinalities. -/
theorem boundaryNegativeCount_bookkeeping
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.negativeElementCount +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 :=
  D.faceData.boundaryNegativeCount_bookkeeping

/-- Expanded negative-element E12 on the refined M8 route. -/
theorem boundaryNegativeCount_bookkeeping_expanded
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.b + D.boundaryBookkeeping.d5 +
        D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 :=
  D.faceData.boundaryNegativeCount_bookkeeping_expanded

/-- The concrete boundary-label package obtained from the M8 route. -/
def toBoundaryLabelPackage
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryLabelPackage C :=
  D.toM8BoundaryRouteData.toBoundaryLabelPackage

@[simp]
theorem toBoundaryLabelPackage_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.context = D.context :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_spine
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.spine = D.spine :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_lemma8
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.lemma8 = D.lemma8 :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_p
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8BoundaryIndex) :
    D.toBoundaryLabelPackage.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_q
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8TriangleIndex) :
    D.toBoundaryLabelPackage.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_r
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.toBoundaryLabelPackage.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_s
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.toBoundaryLabelPackage.labels.s i = D.lemma8.s i :=
  rfl

/-- The local labels determined by the refined route. -/
def toM8LocalLabels
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8LocalLabels C :=
  D.toM8BoundaryRouteData.toM8LocalLabels

@[simp]
theorem toM8LocalLabels_eq
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8LocalLabels =
      D.toBoundaryLabelPackage.toM8LocalLabels :=
  rfl

@[simp]
theorem toM8LocalLabels_labels
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8LocalLabels.labels = D.toBoundaryLabelPackage.labels :=
  rfl

/-- The face-counting package in the route is exactly the one determined by
the refined planar-boundary data. -/
theorem route_faceCounting_eq
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting = D.faceCounting :=
  rfl

/-- The refined route carries the planar-boundary face-counting theorem
summary for the same projected planar-boundary package. -/
theorem faceCountingTheorems
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.planarBoundary :=
  D.faceData.faceCountingTheorems

/-- The route's canonical boundary-count package is attached to the same
face-boundary witness as the structural M8 context. -/
theorem boundaryCountHypotheses_faceBoundary_eq_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.faceBoundary =
      D.context.outerBoundary.faceBoundary :=
  D.toM8BoundaryRouteData.boundaryCountHypotheses_faceBoundary_eq_context

/-- The route's canonical boundary-count package uses exactly the route's
concrete outer-boundary counts. -/
theorem boundaryCountHypotheses_counts_eq_concrete
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.counts =
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts :=
  D.toM8BoundaryRouteData.boundaryCountHypotheses_counts_eq_concrete

/-- The route keeps the checked outer-boundary count package on the same
face-boundary witness supplied by the refined Jordan/topology data. -/
theorem boundaryCountHypotheses_faceBoundary_eq_refined
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.faceBoundary =
      D.faceData.faceBoundary :=
  rfl

@[simp]
theorem boundaryCountHypotheses_counts_eq_refined
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.counts =
      D.faceData.outerAngleBounds.counts :=
  rfl

/-- The E12 count conclusion available after projecting to the M8 route. -/
theorem boundaryAngleCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d5 +
        2 * D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d6 +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.b +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 :=
  D.toM8BoundaryRouteData.boundaryAngleCount

/-- The negative-element E12 conclusion available after projecting to the M8
route. -/
theorem boundaryNegativeCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.negativeCount +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 :=
  D.toM8BoundaryRouteData.boundaryNegativeCount

/-- The E13 high-degree-slack conclusion after projecting to the refined
face data. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (S : D.faceData.Subpolygon) :
    (D.faceData.subpolygonData S).counts.D5 +
        2 * (D.faceData.subpolygonData S).counts.D6 + 6 <=
      2 * (D.faceData.subpolygonData S).counts.D2 +
        (D.faceData.subpolygonData S).counts.D3 :=
  D.faceData.subpolygonLowDegreeWithHighDegreeSlack S

/-- The Lemma 4 low-degree conclusion after projecting to the refined face
data. -/
theorem subpolygonLowDegree
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (S : D.faceData.Subpolygon) :
    6 <= 2 * (D.faceData.subpolygonData S).counts.D2 +
      (D.faceData.subpolygonData S).counts.D3 :=
  D.faceData.subpolygonLowDegree S

/-- Assemble the existing clean M8 construction interface from the refined
route once the later M8 fields are supplied. -/
def toM8ConstructionData
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin :=
  D.toM8BoundaryRouteData.toM8ConstructionData
    turnBounds lateTriples windowGeometry

@[simp]
theorem toM8ConstructionData_localLabels
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels =
        D.toM8LocalLabels :=
  rfl

@[simp]
theorem toM8ConstructionData_turnBounds
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData
      turnBounds lateTriples windowGeometry).turnBounds =
        turnBounds :=
  rfl

/-- Project the refined route to the existing broken-lattice minimal-failure
interface. -/
def toBrokenLatticeMinimalFailure
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  (D.toM8ConstructionData
    turnBounds lateTriples windowGeometry).toBrokenLatticeMinimalFailure

/-- Final conditional endpoint after projecting the refined route into the
existing M8 construction interface. -/
theorem contradiction
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    False :=
  (D.toBrokenLatticeMinimalFailure
    turnBounds lateTriples windowGeometry).contradiction

end M8RefinedBoundaryRouteData

end

end PlanarBoundaryFaceDataRefinement
end Swanepoel
end ErdosProblems1066
