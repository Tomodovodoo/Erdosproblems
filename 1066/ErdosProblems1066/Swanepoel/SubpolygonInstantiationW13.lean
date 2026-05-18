import ErdosProblems1066.Swanepoel.SubpolygonPackageW12

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonInstantiationW13

open BoundaryCounting
open FaceReduction
open PlanarInterface
open SubpolygonAssembly
open SubpolygonCore

universe u

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}

def countsOfBoundaryData
    (boundary : BoundaryCycle G)
    (vertices : Finset (Fin n))
    (boundary_subset : boundary.vertexFinset ⊆ vertices) :
    SubpolygonDegreeCounts :=
  (inducedVertexSetOfFinset boundary vertices boundary_subset).degreeCounts

structure ExplicitBoundaryData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  vertices : Finset (Fin n)
  boundary_subset : boundary.vertexFinset ⊆ vertices
  geometricAngleSum : Real
  forced_le_geometric :
    (countsOfBoundaryData boundary vertices boundary_subset).forcedSubpolygonAngleSum <=
      geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <=
      (countsOfBoundaryData boundary vertices boundary_subset).polygonAngleSum

namespace ExplicitBoundaryData

def vertexSet (D : ExplicitBoundaryData G) :
    InducedVertexSet G D.boundary :=
  inducedVertexSetOfFinset D.boundary D.vertices D.boundary_subset

@[simp]
theorem vertexSet_vertices (D : ExplicitBoundaryData G) :
    D.vertexSet.vertices = D.vertices :=
  rfl

def counts (D : ExplicitBoundaryData G) :
    SubpolygonDegreeCounts :=
  D.vertexSet.degreeCounts

@[simp]
theorem counts_eq_degreeCounts (D : ExplicitBoundaryData G) :
    D.counts = D.vertexSet.degreeCounts :=
  rfl

theorem angleLowerBound
    (D : ExplicitBoundaryData G) :
    D.counts.AngleLowerBound := by
  simpa [counts, vertexSet] using
    le_trans D.forced_le_geometric D.geometric_le_polygon

def toDegreeCountData
    (D : ExplicitBoundaryData G) :
    DegreeCountData G D.boundary D.vertexSet where
  angleLowerBound := by
    simpa [counts] using D.angleLowerBound

def toSubpolygonPackage
    (D : ExplicitBoundaryData G) :
    SubpolygonPackage G where
  boundary := D.boundary
  vertexSet := D.vertexSet
  degreeData := D.toDegreeCountData

@[simp]
theorem toSubpolygonPackage_counts
    (D : ExplicitBoundaryData G) :
    D.toSubpolygonPackage.counts = D.counts :=
  rfl

def toCycleCountAngleData
    (D : ExplicitBoundaryData G) :
    SubpolygonCycleCountAngleData G where
  boundary := D.boundary
  vertexSet := D.vertexSet
  countRealization := SubpolygonCountRealization.canonical D.vertexSet
  geometricAngleSum := D.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, vertexSet, SubpolygonCountRealization.canonical] using
      D.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, vertexSet, SubpolygonCountRealization.canonical] using
      D.geometric_le_polygon

@[simp]
theorem toCycleCountAngleData_counts
    (D : ExplicitBoundaryData G) :
    D.toCycleCountAngleData.counts = D.counts :=
  rfl

@[simp]
theorem toCycleCountAngleData_boundary
    (D : ExplicitBoundaryData G) :
    D.toCycleCountAngleData.boundary = D.boundary :=
  rfl

@[simp]
theorem toCycleCountAngleData_vertexSet
    (D : ExplicitBoundaryData G) :
    D.toCycleCountAngleData.vertexSet = D.vertexSet :=
  rfl

theorem lowDegreeWithHighDegreeSlack
    (D : ExplicitBoundaryData G) :
    D.counts.D5 + 2 * D.counts.D6 + 6 <=
      2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toDegreeCountData.lowDegreeWithHighDegreeSlack

theorem lowDegree
    (D : ExplicitBoundaryData G) :
    6 <= 2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toDegreeCountData.lowDegreeInequality

theorem lowDegree_viaCycleCountAngleData
    (D : ExplicitBoundaryData G) :
    6 <= 2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toCycleCountAngleData.lowDegreeInequality

end ExplicitBoundaryData

theorem subpolygonLowDegreeWithHighDegreeSlack_of_explicitBoundaryData
    (boundary : BoundaryCycle G)
    (vertices : Finset (Fin n))
    (boundary_subset : boundary.vertexFinset ⊆ vertices)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      (countsOfBoundaryData boundary vertices boundary_subset).forcedSubpolygonAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        (countsOfBoundaryData boundary vertices boundary_subset).polygonAngleSum) :
    (countsOfBoundaryData boundary vertices boundary_subset).D5 +
        2 * (countsOfBoundaryData boundary vertices boundary_subset).D6 +
          6 <=
      2 * (countsOfBoundaryData boundary vertices boundary_subset).D2 +
        (countsOfBoundaryData boundary vertices boundary_subset).D3 := by
  let D : ExplicitBoundaryData G := {
    boundary := boundary
    vertices := vertices
    boundary_subset := boundary_subset
    geometricAngleSum := geometricAngleSum
    forced_le_geometric := forced_le_geometric
    geometric_le_polygon := geometric_le_polygon
  }
  simpa [ExplicitBoundaryData.counts, ExplicitBoundaryData.vertexSet] using
    D.lowDegreeWithHighDegreeSlack

theorem subpolygonLowDegree_of_explicitBoundaryData
    (boundary : BoundaryCycle G)
    (vertices : Finset (Fin n))
    (boundary_subset : boundary.vertexFinset ⊆ vertices)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      (countsOfBoundaryData boundary vertices boundary_subset).forcedSubpolygonAngleSum <=
        geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <=
        (countsOfBoundaryData boundary vertices boundary_subset).polygonAngleSum) :
    6 <=
      2 * (countsOfBoundaryData boundary vertices boundary_subset).D2 +
        (countsOfBoundaryData boundary vertices boundary_subset).D3 := by
  let D : ExplicitBoundaryData G := {
    boundary := boundary
    vertices := vertices
    boundary_subset := boundary_subset
    geometricAngleSum := geometricAngleSum
    forced_le_geometric := forced_le_geometric
    geometric_le_polygon := geometric_le_polygon
  }
  simpa [ExplicitBoundaryData.counts, ExplicitBoundaryData.vertexSet] using
    D.lowDegree

def countsOfFaceBoundaryData
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (face : faceBoundary.Face)
    (vertices : Finset (Fin n))
    (boundary_subset :
      (boundaryCycleOfFaceBoundary faceBoundary face).vertexFinset ⊆
        vertices) :
    SubpolygonDegreeCounts :=
  countsOfBoundaryData (boundaryCycleOfFaceBoundary faceBoundary face)
    vertices boundary_subset

structure ExplicitFaceBoundaryData
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) where
  face : faceBoundary.Face
  vertices : Finset (Fin n)
  boundary_subset :
    (boundaryCycleOfFaceBoundary faceBoundary face).vertexFinset ⊆ vertices
  geometricAngleSum : Real
  forced_le_geometric :
    (countsOfFaceBoundaryData
      faceBoundary face vertices boundary_subset).forcedSubpolygonAngleSum <=
      geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <=
      (countsOfFaceBoundaryData
        faceBoundary face vertices boundary_subset).polygonAngleSum

namespace ExplicitFaceBoundaryData

variable {faceBoundary : UnitDistanceFaceBoundaryHypotheses G}

def boundary (D : ExplicitFaceBoundaryData faceBoundary) :
    BoundaryCycle G :=
  boundaryCycleOfFaceBoundary faceBoundary D.face

def toExplicitBoundaryData
    (D : ExplicitFaceBoundaryData faceBoundary) :
    ExplicitBoundaryData G where
  boundary := D.boundary
  vertices := D.vertices
  boundary_subset := D.boundary_subset
  geometricAngleSum := D.geometricAngleSum
  forced_le_geometric := by
    simpa [boundary] using D.forced_le_geometric
  geometric_le_polygon := by
    simpa [boundary] using D.geometric_le_polygon

def vertexSet (D : ExplicitFaceBoundaryData faceBoundary) :
    InducedVertexSet G D.boundary :=
  D.toExplicitBoundaryData.vertexSet

@[simp]
theorem vertexSet_vertices
    (D : ExplicitFaceBoundaryData faceBoundary) :
    D.vertexSet.vertices = D.vertices :=
  rfl

def counts (D : ExplicitFaceBoundaryData faceBoundary) :
    SubpolygonDegreeCounts :=
  D.toExplicitBoundaryData.counts

@[simp]
theorem counts_eq_boundary_counts
    (D : ExplicitFaceBoundaryData faceBoundary) :
    D.counts = D.toExplicitBoundaryData.counts :=
  rfl

theorem angleLowerBound
    (D : ExplicitFaceBoundaryData faceBoundary) :
    D.counts.AngleLowerBound := by
  simpa [counts] using D.toExplicitBoundaryData.angleLowerBound

theorem lowDegreeWithHighDegreeSlack
    (D : ExplicitFaceBoundaryData faceBoundary) :
    D.counts.D5 + 2 * D.counts.D6 + 6 <=
      2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using
    D.toExplicitBoundaryData.lowDegreeWithHighDegreeSlack

theorem lowDegree
    (D : ExplicitFaceBoundaryData faceBoundary) :
    6 <= 2 * D.counts.D2 + D.counts.D3 := by
  simpa [counts] using D.toExplicitBoundaryData.lowDegree

end ExplicitFaceBoundaryData

structure ExplicitBoundaryFamilyData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  Subpolygon : Type u
  data : Subpolygon -> ExplicitBoundaryData G

namespace ExplicitBoundaryFamilyData

def subpolygonCounts
    (F : ExplicitBoundaryFamilyData.{u} G)
    (S : F.Subpolygon) :
    SubpolygonDegreeCounts :=
  (F.data S).counts

theorem subpolygonLowDegreeWithHighDegreeSlack
    (F : ExplicitBoundaryFamilyData.{u} G)
    (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using
    (F.data S).lowDegreeWithHighDegreeSlack

theorem subpolygonLowDegree
    (F : ExplicitBoundaryFamilyData.{u} G)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 +
      (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using (F.data S).lowDegree

end ExplicitBoundaryFamilyData

end

end SubpolygonInstantiationW13
end Swanepoel
end ErdosProblems1066
