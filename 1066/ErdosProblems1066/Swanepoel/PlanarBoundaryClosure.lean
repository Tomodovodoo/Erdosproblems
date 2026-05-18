import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.OuterBoundaryAssembly
import ErdosProblems1066.Swanepoel.OuterBoundaryAngleClosure
import ErdosProblems1066.Swanepoel.SubpolygonAssembly

set_option autoImplicit false

/-!
# Conditional planar boundary closure

This module is the final conditional adapter for the Swanepoel planar-boundary
route currently needed by `FaceCountingBridge`.

It deliberately keeps the topological input explicit.  The caller still
supplies the face-boundary data, the selected outer face, and the recorded
outer enclosure through `OuterBoundaryCore`; this file only combines that
explicit planar/Jordan-style data with the finite boundary bookkeeping, outer
angle comparisons, and supplied subpolygon cycle/count/angle data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarBoundaryClosure

open BoundaryCounting

universe u

noncomputable section

variable {n : Nat}

/--
The complete conditional planar-boundary data needed to feed Swanepoel's
face-counting bridge.

The `core` field is the explicit face/Jordan-style part: it contains the
face-boundary witness, the chosen outer face, the proof that it is outer, and
the enclosure predicates.  The remaining fields are finite count and angle
data already assembled by the outer-boundary and subpolygon layers.
-/
structure PlanarBoundaryData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  core : OuterBoundaryCore G
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G

/--
The exact `FaceCountingBridge` inputs obtained from the explicit
planar-boundary data.

This structure keeps both the outer-boundary count package and all subpolygon
count packages tied to the same supplied face-boundary witness.
-/
structure FaceCountingBridgeData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : FaceReduction.UnitDistanceFaceBoundaryHypotheses G
  planarFaceBoundary :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine
  boundaryCounts :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G
  Subpolygon : Type u
  subpolygonCounts :
    Subpolygon -> FaceCountingBridge.CanonicalSubpolygonCountHypotheses G
  boundary_faceBoundary_eq :
    boundaryCounts.faceBoundary = faceBoundary
  subpolygon_faceBoundary_eq :
    forall S : Subpolygon, (subpolygonCounts S).faceBoundary = faceBoundary

namespace FaceCountingBridgeData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The outer-boundary counts retained by a bridge package. -/
def outerCounts (H : FaceCountingBridgeData.{u} G) :
    BoundaryCounts :=
  H.boundaryCounts.counts

/-- The subpolygon counts retained by a bridge package. -/
def subpolygonDegreeCounts
    (H : FaceCountingBridgeData.{u} G) (S : H.Subpolygon) :
    SubpolygonDegreeCounts :=
  (H.subpolygonCounts S).counts

/-- E12 for the outer-boundary counts retained by a bridge package. -/
theorem boundaryAngleCount
    (H : FaceCountingBridgeData.{u} G) :
    H.outerCounts.d5 + 2 * H.outerCounts.d6 +
        H.outerCounts.b + H.outerCounts.B + 6 <=
      H.outerCounts.d3 :=
  H.boundaryCounts.boundaryAngleCountInequality

/-- The negative-element E12 form for the outer-boundary counts retained by a
bridge package. -/
theorem boundaryNegativeCount
    (H : FaceCountingBridgeData.{u} G) :
    H.outerCounts.negativeCount + H.outerCounts.B + 6 <=
      H.outerCounts.d3 :=
  H.boundaryCounts.boundaryNegativeCountInequality

/-- E13 with high-degree slack for the subpolygon counts retained by a bridge
package. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (H : FaceCountingBridgeData.{u} G) (S : H.Subpolygon) :
    (H.subpolygonDegreeCounts S).D5 +
        2 * (H.subpolygonDegreeCounts S).D6 + 6 <=
      2 * (H.subpolygonDegreeCounts S).D2 +
        (H.subpolygonDegreeCounts S).D3 :=
  (H.subpolygonCounts S).subpolygonLowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for the subpolygon counts
retained by a bridge package. -/
theorem subpolygonLowDegree
    (H : FaceCountingBridgeData.{u} G) (S : H.Subpolygon) :
    6 <= 2 * (H.subpolygonDegreeCounts S).D2 +
      (H.subpolygonDegreeCounts S).D3 :=
  (H.subpolygonCounts S).subpolygonLowDegreeInequality

/-- Proposition-valued summary of the checked counting conclusions available
from a face-counting bridge package. -/
structure CountingTheorems (H : FaceCountingBridgeData.{u} G) : Prop where
  boundaryAngleCount :
    H.outerCounts.d5 + 2 * H.outerCounts.d6 +
        H.outerCounts.b + H.outerCounts.B + 6 <=
      H.outerCounts.d3
  boundaryNegativeCount :
    H.outerCounts.negativeCount + H.outerCounts.B + 6 <=
      H.outerCounts.d3
  subpolygonLowDegreeWithHighDegreeSlack :
    forall S : H.Subpolygon,
      (H.subpolygonDegreeCounts S).D5 +
          2 * (H.subpolygonDegreeCounts S).D6 + 6 <=
        2 * (H.subpolygonDegreeCounts S).D2 +
          (H.subpolygonDegreeCounts S).D3
  subpolygonLowDegree :
    forall S : H.Subpolygon,
      6 <= 2 * (H.subpolygonDegreeCounts S).D2 +
        (H.subpolygonDegreeCounts S).D3

/-- Bundle the bridge package's checked E12/E13 conclusions. -/
theorem countingTheorems
    (H : FaceCountingBridgeData.{u} G) :
    CountingTheorems H where
  boundaryAngleCount := H.boundaryAngleCount
  boundaryNegativeCount := H.boundaryNegativeCount
  subpolygonLowDegreeWithHighDegreeSlack :=
    H.subpolygonLowDegreeWithHighDegreeSlack
  subpolygonLowDegree := H.subpolygonLowDegree

end FaceCountingBridgeData

namespace PlanarBoundaryData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ## Explicit planar and Jordan-style projections -/

/-- The supplied canonical face-boundary witness. -/
def faceBoundary (D : PlanarBoundaryData.{u} G) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses G :=
  D.core.faceBoundary

/-- The same face-boundary witness in the older planar interface. -/
def planarFaceBoundary (D : PlanarBoundaryData.{u} G) :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  D.core.toFaceBoundaryHypotheses

/-- The supplied selected outer face. -/
def outerFace (D : PlanarBoundaryData.{u} G) :
    D.faceBoundary.Face :=
  D.core.outerFace

/-- The supplied proof that the selected face is outer. -/
theorem outerFace_isOuter (D : PlanarBoundaryData.{u} G) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.core.outerFace_isOuter

/-- The selected outer boundary cycle recorded by the face data. -/
def outerCycle (D : PlanarBoundaryData.{u} G) :
    OuterBoundaryInterface.BoundaryCycle G :=
  D.core.outerCycle

/-- The selected outer boundary is vertex-simple. -/
theorem outerCycle_vertex_injective (D : PlanarBoundaryData.{u} G) :
    Function.Injective D.outerCycle.vertex :=
  D.core.outerCycle_vertex_injective

/-- The canonical unit-distance graph supplies the separated-edge
noncrossing witness for the selected outer cycle. -/
def outerSimplePolygon (D : PlanarBoundaryData.{u} G) :
    OuterBoundaryInterface.SimplePolygon G D.outerCycle :=
  D.core.outerSimplePolygon

/-- Boundary vertices of the selected outer face satisfy the supplied boundary
predicate. -/
theorem boundary_vertex_onBoundary
    (D : PlanarBoundaryData.{u} G)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    D.core.outerEnclosure.onBoundary
      (D.faceBoundary.boundaryVertex D.outerFace k) :=
  D.core.boundary_vertex_onBoundary k

/-- Every ambient vertex is inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn
    (D : PlanarBoundaryData.{u} G) (v : Fin n) :
    D.core.outerEnclosure.insideOrOn (G.point v) :=
  D.core.all_vertices_insideOrOn v

/-! ## Outer-boundary assembly and angle closure -/

/-- The realized outer-boundary counts carried by the angle-bound data. -/
def outerBoundaryCounts (D : PlanarBoundaryData.{u} G) :
    BoundaryCounts :=
  D.outerAngleBounds.counts

/-- Convert the explicit outer angle comparisons to the interface package used
by `OuterBoundaryAssembly`. -/
def outerAssemblyRealization (D : PlanarBoundaryData.{u} G) :
    OuterBoundaryAssembly.BoundaryBookkeepingAngleRealization.{u} where
  countsRealization := D.outerAngleBounds.countsRealization
  anglePackage := D.outerAngleBounds.toBoundaryAngleLowerBoundPackage
  angle_counts_eq_realized := rfl

/-- The outer-boundary angle data as the package from
`OuterBoundaryAngleClosure`. -/
def outerAngleData (D : PlanarBoundaryData.{u} G) :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G where
  core := D.core
  angleBounds := D.outerAngleBounds

/-- The face-boundary/count hypotheses assembled from the explicit core and
the outer angle data. -/
def faceBoundaryCountHypotheses (D : PlanarBoundaryData.{u} G) :
    OuterBoundaryAssembly.FaceBoundaryCountHypotheses G :=
  OuterBoundaryAssembly.faceBoundaryCountHypothesesOfCore
    D.core D.outerAssemblyRealization

/-- The canonical outer-boundary count package consumed by
`FaceCountingBridge`. -/
def canonicalBoundaryCountHypotheses (D : PlanarBoundaryData.{u} G) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  D.faceBoundaryCountHypotheses.canonicalBoundaryCounts

/-- The assembled outer-boundary package uses the supplied face-boundary
witness. -/
theorem canonicalBoundaryCountHypotheses_faceBoundary
    (D : PlanarBoundaryData.{u} G) :
    D.canonicalBoundaryCountHypotheses.faceBoundary = D.faceBoundary :=
  rfl

/-- The assembled outer-boundary package uses the realized outer counts. -/
theorem canonicalBoundaryCountHypotheses_counts
    (D : PlanarBoundaryData.{u} G) :
    D.canonicalBoundaryCountHypotheses.counts = D.outerBoundaryCounts :=
  rfl

/-- The outer-boundary E12 inequality, routed through the assembled
`FaceCountingBridge` package. -/
theorem boundaryAngleCountInequality
    (D : PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.d5 + 2 * D.outerBoundaryCounts.d6 +
        D.outerBoundaryCounts.b + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3 :=
  D.canonicalBoundaryCountHypotheses.boundaryAngleCountInequality

/-- The negative-element form of E12, routed through the assembled
`FaceCountingBridge` package. -/
theorem boundaryNegativeCountInequality
    (D : PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.negativeCount + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3 :=
  D.canonicalBoundaryCountHypotheses.boundaryNegativeCountInequality

/-! ## Subpolygon assembly -/

/-- The canonical subpolygon count package consumed by `FaceCountingBridge`. -/
def canonicalSubpolygonCountHypotheses
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  (D.subpolygonData S).toCanonicalSubpolygonCountHypotheses D.faceBoundary

/-- Each assembled subpolygon package uses the same supplied face-boundary
witness as the outer-boundary package. -/
theorem canonicalSubpolygonCountHypotheses_faceBoundary
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.canonicalSubpolygonCountHypotheses S).faceBoundary = D.faceBoundary :=
  rfl

/-- E13 with high-degree slack for any supplied subpolygon. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.D5 +
        2 * (D.subpolygonData S).counts.D6 + 6 <=
      2 * (D.subpolygonData S).counts.D2 +
        (D.subpolygonData S).counts.D3 :=
  (D.canonicalSubpolygonCountHypotheses S).subpolygonLowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for any supplied subpolygon. -/
theorem subpolygonLowDegreeInequality
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    6 <= 2 * (D.subpolygonData S).counts.D2 +
      (D.subpolygonData S).counts.D3 :=
  (D.canonicalSubpolygonCountHypotheses S).subpolygonLowDegreeInequality

/-! ## Combined bridge data and theorem package -/

/-- Package all assembled inputs for `FaceCountingBridge`. -/
def toFaceCountingBridgeData (D : PlanarBoundaryData.{u} G) :
    FaceCountingBridgeData.{u} G where
  faceBoundary := D.faceBoundary
  planarFaceBoundary := D.planarFaceBoundary
  boundaryCounts := D.canonicalBoundaryCountHypotheses
  Subpolygon := D.Subpolygon
  subpolygonCounts := D.canonicalSubpolygonCountHypotheses
  boundary_faceBoundary_eq := D.canonicalBoundaryCountHypotheses_faceBoundary
  subpolygon_faceBoundary_eq :=
    D.canonicalSubpolygonCountHypotheses_faceBoundary

@[simp]
theorem toFaceCountingBridgeData_faceBoundary
    (D : PlanarBoundaryData.{u} G) :
    D.toFaceCountingBridgeData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_planarFaceBoundary
    (D : PlanarBoundaryData.{u} G) :
    D.toFaceCountingBridgeData.planarFaceBoundary = D.planarFaceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_boundaryCounts
    (D : PlanarBoundaryData.{u} G) :
    D.toFaceCountingBridgeData.boundaryCounts =
      D.canonicalBoundaryCountHypotheses :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_outerCounts
    (D : PlanarBoundaryData.{u} G) :
    D.toFaceCountingBridgeData.outerCounts = D.outerBoundaryCounts :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_boundaryCounts_faceBoundary
    (D : PlanarBoundaryData.{u} G) :
    D.toFaceCountingBridgeData.boundaryCounts.faceBoundary =
      D.faceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_boundaryCounts_counts
    (D : PlanarBoundaryData.{u} G) :
    D.toFaceCountingBridgeData.boundaryCounts.counts =
      D.outerBoundaryCounts :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_Subpolygon
    (D : PlanarBoundaryData.{u} G) :
    D.toFaceCountingBridgeData.Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonCounts
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    D.toFaceCountingBridgeData.subpolygonCounts S =
      D.canonicalSubpolygonCountHypotheses S :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonDegreeCounts
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    D.toFaceCountingBridgeData.subpolygonDegreeCounts S =
      (D.subpolygonData S).counts :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonCounts_faceBoundary
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.toFaceCountingBridgeData.subpolygonCounts S).faceBoundary =
      D.faceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonCounts_counts
    (D : PlanarBoundaryData.{u} G) (S : D.Subpolygon) :
    (D.toFaceCountingBridgeData.subpolygonCounts S).counts =
      (D.subpolygonData S).counts :=
  rfl

/-- Proposition-valued summary of the strongest checked counting conclusions
available from the explicit planar-boundary data. -/
structure FaceCountingTheorems (D : PlanarBoundaryData.{u} G) : Prop where
  boundaryAngleCount :
    D.outerBoundaryCounts.d5 + 2 * D.outerBoundaryCounts.d6 +
        D.outerBoundaryCounts.b + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3
  boundaryNegativeCount :
    D.outerBoundaryCounts.negativeCount + D.outerBoundaryCounts.B + 6 <=
      D.outerBoundaryCounts.d3
  subpolygonLowDegreeWithHighDegreeSlack :
    forall S : D.Subpolygon,
      (D.subpolygonData S).counts.D5 +
          2 * (D.subpolygonData S).counts.D6 + 6 <=
        2 * (D.subpolygonData S).counts.D2 +
          (D.subpolygonData S).counts.D3
  subpolygonLowDegree :
    forall S : D.Subpolygon,
      6 <= 2 * (D.subpolygonData S).counts.D2 +
        (D.subpolygonData S).counts.D3

namespace FaceCountingTheorems

variable {D : PlanarBoundaryData.{u} G}

/-- Re-index the planar-boundary theorem summary to the assembled bridge
package. -/
theorem toBridgeCountingTheorems
    (H : FaceCountingTheorems D) :
    FaceCountingBridgeData.CountingTheorems D.toFaceCountingBridgeData where
  boundaryAngleCount := by
    simpa using H.boundaryAngleCount
  boundaryNegativeCount := by
    simpa using H.boundaryNegativeCount
  subpolygonLowDegreeWithHighDegreeSlack := by
    intro S
    simpa using H.subpolygonLowDegreeWithHighDegreeSlack S
  subpolygonLowDegree := by
    intro S
    simpa using H.subpolygonLowDegree S

/-- Re-index a bridge theorem summary back to the planar-boundary count
fields. -/
theorem ofBridgeCountingTheorems
    (H : FaceCountingBridgeData.CountingTheorems
      D.toFaceCountingBridgeData) :
    FaceCountingTheorems D where
  boundaryAngleCount := by
    simpa using H.boundaryAngleCount
  boundaryNegativeCount := by
    simpa using H.boundaryNegativeCount
  subpolygonLowDegreeWithHighDegreeSlack := by
    intro S
    simpa using H.subpolygonLowDegreeWithHighDegreeSlack S
  subpolygonLowDegree := by
    intro S
    simpa using H.subpolygonLowDegree S

end FaceCountingTheorems

/--
The combined conditional planar-boundary theorem: explicit face/Jordan-style
outer-boundary data, realized outer angle bounds, and supplied subpolygon
cycle/count/angle data give every `FaceCountingBridge` counting conclusion
currently used downstream.
-/
theorem faceCountingTheorems (D : PlanarBoundaryData.{u} G) :
    FaceCountingTheorems D where
  boundaryAngleCount := D.boundaryAngleCountInequality
  boundaryNegativeCount := D.boundaryNegativeCountInequality
  subpolygonLowDegreeWithHighDegreeSlack :=
    D.subpolygonLowDegreeWithHighDegreeSlack
  subpolygonLowDegree := D.subpolygonLowDegreeInequality

/-- The theorem summary from planar-boundary data, re-indexed to the assembled
face-counting bridge package. -/
theorem faceCountingTheorems_toBridgeCountingTheorems
    (D : PlanarBoundaryData.{u} G) :
    FaceCountingBridgeData.CountingTheorems D.toFaceCountingBridgeData :=
  D.faceCountingTheorems.toBridgeCountingTheorems

/-- The generic bridge theorem package obtained from the assembled
face-counting bridge data. -/
theorem toFaceCountingBridgeData_countingTheorems
    (D : PlanarBoundaryData.{u} G) :
    FaceCountingBridgeData.CountingTheorems D.toFaceCountingBridgeData :=
  D.toFaceCountingBridgeData.countingTheorems

end PlanarBoundaryData

end

end PlanarBoundaryClosure
end Swanepoel
end ErdosProblems1066
