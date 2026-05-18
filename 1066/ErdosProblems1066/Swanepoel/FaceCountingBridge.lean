import ErdosProblems1066.Swanepoel.FaceReduction
import ErdosProblems1066.Swanepoel.BoundaryCounting

/-!
# Face-counting bridge for canonical unit-distance graphs

This module gives canonical unit-distance entry points for the existing
face-boundary and boundary-counting interfaces.  The noncrossing hypothesis is
filled from the canonical edge set, while the geometric angle lower bounds used
by the counting theorems remain explicit.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FaceCountingBridge

open PlanarInterface
open FaceReduction
open BoundaryCounting

universe u

noncomputable section

variable {n : Nat}

/-! ## Canonical face-boundary data as planar-interface data -/

/-- Canonical unit-distance face data supplies the old planar interface. -/
def faceBoundaryHypothesesOfCanonical
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (H : UnitDistanceFaceBoundaryHypotheses G) :
    FaceBoundaryHypotheses G.toStraightLine :=
  H.toFaceBoundaryHypotheses

/-- The canonical edge set is noncrossing, without an extra hypothesis. -/
theorem pairwiseNoncrossingOfCanonical
    (G : CanonicalStraightLineUnitDistanceGraph n) :
    PairwiseNoncrossing G.config G.edgeSet :=
  G.pairwiseNoncrossing

/-- Disjoint canonical unit-distance edges do not cross. -/
theorem noCrossingOfCanonicalDisjoint
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (_H : UnitDistanceFaceBoundaryHypotheses G)
    {e f : Edge n} (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet)
    (hdisj : EdgeVertexDisjoint e f) :
    Not (EdgeSegmentsCross G.config e f) :=
  G.pairwiseNoncrossing e he f hf hdisj

/-- Boundary adjacency in canonical face data is unit-distance adjacency. -/
theorem boundaryAdjUnitDistanceAdjOfCanonical
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (H : UnitDistanceFaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    GraphBridge.UnitDistanceAdj G.config (H.boundaryVertex F k)
      (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k)) :=
  H.boundary_adj_unitDistanceAdj F k

/-- Boundary edges in canonical face data have geometric length one. -/
theorem boundaryEdgeGeometryDistEqOneOfCanonical
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (H : UnitDistanceFaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    Geometry.Distance.eucDist
        (G.point (H.boundaryVertex F k))
        (G.point (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k))) = 1 :=
  H.boundary_edge_geometry_dist_eq_one F k

/-- Boundary edges in canonical face data have root Euclidean length one. -/
theorem boundaryEdgeRootDistEqOneOfCanonical
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (H : UnitDistanceFaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    _root_.eucDist
        (G.point (H.boundaryVertex F k))
        (G.point (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k))) = 1 :=
  H.boundary_edge_root_dist_eq_one F k

/-! ## Boundary-counting packages with canonical face data -/

/--
Canonical face-boundary data together with the angle lower bound used by the
outer-boundary count.
-/
structure CanonicalBoundaryCountHypotheses
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  counts : BoundaryCounts
  angleLowerBound : BoundaryCounts.AngleLowerBound counts

namespace CanonicalBoundaryCountHypotheses

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Forget to the original planar face-boundary interface. -/
def toFaceBoundaryHypotheses (H : CanonicalBoundaryCountHypotheses G) :
    FaceBoundaryHypotheses G.toStraightLine :=
  H.faceBoundary.toFaceBoundaryHypotheses

/-- The canonical noncrossing fact packaged with boundary-count data. -/
theorem noncrossing (_H : CanonicalBoundaryCountHypotheses G) :
    PairwiseNoncrossing G.config G.edgeSet :=
  G.pairwiseNoncrossing

/-- Outer-boundary E12 count from canonical face-boundary data. -/
theorem boundaryAngleCountInequality
    (H : CanonicalBoundaryCountHypotheses G) :
    H.counts.d5 + 2 * H.counts.d6 + H.counts.b + H.counts.B + 6 <=
      H.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality H.counts H.angleLowerBound

/-- Negative-element form of the outer-boundary E12 count. -/
theorem boundaryNegativeCountInequality
    (H : CanonicalBoundaryCountHypotheses G) :
    H.counts.negativeCount + H.counts.B + 6 <= H.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality H.counts H.angleLowerBound

end CanonicalBoundaryCountHypotheses

/-- Direct E12 entry point with reduced canonical face-boundary hypotheses. -/
theorem boundaryAngleCountInequalityOfCanonicalFaces
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (_H : UnitDistanceFaceBoundaryHypotheses G)
    (c : BoundaryCounts) (hangle : BoundaryCounts.AngleLowerBound c) :
    c.d5 + 2 * c.d6 + c.b + c.B + 6 <= c.d3 :=
  BoundaryCounts.boundary_angle_count_inequality c hangle

/-- Direct negative-count E12 entry point with reduced canonical hypotheses. -/
theorem boundaryNegativeCountInequalityOfCanonicalFaces
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (_H : UnitDistanceFaceBoundaryHypotheses G)
    (c : BoundaryCounts) (hangle : BoundaryCounts.AngleLowerBound c) :
    c.negativeCount + c.B + 6 <= c.d3 :=
  BoundaryCounts.boundary_negative_count_inequality c hangle

/-! ## Subpolygon count packages with canonical face data -/

/--
Canonical face-boundary data together with the angle lower bound used by the
subpolygon boundary count.
-/
structure CanonicalSubpolygonCountHypotheses
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  counts : SubpolygonDegreeCounts
  angleLowerBound : SubpolygonDegreeCounts.AngleLowerBound counts

namespace CanonicalSubpolygonCountHypotheses

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Forget to the original planar face-boundary interface. -/
def toFaceBoundaryHypotheses (H : CanonicalSubpolygonCountHypotheses G) :
    FaceBoundaryHypotheses G.toStraightLine :=
  H.faceBoundary.toFaceBoundaryHypotheses

/-- The canonical noncrossing fact packaged with subpolygon count data. -/
theorem noncrossing (_H : CanonicalSubpolygonCountHypotheses G) :
    PairwiseNoncrossing G.config G.edgeSet :=
  G.pairwiseNoncrossing

/-- E13 with high-degree slack from canonical face-boundary data. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (H : CanonicalSubpolygonCountHypotheses G) :
    H.counts.D5 + 2 * H.counts.D6 + 6 <=
      2 * H.counts.D2 + H.counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    H.counts H.angleLowerBound

/-- Swanepoel Lemma 4 counting conclusion from canonical face-boundary data. -/
theorem subpolygonLowDegreeInequality
    (H : CanonicalSubpolygonCountHypotheses G) :
    6 <= 2 * H.counts.D2 + H.counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    H.counts H.angleLowerBound

end CanonicalSubpolygonCountHypotheses

/-- Direct strengthened E13 entry point with reduced canonical hypotheses. -/
theorem subpolygonLowDegreeWithHighDegreeSlackOfCanonicalFaces
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (_H : UnitDistanceFaceBoundaryHypotheses G)
    (c : SubpolygonDegreeCounts)
    (hangle : SubpolygonDegreeCounts.AngleLowerBound c) :
    c.D5 + 2 * c.D6 + 6 <= 2 * c.D2 + c.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack c hangle

/-- Direct E13 entry point with reduced canonical face-boundary hypotheses. -/
theorem subpolygonLowDegreeInequalityOfCanonicalFaces
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (_H : UnitDistanceFaceBoundaryHypotheses G)
    (c : SubpolygonDegreeCounts)
    (hangle : SubpolygonDegreeCounts.AngleLowerBound c) :
    6 <= 2 * c.D2 + c.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality c hangle

end

end FaceCountingBridge
end Swanepoel
end ErdosProblems1066
