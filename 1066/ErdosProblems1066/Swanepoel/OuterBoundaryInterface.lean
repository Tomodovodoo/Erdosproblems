import ErdosProblems1066.Swanepoel.FaceCountingBridge

/-!
# Explicit outer-boundary interface for the Swanepoel route

This module starts the outer-boundary/simple-polygon route without constructing
faces.  The central package records the boundary cycle, simple-polygon and
enclosure data, subpolygon witnesses, degree counts, and the angle lower-bound
hypotheses as explicit fields.  The only conclusions proved here are projections
and routes into the already checked counting interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryInterface

open PlanarInterface
open FaceReduction
open BoundaryCounting

universe u

noncomputable section

variable {n : Nat}

/-! ## Boundary cycles and simple polygon data -/

/-- A concrete cyclic boundary walk in a canonical unit-distance graph. -/
structure BoundaryCycle (G : CanonicalStraightLineUnitDistanceGraph n) where
  length : Nat
  length_pos : 0 < length
  vertex : Fin length -> Fin n
  adjacent :
    forall k : Fin length,
      G.Adj (vertex k) (vertex (cyclicSucc length_pos k))
  simple : Function.Injective vertex

namespace BoundaryCycle

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The geometric point of a boundary vertex. -/
def point (C : BoundaryCycle G) (k : Fin C.length) : Point :=
  G.point (C.vertex k)

/-- The next boundary vertex is unit-distance adjacent. -/
theorem adjacent_unitDistanceAdj (C : BoundaryCycle G) (k : Fin C.length) :
    GraphBridge.UnitDistanceAdj G.config (C.vertex k)
      (C.vertex (cyclicSucc C.length_pos k)) :=
  (G.adj_iff_unitDistanceAdj _ _).1 (C.adjacent k)

/-- Boundary-cycle edges have Euclidean length one. -/
theorem edge_geometry_dist_eq_one (C : BoundaryCycle G) (k : Fin C.length) :
    Geometry.Distance.eucDist (C.point k)
      (C.point (cyclicSucc C.length_pos k)) = 1 :=
  G.adj_geometry_dist_eq_one (C.adjacent k)

/-- The boundary cycle attached to a recorded face-boundary witness. -/
def ofFaceBoundary
    (H : UnitDistanceFaceBoundaryHypotheses G) (F : H.Face) :
    BoundaryCycle G where
  length := H.boundaryLength F
  length_pos := H.boundaryLength_pos F
  vertex := H.boundaryVertex F
  adjacent := H.boundaryAdjacent F
  simple := H.boundarySimple F

end BoundaryCycle

/-- Two boundary edges are adjacent in the cyclic index set. -/
def CyclicEdgesAdjacent {m : Nat} (hm : 0 < m) (i j : Fin m) : Prop :=
  i = j \/ cyclicSucc hm i = j \/ cyclicSucc hm j = i

/-- Two boundary edges are separated in the cyclic index set. -/
def CyclicEdgesSeparated {m : Nat} (hm : 0 < m) (i j : Fin m) : Prop :=
  Not (CyclicEdgesAdjacent hm i j)

/-- A Lean-friendly simple polygon witness for a boundary cycle.

The geometric noncrossing assertion is only recorded for separated boundary
edges; it is not derived here.
-/
structure SimplePolygon
    (G : CanonicalStraightLineUnitDistanceGraph n) (C : BoundaryCycle G) where
  vertices_injective : Function.Injective C.vertex
  separated_edges_do_not_cross :
    forall i j : Fin C.length,
      CyclicEdgesSeparated C.length_pos i j ->
        Not (SegmentsCrossInterior
          (C.point i) (C.point (cyclicSucc C.length_pos i))
          (C.point j) (C.point (cyclicSucc C.length_pos j)))

/-- Outer-boundary enclosure data.

`insideOrOn` and `onBoundary` are supplied predicates; this interface merely
records the facts downstream arguments are allowed to use.
-/
structure OuterBoundaryEnclosure
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (H : UnitDistanceFaceBoundaryHypotheses G) (F : H.Face) where
  insideOrOn : Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin (H.boundaryLength F), onBoundary (H.boundaryVertex F k)
  boundary_point_insideOrOn :
    forall k : Fin (H.boundaryLength F),
      insideOrOn (G.point (H.boundaryVertex F k))
  all_vertices_insideOrOn :
    forall v : Fin n, insideOrOn (G.point v)
  onBoundary_iff_outer_cycle :
    forall v : Fin n,
      onBoundary v <->
        Exists fun k : Fin (H.boundaryLength F) => H.boundaryVertex F k = v

/-! ## Subpolygon data -/

/-- Explicit data for one subpolygon boundary and its degree count. -/
structure SubpolygonData (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  simplePolygon : SimplePolygon G boundary
  vertexSet : Finset (Fin n)
  boundary_vertices_mem :
    forall k : Fin boundary.length, boundary.vertex k ∈ vertexSet
  insideOrOn : Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin boundary.length, onBoundary (boundary.vertex k)
  vertices_insideOrOn :
    forall v : Fin n, v ∈ vertexSet -> insideOrOn (G.point v)
  onBoundary_iff_cycle :
    forall v : Fin n,
      onBoundary v <-> Exists fun k : Fin boundary.length => boundary.vertex k = v
  counts : SubpolygonDegreeCounts
  angleLowerBound : counts.AngleLowerBound

namespace SubpolygonData

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- A subpolygon supplies the canonical subpolygon-count package. -/
def toCanonicalSubpolygonCountHypotheses
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (S : SubpolygonData G) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G where
  faceBoundary := faceBoundary
  counts := S.counts
  angleLowerBound := S.angleLowerBound

/-- Route a subpolygon witness through the face-counting bridge. -/
theorem lowDegreeWithHighDegreeSlack_viaFaceCountingBridge
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (S : SubpolygonData G) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 :=
  (S.toCanonicalSubpolygonCountHypotheses faceBoundary).subpolygonLowDegreeWithHighDegreeSlack

/-- Route a subpolygon witness directly through the boundary-counting theorem. -/
theorem lowDegreeWithHighDegreeSlack_viaBoundaryCounting
    (S : SubpolygonData G) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    S.counts S.angleLowerBound

/-- Swanepoel Lemma 4 counting conclusion through the face-counting bridge. -/
theorem lowDegreeInequality_viaFaceCountingBridge
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (S : SubpolygonData G) :
    6 <= 2 * S.counts.D2 + S.counts.D3 :=
  (S.toCanonicalSubpolygonCountHypotheses faceBoundary).subpolygonLowDegreeInequality

/-- Swanepoel Lemma 4 counting conclusion directly through boundary counting. -/
theorem lowDegreeInequality_viaBoundaryCounting
    (S : SubpolygonData G) :
    6 <= 2 * S.counts.D2 + S.counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    S.counts S.angleLowerBound

end SubpolygonData

/-! ## Full explicit outer-boundary package -/

/-- Explicit data for the outer-boundary/face construction route.

This structure deliberately contains no face-existence theorem.  A caller must
supply the face-boundary interface, the selected outer face, simple-polygon and
enclosure witnesses, subpolygon witnesses, and the angle lower bounds.
-/
structure OuterBoundaryPackage
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerSimplePolygon :
    SimplePolygon G (BoundaryCycle.ofFaceBoundary faceBoundary outerFace)
  outerEnclosure : OuterBoundaryEnclosure G faceBoundary outerFace
  boundaryCounts : BoundaryCounts
  boundaryAngleLowerBound : boundaryCounts.AngleLowerBound
  Subpolygon : Type u
  subpolygonData : Subpolygon -> SubpolygonData G

namespace OuterBoundaryPackage

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The recorded outer boundary cycle. -/
def outerCycle (P : OuterBoundaryPackage G) : BoundaryCycle G :=
  BoundaryCycle.ofFaceBoundary P.faceBoundary P.outerFace

/-- Forget to the original planar face-boundary interface. -/
def toFaceBoundaryHypotheses (P : OuterBoundaryPackage G) :
    FaceBoundaryHypotheses G.toStraightLine :=
  P.faceBoundary.toFaceBoundaryHypotheses

/-- Package the outer-boundary counts for the canonical face-counting bridge. -/
def toCanonicalBoundaryCountHypotheses (P : OuterBoundaryPackage G) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G where
  faceBoundary := P.faceBoundary
  counts := P.boundaryCounts
  angleLowerBound := P.boundaryAngleLowerBound

/-- Package one subpolygon's counts for the canonical face-counting bridge. -/
def subpolygonCountHypotheses
    (P : OuterBoundaryPackage G) (S : P.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  (P.subpolygonData S).toCanonicalSubpolygonCountHypotheses P.faceBoundary

/-- The outer boundary cycle is simple at the vertex level. -/
theorem outerCycle_vertex_injective (P : OuterBoundaryPackage G) :
    Function.Injective P.outerCycle.vertex :=
  P.faceBoundary.boundarySimple P.outerFace

/-- Boundary adjacency on the selected outer cycle is unit-distance adjacency. -/
theorem outerCycle_adjacent_unitDistanceAdj
    (P : OuterBoundaryPackage G) (k : Fin P.outerCycle.length) :
    GraphBridge.UnitDistanceAdj G.config (P.outerCycle.vertex k)
      (P.outerCycle.vertex (cyclicSucc P.outerCycle.length_pos k)) :=
  P.outerCycle.adjacent_unitDistanceAdj k

/-- Boundary edges on the selected outer cycle have Euclidean length one. -/
theorem outerCycle_edge_geometry_dist_eq_one
    (P : OuterBoundaryPackage G) (k : Fin P.outerCycle.length) :
    Geometry.Distance.eucDist (P.outerCycle.point k)
      (P.outerCycle.point (cyclicSucc P.outerCycle.length_pos k)) = 1 :=
  P.outerCycle.edge_geometry_dist_eq_one k

/-- Route the outer-boundary E12 inequality through the face-counting bridge. -/
theorem boundaryAngleCountInequality_viaFaceCountingBridge
    (P : OuterBoundaryPackage G) :
    P.boundaryCounts.d5 + 2 * P.boundaryCounts.d6 +
        P.boundaryCounts.b + P.boundaryCounts.B + 6 <=
      P.boundaryCounts.d3 :=
  P.toCanonicalBoundaryCountHypotheses.boundaryAngleCountInequality

/-- Route the outer-boundary E12 inequality directly through boundary counting. -/
theorem boundaryAngleCountInequality_viaBoundaryCounting
    (P : OuterBoundaryPackage G) :
    P.boundaryCounts.d5 + 2 * P.boundaryCounts.d6 +
        P.boundaryCounts.b + P.boundaryCounts.B + 6 <=
      P.boundaryCounts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality
    P.boundaryCounts P.boundaryAngleLowerBound

/-- Route the negative-element E12 form through the face-counting bridge. -/
theorem boundaryNegativeCountInequality_viaFaceCountingBridge
    (P : OuterBoundaryPackage G) :
    P.boundaryCounts.negativeCount + P.boundaryCounts.B + 6 <=
      P.boundaryCounts.d3 :=
  P.toCanonicalBoundaryCountHypotheses.boundaryNegativeCountInequality

/-- Route the negative-element E12 form directly through boundary counting. -/
theorem boundaryNegativeCountInequality_viaBoundaryCounting
    (P : OuterBoundaryPackage G) :
    P.boundaryCounts.negativeCount + P.boundaryCounts.B + 6 <=
      P.boundaryCounts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    P.boundaryCounts P.boundaryAngleLowerBound

/-- Route a recorded subpolygon through the face-counting bridge. -/
theorem subpolygonLowDegreeWithHighDegreeSlack_viaFaceCountingBridge
    (P : OuterBoundaryPackage G) (S : P.Subpolygon) :
    (P.subpolygonData S).counts.D5 + 2 * (P.subpolygonData S).counts.D6 + 6 <=
      2 * (P.subpolygonData S).counts.D2 + (P.subpolygonData S).counts.D3 :=
  (P.subpolygonCountHypotheses S).subpolygonLowDegreeWithHighDegreeSlack

/-- Route a recorded subpolygon directly through boundary counting. -/
theorem subpolygonLowDegreeWithHighDegreeSlack_viaBoundaryCounting
    (P : OuterBoundaryPackage G) (S : P.Subpolygon) :
    (P.subpolygonData S).counts.D5 + 2 * (P.subpolygonData S).counts.D6 + 6 <=
      2 * (P.subpolygonData S).counts.D2 + (P.subpolygonData S).counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    (P.subpolygonData S).counts (P.subpolygonData S).angleLowerBound

/-- Route the Lemma 4 low-degree conclusion through the face-counting bridge. -/
theorem subpolygonLowDegreeInequality_viaFaceCountingBridge
    (P : OuterBoundaryPackage G) (S : P.Subpolygon) :
    6 <= 2 * (P.subpolygonData S).counts.D2 + (P.subpolygonData S).counts.D3 :=
  (P.subpolygonCountHypotheses S).subpolygonLowDegreeInequality

/-- Route the Lemma 4 low-degree conclusion directly through boundary counting. -/
theorem subpolygonLowDegreeInequality_viaBoundaryCounting
    (P : OuterBoundaryPackage G) (S : P.Subpolygon) :
    6 <= 2 * (P.subpolygonData S).counts.D2 + (P.subpolygonData S).counts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    (P.subpolygonData S).counts (P.subpolygonData S).angleLowerBound

end OuterBoundaryPackage

end

end OuterBoundaryInterface
end Swanepoel
end ErdosProblems1066
