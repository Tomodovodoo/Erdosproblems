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

/-- Equality of vertices on an injectively indexed boundary cycle is exactly
equality of the cyclic indices. -/
theorem vertex_eq_iff_index_eq
    (C : BoundaryCycle G) {i j : Fin C.length} :
    C.vertex i = C.vertex j <-> i = j := by
  constructor
  · intro h
    exact C.simple h
  · intro h
    subst h
    rfl

/-- Distinct cyclic indices give distinct boundary vertices. -/
theorem vertex_ne_of_index_ne
    (C : BoundaryCycle G) {i j : Fin C.length} (hij : i ≠ j) :
    C.vertex i ≠ C.vertex j := by
  intro h
  exact hij (C.simple h)

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

namespace OuterBoundaryEnclosure

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {H : UnitDistanceFaceBoundaryHypotheses G} {F : H.Face}

/-- The boundary cycle whose predicates are recorded by an enclosure. -/
def boundaryCycle (_ : OuterBoundaryEnclosure G H F) : BoundaryCycle G :=
  BoundaryCycle.ofFaceBoundary H F

/-- Recorded boundary vertices satisfy the enclosure's boundary predicate. -/
theorem boundaryCycle_vertex_onBoundary
    (E : OuterBoundaryEnclosure G H F) (k : Fin E.boundaryCycle.length) :
    E.onBoundary (E.boundaryCycle.vertex k) := by
  simpa [boundaryCycle, BoundaryCycle.ofFaceBoundary] using
    E.boundary_vertex_onBoundary k

/-- Recorded boundary vertices lie in the enclosed region. -/
theorem boundaryCycle_point_insideOrOn
    (E : OuterBoundaryEnclosure G H F) (k : Fin E.boundaryCycle.length) :
    E.insideOrOn (E.boundaryCycle.point k) := by
  simpa [boundaryCycle, BoundaryCycle.point, BoundaryCycle.ofFaceBoundary] using
    E.boundary_point_insideOrOn k

/-- The enclosure boundary predicate is exactly membership in the recorded
boundary cycle. -/
theorem onBoundary_iff_boundaryCycle
    (E : OuterBoundaryEnclosure G H F) (v : Fin n) :
    E.onBoundary v <->
      Exists fun k : Fin E.boundaryCycle.length => E.boundaryCycle.vertex k = v := by
  simpa [boundaryCycle, BoundaryCycle.ofFaceBoundary] using
    E.onBoundary_iff_outer_cycle v

/-- Extract the boundary-cycle index of a vertex known to lie on the boundary. -/
theorem exists_boundaryCycle_vertex_eq_of_onBoundary
    (E : OuterBoundaryEnclosure G H F) {v : Fin n} (hv : E.onBoundary v) :
    Exists fun k : Fin E.boundaryCycle.length => E.boundaryCycle.vertex k = v :=
  (E.onBoundary_iff_boundaryCycle v).1 hv

/-- A vertex equal to a recorded cycle vertex lies on the enclosure boundary. -/
theorem onBoundary_of_boundaryCycle_vertex_eq
    (E : OuterBoundaryEnclosure G H F) {k : Fin E.boundaryCycle.length}
    {v : Fin n} (hv : E.boundaryCycle.vertex k = v) :
    E.onBoundary v :=
  (E.onBoundary_iff_boundaryCycle v).2 (Exists.intro k hv)

/-- Boundary vertices lie inside-or-on the enclosed region, transported through
the boundary predicate. -/
theorem insideOrOn_of_onBoundary
    (E : OuterBoundaryEnclosure G H F) {v : Fin n} (hv : E.onBoundary v) :
    E.insideOrOn (G.point v) := by
  rcases E.exists_boundaryCycle_vertex_eq_of_onBoundary hv with ⟨k, hk⟩
  rw [← hk]
  simpa [BoundaryCycle.point] using E.boundaryCycle_point_insideOrOn k

end OuterBoundaryEnclosure

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

/-- Boundary vertices of a subpolygon lie in its enclosed region. -/
theorem boundary_point_insideOrOn
    (S : SubpolygonData G) (k : Fin S.boundary.length) :
    S.insideOrOn (G.point (S.boundary.vertex k)) :=
  S.vertices_insideOrOn (S.boundary.vertex k) (S.boundary_vertices_mem k)

/-- Extract the boundary-cycle index of a vertex known to lie on a subpolygon
boundary. -/
theorem exists_boundaryIndex_of_onBoundary
    (S : SubpolygonData G) {v : Fin n} (hv : S.onBoundary v) :
    Exists fun k : Fin S.boundary.length => S.boundary.vertex k = v :=
  (S.onBoundary_iff_cycle v).1 hv

/-- A vertex equal to a recorded subpolygon cycle vertex lies on that
subpolygon boundary. -/
theorem onBoundary_of_boundary_vertex_eq
    (S : SubpolygonData G) {k : Fin S.boundary.length} {v : Fin n}
    (hv : S.boundary.vertex k = v) :
    S.onBoundary v :=
  (S.onBoundary_iff_cycle v).2 (Exists.intro k hv)

/-- Subpolygon boundary vertices lie inside-or-on the subpolygon region,
transported through the boundary predicate. -/
theorem insideOrOn_of_onBoundary
    (S : SubpolygonData G) {v : Fin n} (hv : S.onBoundary v) :
    S.insideOrOn (G.point v) := by
  rcases S.exists_boundaryIndex_of_onBoundary hv with ⟨k, hk⟩
  rw [← hk]
  exact S.boundary_point_insideOrOn k

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

/-- Recorded vertices of the selected outer cycle satisfy the package's
boundary predicate. -/
theorem outerCycle_vertex_onBoundary
    (P : OuterBoundaryPackage G) (k : Fin P.outerCycle.length) :
    P.outerEnclosure.onBoundary (P.outerCycle.vertex k) := by
  simpa [outerCycle, OuterBoundaryEnclosure.boundaryCycle] using
    P.outerEnclosure.boundaryCycle_vertex_onBoundary k

/-- Recorded vertices of the selected outer cycle lie inside-or-on the
package's enclosed region. -/
theorem outerCycle_point_insideOrOn
    (P : OuterBoundaryPackage G) (k : Fin P.outerCycle.length) :
    P.outerEnclosure.insideOrOn (P.outerCycle.point k) := by
  simpa [outerCycle, OuterBoundaryEnclosure.boundaryCycle] using
    P.outerEnclosure.boundaryCycle_point_insideOrOn k

/-- Every graph vertex lies inside-or-on the selected outer enclosure. -/
theorem all_vertices_insideOrOn
    (P : OuterBoundaryPackage G) (v : Fin n) :
    P.outerEnclosure.insideOrOn (G.point v) :=
  P.outerEnclosure.all_vertices_insideOrOn v

/-- The package boundary predicate is exactly membership in the selected outer
cycle. -/
theorem onBoundary_iff_outerCycle
    (P : OuterBoundaryPackage G) (v : Fin n) :
    P.outerEnclosure.onBoundary v <->
      Exists fun k : Fin P.outerCycle.length => P.outerCycle.vertex k = v := by
  simpa [outerCycle, OuterBoundaryEnclosure.boundaryCycle] using
    P.outerEnclosure.onBoundary_iff_boundaryCycle v

/-- Extract the selected outer-cycle index of a vertex known to lie on the
package boundary. -/
theorem exists_outerCycle_vertex_eq_of_onBoundary
    (P : OuterBoundaryPackage G) {v : Fin n}
    (hv : P.outerEnclosure.onBoundary v) :
    Exists fun k : Fin P.outerCycle.length => P.outerCycle.vertex k = v :=
  (P.onBoundary_iff_outerCycle v).1 hv

/-- A vertex equal to a recorded selected outer-cycle vertex lies on the
package boundary. -/
theorem onBoundary_of_outerCycle_vertex_eq
    (P : OuterBoundaryPackage G) {k : Fin P.outerCycle.length} {v : Fin n}
    (hv : P.outerCycle.vertex k = v) :
    P.outerEnclosure.onBoundary v :=
  (P.onBoundary_iff_outerCycle v).2 (Exists.intro k hv)

/-- Boundary vertices of the selected outer cycle lie inside-or-on the selected
outer enclosure, transported through the boundary predicate. -/
theorem insideOrOn_of_onBoundary
    (P : OuterBoundaryPackage G) {v : Fin n}
    (hv : P.outerEnclosure.onBoundary v) :
    P.outerEnclosure.insideOrOn (G.point v) :=
  P.outerEnclosure.insideOrOn_of_onBoundary hv

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
