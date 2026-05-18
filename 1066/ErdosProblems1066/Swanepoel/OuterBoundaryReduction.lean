import ErdosProblems1066.Swanepoel.OuterBoundaryInterface

/-!
# Reductions for explicit Swanepoel outer-boundary data

This module removes one redundant hypothesis from the outer-boundary route:
once a boundary cycle in the canonical unit-distance graph is supplied, its
separated boundary edges do not cross.  The proof uses the canonical
minimum-distance noncrossing obstruction, not a face-existence theorem.

The construction records below therefore ask for the same face, enclosure, and
counting data as `OuterBoundaryPackage`, but they do not ask separately for the
outer/simple-polygon witnesses that can be built from the recorded cycles.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryReduction

open PlanarInterface
open FaceReduction
open BoundaryCounting
open OuterBoundaryInterface

universe u

noncomputable section

variable {n : Nat}

/-! ## Cyclic index facts -/

/-- `cyclicSucc` is addition by one in the additive group on `Fin m`. -/
lemma cyclicSucc_eq_add_oneFin {m : Nat} (hm : 0 < m) (i : Fin m) :
    cyclicSucc hm i = i + (Fin.mk (1 % m) (Nat.mod_lt 1 hm)) := by
  ext
  simp [cyclicSucc, Fin.val_add, Nat.add_mod]

/-- The cyclic successor map is injective on a nonempty cyclic index set. -/
lemma cyclicSucc_injective {m : Nat} (hm : 0 < m) :
    Function.Injective (cyclicSucc (m := m) hm) := by
  intro i j h
  have h' :
      i + (Fin.mk (1 % m) (Nat.mod_lt 1 hm)) =
        j + (Fin.mk (1 % m) (Nat.mod_lt 1 hm)) := by
    simpa [cyclicSucc_eq_add_oneFin hm] using h
  exact add_right_cancel h'

/-! ## Boundary cycles give simple polygon noncrossing data -/

namespace BoundaryCycle

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Separated edges of an injectively indexed boundary cycle have no common
endpoint. -/
lemma edgeVertexDisjoint_of_cyclicEdgesSeparated
    (C : BoundaryCycle G) {i j : Fin C.length}
    (hsep : CyclicEdgesSeparated C.length_pos i j) :
    EdgeVertexDisjoint
      (C.vertex i, C.vertex (cyclicSucc C.length_pos i))
      (C.vertex j, C.vertex (cyclicSucc C.length_pos j)) := by
  unfold CyclicEdgesSeparated CyclicEdgesAdjacent at hsep
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hsep (Or.inl (C.simple h))
  · intro h
    exact hsep (Or.inr (Or.inr ((C.simple h).symm)))
  · intro h
    exact hsep (Or.inr (Or.inl (C.simple h)))
  · intro h
    have hsucc : cyclicSucc C.length_pos i = cyclicSucc C.length_pos j :=
      C.simple h
    exact hsep (Or.inl (cyclicSucc_injective C.length_pos hsucc))

/-- A boundary cycle in a canonical unit-distance graph supplies the
`SimplePolygon` noncrossing field for separated boundary edges. -/
def toSimplePolygon (C : BoundaryCycle G) : SimplePolygon G C where
  vertices_injective := C.simple
  separated_edges_do_not_cross := by
    intro i j hsep hcross
    let e : Edge n := (C.vertex i, C.vertex (cyclicSucc C.length_pos i))
    let f : Edge n := (C.vertex j, C.vertex (cyclicSucc C.length_pos j))
    have hdisj : EdgeVertexDisjoint e f := by
      simpa [e, f] using edgeVertexDisjoint_of_cyclicEdgesSeparated C hsep
    have he :
        Geometry.Distance.eucDist (G.config.pts e.1) (G.config.pts e.2) = 1 := by
      simpa [e, BoundaryCycle.point, StraightLineUnitDistanceGraph.point] using
        C.edge_geometry_dist_eq_one i
    have hf :
        Geometry.Distance.eucDist (G.config.pts f.1) (G.config.pts f.2) = 1 := by
      simpa [f, BoundaryCycle.point, StraightLineUnitDistanceGraph.point] using
        C.edge_geometry_dist_eq_one j
    exact
      (NoncrossingUnitEdges.separated_unit_edges_not_cross G.config hdisj he hf)
        hcross

/-- The boundary cycle of recorded face-boundary data supplies the
`SimplePolygon` witness needed by the outer-boundary package. -/
def simplePolygonOfFaceBoundary
    (H : UnitDistanceFaceBoundaryHypotheses G) (F : H.Face) :
    SimplePolygon G (BoundaryCycle.ofFaceBoundary H F) :=
  toSimplePolygon (BoundaryCycle.ofFaceBoundary H F)

end BoundaryCycle

/-! ## Construction records with derived simple-polygon fields -/

/-- Subpolygon data with the simple-polygon witness omitted because it is
derived from the supplied boundary cycle. -/
structure SubpolygonConstructionData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
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

namespace SubpolygonConstructionData

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Fill the original `SubpolygonData` record by deriving the simple-polygon
witness from the boundary cycle. -/
def toSubpolygonData (S : SubpolygonConstructionData G) :
    SubpolygonData G where
  boundary := S.boundary
  simplePolygon := BoundaryCycle.toSimplePolygon S.boundary
  vertexSet := S.vertexSet
  boundary_vertices_mem := S.boundary_vertices_mem
  insideOrOn := S.insideOrOn
  onBoundary := S.onBoundary
  boundary_vertex_onBoundary := S.boundary_vertex_onBoundary
  vertices_insideOrOn := S.vertices_insideOrOn
  onBoundary_iff_cycle := S.onBoundary_iff_cycle
  counts := S.counts
  angleLowerBound := S.angleLowerBound

/-- Route the derived subpolygon package through the existing counting theorem. -/
theorem lowDegreeInequality
    (S : SubpolygonConstructionData G) :
    6 <= 2 * S.counts.D2 + S.counts.D3 :=
  S.toSubpolygonData.lowDegreeInequality_viaBoundaryCounting

end SubpolygonConstructionData

/-- Outer-boundary data with the outer simple-polygon witness, and each
subpolygon simple-polygon witness, derived from the supplied cycles. -/
structure OuterBoundaryConstruction
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure : OuterBoundaryEnclosure G faceBoundary outerFace
  boundaryCounts : BoundaryCounts
  boundaryAngleLowerBound : boundaryCounts.AngleLowerBound
  Subpolygon : Type u
  subpolygonData : Subpolygon -> SubpolygonConstructionData G

namespace OuterBoundaryConstruction

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The recorded outer boundary cycle. -/
def outerCycle (P : OuterBoundaryConstruction G) : BoundaryCycle G :=
  BoundaryCycle.ofFaceBoundary P.faceBoundary P.outerFace

/-- Fill the original `OuterBoundaryPackage` record, deriving all
simple-polygon fields from canonical boundary cycles. -/
def toOuterBoundaryPackage (P : OuterBoundaryConstruction G) :
    OuterBoundaryPackage G where
  faceBoundary := P.faceBoundary
  outerFace := P.outerFace
  outerFace_isOuter := P.outerFace_isOuter
  outerSimplePolygon := BoundaryCycle.simplePolygonOfFaceBoundary
    P.faceBoundary P.outerFace
  outerEnclosure := P.outerEnclosure
  boundaryCounts := P.boundaryCounts
  boundaryAngleLowerBound := P.boundaryAngleLowerBound
  Subpolygon := P.Subpolygon
  subpolygonData := fun S => (P.subpolygonData S).toSubpolygonData

/-- The outer boundary cycle is simple at the vertex level. -/
theorem outerCycle_vertex_injective (P : OuterBoundaryConstruction G) :
    Function.Injective P.outerCycle.vertex :=
  P.toOuterBoundaryPackage.outerCycle_vertex_injective

/-- Route the outer-boundary E12 inequality through the derived package. -/
theorem boundaryAngleCountInequality
    (P : OuterBoundaryConstruction G) :
    P.boundaryCounts.d5 + 2 * P.boundaryCounts.d6 +
        P.boundaryCounts.b + P.boundaryCounts.B + 6 <=
      P.boundaryCounts.d3 :=
  P.toOuterBoundaryPackage.boundaryAngleCountInequality_viaBoundaryCounting

/-- Route a constructed subpolygon through Swanepoel Lemma 4 counting. -/
theorem subpolygonLowDegreeInequality
    (P : OuterBoundaryConstruction G) (S : P.Subpolygon) :
    6 <= 2 * (P.subpolygonData S).counts.D2 + (P.subpolygonData S).counts.D3 :=
  (P.subpolygonData S).lowDegreeInequality

end OuterBoundaryConstruction

end

end OuterBoundaryReduction
end Swanepoel
end ErdosProblems1066
