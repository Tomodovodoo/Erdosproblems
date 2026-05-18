import ErdosProblems1066.Geometry.Distance
import ErdosProblems1066.Swanepoel.GraphBridge

/-!
# Straight-line planar interface for Swanepoel

This file provides a small interface between the finite graph language in
`Swanepoel.GraphBridge` and straight-line geometry.  It intentionally does not
prove planarity or face existence.  Noncrossing, faces, and boundary walks are
recorded as explicit hypotheses for later Swanepoel modules to consume.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarInterface

universe u

noncomputable section

abbrev Point : Type :=
  Prod Real Real

abbrev Edge (n : Nat) : Type :=
  Prod (Fin n) (Fin n)

/-! ## Segment predicates -/

/-- The affine point `(1 - t) a + t b` on the line through `a` and `b`. -/
def segmentPoint (a b : Point) (t : Real) : Point :=
  ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2)

/-- A point lies in the open segment from `a` to `b`. -/
def InOpenSegment (x a b : Point) : Prop :=
  Exists fun t : Real => 0 < t /\ t < 1 /\ x = segmentPoint a b t

/-- Two straight-line segments cross in their relative interiors. -/
def SegmentsCrossInterior (a b c d : Point) : Prop :=
  Exists fun x : Point => InOpenSegment x a b /\ InOpenSegment x c d

/-- Two finite graph edges have no endpoint in common. -/
def EdgeVertexDisjoint {n : Nat} (e f : Edge n) : Prop :=
  e.1 ≠ f.1 /\ e.1 ≠ f.2 /\ e.2 ≠ f.1 /\ e.2 ≠ f.2

/-- The straight-line segments attached to two finite graph edges cross. -/
def EdgeSegmentsCross {n : Nat} (C : _root_.UDConfig n) (e f : Edge n) : Prop :=
  SegmentsCrossInterior (C.pts e.1) (C.pts e.2) (C.pts f.1) (C.pts f.2)

/-- Explicit noncrossing hypothesis for straight-line drawings.

This is deliberately an assumption, not a theorem: the topology proving that a
particular unit-distance drawing is noncrossing belongs in a later module. -/
def PairwiseNoncrossing {n : Nat} (C : _root_.UDConfig n) (edges : Finset (Edge n)) :
    Prop :=
  forall e, e ∈ edges ->
    forall f, f ∈ edges -> EdgeVertexDisjoint e f -> Not (EdgeSegmentsCross C e f)

/-! ## Geometric endpoints of finite graph edges -/

/-- The ordered geometric endpoints of a finite graph edge. -/
def edgeEndpoints {n : Nat} (C : _root_.UDConfig n) (e : Edge n) : Prod Point Point :=
  (C.pts e.1, C.pts e.2)

@[simp]
lemma edgeEndpoints_fst {n : Nat} (C : _root_.UDConfig n) (e : Edge n) :
    (edgeEndpoints C e).1 = C.pts e.1 :=
  rfl

@[simp]
lemma edgeEndpoints_snd {n : Nat} (C : _root_.UDConfig n) (e : Edge n) :
    (edgeEndpoints C e).2 = C.pts e.2 :=
  rfl

lemma geometry_eucDist_eq_root (p q : Point) :
    Geometry.Distance.eucDist p q = _root_.eucDist p q :=
  rfl

lemma unitDistanceAdj_iff_geometry_eucDist {n : Nat} (C : _root_.UDConfig n)
    (i j : Fin n) :
    GraphBridge.UnitDistanceAdj C i j <->
      Geometry.Distance.eucDist (C.pts i) (C.pts j) = 1 := by
  simpa [geometry_eucDist_eq_root] using GraphBridge.unitDistanceAdj_iff C i j

lemma mem_unitDistanceEdges_unitDistanceAdj {n : Nat} (C : _root_.UDConfig n)
    {e : Edge n} (he : e ∈ GraphBridge.unitDistanceEdges C) :
    GraphBridge.UnitDistanceAdj C e.1 e.2 :=
  ((GraphBridge.mem_unitDistanceEdges_iff C e.1 e.2).1 he).2

lemma mem_unitDistanceEdges_endpoints_geometry_dist_eq_one {n : Nat}
    (C : _root_.UDConfig n) {e : Edge n}
    (he : e ∈ GraphBridge.unitDistanceEdges C) :
    Geometry.Distance.eucDist (edgeEndpoints C e).1 (edgeEndpoints C e).2 = 1 :=
  (unitDistanceAdj_iff_geometry_eucDist C e.1 e.2).1
    (mem_unitDistanceEdges_unitDistanceAdj C he)

lemma adjFrom_unitDistanceEdges_geometry_dist_eq_one {n : Nat} (C : _root_.UDConfig n)
    {i j : Fin n} (hAdj : GraphBridge.AdjFromEdges (GraphBridge.unitDistanceEdges C) i j) :
    Geometry.Distance.eucDist (C.pts i) (C.pts j) = 1 :=
  (unitDistanceAdj_iff_geometry_eucDist C i j).1
    ((GraphBridge.adjFrom_unitDistanceEdges_iff C i j).1 hAdj)

/-! ## Straight-line unit-distance graph wrapper -/

/-- A finite straight-line unit-distance graph on the vertices of a `UDConfig`.

The edge set is the unordered unit-distance edge set, stored once with the
smaller endpoint first.  This wrapper packages the exact bridge facts needed by
later Swanepoel modules without asserting any planarity. -/
structure StraightLineUnitDistanceGraph (n : Nat) where
  config : _root_.UDConfig n
  edgeSet : Finset (Edge n)
  edgeSet_ordered : forall e : Edge n, e ∈ edgeSet -> e.1 < e.2
  edgeSet_iff_unit :
    forall i j : Fin n, (i, j) ∈ edgeSet <-> i < j /\ GraphBridge.UnitDistanceAdj config i j

namespace StraightLineUnitDistanceGraph

variable {n : Nat}

/-- The point assigned to a vertex. -/
def point (G : StraightLineUnitDistanceGraph n) (i : Fin n) : Point :=
  G.config.pts i

/-- Adjacency induced by the stored unordered finite edge set. -/
def Adj (G : StraightLineUnitDistanceGraph n) (i j : Fin n) : Prop :=
  GraphBridge.AdjFromEdges G.edgeSet i j

/-- The associated Swanepoel local graph. -/
def localGraph (G : StraightLineUnitDistanceGraph n) :
    LocalConfigurations.LocalGraph (Fin n) :=
  GraphBridge.localGraphFromOrderedEdges G.edgeSet G.edgeSet_ordered

/-- The canonical interface attached to a `UDConfig`. -/
def ofUDConfig (C : _root_.UDConfig n) : StraightLineUnitDistanceGraph n where
  config := C
  edgeSet := GraphBridge.unitDistanceEdges C
  edgeSet_ordered := fun _ he => GraphBridge.unitDistanceEdges_ordered C he
  edgeSet_iff_unit := fun i j => GraphBridge.mem_unitDistanceEdges_iff C i j

@[simp]
lemma ofUDConfig_edgeSet (C : _root_.UDConfig n) :
    (ofUDConfig C).edgeSet = GraphBridge.unitDistanceEdges C :=
  rfl

@[simp]
lemma localGraph_adj (G : StraightLineUnitDistanceGraph n) (i j : Fin n) :
    (G.localGraph).Adj i j <-> G.Adj i j :=
  Iff.rfl

lemma edge_mem_ordered (G : StraightLineUnitDistanceGraph n) {e : Edge n}
    (he : e ∈ G.edgeSet) :
    e.1 < e.2 :=
  G.edgeSet_ordered e he

lemma edge_mem_unitDistanceAdj (G : StraightLineUnitDistanceGraph n) {e : Edge n}
    (he : e ∈ G.edgeSet) :
    GraphBridge.UnitDistanceAdj G.config e.1 e.2 :=
  ((G.edgeSet_iff_unit e.1 e.2).1 he).2

lemma edge_mem_geometry_dist_eq_one (G : StraightLineUnitDistanceGraph n) {e : Edge n}
    (he : e ∈ G.edgeSet) :
    Geometry.Distance.eucDist (G.point e.1) (G.point e.2) = 1 :=
  (unitDistanceAdj_iff_geometry_eucDist G.config e.1 e.2).1
    (G.edge_mem_unitDistanceAdj he)

lemma edge_mem_endpoints_geometry_dist_eq_one (G : StraightLineUnitDistanceGraph n)
    {e : Edge n} (he : e ∈ G.edgeSet) :
    Geometry.Distance.eucDist (edgeEndpoints G.config e).1 (edgeEndpoints G.config e).2 = 1 :=
  G.edge_mem_geometry_dist_eq_one he

lemma adj_iff_unitDistanceAdj (G : StraightLineUnitDistanceGraph n) (i j : Fin n) :
    G.Adj i j <-> GraphBridge.UnitDistanceAdj G.config i j := by
  constructor
  · intro hAdj
    cases hAdj with
    | inl h =>
        exact ((G.edgeSet_iff_unit i j).1 h).2
    | inr h =>
        exact GraphBridge.unitDistanceAdj_symm G.config ((G.edgeSet_iff_unit j i).1 h).2
  · intro hUnit
    rcases lt_trichotomy i j with hij | hij | hji
    · exact Or.inl ((G.edgeSet_iff_unit i j).2 ⟨hij, hUnit⟩)
    · subst j
      exact False.elim ((GraphBridge.unitDistanceAdj_loopless G.config i) hUnit)
    · exact Or.inr
        ((G.edgeSet_iff_unit j i).2
          ⟨hji, GraphBridge.unitDistanceAdj_symm G.config hUnit⟩)

lemma adj_geometry_dist_eq_one (G : StraightLineUnitDistanceGraph n) {i j : Fin n}
    (hAdj : G.Adj i j) :
    Geometry.Distance.eucDist (G.point i) (G.point j) = 1 :=
  (unitDistanceAdj_iff_geometry_eucDist G.config i j).1
    ((G.adj_iff_unitDistanceAdj i j).1 hAdj)

lemma localGraph_adj_geometry_dist_eq_one (G : StraightLineUnitDistanceGraph n)
    {i j : Fin n} (hAdj : (G.localGraph).Adj i j) :
    Geometry.Distance.eucDist (G.point i) (G.point j) = 1 :=
  G.adj_geometry_dist_eq_one hAdj

lemma ofUDConfig_adj_iff (C : _root_.UDConfig n) (i j : Fin n) :
    (ofUDConfig C).Adj i j <-> GraphBridge.UnitDistanceAdj C i j :=
  (ofUDConfig C).adj_iff_unitDistanceAdj i j

end StraightLineUnitDistanceGraph

/-! ## Explicit planar, face, and boundary assumptions -/

/-- Cyclic successor on a nonempty `Fin m`. -/
def cyclicSucc {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

/-- Face and boundary data assumed by downstream planar arguments.

The fields name exactly what later modules may use: a noncrossing drawing,
abstract faces, a distinguished outer-face predicate, and cyclic boundary walks.
No theorem here constructs those faces from the drawing. -/
structure FaceBoundaryHypotheses {n : Nat} (G : StraightLineUnitDistanceGraph n) where
  noncrossing : PairwiseNoncrossing G.config G.edgeSet
  Face : Type u
  IsOuterFace : Face -> Prop
  boundaryLength : Face -> Nat
  boundaryLength_pos : forall F : Face, 0 < boundaryLength F
  boundaryVertex : forall F : Face, Fin (boundaryLength F) -> Fin n
  boundaryAdjacent :
    forall F : Face, forall k : Fin (boundaryLength F),
      G.Adj (boundaryVertex F k)
        (boundaryVertex F (cyclicSucc (boundaryLength_pos F) k))
  boundarySimple :
    forall F : Face, Function.Injective (boundaryVertex F)

namespace FaceBoundaryHypotheses

variable {n : Nat} {G : StraightLineUnitDistanceGraph n}

lemma no_crossing_of_disjoint (H : FaceBoundaryHypotheses G) {e f : Edge n}
    (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet) (hdisj : EdgeVertexDisjoint e f) :
    Not (EdgeSegmentsCross G.config e f) :=
  H.noncrossing e he f hf hdisj

lemma boundary_adj_unitDistanceAdj (H : FaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    GraphBridge.UnitDistanceAdj G.config (H.boundaryVertex F k)
      (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k)) :=
  (G.adj_iff_unitDistanceAdj _ _).1 (H.boundaryAdjacent F k)

lemma boundary_edge_geometry_dist_eq_one (H : FaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    Geometry.Distance.eucDist
        (G.point (H.boundaryVertex F k))
        (G.point (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k))) = 1 :=
  G.adj_geometry_dist_eq_one (H.boundaryAdjacent F k)

lemma boundary_edge_root_dist_eq_one (H : FaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    _root_.eucDist
        (G.point (H.boundaryVertex F k))
        (G.point (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k))) = 1 := by
  simpa [geometry_eucDist_eq_root] using H.boundary_edge_geometry_dist_eq_one F k

end FaceBoundaryHypotheses

end

end PlanarInterface
end Swanepoel
end ErdosProblems1066
