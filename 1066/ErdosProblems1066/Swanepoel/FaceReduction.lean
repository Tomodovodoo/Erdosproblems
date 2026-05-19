import ErdosProblems1066.Swanepoel.NoncrossingUnitEdges

/-!
# Face-boundary reduction for canonical unit-distance edges

This file removes the explicit noncrossing assumption from the canonical
unit-distance edge set.  It does not construct faces or boundary cycles: those
remain explicit data in the unit-distance face-boundary hypotheses below.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FaceReduction

open PlanarInterface

universe u

noncomputable section

/-- The canonical finite unit-distance edge set is pairwise noncrossing. -/
theorem unitDistanceEdges_pairwiseNoncrossing {n : Nat} (C : _root_.UDConfig n) :
    PairwiseNoncrossing C (GraphBridge.unitDistanceEdges C) := by
  intro e he f hf hdisj
  exact NoncrossingUnitEdges.unitDistanceEdges_not_cross C hdisj he hf

/--
A straight-line unit-distance graph whose edge set is the canonical
unit-distance edge set.  The noncrossing fact is derived from the canonical
edge-set identity, rather than stored as an extra assumption.
-/
structure CanonicalStraightLineUnitDistanceGraph (n : Nat) extends
    StraightLineUnitDistanceGraph n where
  edgeSet_eq_unitDistanceEdges : edgeSet = GraphBridge.unitDistanceEdges config

namespace CanonicalStraightLineUnitDistanceGraph

variable {n : Nat}

/-- The canonical graph attached to a unit-distance configuration. -/
def ofUDConfig (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n where
  toStraightLineUnitDistanceGraph := StraightLineUnitDistanceGraph.ofUDConfig C
  edgeSet_eq_unitDistanceEdges := rfl

@[simp]
lemma ofUDConfig_edgeSet (C : _root_.UDConfig n) :
    (ofUDConfig C).edgeSet = GraphBridge.unitDistanceEdges C :=
  rfl

/-- Noncrossing is a theorem for canonical unit-distance graphs. -/
theorem pairwiseNoncrossing (G : CanonicalStraightLineUnitDistanceGraph n) :
    PairwiseNoncrossing G.config G.edgeSet := by
  rw [G.edgeSet_eq_unitDistanceEdges]
  exact unitDistanceEdges_pairwiseNoncrossing G.config

/-- Forget the canonical certificate, retaining the existing planar interface. -/
def toStraightLine (G : CanonicalStraightLineUnitDistanceGraph n) :
    StraightLineUnitDistanceGraph n :=
  G.toStraightLineUnitDistanceGraph

@[simp]
lemma toStraightLine_edgeSet (G : CanonicalStraightLineUnitDistanceGraph n) :
    G.toStraightLine.edgeSet = G.edgeSet :=
  rfl

@[simp]
lemma toStraightLine_config (G : CanonicalStraightLineUnitDistanceGraph n) :
    G.toStraightLine.config = G.config :=
  rfl

end CanonicalStraightLineUnitDistanceGraph

/-! ## Face-boundary hypotheses with noncrossing discharged for unit edges -/

/--
Face and boundary data for a canonical unit-distance drawing.

This is the same face/boundary surface as `PlanarInterface.FaceBoundaryHypotheses`,
except it omits the noncrossing field.  Conversion to the old interface fills
that field using `unitDistanceEdges_pairwiseNoncrossing`.
-/
structure UnitDistanceFaceBoundaryHypotheses {n : Nat}
    (G : CanonicalStraightLineUnitDistanceGraph n) where
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

namespace UnitDistanceFaceBoundaryHypotheses

variable {n : Nat} {G : CanonicalStraightLineUnitDistanceGraph n}

/--
Convert unit-distance face-boundary data to the existing planar interface,
supplying the canonical noncrossing theorem automatically.
-/
def toFaceBoundaryHypotheses (H : UnitDistanceFaceBoundaryHypotheses G) :
    FaceBoundaryHypotheses G.toStraightLine where
  noncrossing := by
    simpa using G.pairwiseNoncrossing
  Face := H.Face
  IsOuterFace := H.IsOuterFace
  boundaryLength := H.boundaryLength
  boundaryLength_pos := H.boundaryLength_pos
  boundaryVertex := H.boundaryVertex
  boundaryAdjacent := H.boundaryAdjacent
  boundarySimple := H.boundarySimple

lemma no_crossing_of_disjoint (_H : UnitDistanceFaceBoundaryHypotheses G)
    {e f : Edge n} (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet)
    (hdisj : EdgeVertexDisjoint e f) :
    Not (EdgeSegmentsCross G.config e f) :=
  G.pairwiseNoncrossing e he f hf hdisj

lemma boundary_adj_unitDistanceAdj (H : UnitDistanceFaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    GraphBridge.UnitDistanceAdj G.config (H.boundaryVertex F k)
      (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k)) :=
  (G.adj_iff_unitDistanceAdj _ _).1 (H.boundaryAdjacent F k)

lemma boundary_edge_geometry_dist_eq_one (H : UnitDistanceFaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    Geometry.Distance.eucDist
        (G.point (H.boundaryVertex F k))
        (G.point (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k))) = 1 :=
  G.adj_geometry_dist_eq_one (H.boundaryAdjacent F k)

lemma boundary_edge_root_dist_eq_one (H : UnitDistanceFaceBoundaryHypotheses G)
    (F : H.Face) (k : Fin (H.boundaryLength F)) :
    _root_.eucDist
        (G.point (H.boundaryVertex F k))
        (G.point (H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k))) = 1 := by
  simpa [PlanarInterface.geometry_eucDist_eq_root] using
    H.boundary_edge_geometry_dist_eq_one F k

/-! ## Face-boundary surface from an extracted outer-boundary cycle -/

/--
Package an already extracted simple cyclic outer-boundary row as the
face-boundary interface used downstream.  This does not construct the cycle:
the caller supplies the positive length, cyclic adjacency, and injective vertex
map, and the resulting interface has one selected outer face.
-/
def ofOuterBoundaryCycle (G : CanonicalStraightLineUnitDistanceGraph n)
    {m : Nat} (hm : 0 < m)
    (vertex : Fin m -> Fin n)
    (adjacent :
      forall k : Fin m,
        G.Adj (vertex k) (vertex (cyclicSucc hm k)))
    (simple : Function.Injective vertex) :
    UnitDistanceFaceBoundaryHypotheses G where
  Face := PUnit
  IsOuterFace := fun _ => True
  boundaryLength := fun _ => m
  boundaryLength_pos := fun _ => hm
  boundaryVertex := fun _ => vertex
  boundaryAdjacent := fun _ => adjacent
  boundarySimple := fun _ => simple

@[simp]
theorem ofOuterBoundaryCycle_boundaryLength
    (G : CanonicalStraightLineUnitDistanceGraph n)
    {m : Nat} (hm : 0 < m)
    (vertex : Fin m -> Fin n)
    (adjacent :
      forall k : Fin m,
        G.Adj (vertex k) (vertex (cyclicSucc hm k)))
    (simple : Function.Injective vertex) :
    (ofOuterBoundaryCycle G hm vertex adjacent simple).boundaryLength PUnit.unit = m :=
  rfl

@[simp]
theorem ofOuterBoundaryCycle_boundaryVertex
    (G : CanonicalStraightLineUnitDistanceGraph n)
    {m : Nat} (hm : 0 < m)
    (vertex : Fin m -> Fin n)
    (adjacent :
      forall k : Fin m,
        G.Adj (vertex k) (vertex (cyclicSucc hm k)))
    (simple : Function.Injective vertex) :
    (ofOuterBoundaryCycle G hm vertex adjacent simple).boundaryVertex PUnit.unit = vertex :=
  rfl

@[simp]
theorem ofOuterBoundaryCycle_isOuterFace
    (G : CanonicalStraightLineUnitDistanceGraph n)
    {m : Nat} (hm : 0 < m)
    (vertex : Fin m -> Fin n)
    (adjacent :
      forall k : Fin m,
        G.Adj (vertex k) (vertex (cyclicSucc hm k)))
    (simple : Function.Injective vertex) :
    (ofOuterBoundaryCycle G hm vertex adjacent simple).IsOuterFace PUnit.unit :=
  trivial

/--
An extracted nondegenerate outer-boundary cycle supplies the selected
face-boundary rows needed before the separate enclosure field is attached.
-/
theorem exists_outerFace_length_ge_three_ofOuterBoundaryCycle
    (G : CanonicalStraightLineUnitDistanceGraph n)
    {m : Nat} (hm : 0 < m)
    (vertex : Fin m -> Fin n)
    (adjacent :
      forall k : Fin m,
        G.Adj (vertex k) (vertex (cyclicSucc hm k)))
    (simple : Function.Injective vertex)
    (hlen : 3 <= m) :
    Exists fun H : UnitDistanceFaceBoundaryHypotheses G =>
      Exists fun F : H.Face =>
        H.IsOuterFace F /\ 3 <= H.boundaryLength F := by
  refine
    ⟨ofOuterBoundaryCycle G hm vertex adjacent simple, PUnit.unit, ?_, ?_⟩
  · simp [ofOuterBoundaryCycle]
  · simpa [ofOuterBoundaryCycle] using hlen

/-! ## Small concrete selected-face surface from one canonical edge -/

/--
Build the minimal face-boundary surface carried by one actual canonical graph
edge.  The unique face has the two endpoints as its cyclic boundary.
-/
def ofAdjacentPair (G : CanonicalStraightLineUnitDistanceGraph n)
    {i j : Fin n} (hAdj : G.Adj i j) :
    UnitDistanceFaceBoundaryHypotheses G where
  Face := PUnit
  IsOuterFace := fun _ => True
  boundaryLength := fun _ => 2
  boundaryLength_pos := fun _ => by norm_num
  boundaryVertex := fun _ k => if k = (0 : Fin 2) then i else j
  boundaryAdjacent := by
    intro _ k
    have hAdj_symm : G.Adj j i :=
      GraphBridge.adjFromEdges_symm G.edgeSet hAdj
    fin_cases k <;> simp [PlanarInterface.cyclicSucc, hAdj, hAdj_symm]
  boundarySimple := by
    intro _ a b h
    have hij : i = j -> False := by
      intro hij
      subst j
      exact
        (GraphBridge.adjFromEdges_loopless_of_ordered
          (edges := G.edgeSet) G.edgeSet_ordered i) hAdj
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      exact hij h
    · exfalso
      exact hij h.symm
    · rfl

theorem exists_unitDistanceAdj_of_selectedFace
    (H : UnitDistanceFaceBoundaryHypotheses G) (F : H.Face) :
    Exists fun i : Fin n =>
      Exists fun j : Fin n => GraphBridge.UnitDistanceAdj G.config i j := by
  let k : Fin (H.boundaryLength F) := ⟨0, H.boundaryLength_pos F⟩
  exact
    ⟨H.boundaryVertex F k,
      H.boundaryVertex F (cyclicSucc (H.boundaryLength_pos F) k),
      H.boundary_adj_unitDistanceAdj F k⟩

end UnitDistanceFaceBoundaryHypotheses

end

end FaceReduction
end Swanepoel
end ErdosProblems1066
