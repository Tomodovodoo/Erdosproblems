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

end UnitDistanceFaceBoundaryHypotheses

end

end FaceReduction
end Swanepoel
end ErdosProblems1066
