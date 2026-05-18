import Mathlib.Geometry.Polygon.Basic
import ErdosProblems1066.Swanepoel.OuterBoundaryInterface

/-!
# Boundary-walk bridge

This module gives a small bridge from the explicit Swanepoel boundary-cycle
records to Mathlib's lightweight `Polygon` API and to finite cyclic-edge helper
data.  It only exposes the recorded boundary walk, successor, adjacency, and
unit-length facts; it does not construct faces, interiors, or Jordan-curve data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryInterface

open PlanarInterface
open FaceReduction

variable {n : Nat}

/-! ## Cyclic successor compatibility -/

/-- The repository cyclic successor agrees with Mathlib's polygon rotation. -/
lemma finRotate_eq_cyclicSucc {m : Nat} (hm : 0 < m) (i : Fin m) :
    finRotate m i = cyclicSucc hm i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
      ext
      simp [cyclicSucc, Fin.val_add, Nat.add_mod]

/-! ## Boundary-cycle projections -/

namespace BoundaryCycle

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The next index in the boundary cycle. -/
def next (C : BoundaryCycle G) (k : Fin C.length) : Fin C.length :=
  cyclicSucc C.length_pos k

/-- The next vertex in the boundary cycle. -/
def nextVertex (C : BoundaryCycle G) (k : Fin C.length) : Fin n :=
  C.vertex (C.next k)

/-- The next geometric point in the boundary cycle. -/
def nextPoint (C : BoundaryCycle G) (k : Fin C.length) : Point :=
  C.point (C.next k)

/-- The directed boundary edge beginning at `k`. -/
def edge (C : BoundaryCycle G) (k : Fin C.length) : Edge n :=
  (C.vertex k, C.nextVertex k)

/-- The finite set of directed cyclic boundary edges. -/
noncomputable def edgeFinset (C : BoundaryCycle G) : Finset (Edge n) :=
  Finset.univ.image C.edge

/-- The Mathlib polygon with the same geometric vertices as the boundary cycle. -/
def toPolygon (C : BoundaryCycle G) : Polygon Point C.length where
  vertices := C.point

@[simp]
theorem next_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.next k = cyclicSucc C.length_pos k :=
  rfl

@[simp]
theorem nextVertex_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.nextVertex k = C.vertex (cyclicSucc C.length_pos k) :=
  rfl

@[simp]
theorem nextPoint_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.nextPoint k = C.point (cyclicSucc C.length_pos k) :=
  rfl

@[simp]
theorem edge_fst (C : BoundaryCycle G) (k : Fin C.length) :
    (C.edge k).1 = C.vertex k :=
  rfl

@[simp]
theorem edge_snd (C : BoundaryCycle G) (k : Fin C.length) :
    (C.edge k).2 = C.vertex (cyclicSucc C.length_pos k) :=
  rfl

/-- A boundary edge belongs to the finite set of cyclic boundary edges. -/
theorem edge_mem_edgeFinset (C : BoundaryCycle G) (k : Fin C.length) :
    Membership.mem C.edgeFinset (C.edge k) := by
  classical
  refine Finset.mem_image.mpr ?_
  exact Exists.intro k (And.intro (Finset.mem_univ k) rfl)

/-- Membership in the finite cyclic-edge set is exactly being one indexed edge. -/
theorem mem_edgeFinset_iff (C : BoundaryCycle G) (e : Edge n) :
    Membership.mem C.edgeFinset e <-> Exists fun k : Fin C.length => C.edge k = e := by
  classical
  simp [edgeFinset]

/-- The edge projection recovers the recorded graph adjacency. -/
theorem edge_adjacent (C : BoundaryCycle G) (k : Fin C.length) :
    G.Adj (C.edge k).1 (C.edge k).2 := by
  simpa [edge] using C.adjacent k

/-- The edge projection recovers unit-distance adjacency. -/
theorem edge_unitDistanceAdj (C : BoundaryCycle G) (k : Fin C.length) :
    GraphBridge.UnitDistanceAdj G.config (C.edge k).1 (C.edge k).2 := by
  simpa [edge] using C.adjacent_unitDistanceAdj k

/-- The edge projection recovers the unit Euclidean length fact. -/
theorem edge_dist_eq_one (C : BoundaryCycle G) (k : Fin C.length) :
    Geometry.Distance.eucDist (G.point (C.edge k).1) (G.point (C.edge k).2) = 1 := by
  simpa [edge, BoundaryCycle.point] using C.edge_geometry_dist_eq_one k

@[simp]
theorem toPolygon_apply (C : BoundaryCycle G) (k : Fin C.length) :
    C.toPolygon k = C.point k :=
  rfl

@[simp]
theorem toPolygon_vertices (C : BoundaryCycle G) :
    C.toPolygon.vertices = C.point :=
  rfl

/-- Mathlib's polygon rotation selects the repository cyclic successor. -/
theorem toPolygon_apply_finRotate (C : BoundaryCycle G) (k : Fin C.length) :
    C.toPolygon (finRotate C.length k) = C.nextPoint k := by
  rw [finRotate_eq_cyclicSucc C.length_pos]
  rfl

/-- The `k`-th Mathlib polygon edge is the segment from a boundary point to its successor. -/
theorem toPolygon_edgeSet (C : BoundaryCycle G) (k : Fin C.length) :
    C.toPolygon.edgeSet Real k = affineSegment Real (C.point k) (C.nextPoint k) := by
  rw [Polygon.edgeSet, finRotate_eq_cyclicSucc C.length_pos]
  rfl

end BoundaryCycle

/-! ## Simple-polygon projections -/

namespace SimplePolygon

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}

/-- Forget a recorded simple-polygon witness to the corresponding Mathlib polygon. -/
def toPolygon (_S : SimplePolygon G C) : Polygon Point C.length :=
  C.toPolygon

/-- The simple-polygon witness includes injectivity of boundary vertices. -/
theorem boundaryVertex_injective (S : SimplePolygon G C) :
    Function.Injective C.vertex :=
  S.vertices_injective

/-- Projection of the recorded noncrossing condition for separated boundary edges. -/
theorem separated_edges_do_not_cross' (S : SimplePolygon G C)
    {i j : Fin C.length} (hsep : CyclicEdgesSeparated C.length_pos i j) :
    Not (SegmentsCrossInterior
      (C.point i) (C.nextPoint i) (C.point j) (C.nextPoint j)) := by
  simpa [BoundaryCycle.nextPoint] using S.separated_edges_do_not_cross i j hsep

@[simp]
theorem toPolygon_apply (S : SimplePolygon G C) (k : Fin C.length) :
    S.toPolygon k = C.point k :=
  rfl

end SimplePolygon

end OuterBoundaryInterface
end Swanepoel
end ErdosProblems1066
