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

namespace PlanarInterface

/-! ## Cyclic predecessor/index facts -/

/-- Cyclic predecessor on a nonempty `Fin m`. -/
def cyclicPred {m : Nat} (hm : 0 < m) (i : Fin m) : Fin m :=
  { val := (i.val + (m - 1)) % m, isLt := Nat.mod_lt _ hm }

/-- The one-step element of the cyclic index group. -/
def cyclicOneStep {m : Nat} (hm : 0 < m) : Fin m :=
  { val := 1 % m, isLt := Nat.mod_lt _ hm }

/-- The predecessor-step element of the cyclic index group. -/
def cyclicPredStep {m : Nat} (hm : 0 < m) : Fin m :=
  { val := (m - 1) % m, isLt := Nat.mod_lt _ hm }

@[simp]
theorem cyclicSucc_val {m : Nat} (hm : 0 < m) (i : Fin m) :
    (cyclicSucc hm i).val = (i.val + 1) % m :=
  rfl

@[simp]
theorem cyclicPred_val {m : Nat} (hm : 0 < m) (i : Fin m) :
    (cyclicPred hm i).val = (i.val + (m - 1)) % m :=
  rfl

/-- `cyclicSucc` is addition by the one-step element on `Fin m`. -/
theorem cyclicSucc_eq_add_oneStep {m : Nat} (hm : 0 < m) (i : Fin m) :
    cyclicSucc hm i = i + cyclicOneStep hm := by
  ext
  simp [cyclicSucc, cyclicOneStep, Fin.val_add, Nat.add_mod]

/-- `cyclicPred` is addition by the predecessor-step element on `Fin m`. -/
theorem cyclicPred_eq_add_predStep {m : Nat} (hm : 0 < m) (i : Fin m) :
    cyclicPred hm i = i + cyclicPredStep hm := by
  ext
  simp [cyclicPred, cyclicPredStep, Fin.val_add, Nat.add_mod]

@[simp]
theorem cyclicSucc_cyclicPred {m : Nat} (hm : 0 < m) (i : Fin m) :
    cyclicSucc hm (cyclicPred hm i) = i := by
  ext
  simp only [cyclicSucc_val, cyclicPred_val, Nat.mod_add_mod]
  rw [Nat.add_assoc]
  rw [Nat.sub_add_cancel hm]
  simp [Nat.mod_eq_of_lt i.isLt]

@[simp]
theorem cyclicPred_cyclicSucc {m : Nat} (hm : 0 < m) (i : Fin m) :
    cyclicPred hm (cyclicSucc hm i) = i := by
  ext
  simp only [cyclicPred_val, cyclicSucc_val, Nat.mod_add_mod]
  rw [Nat.add_assoc]
  rw [show 1 + (m - 1) = m by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hm]
  simp [Nat.mod_eq_of_lt i.isLt]

/-- The cyclic successor map is injective on a nonempty cyclic index set. -/
theorem cyclicSucc_injective {m : Nat} (hm : 0 < m) :
    Function.Injective (cyclicSucc (m := m) hm) := by
  intro i j h
  calc
    i = cyclicPred hm (cyclicSucc hm i) := (cyclicPred_cyclicSucc hm i).symm
    _ = cyclicPred hm (cyclicSucc hm j) := by rw [h]
    _ = j := cyclicPred_cyclicSucc hm j

/-- On a cycle of length at least three, predecessor and successor indices differ. -/
theorem cyclicPred_ne_cyclicSucc_of_three_le {m : Nat} (hm : 0 < m)
    (hm3 : 3 <= m) (i : Fin m) :
    Ne (cyclicPred hm i) (cyclicSucc hm i) := by
  intro h
  have hstep : cyclicPredStep hm = cyclicOneStep hm := by
    have h' : i + cyclicPredStep hm = i + cyclicOneStep hm := by
      simpa [cyclicPred_eq_add_predStep hm, cyclicSucc_eq_add_oneStep hm] using h
    exact add_left_cancel h'
  have hval := congrArg Fin.val hstep
  have hpred_lt : m - 1 < m := Nat.sub_lt hm Nat.zero_lt_one
  have hone_lt : 1 < m := by omega
  simp [cyclicPredStep, cyclicOneStep, Nat.mod_eq_of_lt hpred_lt,
    Nat.mod_eq_of_lt hone_lt] at hval
  omega

end PlanarInterface

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

/-- The previous index in the boundary cycle. -/
def prev (C : BoundaryCycle G) (k : Fin C.length) : Fin C.length :=
  cyclicPred C.length_pos k

/-- The next vertex in the boundary cycle. -/
def nextVertex (C : BoundaryCycle G) (k : Fin C.length) : Fin n :=
  C.vertex (C.next k)

/-- The previous vertex in the boundary cycle. -/
def prevVertex (C : BoundaryCycle G) (k : Fin C.length) : Fin n :=
  C.vertex (C.prev k)

/-- The next geometric point in the boundary cycle. -/
def nextPoint (C : BoundaryCycle G) (k : Fin C.length) : Point :=
  C.point (C.next k)

/-- The previous geometric point in the boundary cycle. -/
def prevPoint (C : BoundaryCycle G) (k : Fin C.length) : Point :=
  C.point (C.prev k)

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
theorem prev_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.prev k = cyclicPred C.length_pos k :=
  rfl

@[simp]
theorem next_prev (C : BoundaryCycle G) (k : Fin C.length) :
    C.next (C.prev k) = k := by
  simp [next, prev]

@[simp]
theorem prev_next (C : BoundaryCycle G) (k : Fin C.length) :
    C.prev (C.next k) = k := by
  simp [next, prev]

@[simp]
theorem nextVertex_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.nextVertex k = C.vertex (cyclicSucc C.length_pos k) :=
  rfl

@[simp]
theorem prevVertex_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.prevVertex k = C.vertex (cyclicPred C.length_pos k) :=
  rfl

@[simp]
theorem nextPoint_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.nextPoint k = C.point (cyclicSucc C.length_pos k) :=
  rfl

@[simp]
theorem prevPoint_eq (C : BoundaryCycle G) (k : Fin C.length) :
    C.prevPoint k = C.point (cyclicPred C.length_pos k) :=
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

/-- The forward boundary edge begins at `k` and ends at `C.next k`. -/
theorem next_adjacent (C : BoundaryCycle G) (k : Fin C.length) :
    G.Adj (C.vertex k) (C.nextVertex k) := by
  simpa [nextVertex, next] using C.adjacent k

/-- The forward boundary edge can be used as an incoming edge at `k`. -/
theorem next_adjacent_symm (C : BoundaryCycle G) (k : Fin C.length) :
    G.Adj (C.nextVertex k) (C.vertex k) :=
  (G.adj_iff_unitDistanceAdj _ _).2
    (GraphBridge.unitDistanceAdj_symm G.config (C.adjacent_unitDistanceAdj k))

/-- The predecessor boundary edge ends at `k`. -/
theorem prev_adjacent (C : BoundaryCycle G) (k : Fin C.length) :
    G.Adj (C.prevVertex k) (C.vertex k) := by
  simpa [prevVertex, prev] using C.adjacent (C.prev k)

/-- The predecessor boundary edge is a unit-distance adjacency. -/
theorem prev_unitDistanceAdj (C : BoundaryCycle G) (k : Fin C.length) :
    GraphBridge.UnitDistanceAdj G.config (C.prevVertex k) (C.vertex k) :=
  (G.adj_iff_unitDistanceAdj _ _).1 (C.prev_adjacent k)

/-- The predecessor boundary edge has Euclidean length one. -/
theorem prev_dist_eq_one (C : BoundaryCycle G) (k : Fin C.length) :
    Geometry.Distance.eucDist (G.point (C.prevVertex k)) (G.point (C.vertex k)) = 1 :=
  G.adj_geometry_dist_eq_one (C.prev_adjacent k)

/-- On a boundary cycle of length at least three, predecessor and successor
indices around a vertex are distinct. -/
theorem prev_ne_next_of_three_le (C : BoundaryCycle G)
    (h3 : 3 <= C.length) (k : Fin C.length) :
    Ne (C.prev k) (C.next k) := by
  simpa [prev, next] using
    cyclicPred_ne_cyclicSucc_of_three_le C.length_pos h3 k

/-- On a simple boundary cycle of length at least three, predecessor and
successor vertices around a boundary vertex are distinct. -/
theorem prevVertex_ne_nextVertex_of_three_le (C : BoundaryCycle G)
    (h3 : 3 <= C.length) (k : Fin C.length) :
    Ne (C.prevVertex k) (C.nextVertex k) := by
  intro h
  have hidx : C.prev k = C.next k := by
    exact C.simple (by simpa [prevVertex, nextVertex] using h)
  exact C.prev_ne_next_of_three_le h3 k hidx

/-- The local predecessor/successor rows needed to build the concrete
unit-separated angle at a boundary vertex. -/
theorem predecessor_successor_angleRows (C : BoundaryCycle G)
    (h3 : 3 <= C.length) (k : Fin C.length) :
    G.Adj (C.prevVertex k) (C.vertex k) /\
      G.Adj (C.nextVertex k) (C.vertex k) /\
        Ne (C.prevVertex k) (C.nextVertex k) :=
  And.intro (C.prev_adjacent k)
    (And.intro (C.next_adjacent_symm k)
      (C.prevVertex_ne_nextVertex_of_three_le h3 k))

/-! ## Boundary endpoint-neighbour interval rows -/

/-- The part of the W34 neighbour-interval data that is forced by the boundary
walk alone: the interval starts at the boundary predecessor, ends at the
boundary successor, both endpoints are unit neighbours of the center, and the
two endpoint entries are distinct on a cycle of length at least three.

This is deliberately only an endpoint package.  It does not claim that all
unit neighbours between predecessor and successor have been enumerated in
cyclic order. -/
structure EndpointNeighborInterval (C : BoundaryCycle G) (k : Fin C.length) where
  gapCount : Nat
  neighbor : Fin (gapCount + 1) -> Fin n
  neighbor_injective : Function.Injective neighbor
  first_neighbor_eq_boundary_predecessor :
    neighbor ⟨0, Nat.succ_pos gapCount⟩ = C.prevVertex k
  last_neighbor_eq_boundary_successor :
    neighbor ⟨gapCount, Nat.lt_succ_self gapCount⟩ = C.nextVertex k
  neighbor_unit :
    forall j, G.Adj (neighbor j) (C.vertex k)

namespace EndpointNeighborInterval

variable {C : BoundaryCycle G} {k : Fin C.length}

@[simp]
theorem gapCount_mk
    (gapCount : Nat) (neighbor : Fin (gapCount + 1) -> Fin n)
    (neighbor_injective : Function.Injective neighbor)
    (first_neighbor_eq_boundary_predecessor :
      neighbor ⟨0, Nat.succ_pos gapCount⟩ = C.prevVertex k)
    (last_neighbor_eq_boundary_successor :
      neighbor ⟨gapCount, Nat.lt_succ_self gapCount⟩ = C.nextVertex k)
    (neighbor_unit : forall j, G.Adj (neighbor j) (C.vertex k)) :
    (EndpointNeighborInterval.mk gapCount neighbor neighbor_injective
      first_neighbor_eq_boundary_predecessor
      last_neighbor_eq_boundary_successor neighbor_unit).gapCount =
      gapCount :=
  rfl

end EndpointNeighborInterval

/-- The boundary-forced two-entry endpoint list, predecessor then successor. -/
def endpointNeighbor (C : BoundaryCycle G) (k : Fin C.length) :
    Fin (1 + 1) -> Fin n :=
  fun j => if j = 0 then C.prevVertex k else C.nextVertex k

@[simp]
theorem endpointNeighbor_first (C : BoundaryCycle G) (k : Fin C.length) :
    C.endpointNeighbor k ⟨0, Nat.succ_pos 1⟩ = C.prevVertex k := by
  simp [endpointNeighbor]

@[simp]
theorem endpointNeighbor_last (C : BoundaryCycle G) (k : Fin C.length) :
    C.endpointNeighbor k ⟨1, Nat.lt_succ_self 1⟩ = C.nextVertex k := by
  simp [endpointNeighbor]

/-- The two boundary endpoint-neighbours are distinct as entries of the
endpoint list. -/
theorem endpointNeighbor_injective_of_three_le (C : BoundaryCycle G)
    (h3 : 3 <= C.length) (k : Fin C.length) :
    Function.Injective (C.endpointNeighbor k) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [endpointNeighbor] at hij ⊢
  · exact False.elim (C.prevVertex_ne_nextVertex_of_three_le h3 k hij)
  · exact False.elim (C.prevVertex_ne_nextVertex_of_three_le h3 k hij.symm)

/-- Every entry of the boundary endpoint list is a unit-distance graph
neighbour of the boundary center. -/
theorem endpointNeighbor_unit (C : BoundaryCycle G)
    (k : Fin C.length) (j : Fin (1 + 1)) :
    G.Adj (C.endpointNeighbor k j) (C.vertex k) := by
  fin_cases j
  · simpa [endpointNeighbor, prevVertex, prev] using C.prev_adjacent k
  · simpa [endpointNeighbor, nextVertex, next] using C.next_adjacent_symm k

/-- The boundary walk supplies the endpoint part of a predecessor-to-successor
neighbour interval at each boundary index. -/
def endpointNeighborInterval (C : BoundaryCycle G)
    (h3 : 3 <= C.length) (k : Fin C.length) :
    EndpointNeighborInterval C k where
  gapCount := 1
  neighbor := C.endpointNeighbor k
  neighbor_injective := C.endpointNeighbor_injective_of_three_le h3 k
  first_neighbor_eq_boundary_predecessor := C.endpointNeighbor_first k
  last_neighbor_eq_boundary_successor := C.endpointNeighbor_last k
  neighbor_unit := C.endpointNeighbor_unit k

@[simp]
theorem endpointNeighborInterval_gapCount (C : BoundaryCycle G)
    (h3 : 3 <= C.length) (k : Fin C.length) :
    (C.endpointNeighborInterval h3 k).gapCount = 1 :=
  rfl

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
