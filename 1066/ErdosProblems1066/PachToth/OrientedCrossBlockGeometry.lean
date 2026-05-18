import ErdosProblems1066.PachToth.CrossBlock
import ErdosProblems1066.PachToth.CrossBlockGeometry

/-!
# Oriented Cross-Block Connector Geometry

This module extends the pure-translation connector check from
`CrossBlockGeometry` to a finite family of exact grid orientations.

The exact local coordinates lie in the even-parity triangular grid represented
as `(i * sqrt 3 / 2, j / 2)`.  On this grid, rotations by multiples of
60 degrees and their reflected variants have integer coordinates on all local
Pach--Toth vertices and preserve the integral norm
`3 * di ^ 2 + dj ^ 2`.

The finite check below shows that no orientation in this dihedral family,
together with a single grid offset for the next block, realizes all four
directed connector edges as unit distances.  A later global construction
therefore needs either a larger placement model or explicit connector-distance
hypotheses.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace OrientedCrossBlockGeometry

open Geometry.Distance
open FiniteGraph
open FiniteGraph.LocalVertex
open ExactLocalGeometry

abbrev R2 := Prod Real Real

/-- The twelve triangular-grid orientations used for the finite search. -/
inductive GridOrientation where
  | rot0
  | rot60
  | rot120
  | rot180
  | rot240
  | rot300
  | refl0
  | refl60
  | refl120
  | refl180
  | refl240
  | refl300
  deriving DecidableEq, Repr, Fintype

namespace GridOrientation

/-- Apply a triangular-grid orientation to grid coordinates.

The formulas with division by `2` are integer-valued on the local even-parity
grid used by `ExactLocalGeometry.localGrid`. -/
def mapGrid : GridOrientation -> GridPoint -> GridPoint
  | rot0, p => p
  | rot60, p => { i := (p.i - p.j) / 2, j := (3 * p.i + p.j) / 2 }
  | rot120, p => { i := -(p.i + p.j) / 2, j := (3 * p.i - p.j) / 2 }
  | rot180, p => { i := -p.i, j := -p.j }
  | rot240, p => { i := (-p.i + p.j) / 2, j := (-3 * p.i - p.j) / 2 }
  | rot300, p => { i := (p.i + p.j) / 2, j := (-3 * p.i + p.j) / 2 }
  | refl0, p => { i := p.i, j := -p.j }
  | refl60, p => { i := (p.i - p.j) / 2, j := -(3 * p.i + p.j) / 2 }
  | refl120, p => { i := -(p.i + p.j) / 2, j := -(3 * p.i - p.j) / 2 }
  | refl180, p => { i := -p.i, j := p.j }
  | refl240, p => { i := (-p.i + p.j) / 2, j := (3 * p.i + p.j) / 2 }
  | refl300, p => { i := (p.i + p.j) / 2, j := (3 * p.i - p.j) / 2 }

end GridOrientation

/-- The oriented grid point for a local vertex. -/
def orientedLocalGrid (o : GridOrientation) (v : LocalVertex) : GridPoint :=
  o.mapGrid (localGrid v)

/-- The oriented real point for a local vertex. -/
def orientedLocalPoint (o : GridOrientation) (v : LocalVertex) : R2 :=
  (orientedLocalGrid o v).toPoint

/-- Four times the squared distance between two oriented local vertices. -/
def orientedLocalNorm4 (o : GridOrientation) (u v : LocalVertex) : Int :=
  (orientedLocalGrid o u).norm4 (orientedLocalGrid o v)

theorem orientedLocalNorm4_eq_localNorm4
    (o : GridOrientation) (u v : LocalVertex) :
    orientedLocalNorm4 o u v = localNorm4 u v := by
  revert o u v
  decide

theorem oriented_sqDist' (o : GridOrientation) (u v : LocalVertex) :
    ((orientedLocalPoint o u).1 - (orientedLocalPoint o v).1) ^ 2 +
        ((orientedLocalPoint o u).2 - (orientedLocalPoint o v).2) ^ 2 =
      ((orientedLocalNorm4 o u v : Int) : Real) / 4 := by
  simpa [orientedLocalPoint, orientedLocalNorm4] using
    GridPoint.sqDist_toPoint' (orientedLocalGrid o u) (orientedLocalGrid o v)

/-- Every local edge remains a unit edge after any listed orientation. -/
theorem orientedLocal_adj_unit_distance (o : GridOrientation) :
    forall u v : LocalVertex, adj u v = true ->
      eucDist (orientedLocalPoint o u) (orientedLocalPoint o v) = 1 := by
  intro u v huv
  rw [eucDist_eq_one_iff]
  rw [oriented_sqDist', orientedLocalNorm4_eq_localNorm4]
  have hnorm : localNorm4 u v = 4 := by
    revert u v
    decide
  rw [hnorm]
  norm_num

/-- Distinct local vertices remain separated after any listed orientation. -/
theorem orientedLocal_separated (o : GridOrientation) :
    forall u v : LocalVertex, u ≠ v ->
      1 <= eucDist (orientedLocalPoint o u) (orientedLocalPoint o v) := by
  intro u v huv
  rw [eucDist_ge_one_iff]
  rw [oriented_sqDist', orientedLocalNorm4_eq_localNorm4]
  have hnorm : 4 <= localNorm4 u v := by
    revert u v
    decide
  have hnormReal : (4 : Real) <= (localNorm4 u v : Real) := by
    exact_mod_cast hnorm
  nlinarith

/-- Translate an oriented next-block local grid point by a grid offset. -/
def orientedTranslatedLocalGrid
    (d : GridPoint) (o : GridOrientation) (v : LocalVertex) : GridPoint :=
  CrossBlockGeometry.translateGrid d (orientedLocalGrid o v)

/-- Translate an oriented next-block local point by a grid offset. -/
def orientedTranslatedLocalPoint
    (d : GridPoint) (o : GridOrientation) (v : LocalVertex) : R2 :=
  (orientedTranslatedLocalGrid d o v).toPoint

/-- Four times the squared distance from a source vertex to an oriented,
translated target vertex. -/
def orientedCrossNorm4
    (d : GridPoint) (o : GridOrientation) (u v : LocalVertex) : Int :=
  (localGrid u).norm4 (orientedTranslatedLocalGrid d o v)

theorem oriented_cross_sqDist'
    (d : GridPoint) (o : GridOrientation) (u v : LocalVertex) :
    ((localPoint u).1 - (orientedTranslatedLocalPoint d o v).1) ^ 2 +
        ((localPoint u).2 - (orientedTranslatedLocalPoint d o v).2) ^ 2 =
      ((orientedCrossNorm4 d o u v : Int) : Real) / 4 := by
  simpa [localPoint, orientedTranslatedLocalPoint, orientedCrossNorm4] using
    GridPoint.sqDist_toPoint' (localGrid u) (orientedTranslatedLocalGrid d o v)

/-- A norm certificate gives a unit oriented connector edge. -/
theorem oriented_cross_unit_distance_of_norm4_eq_four
    {d : GridPoint} {o : GridOrientation} {u v : LocalVertex}
    (h : orientedCrossNorm4 d o u v = 4) :
    eucDist (localPoint u) (orientedTranslatedLocalPoint d o v) = 1 := by
  rw [eucDist_eq_one_iff]
  rw [oriented_cross_sqDist']
  rw [h]
  norm_num

/-- No listed orientation and single grid offset realizes all four connector
norm equations. -/
theorem no_oriented_grid_placement_realizes_all_connector_norms
    (o : GridOrientation) (d : GridPoint) :
    Not (orientedCrossNorm4 d o T2_2 T1_1 = 4 ∧
        orientedCrossNorm4 d o T2_2 T1_2 = 4 ∧
        orientedCrossNorm4 d o T4_0 T0_0 = 4 ∧
        orientedCrossNorm4 d o T4_0 T0_2 = 4) := by
  cases o <;>
    intro h <;>
    rcases h with ⟨h211, h212, h400, h402⟩ <;>
    norm_num [orientedCrossNorm4, orientedTranslatedLocalGrid,
      CrossBlockGeometry.translateGrid, orientedLocalGrid, GridOrientation.mapGrid,
      localGrid, GridPoint.norm4, T2_2, T1_1, T1_2, T4_0, T0_0, T0_2, T] at h211 h212 h400 h402 <;>
    nlinarith

/-- No listed orientation and single grid offset realizes all four connector
edges as unit distances. -/
theorem no_oriented_grid_placement_realizes_all_connector_units
    (o : GridOrientation) (d : GridPoint) :
    Not (eucDist (localPoint T2_2) (orientedTranslatedLocalPoint d o T1_1) = 1 ∧
        eucDist (localPoint T2_2) (orientedTranslatedLocalPoint d o T1_2) = 1 ∧
        eucDist (localPoint T4_0) (orientedTranslatedLocalPoint d o T0_0) = 1 ∧
        eucDist (localPoint T4_0) (orientedTranslatedLocalPoint d o T0_2) = 1) := by
  cases o <;>
    intro h <;>
    rcases h with ⟨h211, h212, h400, h402⟩ <;>
    rw [eucDist_eq_one_iff, oriented_cross_sqDist'] at h211 h212 h400 h402 <;>
    norm_num [orientedCrossNorm4, orientedTranslatedLocalGrid,
      CrossBlockGeometry.translateGrid, orientedLocalGrid, GridOrientation.mapGrid,
      localGrid, GridPoint.norm4, T2_2, T1_1, T1_2, T4_0, T0_0, T0_2, T] at h211 h212 h400 h402 <;>
    nlinarith

/-- A point-level predicate for same-block unit edges. -/
def OneBlockUnitEdges (place : LocalVertex -> R2) : Prop :=
  forall u v : LocalVertex, adj u v = true -> eucDist (place u) (place v) = 1

/-- A point-level predicate for the four directed next-block connector edges. -/
def NextConnectorUnitEdges
    (left right : LocalVertex -> R2) : Prop :=
  forall u v : LocalVertex,
    CrossBlock.NextConnector u v -> eucDist (left u) (right v) = 1

/-- General interface for a next-block placement.  This deliberately does not
assert that the right block comes from a single orientation and offset. -/
structure GeneralNextBlockPlacement where
  left : LocalVertex -> R2
  right : LocalVertex -> R2
  left_unit_edges : OneBlockUnitEdges left
  right_unit_edges : OneBlockUnitEdges right
  connector_unit_edges : NextConnectorUnitEdges left right

theorem GeneralNextBlockPlacement.connector_unit
    (P : GeneralNextBlockPlacement) {u v : LocalVertex}
    (h : CrossBlock.NextConnector u v) :
    eucDist (P.left u) (P.right v) = 1 :=
  P.connector_unit_edges u v h

theorem exact_left_oriented_right_one_block_units
    (o : GridOrientation) :
    OneBlockUnitEdges localPoint ∧ OneBlockUnitEdges (orientedLocalPoint o) := by
  constructor
  · exact adj_unit_distance
  · exact orientedLocal_adj_unit_distance o

/-!
For reference, the exact offset pairs that separately solve the two source
families are as follows.  Each row lists the two offsets for
`T2_2 -> T1_1/T1_2`, then the two offsets for `T4_0 -> T0_0/T0_2`.

* `rot0`: `(2,-4)`, `(3,-7)` versus `(4,4)`, `(5,7)`.
* `rot60`: `(3,-5)`, `(5,-5)` versus `(3,5)`, `(4,2)`.
* `rot120`: `(4,-4)`, `(5,-1)` versus `(3,1)`, `(5,1)`.
* `rot180`: `(3,1)`, `(4,-2)` versus `(5,-1)`, `(6,2)`.
* `rot240`: `(1,-1)`, `(3,-1)` versus `(6,4)`, `(7,1)`.
* `rot300`: `(1,-5)`, `(2,-2)` versus `(5,5)`, `(7,5)`.
* `refl0`: `(2,-2)`, `(3,1)` versus `(4,2)`, `(5,-1)`.
* `refl60`: `(3,-1)`, `(5,-1)` versus `(3,1)`, `(4,4)`.
* `refl120`: `(4,-2)`, `(5,-5)` versus `(3,5)`, `(5,5)`.
* `refl180`: `(3,-7)`, `(4,-4)` versus `(5,7)`, `(6,4)`.
* `refl240`: `(1,-5)`, `(3,-5)` versus `(6,2)`, `(7,5)`.
* `refl300`: `(1,-1)`, `(2,-4)` versus `(5,1)`, `(7,1)`.

In every row the two offset sets are disjoint, which is the obstruction proved
by `no_oriented_grid_placement_realizes_all_connector_norms`.
-/

end OrientedCrossBlockGeometry
end PachToth
end ErdosProblems1066

end
