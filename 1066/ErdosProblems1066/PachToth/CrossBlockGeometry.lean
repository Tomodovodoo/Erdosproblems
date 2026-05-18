import ErdosProblems1066.PachToth.CrossBlock
import ErdosProblems1066.PachToth.ExactLocalGeometry

/-!
# Exact Cross-Block Connector Geometry

This module studies translations of the exact local Pach--Toth block from
`ExactLocalGeometry`.  A grid offset `(a,b)` sends a next-block local grid
point `(i,j)` to `(i + a, j + b)`, interpreted as the real point
`((i + a) * sqrt 3 / 2, (j + b) / 2)`.

The finite connector relation in `CrossBlock` has four directed edges.  In the
current exact local coordinates, the two edges out of `T2_2` and the two edges
out of `T4_0` are realized by different families of translations:

* `T2_2 -> T1_1/T1_2`: offsets `(2,-4)` and `(3,-7)`.
* `T4_0 -> T0_0/T0_2`: offsets `(4,4)` and `(5,7)`.

Consequently a single pure translation of the next block cannot make all four
connector edges unit in this coordinate model.  A cyclic/global construction
therefore needs additional placement data, for example separate block
placements, rotations/reflections, or hypotheses asserting the intended
cross-block distances directly.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockGeometry

open Geometry.Distance
open FiniteGraph
open FiniteGraph.LocalVertex
open ExactLocalGeometry

abbrev R2 := Prod Real Real

/-- Translate an exact grid point by an integer grid offset. -/
def translateGrid (d p : GridPoint) : GridPoint :=
  { i := p.i + d.i, j := p.j + d.j }

/-- The translated next-block grid point for a local vertex. -/
def translatedLocalGrid (d : GridPoint) (v : LocalVertex) : GridPoint :=
  translateGrid d (localGrid v)

/-- The translated next-block real point for a local vertex. -/
def translatedLocalPoint (d : GridPoint) (v : LocalVertex) : R2 :=
  (translatedLocalGrid d v).toPoint

/-- Four times the squared distance from a source vertex to a translated target. -/
def crossNorm4 (d : GridPoint) (u v : LocalVertex) : Int :=
  (localGrid u).norm4 (translatedLocalGrid d v)

theorem cross_sqDist' (d : GridPoint) (u v : LocalVertex) :
    ((localPoint u).1 - (translatedLocalPoint d v).1) ^ 2 +
        ((localPoint u).2 - (translatedLocalPoint d v).2) ^ 2 =
      ((crossNorm4 d u v : Int) : Real) / 4 := by
  simpa [localPoint, translatedLocalPoint, crossNorm4] using
    GridPoint.sqDist_toPoint' (localGrid u) (translatedLocalGrid d v)

/-- A `crossNorm4 = 4` certificate gives a unit translated connector edge. -/
theorem cross_unit_distance_of_norm4_eq_four {d : GridPoint} {u v : LocalVertex}
    (h : crossNorm4 d u v = 4) :
    eucDist (localPoint u) (translatedLocalPoint d v) = 1 := by
  rw [eucDist_eq_one_iff]
  rw [cross_sqDist']
  rw [h]
  norm_num

/-- First translation realizing both connector targets from `T2_2`. -/
def t2ConnectorOffsetA : GridPoint := { i := 2, j := -4 }

/-- Second translation realizing both connector targets from `T2_2`. -/
def t2ConnectorOffsetB : GridPoint := { i := 3, j := -7 }

/-- First translation realizing both connector targets from `T4_0`. -/
def t4ConnectorOffsetA : GridPoint := { i := 4, j := 4 }

/-- Second translation realizing both connector targets from `T4_0`. -/
def t4ConnectorOffsetB : GridPoint := { i := 5, j := 7 }

theorem t2ConnectorOffsetA_norm4_T1_1 :
    crossNorm4 t2ConnectorOffsetA T2_2 T1_1 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetA, T2_2, T1_1, T]

theorem t2ConnectorOffsetA_norm4_T1_2 :
    crossNorm4 t2ConnectorOffsetA T2_2 T1_2 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetA, T2_2, T1_2, T]

theorem t2ConnectorOffsetB_norm4_T1_1 :
    crossNorm4 t2ConnectorOffsetB T2_2 T1_1 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetB, T2_2, T1_1, T]

theorem t2ConnectorOffsetB_norm4_T1_2 :
    crossNorm4 t2ConnectorOffsetB T2_2 T1_2 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetB, T2_2, T1_2, T]

theorem t4ConnectorOffsetA_norm4_T0_0 :
    crossNorm4 t4ConnectorOffsetA T4_0 T0_0 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetA, T4_0, T0_0, T]

theorem t4ConnectorOffsetA_norm4_T0_2 :
    crossNorm4 t4ConnectorOffsetA T4_0 T0_2 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetA, T4_0, T0_2, T]

theorem t4ConnectorOffsetB_norm4_T0_0 :
    crossNorm4 t4ConnectorOffsetB T4_0 T0_0 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetB, T4_0, T0_0, T]

theorem t4ConnectorOffsetB_norm4_T0_2 :
    crossNorm4 t4ConnectorOffsetB T4_0 T0_2 = 4 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetB, T4_0, T0_2, T]

theorem t2ConnectorOffsetA_unit_T1_1 :
    eucDist (localPoint T2_2) (translatedLocalPoint t2ConnectorOffsetA T1_1) = 1 :=
  cross_unit_distance_of_norm4_eq_four t2ConnectorOffsetA_norm4_T1_1

theorem t2ConnectorOffsetA_unit_T1_2 :
    eucDist (localPoint T2_2) (translatedLocalPoint t2ConnectorOffsetA T1_2) = 1 :=
  cross_unit_distance_of_norm4_eq_four t2ConnectorOffsetA_norm4_T1_2

theorem t2ConnectorOffsetB_unit_T1_1 :
    eucDist (localPoint T2_2) (translatedLocalPoint t2ConnectorOffsetB T1_1) = 1 :=
  cross_unit_distance_of_norm4_eq_four t2ConnectorOffsetB_norm4_T1_1

theorem t2ConnectorOffsetB_unit_T1_2 :
    eucDist (localPoint T2_2) (translatedLocalPoint t2ConnectorOffsetB T1_2) = 1 :=
  cross_unit_distance_of_norm4_eq_four t2ConnectorOffsetB_norm4_T1_2

theorem t4ConnectorOffsetA_unit_T0_0 :
    eucDist (localPoint T4_0) (translatedLocalPoint t4ConnectorOffsetA T0_0) = 1 :=
  cross_unit_distance_of_norm4_eq_four t4ConnectorOffsetA_norm4_T0_0

theorem t4ConnectorOffsetA_unit_T0_2 :
    eucDist (localPoint T4_0) (translatedLocalPoint t4ConnectorOffsetA T0_2) = 1 :=
  cross_unit_distance_of_norm4_eq_four t4ConnectorOffsetA_norm4_T0_2

theorem t4ConnectorOffsetB_unit_T0_0 :
    eucDist (localPoint T4_0) (translatedLocalPoint t4ConnectorOffsetB T0_0) = 1 :=
  cross_unit_distance_of_norm4_eq_four t4ConnectorOffsetB_norm4_T0_0

theorem t4ConnectorOffsetB_unit_T0_2 :
    eucDist (localPoint T4_0) (translatedLocalPoint t4ConnectorOffsetB T0_2) = 1 :=
  cross_unit_distance_of_norm4_eq_four t4ConnectorOffsetB_norm4_T0_2

theorem t2ConnectorOffsetA_misses_T4_T0_0 :
    crossNorm4 t2ConnectorOffsetA T4_0 T0_0 = 112 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetA, T4_0, T0_0, T]

theorem t2ConnectorOffsetA_misses_T4_T0_2 :
    crossNorm4 t2ConnectorOffsetA T4_0 T0_2 = 108 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetA, T4_0, T0_2, T]

theorem t2ConnectorOffsetB_misses_T4_T0_0 :
    crossNorm4 t2ConnectorOffsetB T4_0 T0_0 = 172 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetB, T4_0, T0_0, T]

theorem t2ConnectorOffsetB_misses_T4_T0_2 :
    crossNorm4 t2ConnectorOffsetB T4_0 T0_2 = 156 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t2ConnectorOffsetB, T4_0, T0_2, T]

theorem t4ConnectorOffsetA_misses_T2_T1_1 :
    crossNorm4 t4ConnectorOffsetA T2_2 T1_1 = 112 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetA, T2_2, T1_1, T]

theorem t4ConnectorOffsetA_misses_T2_T1_2 :
    crossNorm4 t4ConnectorOffsetA T2_2 T1_2 = 84 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetA, T2_2, T1_2, T]

theorem t4ConnectorOffsetB_misses_T2_T1_1 :
    crossNorm4 t4ConnectorOffsetB T2_2 T1_1 = 196 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetB, T2_2, T1_1, T]

theorem t4ConnectorOffsetB_misses_T2_T1_2 :
    crossNorm4 t4ConnectorOffsetB T2_2 T1_2 = 156 := by
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, t4ConnectorOffsetB, T2_2, T1_2, T]

theorem no_single_translation_realizes_all_connector_norms (d : GridPoint) :
    ¬ (crossNorm4 d T2_2 T1_1 = 4 /\
        crossNorm4 d T2_2 T1_2 = 4 /\
        crossNorm4 d T4_0 T0_0 = 4 /\
        crossNorm4 d T4_0 T0_2 = 4) := by
  intro h
  rcases h with ⟨h211, h212, h400, h402⟩
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, T2_2, T1_1, T1_2, T4_0, T0_0, T0_2, T] at h211 h212 h400 h402
  nlinarith

theorem no_single_translation_realizes_all_connector_units (d : GridPoint) :
    ¬ (eucDist (localPoint T2_2) (translatedLocalPoint d T1_1) = 1 /\
        eucDist (localPoint T2_2) (translatedLocalPoint d T1_2) = 1 /\
        eucDist (localPoint T4_0) (translatedLocalPoint d T0_0) = 1 /\
        eucDist (localPoint T4_0) (translatedLocalPoint d T0_2) = 1) := by
  intro h
  rcases h with ⟨h211, h212, h400, h402⟩
  rw [eucDist_eq_one_iff, cross_sqDist'] at h211 h212 h400 h402
  norm_num [crossNorm4, translatedLocalGrid, translateGrid, localGrid,
    GridPoint.norm4, T2_2, T1_1, T1_2, T4_0, T0_0, T0_2, T] at h211 h212 h400 h402
  nlinarith

/-!
The intended global bridge should avoid asserting a false one-translation
closure.  A useful future interface is:

```
theorem connector_edges_unit_of_placement
    (place : Fin k -> LocalVertex -> R2)
    (hconnector :
      forall i u v,
        CrossBlock.NextConnector u v ->
        eucDist (place i u) (place (cyclicSucc hk i) v) = 1) :
    forall i u v,
      CrossBlock.NextConnector u v ->
      eucDist (place i u) (place (cyclicSucc hk i) v) = 1
```

The remaining exact equations for a pure grid translation `d = (a,b)` are:

* `T2_2 -> T1_1`: `3 * (a - 2)^2 + (b + 6)^2 = 4`.
* `T2_2 -> T1_2`: `3 * (a - 3)^2 + (b + 5)^2 = 4`.
* `T4_0 -> T0_0`: `3 * (a - 4)^2 + (b - 6)^2 = 4`.
* `T4_0 -> T0_2`: `3 * (a - 5)^2 + (b - 5)^2 = 4`.

The first two equations have solutions `(2,-4)` and `(3,-7)`.  The last two
have solutions `(4,4)` and `(5,7)`.  These sets are disjoint.
-/

end CrossBlockGeometry
end PachToth
end ErdosProblems1066

end
