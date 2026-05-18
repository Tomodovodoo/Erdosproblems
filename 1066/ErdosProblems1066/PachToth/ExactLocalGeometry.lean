import ErdosProblems1066.Geometry.Distance
import ErdosProblems1066.PachToth.FiniteGraph

/-!
# Exact Pach--Toth Local Geometry

This module gives an exact algebraic realization of the transcribed
Pach--Toth first-block graph from `FiniteGraph`.

The coordinates are not the rounded PostScript drawing coordinates.  They
place the sixteen local vertices on the grid
`(i * sqrt 3 / 2, j / 2)`, where all finite checks reduce to exact integer
arithmetic for the squared distances.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalGeometry

open Geometry.Distance
open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real

/-- The horizontal half-height used by exact unit equilateral triangles. -/
def h : Real := Real.sqrt 3 / 2

/-- Integer grid coordinates interpreted as `(i * sqrt 3 / 2, j / 2)`. -/
structure GridPoint where
  i : Int
  j : Int
  deriving DecidableEq, Repr

namespace GridPoint

/-- Interpret a grid point as an exact real point. -/
def toPoint (p : GridPoint) : R2 :=
  ((p.i : Real) * h, (p.j : Real) / 2)

/-- Four times the squared Euclidean distance, kept integral. -/
def norm4 (p q : GridPoint) : Int :=
  3 * (p.i - q.i) ^ 2 + (p.j - q.j) ^ 2

theorem h_sq : h ^ 2 = (3 : Real) / 4 := by
  unfold h
  rw [div_pow, Real.sq_sqrt]
  · norm_num
  · norm_num

theorem sqDist_toPoint' (p q : GridPoint) :
    ((toPoint p).1 - (toPoint q).1) ^ 2 + ((toPoint p).2 - (toPoint q).2) ^ 2 =
      ((norm4 p q : Int) : Real) / 4 := by
  have hcast :
      (((norm4 p q : Int) : Real) / 4) =
        (3 * ((p.i : Real) - (q.i : Real)) ^ 2 +
            ((p.j : Real) - (q.j : Real)) ^ 2) / 4 := by
    unfold norm4
    push_cast
    ring
  rw [hcast]
  unfold toPoint
  ring_nf
  rw [h_sq]
  ring_nf

end GridPoint

/-- Exact grid coordinates for all sixteen local vertices. -/
def localGrid : LocalVertex -> GridPoint
  | .r => { i := 0, j := 0 }
  | .tri 0 0 => { i := 1, j := -3 }
  | .tri 0 1 => { i := 1, j := -1 }
  | .tri 0 2 => { i := 0, j := -2 }
  | .tri 1 0 => { i := 1, j := 1 }
  | .tri 1 1 => { i := 1, j := 3 }
  | .tri 1 2 => { i := 0, j := 2 }
  | .tri 2 0 => { i := 2, j := -4 }
  | .tri 2 1 => { i := 2, j := -2 }
  | .tri 2 2 => { i := 3, j := -3 }
  | .tri 3 0 => { i := 3, j := 3 }
  | .tri 3 1 => { i := 2, j := 2 }
  | .tri 3 2 => { i := 2, j := 4 }
  | .tri 4 0 => { i := 5, j := 3 }
  | .tri 4 1 => { i := 4, j := 2 }
  | .tri 4 2 => { i := 4, j := 4 }

/-- Exact real coordinates for all sixteen local vertices. -/
def localPoint (v : LocalVertex) : R2 :=
  (localGrid v).toPoint

/-- Four times the squared distance between local vertices. -/
def localNorm4 (u v : LocalVertex) : Int :=
  (localGrid u).norm4 (localGrid v)

theorem local_sqDist' (u v : LocalVertex) :
    ((localPoint u).1 - (localPoint v).1) ^ 2 + ((localPoint u).2 - (localPoint v).2) ^ 2 =
      ((localNorm4 u v : Int) : Real) / 4 := by
  simpa [localPoint, localNorm4] using GridPoint.sqDist_toPoint' (localGrid u) (localGrid v)

/-- Every finite graph edge is a unit-distance edge in the exact realization. -/
theorem adj_unit_distance :
    forall u v : LocalVertex, adj u v = true ->
      eucDist (localPoint u) (localPoint v) = 1 := by
  intro u v huv
  rw [eucDist_eq_one_iff]
  rw [local_sqDist']
  have hnorm : localNorm4 u v = 4 := by
    revert u v
    decide
  rw [hnorm]
  norm_num

/-- Distinct local vertices are separated by distance at least `1`. -/
theorem local_separated :
    forall u v : LocalVertex, u ≠ v ->
      1 <= eucDist (localPoint u) (localPoint v) := by
  intro u v huv
  rw [eucDist_ge_one_iff]
  rw [local_sqDist']
  have hnorm : 4 <= localNorm4 u v := by
    revert u v
    decide
  have hnormReal : (4 : Real) <= (localNorm4 u v : Real) := by
    exact_mod_cast hnorm
  nlinarith

/-- The exact coordinates are injective on local vertices. -/
theorem localPoint_injective : Function.Injective localPoint := by
  intro u v hpoint
  by_contra hne
  have hsep := local_separated u v hne
  have hzero : eucDist (localPoint u) (localPoint v) = 0 := by
    rw [hpoint]
    exact eucDist_self (localPoint v)
  linarith

/-- Packaged exact local realization certificate for the finite graph. -/
theorem exact_local_realization :
    (forall u v : LocalVertex, adj u v = true ->
      eucDist (localPoint u) (localPoint v) = 1) /\
    (forall u v : LocalVertex, u ≠ v ->
      1 <= eucDist (localPoint u) (localPoint v)) :=
  ⟨adj_unit_distance, local_separated⟩

end ExactLocalGeometry
end PachToth
end ErdosProblems1066

end
