import ErdosProblems1066.PachToth.AffineLocalGeometry
import ErdosProblems1066.PachToth.CrossBlockGeometry
import ErdosProblems1066.PachToth.CrossBlockLowerBoundsInterface

set_option autoImplicit false

/-!
# Cross-block distance square reductions

This module records helper lemmas that remove square roots from cross-block
lower-bound obligations.  For exact translated local blocks, the remaining
condition is an integer `norm4` polynomial.  For the role-hinged generated
family, the generated coordinates are still abstract, so the compile-checked
interface asks directly for coordinate square-distance inequalities and
projects them to the existing Euclidean lower-bound table.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockDistanceSqReduction

open FiniteGraph
open CrossBlockGeometry
open CrossBlockLowerBoundsInterface

noncomputable section

abbrev R2 := Prod Real Real

/-- Squared coordinate distance for real plane points. -/
def sqDist (p q : R2) : Real :=
  AffineLocalGeometry.distSq p q

@[simp]
theorem sqDist_eq_coordinate (p q : R2) :
    sqDist p q = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  rfl

/-- Root Euclidean separation at threshold `1` is exactly coordinate
square-distance separation at threshold `1`. -/
theorem one_le_root_eucDist_iff_one_le_sqDist (p q : R2) :
    1 <= _root_.eucDist p q <-> 1 <= sqDist p q := by
  simpa [sqDist, AffineLocalGeometry.distSq,
    AffineLocalGeometry.eucDist_eq_root_eucDist] using
    (Geometry.Distance.eucDist_ge_one_iff p q)

/-- Coordinate square-distance separation gives the root Euclidean lower
bound used by the global Pach--Toth interfaces. -/
theorem one_le_root_eucDist_of_one_le_sqDist {p q : R2}
    (h : 1 <= sqDist p q) :
    1 <= _root_.eucDist p q :=
  (one_le_root_eucDist_iff_one_le_sqDist p q).2 h

/-- The translated exact cross-block integer norm is the explicit grid
polynomial in the translation offset and the two local grid coordinates. -/
theorem crossNorm4_eq_grid_polynomial
    (d : ExactLocalGeometry.GridPoint) (u v : LocalVertex) :
    crossNorm4 d u v =
      3 * ((ExactLocalGeometry.localGrid u).i -
          ((ExactLocalGeometry.localGrid v).i + d.i)) ^ 2 +
        ((ExactLocalGeometry.localGrid u).j -
          ((ExactLocalGeometry.localGrid v).j + d.j)) ^ 2 := by
  rfl

/-- Exact translated cross-block lower bounds reduce to `4 <= crossNorm4`. -/
theorem one_le_cross_eucDist_iff_four_le_crossNorm4
    (d : ExactLocalGeometry.GridPoint) (u v : LocalVertex) :
    1 <= Geometry.Distance.eucDist
        (ExactLocalGeometry.localPoint u) (translatedLocalPoint d v) <->
      (4 : Int) <= crossNorm4 d u v := by
  rw [Geometry.Distance.eucDist_ge_one_iff]
  rw [cross_sqDist']
  constructor
  · intro h
    have hreal : (4 : Real) <= ((crossNorm4 d u v : Int) : Real) := by
      nlinarith
    exact_mod_cast hreal
  · intro h
    have hreal : (4 : Real) <= ((crossNorm4 d u v : Int) : Real) := by
      exact_mod_cast h
    nlinarith

/-- Root-distance version of `one_le_cross_eucDist_iff_four_le_crossNorm4`. -/
theorem one_le_cross_root_eucDist_iff_four_le_crossNorm4
    (d : ExactLocalGeometry.GridPoint) (u v : LocalVertex) :
    1 <= _root_.eucDist
        (ExactLocalGeometry.localPoint u) (translatedLocalPoint d v) <->
      (4 : Int) <= crossNorm4 d u v := by
  simpa [AffineLocalGeometry.eucDist_eq_root_eucDist] using
    (one_le_cross_eucDist_iff_four_le_crossNorm4 d u v)

/-- Exact translated cross-block lower bounds reduce directly to the integer
grid-coordinate polynomial. -/
theorem one_le_cross_root_eucDist_iff_grid_polynomial
    (d : ExactLocalGeometry.GridPoint) (u v : LocalVertex) :
    1 <= _root_.eucDist
        (ExactLocalGeometry.localPoint u) (translatedLocalPoint d v) <->
      (4 : Int) <=
        3 * ((ExactLocalGeometry.localGrid u).i -
            ((ExactLocalGeometry.localGrid v).i + d.i)) ^ 2 +
          ((ExactLocalGeometry.localGrid u).j -
            ((ExactLocalGeometry.localGrid v).j + d.j)) ^ 2 := by
  simpa [crossNorm4_eq_grid_polynomial] using
    (one_le_cross_root_eucDist_iff_four_le_crossNorm4 d u v)

/-- Squared coordinate distance between generated finite-indexed points. -/
def indexedGeneratedSqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  sqDist (indexedGeneratedPoint F hk i u) (indexedGeneratedPoint F hk j v)

@[simp]
theorem indexedGeneratedSqDist_eq_coordinate
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    indexedGeneratedSqDist F hk i u j v =
      ((indexedGeneratedPoint F hk i u).1 -
          (indexedGeneratedPoint F hk j v).1) ^ 2 +
        ((indexedGeneratedPoint F hk i u).2 -
          (indexedGeneratedPoint F hk j v).2) ^ 2 := by
  rfl

/-- Generated finite-index Euclidean separation at threshold `1` is equivalent
to the coordinate square-distance inequality. -/
theorem one_le_indexedGenerated_eucDist_iff_sqDist
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    1 <=
        _root_.eucDist
          (indexedGeneratedPoint F hk i u)
          (indexedGeneratedPoint F hk j v) <->
      1 <= indexedGeneratedSqDist F hk i u j v := by
  exact one_le_root_eucDist_iff_one_le_sqDist
    (indexedGeneratedPoint F hk i u) (indexedGeneratedPoint F hk j v)

/-- A generated finite-index cross-block table stated only in squared
coordinate distances. -/
structure IndexedCrossBlockSqDistanceTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  sqDist_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j -> 1 <= indexedGeneratedSqDist F hk i u j v

namespace IndexedCrossBlockSqDistanceTable

/-- The square-distance table induces the existing Euclidean lower table by
using the fixed lower bound `1`. -/
def toLowerTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedCrossBlockSqDistanceTable F k hk) :
    IndexedCrossBlockLowerTable F k hk where
  lower := fun _ _ _ _ => 1
  lower_ge_one := by
    intro i u j v hij
    norm_num
  lower_bound := by
    intro i u j v hij
    exact
      (one_le_indexedGenerated_eucDist_iff_sqDist F hk i u j v).2
        (T.sqDist_ge_one i u j v hij)

/-- The induced lower table has the expected fixed value. -/
@[simp]
theorem toLowerTable_lower
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedCrossBlockSqDistanceTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    T.toLowerTable.lower i u j v = 1 :=
  rfl

/-- A square-distance table supplies generated global separation for one block
count through the existing cross-block lower-bound interface. -/
theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedCrossBlockSqDistanceTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toLowerTable.generatedGlobalSeparation

end IndexedCrossBlockSqDistanceTable

/-- A family of generated finite-index square-distance tables, one for each
positive block count. -/
structure IndexedCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      IndexedCrossBlockSqDistanceTable F k hk

namespace IndexedCrossBlockSqDistanceTableFamily

/-- Convert a square-distance table family to the existing lower-table
family. -/
def toLowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockSqDistanceTableFamily F) :
    IndexedCrossBlockLowerTableFamily F where
  table := fun k hk => (T.table k hk).toLowerTable

/-- Convert a square-distance table family to the final cross-block
lower-bound facade. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockSqDistanceTableFamily F) :
    CrossBlockLowerBounds F :=
  CrossBlockLowerBounds.ofIndexedTables T.toLowerTableFamily

/-- The square-distance table family supplies generated separation at every
positive block count. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (T.table k hk).generatedGlobalSeparation

/-- Final exact Pach--Toth target from period-search data plus generated
square-distance cross-block inequalities. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

/-- Final arbitrary-`n` Pach--Toth target from period-search data plus
generated square-distance cross-block inequalities. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockSqDistanceTableFamily F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end IndexedCrossBlockSqDistanceTableFamily

end

end CrossBlockDistanceSqReduction
end PachToth
end ErdosProblems1066
