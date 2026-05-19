import ErdosProblems1066.PachToth.CrossBlockDistanceSqReduction
import ErdosProblems1066.PachToth.RoleHingeCandidateSearchSurface

set_option autoImplicit false

/-!
# W33 cross-block metric inequalities

This file records the finite-index metric rows for the flexible
`RoleHingeCandidateSearchSurface` table shape, together with the concrete
length-one obstruction for the all-positive period lane.  The obstruction is
not a route facade: it compares the connector unit row forced by the period
surface with the exact local grid distance between `T2_2` and `T1_1`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace CrossBlockMetricInequalitiesW33

open Arithmetic
open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real

abbrev SameOppositeCandidate : Type :=
  RoleHingeCandidateSearchSurface.SameOppositeCandidate

abbrev PeriodSearchData (T : SameOppositeCandidate) : Type :=
  RoleHingeCandidateSearchSurface.PeriodSearchData T

abbrev LocalVertexIndex : Type :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev IndexedCrossBlockMetricTable
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) : Type :=
  RoleHingeCandidateSearchSurface.IndexedCrossBlockMetricTable P k hk

abbrev IndexedCrossBlockMetricTableFamily
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) : Type :=
  RoleHingeCandidateSearchSurface.IndexedCrossBlockMetricTableFamily P

abbrev CrossBlockMetricData
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) : Type :=
  RoleHingeCandidateSearchSurface.CrossBlockMetricData P

def localVertexIndex (u : LocalVertex) : LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.localVertexIndex u

def localVertexOfIndex (u : LocalVertexIndex) : LocalVertex :=
  CrossBlockLowerBoundsInterface.localVertexOfIndex u

def t2_2Index : LocalVertexIndex :=
  localVertexIndex T2_2

def t1_1Index : LocalVertexIndex :=
  localVertexIndex T1_1

@[simp]
theorem localVertexOfIndex_t2_2Index :
    localVertexOfIndex t2_2Index = T2_2 := by
  simp [localVertexOfIndex, t2_2Index, localVertexIndex]

@[simp]
theorem localVertexOfIndex_t1_1Index :
    localVertexOfIndex t1_1Index = T1_1 := by
  simp [localVertexOfIndex, t1_1Index, localVertexIndex]

/-! ## Sqrt-free rows for the flexible metric table -/

/-- Sqrt-free finite-index cross-block rows for the flexible search surface.
The table value is fixed to `1`; each row only has to prove that the squared
coordinate distance of the generated points is at least `1`. -/
structure IndexedSqDistanceRows
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (k : Nat) (hk : 0 < k) where
  sqDist_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          1 <=
            CrossBlockDistanceSqReduction.sqDist
              (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk i u)
              (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk j v)

namespace IndexedSqDistanceRows

/-- Squared-distance rows give the exact finite-index metric table expected by
`RoleHingeCandidateSearchSurface.IndexedCrossBlockMetricTable`. -/
def toMetricTable
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    {k : Nat} {hk : 0 < k}
    (R : IndexedSqDistanceRows P k hk) :
    IndexedCrossBlockMetricTable P k hk where
  lower := fun _i _u _j _v => 1
  lower_ge_one := by
    intro _i _u _j _v _hij
    norm_num
  lower_bound := by
    intro i u j v hij
    exact
      CrossBlockDistanceSqReduction.one_le_root_eucDist_of_one_le_sqDist
        (R.sqDist_ge_one i u j v hij)

@[simp]
theorem toMetricTable_lower
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    {k : Nat} {hk : 0 < k}
    (R : IndexedSqDistanceRows P k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    R.toMetricTable.lower i u j v = 1 :=
  rfl

end IndexedSqDistanceRows

/-- Sqrt-free rows for every positive period length. -/
structure IndexedSqDistanceRowsFamily
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) where
  rows :
    forall (k : Nat) (hk : 0 < k),
      IndexedSqDistanceRows P k hk

namespace IndexedSqDistanceRowsFamily

/-- Sqrt-free row families materialize the flexible indexed metric table
family. -/
def toMetricTableFamily
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (R : IndexedSqDistanceRowsFamily P) :
    IndexedCrossBlockMetricTableFamily P where
  table := fun k hk => (R.rows k hk).toMetricTable

/-- Sqrt-free row families materialize the `CrossBlockMetricData` package used
by the flexible generated metric route. -/
def toCrossBlockMetricData
    {T : SameOppositeCandidate}
    {P : PeriodSearchData T}
    (R : IndexedSqDistanceRowsFamily P) :
    CrossBlockMetricData P :=
  RoleHingeCandidateSearchSurface.CrossBlockMetricData.ofIndexedTables
    R.toMetricTableFamily

end IndexedSqDistanceRowsFamily

/-! ## Connector unit rows forced by period data -/

/-- A generated period row plus the connector table forces every cyclic
successor connector edge to be a unit row in the finite-indexed generated
points. -/
theorem indexedGeneratedPoint_cyclicSucc_connector_unit
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u v : LocalVertex)
    (hconn : CrossBlock.NextConnector u v) :
    _root_.eucDist
      (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk i
        (localVertexIndex u))
      (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk
        (cyclicSucc hk i) (localVertexIndex v)) = 1 := by
  let O := T.toFigure2TransitionObligations
  let base := BaseTransitionRealization.exactBase
  let orientation := P.orientation k hk
  have hsucc :
      GeneratedClosedChain.generatedPoint O hk base orientation
          (cyclicSucc hk i) v =
        (GeneratedClosedChain.generatedStep O orientation i).placeNext
          (GeneratedClosedChain.generatedPoint O hk base orientation i) v :=
    GeneratedClosedChain.generatedPoint_successor_compatible
      O hk base orientation (P.periodEquation k hk) i v
  have hunit :
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        ((O.transitionFor (orientation i)).placeNext
          (GeneratedClosedChain.generatedPoint O hk base orientation i) v) =
        1 :=
    Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
        O (orientation i)
        (GeneratedClosedChain.generatedPoint O hk base orientation i)
        u v hconn
  simpa [RoleHingeCandidateSearchSurface.indexedGeneratedPoint,
    localVertexIndex, CrossBlockLowerBoundsInterface.localVertexOfIndex_localVertexIndex,
    GeneratedClosedChain.generatedStep, O, base, orientation, hsucc] using hunit

theorem one_le_indexedGeneratedPoint_cyclicSucc_connector
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u v : LocalVertex)
    (hconn : CrossBlock.NextConnector u v) :
    1 <=
      _root_.eucDist
        (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk i
          (localVertexIndex u))
        (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk
          (cyclicSucc hk i) (localVertexIndex v)) := by
  rw [indexedGeneratedPoint_cyclicSucc_connector_unit P hk i u v hconn]

/-- The named `T2_2 -> T1_1` connector unit row. -/
theorem indexedGeneratedPoint_cyclicSucc_t2_2_t1_1_unit
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) :
    _root_.eucDist
      (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk i
        t2_2Index)
      (RoleHingeCandidateSearchSurface.indexedGeneratedPoint P hk
        (cyclicSucc hk i) t1_1Index) = 1 := by
  simpa [t2_2Index, t1_1Index, localVertexIndex] using
    indexedGeneratedPoint_cyclicSucc_connector_unit
      P hk i T2_2 T1_1 (by decide)

/-! ## Exact-base length-one obstruction -/

theorem exactBase_t2_2_t1_1_sqDist :
    CrossBlockDistanceSqReduction.sqDist
        (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) = 12 := by
  calc
    CrossBlockDistanceSqReduction.sqDist
        (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) =
        ((ExactLocalGeometry.localNorm4 T2_2 T1_1 : Int) : Real) / 4 := by
      simpa [CrossBlockDistanceSqReduction.sqDist,
        AffineLocalGeometry.distSq, BaseTransitionRealization.exactBase] using
        ExactLocalGeometry.local_sqDist' T2_2 T1_1
    _ = 12 := by
      norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
        ExactLocalGeometry.GridPoint.norm4, T, T2_2, T1_1]

theorem exactBase_t2_2_t1_1_eucDist_sq :
    _root_.eucDist
        (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) ^ 2 = 12 := by
  rw [_root_.eucDist_sq]
  simpa [CrossBlockDistanceSqReduction.sqDist,
    AffineLocalGeometry.distSq] using exactBase_t2_2_t1_1_sqDist

theorem exactBase_t2_2_t1_1_not_unit :
    Not
      (_root_.eucDist
        (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) = 1) := by
  intro hunit
  have hsq :
      _root_.eucDist
          (BaseTransitionRealization.exactBase T2_2)
          (BaseTransitionRealization.exactBase T1_1) ^ 2 = 1 := by
    rw [hunit]
    norm_num
  linarith [exactBase_t2_2_t1_1_eucDist_sq]

theorem exactBase_t2_2_t1_1_ge_one :
    1 <=
      _root_.eucDist
        (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) := by
  simpa [BaseTransitionRealization.exactBase] using
    ExactLocalGeometry.local_separated T2_2 T1_1 (by decide)

/-- At period length one, the generated connector row collapses to the exact
base `T2_2 -> T1_1` distance. -/
theorem length_one_period_forces_exactBase_t2_2_t1_1_unit
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T) :
    _root_.eucDist
      (BaseTransitionRealization.exactBase T2_2)
      (BaseTransitionRealization.exactBase T1_1) = 1 := by
  have hunit :=
    indexedGeneratedPoint_cyclicSucc_t2_2_t1_1_unit
      P (k := 1) (by decide) (0 : Fin 1)
  simpa [RoleHingeCandidateSearchSurface.indexedGeneratedPoint,
    t2_2Index, t1_1Index, localVertexIndex,
    BaseTransitionRealization.exactBase, cyclicSucc] using hunit

/-- The all-positive `PeriodSearchData` surface is already inconsistent at
length one, before any cross-block metric table can be inhabited. -/
theorem not_nonempty_periodSearchData
    (T : SameOppositeCandidate) :
    Not (Nonempty (PeriodSearchData T)) := by
  intro hP
  cases hP with
  | intro P =>
      exact exactBase_t2_2_t1_1_not_unit
        (length_one_period_forces_exactBase_t2_2_t1_1_unit P)

theorem not_exists_candidate_periodSearchData :
    Not (Exists fun T : SameOppositeCandidate =>
      Nonempty (PeriodSearchData T)) := by
  intro h
  cases h with
  | intro T hP =>
      exact not_nonempty_periodSearchData T hP

/-- Consequently there is no inhabited indexed metric-table family in this
all-positive flexible period lane.  The obstruction is the period/unit row,
not a missing table projection. -/
theorem not_exists_indexedCrossBlockMetricTableFamily :
    Not
      (Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (IndexedCrossBlockMetricTableFamily P)) := by
  intro h
  cases h with
  | intro T hrest =>
      cases hrest with
      | intro P _hM =>
          exact not_nonempty_periodSearchData T (Nonempty.intro P)

/-- The same length-one obstruction blocks `CrossBlockMetricData` in this
all-positive flexible period lane. -/
theorem not_exists_crossBlockMetricData :
    Not
      (Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (CrossBlockMetricData P)) := by
  intro h
  cases h with
  | intro T hrest =>
      cases hrest with
      | intro P _hM =>
          exact not_nonempty_periodSearchData T (Nonempty.intro P)

end

end CrossBlockMetricInequalitiesW33
end PachToth
end ErdosProblems1066
