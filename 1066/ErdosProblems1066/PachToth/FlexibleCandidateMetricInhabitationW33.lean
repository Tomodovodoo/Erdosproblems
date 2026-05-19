import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11

set_option autoImplicit false

/-!
# W33 flexible candidate metric inhabitation

This file pins the direct W11 source gate to the actual candidate/period/
metric package and to the finite indexed cross-block metric-table surface.
The indexed tables are constructively equivalent to the W11 metric data, but
the all-positive period row itself is refuted by the checked length-one
exact-base obstruction.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleCandidateMetricInhabitationW33

noncomputable section

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev SameOppositeCandidate : Type :=
  FlexibleTransitionSearchW11.SameOppositeCandidate

abbrev PeriodSearchData (T : SameOppositeCandidate) : Type :=
  FlexibleTransitionSearchW11.PeriodSearchData T

abbrev CrossBlockMetricData
    {T : SameOppositeCandidate} (P : PeriodSearchData T) : Type :=
  RoleHingeCandidateSearchSurface.CrossBlockMetricData P

abbrev IndexedCrossBlockMetricTableFamily
    {T : SameOppositeCandidate} (P : PeriodSearchData T) : Type :=
  RoleHingeCandidateSearchSurface.IndexedCrossBlockMetricTableFamily P

abbrev CandidatePeriodMetricData : Type :=
  FlexibleTransitionSearchW11.CandidatePeriodMetricData

abbrev DirectFlexibleSourcePayload : Type :=
  FlexibleTransitionSearchW11.DirectFlexibleSourcePayload

/-- Candidate, all-positive period data, and indexed cross-block metric
tables with the built-in `>= 1` and distance-bound rows. -/
abbrev IndexedCandidatePeriodMetricTableData : Type :=
  Sigma fun T : SameOppositeCandidate =>
    Sigma fun P : PeriodSearchData T =>
      IndexedCrossBlockMetricTableFamily P

/-- Repackage indexed metric tables as the real W11 candidate/period/metric
source data. -/
def candidatePeriodMetricDataOfIndexedTables
    (D : IndexedCandidatePeriodMetricTableData) :
    CandidatePeriodMetricData :=
  Sigma.mk D.1
    (Sigma.mk D.2.1
      (RoleHingeCandidateSearchSurface.CrossBlockMetricData.ofIndexedTables
        D.2.2))

/-- Re-index real W11 cross-block metric data as finite table rows. -/
def indexedTablesOfCandidatePeriodMetricData
    (D : CandidatePeriodMetricData) :
    IndexedCandidatePeriodMetricTableData :=
  Sigma.mk D.1
    (Sigma.mk D.2.1
      (RoleHingeCandidateSearchSurface.CrossBlockMetricData.toIndexedTableFamily
        D.2.2))

/-- The real W11 gate is exactly the indexed cross-block table source, once
the same/opposite candidate and all-positive period data have been supplied. -/
theorem nonempty_candidatePeriodMetricData_iff_indexedTables :
    Nonempty CandidatePeriodMetricData <->
      Nonempty IndexedCandidatePeriodMetricTableData := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro D =>
        exact Nonempty.intro (indexedTablesOfCandidatePeriodMetricData D)
  case mpr =>
    intro H
    cases H with
    | intro D =>
        exact Nonempty.intro (candidatePeriodMetricDataOfIndexedTables D)

/-- Existential spelling of the sharpened indexed-table source obligation. -/
theorem nonempty_candidatePeriodMetricData_iff_exists_indexedTables :
    Nonempty CandidatePeriodMetricData <->
      Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (IndexedCrossBlockMetricTableFamily P) := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro D =>
        exact
          Exists.intro D.1
            (Exists.intro D.2.1
              ((RoleHingeCandidateSearchSurface.CrossBlockMetricData.nonempty_iff_indexedTables).1
                (Nonempty.intro D.2.2)))
  case mpr =>
    intro H
    cases H with
    | intro T Hrest =>
        cases Hrest with
        | intro P HM =>
            have hMetric : Nonempty (CrossBlockMetricData P) :=
              (RoleHingeCandidateSearchSurface.CrossBlockMetricData.nonempty_iff_indexedTables).2
                HM
            cases hMetric with
            | intro M =>
                exact Nonempty.intro (Sigma.mk T (Sigma.mk P M))

/-- The provenance-free W11 direct payload has the same indexed-table source
obligation as `CandidatePeriodMetricData`. -/
theorem nonempty_directFlexibleSourcePayload_iff_indexedTables :
    Nonempty DirectFlexibleSourcePayload <->
      Nonempty IndexedCandidatePeriodMetricTableData :=
  Iff.trans
    FlexibleTransitionSearchW11.nonempty_directFlexibleSourcePayload_iff_candidatePeriodMetricData
    nonempty_candidatePeriodMetricData_iff_indexedTables

/-- Exact period-data blocker inherited from the checked length-one
exact-base obstruction. -/
lemma exactBase_T2_2_T1_1_sqDist :
    _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) ^ 2 = 12 := by
  have hdistSq :
      _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
          (BaseTransitionRealization.exactBase T1_1) ^ 2 =
        ((ExactLocalGeometry.localNorm4 T2_2 T1_1 : Int) : Real) / 4 := by
    rw [_root_.eucDist_sq]
    simpa [BaseTransitionRealization.exactBase] using
      ExactLocalGeometry.local_sqDist' T2_2 T1_1
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T1_1, T2_2] at hdistSq
  simpa [T, T1_1, T2_2] using hdistSq

lemma exactBase_T2_2_T1_1_not_unit :
    Not (_root_.eucDist (BaseTransitionRealization.exactBase T2_2)
        (BaseTransitionRealization.exactBase T1_1) = 1) := by
  intro h
  have hsq :
      _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
          (BaseTransitionRealization.exactBase T1_1) ^ 2 = 1 := by
    rw [h]
    norm_num
  linarith [exactBase_T2_2_T1_1_sqDist]

theorem not_nonempty_periodSearchData
    (T : SameOppositeCandidate) :
    Not (Nonempty (PeriodSearchData T)) := by
  intro H
  cases H with
  | intro P =>
      let W := P.word 1 (by decide)
      have hfix :
          (T.toFigure2TransitionObligations.transitionFor
            (W (0 : Fin 1))).placeNext BaseTransitionRealization.exactBase =
            BaseTransitionRealization.exactBase := by
        simpa [PeriodSearchData,
          RoleHingeCandidateSearchSurface.PeriodSearchData.periodEquation,
          RoleHingeCandidateSearchSurface.PeriodSearchData.orientation,
          PeriodInterface.GeneratedPeriodEquation, GeneratedClosedChain.generatedBlock,
          GeneratedClosedChain.orientationAt, W] using
            P.periodEquation 1 (by decide)
      have hunit :
          _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
            ((T.toFigure2TransitionObligations.transitionFor
              (W (0 : Fin 1))).placeNext BaseTransitionRealization.exactBase T1_1) = 1 := by
        exact
          Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
            T.toFigure2TransitionObligations (W (0 : Fin 1))
            BaseTransitionRealization.exactBase T2_2 T1_1
            (by decide)
      have hunitBase :
          _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
            (BaseTransitionRealization.exactBase T1_1) = 1 := by
        simpa [hfix] using hunit
      exact exactBase_T2_2_T1_1_not_unit hunitBase

/-- There is no candidate carrying all-positive period data, before metric
rows are even considered. -/
theorem not_exists_candidate_periodSearchData :
    Not (Exists fun T : SameOppositeCandidate =>
      Nonempty (PeriodSearchData T)) := by
  intro H
  cases H with
  | intro T hP =>
      exact not_nonempty_periodSearchData T hP

/-- Therefore no indexed cross-block metric table family can inhabit the real
candidate/period source shape: any such table package already contains the
refuted period data. -/
theorem not_exists_candidate_period_indexedTables :
    Not
      (Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (IndexedCrossBlockMetricTableFamily P)) := by
  intro H
  cases H with
  | intro T Hrest =>
      cases Hrest with
      | intro P _ =>
          exact not_nonempty_periodSearchData T (Nonempty.intro P)

/-- The requested real W11 candidate/period/metric source is uninhabited in
this exact-base all-positive surface. -/
theorem not_nonempty_candidatePeriodMetricData :
    Not (Nonempty CandidatePeriodMetricData) := by
  intro H
  exact
    not_exists_candidate_period_indexedTables
      (nonempty_candidatePeriodMetricData_iff_exists_indexedTables.1 H)

/-- Equivalently, the indexed cross-block table source with `>= 1` and
distance-bound rows is uninhabited. -/
theorem not_nonempty_indexedCandidatePeriodMetricTableData :
    Not (Nonempty IndexedCandidatePeriodMetricTableData) := by
  intro H
  exact
    not_nonempty_candidatePeriodMetricData
      (nonempty_candidatePeriodMetricData_iff_indexedTables.2 H)

/-- The real `DirectFlexibleSourcePayload` gate is blocked for the same
reason: it would supply `CandidatePeriodMetricData`, hence a refuted
length-one period row. -/
theorem not_nonempty_directFlexibleSourcePayload :
    Not (Nonempty DirectFlexibleSourcePayload) := by
  intro H
  exact
    not_nonempty_candidatePeriodMetricData
      (FlexibleTransitionSearchW11.nonempty_directFlexibleSourcePayload_iff_candidatePeriodMetricData.1
        H)

end
end FlexibleCandidateMetricInhabitationW33
end PachToth
end ErdosProblems1066
