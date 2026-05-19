import ErdosProblems1066.PachToth.PachTothFinalDataAssembly
import ErdosProblems1066.PachToth.RoleHingeCandidateSearchSurface

set_option autoImplicit false

/-!
# W33 finite exact-base candidate search

The all-positive exact-base flexible route has a length-one finite obstruction.
At length one, a stored period row makes the selected same/opposite step fix
`exactBase`. The connector row for `T2_2` to `T1_1` would then make a checked
exact-base distance equal to one, but its squared distance is twelve.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteReducedMetricCandidateSearchW33

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev SameOppositeCandidate : Type :=
  RoleHingeCandidateSearchSurface.SameOppositeCandidate

abbrev PeriodSearchData (T : SameOppositeCandidate) : Type :=
  RoleHingeCandidateSearchSurface.PeriodSearchData T

abbrev CrossBlockMetricData {T : SameOppositeCandidate} (P : PeriodSearchData T) : Type :=
  RoleHingeCandidateSearchSurface.CrossBlockMetricData P

abbrev FlexiblePeriodLowerTableFamily : Type :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily

abbrev DirectFlexibleSourceShape : Prop :=
  Exists fun T : SameOppositeCandidate =>
    Exists fun P : PeriodSearchData T =>
      Nonempty (CrossBlockMetricData P)

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

theorem not_exists_candidate_periodSearchData :
    Not (Exists fun T : SameOppositeCandidate => Nonempty (PeriodSearchData T)) := by
  intro H
  cases H with
  | intro T hP =>
      exact not_nonempty_periodSearchData T hP

theorem not_directFlexibleSourceShape :
    Not DirectFlexibleSourceShape := by
  intro H
  cases H with
  | intro T Hnext =>
      cases Hnext with
      | intro P _ =>
          exact not_nonempty_periodSearchData T (Nonempty.intro P)

theorem not_nonempty_flexiblePeriodLowerTableFamily :
    Not (Nonempty FlexiblePeriodLowerTableFamily) := by
  intro H
  cases H with
  | intro F =>
      let W := F.word 1 (by decide)
      have hfix :
          (F.transitions.toFigure2TransitionObligations.transitionFor
            (W (0 : Fin 1))).placeNext BaseTransitionRealization.exactBase =
            BaseTransitionRealization.exactBase := by
        simpa [FlexiblePeriodLowerTableFamily,
          PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily.orientation,
          PeriodInterface.GeneratedPeriodEquation, GeneratedClosedChain.generatedBlock,
          GeneratedClosedChain.orientationAt, W] using
            F.period 1 (by decide)
      have hunit :
          _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
            ((F.transitions.toFigure2TransitionObligations.transitionFor
              (W (0 : Fin 1))).placeNext BaseTransitionRealization.exactBase T1_1) = 1 := by
        exact
          Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
            F.transitions.toFigure2TransitionObligations (W (0 : Fin 1))
            BaseTransitionRealization.exactBase T2_2 T1_1
            (by decide)
      have hunitBase :
          _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
            (BaseTransitionRealization.exactBase T1_1) = 1 := by
        simpa [hfix] using hunit
      exact exactBase_T2_2_T1_1_not_unit hunitBase

end
end FiniteReducedMetricCandidateSearchW33
end PachToth
end ErdosProblems1066
