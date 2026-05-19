import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11

set_option autoImplicit false

/-!
# W33 direct flexible source payload

This file keeps the W11 direct payload source-facing: the primary constructor
fills the same/opposite candidate, period, and cross-block metric fields
directly.  The concrete lower-table handoffs remain conditional on their
actual source packages.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace DirectFlexibleSourcePayloadW33

abbrev DirectFlexibleSourcePayload : Type :=
  FlexibleTransitionSearchW11.DirectFlexibleSourcePayload

abbrev SameOppositeCandidate : Type :=
  FlexibleTransitionSearchW11.SameOppositeCandidate

abbrev PeriodSearchData (T : SameOppositeCandidate) : Type :=
  FlexibleTransitionSearchW11.PeriodSearchData T

abbrev CrossBlockMetricData
    {T : SameOppositeCandidate} (P : PeriodSearchData T) : Type :=
  RoleHingeCandidateSearchSurface.CrossBlockMetricData P

abbrev NonRigidRouteSourceFields : Type :=
  FlexibleTransitionSearchW11.NonRigidRouteSourceFields

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev ConcreteSourceWithTransition : Type :=
  FlexibleTransitionSearchW11.ConcreteSourceWithTransition

abbrev PeriodCandidatePartialLowerTableData : Type :=
  PeriodCandidateTargetRoute.PeriodCandidatePartialLowerTableData

/-- The explicit field package for `DirectFlexibleSourcePayload`. -/
abbrev CandidatePeriodMetricFields : Type :=
  Sigma fun T : SameOppositeCandidate =>
    Sigma fun P : PeriodSearchData T =>
      CrossBlockMetricData P

/-- Build the direct W11 payload by filling exactly its constructor fields. -/
def payloadOfCandidatePeriodMetric
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (M : CrossBlockMetricData P) :
    DirectFlexibleSourcePayload where
  candidate := T
  periodData := P
  metricData := M

/-- Nonempty direct payload from concrete same/opposite candidate data,
all-positive period data, and cross-block metric data. -/
theorem nonempty_directFlexibleSourcePayload_of_candidate_period_metric
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (M : CrossBlockMetricData P) :
    Nonempty DirectFlexibleSourcePayload :=
  Nonempty.intro (payloadOfCandidatePeriodMetric P M)

/-- Repackage the explicit field package as the direct W11 payload. -/
def payloadOfCandidatePeriodMetricFields
    (S : CandidatePeriodMetricFields) :
    DirectFlexibleSourcePayload :=
  payloadOfCandidatePeriodMetric S.2.1 S.2.2

/-- The direct payload is exactly the explicit candidate/period/metric field
package, with no endpoint-to-source step. -/
theorem nonempty_directFlexibleSourcePayload_iff_candidate_period_metric_fields :
    Nonempty DirectFlexibleSourcePayload <->
      Nonempty CandidatePeriodMetricFields := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro D =>
        exact
          Nonempty.intro
            (Sigma.mk D.candidate (Sigma.mk D.periodData D.metricData))
  case mpr =>
    intro H
    cases H with
    | intro S =>
        exact
          Nonempty.intro
            (payloadOfCandidatePeriodMetricFields S)

/-- Forget W11 source fields to the direct payload name. -/
def payloadOfNonRigidRouteSourceFields
    (S : NonRigidRouteSourceFields) :
    DirectFlexibleSourcePayload :=
  FlexibleTransitionSearchW11.DirectFlexibleSourcePayload.ofSourceFields S

/-- Conditional handoff from an existing concrete period/non-connector lower
table package to the provenance-free direct payload. -/
def payloadOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectFlexibleSourcePayload :=
  payloadOfNonRigidRouteSourceFields
    (FlexibleTransitionSearchW11.sourceFieldsOfConcreteNonConnectorLowerTableFamily
      C)

/-- Any supplied concrete period/non-connector lower-table package inhabits
the direct W11 payload. -/
theorem nonempty_directFlexibleSourcePayload_of_concreteNonConnectorLowerTableFamily
    (H : Nonempty ConcreteNonConnectorLowerTableFamily) :
    Nonempty DirectFlexibleSourcePayload := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (payloadOfConcreteNonConnectorLowerTableFamily C)

/-- Conditional handoff from a concrete value-matrix family through its lower
table projection. -/
def payloadOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    DirectFlexibleSourcePayload :=
  payloadOfConcreteNonConnectorLowerTableFamily
    C.toConcreteNonConnectorLowerTableFamily

/-- Any supplied concrete value-matrix family inhabits the direct W11 payload. -/
theorem nonempty_directFlexibleSourcePayload_of_concreteValueMatrixFamily
    (H : Nonempty ConcreteValueMatrixFamily) :
    Nonempty DirectFlexibleSourcePayload := by
  cases H with
  | intro C =>
      exact Nonempty.intro (payloadOfConcreteValueMatrixFamily C)

/-- The transition-equality wrapper used by the exact-target spelling also
forgets to the direct W11 payload. -/
def payloadOfConcreteSourceWithTransition
    (C : ConcreteSourceWithTransition) :
    DirectFlexibleSourcePayload :=
  payloadOfConcreteNonConnectorLowerTableFamily C.1

/-- Any supplied concrete period/non-connector/transition source inhabits the
direct W11 payload after forgetting the transition equality. -/
theorem nonempty_directFlexibleSourcePayload_of_concreteSourceWithTransition
    (H : Nonempty ConcreteSourceWithTransition) :
    Nonempty DirectFlexibleSourcePayload := by
  cases H with
  | intro C =>
      exact Nonempty.intro (payloadOfConcreteSourceWithTransition C)

/-- The partial period/non-connector source from the target-route file also
forgets to the direct W11 payload. -/
def payloadOfPeriodCandidatePartialLowerTableData
    (D : PeriodCandidatePartialLowerTableData) :
    DirectFlexibleSourcePayload :=
  payloadOfConcreteSourceWithTransition
    D.toConcreteNonConnectorLowerTableFamilyWithTransition

/-- Any supplied partial period/non-connector source inhabits the direct W11
payload. -/
theorem nonempty_directFlexibleSourcePayload_of_periodCandidatePartialLowerTableData
    (H : Nonempty PeriodCandidatePartialLowerTableData) :
    Nonempty DirectFlexibleSourcePayload := by
  cases H with
  | intro D =>
      exact
        Nonempty.intro
          (payloadOfPeriodCandidatePartialLowerTableData D)

end DirectFlexibleSourcePayloadW33
end PachToth
end ErdosProblems1066

end
