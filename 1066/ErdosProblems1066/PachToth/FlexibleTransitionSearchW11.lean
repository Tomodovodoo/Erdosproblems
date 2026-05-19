import ErdosProblems1066.PachToth.ExactLocalObstructionExpansionW10
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW10
import ErdosProblems1066.PachToth.NonRigidPeriodCandidateW10
import ErdosProblems1066.PachToth.PachTothFinalDataAssembly
import ErdosProblems1066.PachToth.PeriodCandidateTargetRoute

set_option autoImplicit false

/-!
# W11 flexible transition search surface

This file tightens the W10 flexible transition surface without closing the
final Pach--Toth target unconditionally.

The main W11 interface separates the reusable non-rigid route from the
particular ways a candidate might be found.  A viable route needs a
`SameOppositeCandidate`, period equations, and metric lower-bound data.  W10
unit-vector fields and completed filtered branches both project into this
smaller interface, while the current concrete four-target filtered branch is
recorded as an explicit blocked over-strong candidate.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth

namespace PeriodCandidateTargetRoute

namespace PeriodCandidatePartialLowerTableData

/-- The partial period/non-connector package feeds the flexible lower-table
route without requiring the blocked concrete exact-local residual rows. -/
def toFlexiblePeriodLowerTableFamily
    (D : PeriodCandidatePartialLowerTableData) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily.ofConcreteNonConnectorLowerTableFamily
    D.toConcreteNonConnectorLowerTableFamily

/-- The named concrete lower-table source package feeds Peirce's flexible
lower-table constructor directly; the exact-target transition equality is
retained by the package but not consumed by this flexible route. -/
def flexiblePeriodLowerTableFamilyOfConcreteSource
    (C : ConcreteNonConnectorLowerTableFamilyWithTransition) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily.ofConcreteNonConnectorLowerTableFamily
    C.1

/-- The generated-closure family obtained from the partial package through
the flexible exact-local route. -/
def toFlexibleGeneratedClosureFamily
    (D : PeriodCandidatePartialLowerTableData) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  D.toFlexiblePeriodLowerTableFamily.toGeneratedClosureFamily

/-- A named concrete lower-table source gives the flexible generated-closure
family without asking for residual full exact-local rows. -/
def flexibleGeneratedClosureFamilyOfConcreteSource
    (C : ConcreteNonConnectorLowerTableFamilyWithTransition) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  (flexiblePeriodLowerTableFamilyOfConcreteSource C).toGeneratedClosureFamily

/-- Exact Pach--Toth target from the checked partial period and
non-connector table package, routed through the flexible exact-local
lower-table family rather than through the blocked exact-local residual
fields. -/
theorem targetUpperConstructionFiveSixteen_viaFlexible
    (D : PeriodCandidatePartialLowerTableData) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toFlexiblePeriodLowerTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target from the checked partial package via the
flexible lower-table route and the checked exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_viaFlexible
    (D : PeriodCandidatePartialLowerTableData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  D.toFlexiblePeriodLowerTableFamily.targetUpperConstructionFiveSixteenArbitrary

/-- Exact Pach--Toth target directly from the named concrete
period/non-connector/transition source package via Peirce's flexible
lower-table route. -/
theorem targetUpperConstructionFiveSixteen_of_concreteSource_viaFlexible
    (C : ConcreteNonConnectorLowerTableFamilyWithTransition) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (flexiblePeriodLowerTableFamilyOfConcreteSource C).targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target directly from the named concrete source
package via the flexible lower-table route and the checked exact-remainder
bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteSource_viaFlexible
    (C : ConcreteNonConnectorLowerTableFamilyWithTransition) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (flexiblePeriodLowerTableFamilyOfConcreteSource C).targetUpperConstructionFiveSixteenArbitrary

theorem nonempty_flexiblePeriodLowerTableFamily_of_partial
    (H : Nonempty PeriodCandidatePartialLowerTableData) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  cases H with
  | intro D => exact Nonempty.intro D.toFlexiblePeriodLowerTableFamily

theorem nonempty_flexiblePeriodLowerTableFamily_of_concreteSource
    (H : Nonempty ConcreteNonConnectorLowerTableFamilyWithTransition) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  cases H with
  | intro C =>
      exact Nonempty.intro (flexiblePeriodLowerTableFamilyOfConcreteSource C)

theorem nonempty_flexibleGeneratedClosureFamily_of_partial
    (H : Nonempty PeriodCandidatePartialLowerTableData) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily := by
  cases H with
  | intro D => exact Nonempty.intro D.toFlexibleGeneratedClosureFamily

theorem nonempty_flexibleGeneratedClosureFamily_of_concreteSource
    (H : Nonempty ConcreteNonConnectorLowerTableFamilyWithTransition) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily := by
  cases H with
  | intro C =>
      exact Nonempty.intro (flexibleGeneratedClosureFamilyOfConcreteSource C)

end PeriodCandidatePartialLowerTableData

namespace PeriodCandidateLowerTableData

/-- The old full record still projects to the flexible lower-table route if
one is supplied, but the route only needs the partial period/non-connector
fields. -/
def toFlexiblePeriodLowerTableFamily
    (D : PeriodCandidateLowerTableData) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  D.toPartialLowerTableData.toFlexiblePeriodLowerTableFamily

/-- Generated closure from the old full record, factored through the partial
flexible route. -/
def toFlexibleGeneratedClosureFamily
    (D : PeriodCandidateLowerTableData) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  D.toPartialLowerTableData.toFlexibleGeneratedClosureFamily

end PeriodCandidateLowerTableData

end PeriodCandidateTargetRoute

namespace FlexibleTransitionSearchW11

open FiniteGraph
open FiniteGraph.LocalVertex
open PeriodCandidateTargetRoute
open PeriodCandidatePartialLowerTableData
open ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily
open ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev R2 := Prod Real Real
abbrev BranchCandidate :=
  RoleHingeCandidateSearchSurface.BranchCandidate
abbrev SameOppositeCandidate :=
  RoleHingeCandidateSearchSurface.SameOppositeCandidate
abbrev PeriodSearchData :=
  RoleHingeCandidateSearchSurface.PeriodSearchData
abbrev FilteredSameOpposite :=
  ExactLocalBranchSolverSurface.FilteredSameOpposite
abbrev FilteredCompletionFields :=
  FlexibleTransitionSearchW10.FilteredSameOppositeCompletionFields
abbrev W10CompleteNonRigidFamilyFields :=
  FlexibleTransitionSearchW10.CompleteNonRigidFamilyFields
abbrev ConcreteLowerTableFamily : Type :=
  ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily
abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily
abbrev ConcreteSourceWithTransition : Type :=
  ConcreteNonConnectorLowerTableFamilyWithTransition

/-! ## Smaller non-rigid route interface -/

/-- Remaining period and metric fields once a same/opposite candidate has
already been supplied. -/
structure NonRigidCandidateRemainingFields
    (T : SameOppositeCandidate) where
  periodData : PeriodSearchData T
  metricData :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData periodData

namespace NonRigidCandidateRemainingFields

/-- Remaining W11 period and metric fields are exactly a flexible exact-local
family field package for the supplied non-rigid candidate. -/
def toFlexibleFamilyFields
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    NonRigidPeriodCandidateW10.FlexibleFamilyFields T :=
  NonRigidPeriodCandidateW10.FlexibleFamilyFields.ofSearchSurfaceMetricData
    R.metricData

/-- Direct flexible generated-closure family for the supplied non-rigid
candidate, period equations, and separation data. -/
def toFlexibleGeneratedClosureFamily
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  R.toFlexibleFamilyFields.toFlexibleGeneratedClosureFamily

/-- The same W11 route fields fill the final flexible lower-table source
directly: the period data supplies words and generated period equations, and
the metric data supplies the lower table and its two checked bounds. -/
def toFlexiblePeriodLowerTableFamily
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily where
  transitions := T.toFlexibleSameOpposite
  word := R.periodData.word
  period := by
    intro k hk
    simpa [RoleHingeCandidateSearchSurface.PeriodSearchData.orientation]
      using R.periodData.periodEquation k hk
  lower := R.metricData.lower
  lower_ge_one := R.metricData.lower_ge_one
  lower_bound := by
    intro k hk
    simpa [RoleHingeCandidateSearchSurface.PeriodSearchData.orientation]
      using R.metricData.lower_bound k hk

/-- The generated family determined by the period fields. -/
def toGeneratedChainFamily
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  R.periodData.toGeneratedChainFamily

/-- Period hypotheses projected from the stored period fields. -/
theorem periods
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    R.toGeneratedChainFamily.Periods :=
  R.periodData.periods

/-- Family metric hypotheses projected from the stored cross-block fields. -/
def toFamilyMetricHypotheses
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      R.toGeneratedChainFamily :=
  R.metricData.toFamilyMetricHypotheses

/-- The exact target route for a supplied candidate plus its remaining
period and metric fields. -/
theorem targetUpperConstructionFiveSixteen
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.toFlexiblePeriodLowerTableFamily.targetUpperConstructionFiveSixteen

/-- The arbitrary-size target projection through the checked exact-remainder
bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {T : SameOppositeCandidate}
    (R : NonRigidCandidateRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachTothFinalDataAssembly.exactRemainderBridge_present
    R.targetUpperConstructionFiveSixteen

end NonRigidCandidateRemainingFields

/-- A complete non-rigid route in the smaller W11 interface. -/
structure NonRigidRouteFields where
  candidate : SameOppositeCandidate
  remaining : NonRigidCandidateRemainingFields candidate

/-- The dependent source package behind the W11 route: choose one
same/opposite candidate, then provide exactly the remaining period and metric
fields for that candidate. -/
abbrev NonRigidRouteSourcePackage : Type :=
  Sigma (fun T : SameOppositeCandidate =>
    NonRigidCandidateRemainingFields T)

namespace NonRigidRouteSourcePackage

/-- Pack the dependent source package as the W11 route record. -/
def toNonRigidRouteFields
    (S : NonRigidRouteSourcePackage) :
    NonRigidRouteFields where
  candidate := S.1
  remaining := S.2

/-- The dependent source package gives the flexible generated-closure family
through the W11 route record. -/
def toFlexibleGeneratedClosureFamily
    (S : NonRigidRouteSourcePackage) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  S.2.toFlexibleGeneratedClosureFamily

/-- The dependent source package gives the final flexible lower-table source
through the W11 route record. -/
def toFlexiblePeriodLowerTableFamily
    (S : NonRigidRouteSourcePackage) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  S.2.toFlexiblePeriodLowerTableFamily

end NonRigidRouteSourcePackage

/-- The un-nested source fields for the W11 non-rigid route.

This is the smallest source shape used by this file: a same/opposite
candidate, all-positive algebraic period equations for that candidate, and
the generated cross-block lower-table data for those period equations.  It
does not remember unit-vector search parameters, filtered-branch provenance,
or any arbitrary-transition metric rows. -/
structure NonRigidRouteSourceFields where
  candidate : SameOppositeCandidate
  periodData : PeriodSearchData candidate
  metricData :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData periodData

namespace NonRigidRouteSourceFields

/-- Re-nest the minimal source fields as the W11 route package. -/
def toNonRigidRouteFields
    (S : NonRigidRouteSourceFields) :
    NonRigidRouteFields where
  candidate := S.candidate
  remaining :=
    { periodData := S.periodData
      metricData := S.metricData }

@[simp]
theorem toNonRigidRouteFields_candidate
    (S : NonRigidRouteSourceFields) :
    S.toNonRigidRouteFields.candidate = S.candidate :=
  rfl

end NonRigidRouteSourceFields

namespace NonRigidRouteFields

/-- Flatten the W11 route package to its dependent source package. -/
def toNonRigidRouteSourcePackage
    (F : NonRigidRouteFields) :
    NonRigidRouteSourcePackage :=
  Sigma.mk F.candidate F.remaining

/-- Flatten the W11 route package to the minimal source field shape. -/
def toNonRigidRouteSourceFields
    (F : NonRigidRouteFields) :
    NonRigidRouteSourceFields where
  candidate := F.candidate
  periodData := F.remaining.periodData
  metricData := F.remaining.metricData

/-- Flexible exact-local transition data projected from the candidate. -/
def toFlexibleSameOpposite
    (F : NonRigidRouteFields) :
    FlexibleExactLocalTransition.SameOpposite :=
  F.candidate.toFlexibleSameOpposite

/-- The complete W11 route fields project directly to a flexible generated
closure family. -/
def toFlexibleGeneratedClosureFamily
    (F : NonRigidRouteFields) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  F.remaining.toFlexibleGeneratedClosureFamily

/-- The complete W11 route fields also materialize the final lower-table
source package. -/
def toFlexiblePeriodLowerTableFamily
    (F : NonRigidRouteFields) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  F.remaining.toFlexiblePeriodLowerTableFamily

/-- The generated-chain family projected from the remaining period fields. -/
def toGeneratedChainFamily
    (F : NonRigidRouteFields) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  F.remaining.toGeneratedChainFamily

/-- Period hypotheses for the projected generated-chain family. -/
theorem periods
    (F : NonRigidRouteFields) :
    F.toGeneratedChainFamily.Periods :=
  F.remaining.periods

/-- Metric hypotheses for the projected generated-chain family. -/
def toFamilyMetricHypotheses
    (F : NonRigidRouteFields) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      F.toGeneratedChainFamily :=
  F.remaining.toFamilyMetricHypotheses

/-- Branchwise exact-local preservation in the candidate gives the generated
same-block invariant used by the route. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (F : NonRigidRouteFields) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      F.candidate.toFigure2TransitionObligations :=
  F.candidate.generatedTransitionsPreserveExactLocalSqDistances

/-- Same-branch row projection from the candidate exact-local field. -/
theorem same_sqDist
    (F : NonRigidRouteFields)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (F.candidate.same.placeNext source u)
        (F.candidate.same.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  F.candidate.same.preserves_exactLocal_sqDistances source hsource u v

/-- Opposite-branch row projection from the candidate exact-local field. -/
theorem opposite_sqDist
    (F : NonRigidRouteFields)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (F.candidate.opposite.placeNext source u)
        (F.candidate.opposite.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  F.candidate.opposite.preserves_exactLocal_sqDistances source hsource u v

/-- Exact target theorem, conditional on the W11 route fields. -/
theorem targetUpperConstructionFiveSixteen
    (F : NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toFlexiblePeriodLowerTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-size target theorem, conditional on the W11 route fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.remaining.targetUpperConstructionFiveSixteenArbitrary

end NonRigidRouteFields

namespace NonRigidRouteSourceFields

/-- The minimal source fields give the flexible generated-closure family
through the W11 route package. -/
def toFlexibleGeneratedClosureFamily
    (S : NonRigidRouteSourceFields) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  S.toNonRigidRouteFields.toFlexibleGeneratedClosureFamily

/-- The minimal source fields give the final flexible lower-table source
through the W11 route package. -/
def toFlexiblePeriodLowerTableFamily
    (S : NonRigidRouteSourceFields) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  S.toNonRigidRouteFields.toFlexiblePeriodLowerTableFamily

end NonRigidRouteSourceFields

/-! ## Direct flexible payload -/

/-- A provenance-free W11 flexible source payload.

This is the same mathematical data as `NonRigidRouteSourceFields`, but named
as the direct payload requested by the search: one flexible same/opposite
candidate, all-positive period equations for that candidate, and generated
cross-block metric data for those periods.  It carries no strong role-hinge
transition record and no concrete four-target table/value shortcut. -/
structure DirectFlexibleSourcePayload where
  candidate : SameOppositeCandidate
  periodData : PeriodSearchData candidate
  metricData :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData periodData

namespace DirectFlexibleSourcePayload

/-- Forget the direct payload name to the minimal W11 source fields. -/
def toSourceFields
    (D : DirectFlexibleSourcePayload) :
    NonRigidRouteSourceFields where
  candidate := D.candidate
  periodData := D.periodData
  metricData := D.metricData

/-- Name existing minimal W11 source fields as a direct flexible payload. -/
def ofSourceFields
    (S : NonRigidRouteSourceFields) :
    DirectFlexibleSourcePayload where
  candidate := S.candidate
  periodData := S.periodData
  metricData := S.metricData

@[simp]
theorem toSourceFields_candidate
    (D : DirectFlexibleSourcePayload) :
    D.toSourceFields.candidate = D.candidate :=
  rfl

@[simp]
theorem ofSourceFields_candidate
    (S : NonRigidRouteSourceFields) :
    (ofSourceFields S).candidate = S.candidate :=
  rfl

end DirectFlexibleSourcePayload

/-! ## Nonempty source reductions -/

/-- The un-nested source fields are exactly equivalent to the W11 route
fields.  This identifies the smallest remaining source package currently
needed for the flexible Pach--Toth route. -/
theorem nonempty_nonRigidRouteFields_iff_sourceFields :
    Nonempty NonRigidRouteFields <->
      Nonempty NonRigidRouteSourceFields := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro F =>
        exact Nonempty.intro F.toNonRigidRouteSourceFields
  case mpr =>
    intro H
    cases H with
    | intro S =>
        exact Nonempty.intro S.toNonRigidRouteFields

/-- The W11 route record is exactly the dependent source package consisting
of one same/opposite candidate and the remaining period/metric fields for
that candidate. -/
theorem nonempty_nonRigidRouteFields_iff_sourcePackage :
    Nonempty NonRigidRouteFields <->
      Nonempty NonRigidRouteSourcePackage := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro F =>
        exact Nonempty.intro F.toNonRigidRouteSourcePackage
  case mpr =>
    intro H
    cases H with
    | intro S =>
        exact Nonempty.intro S.toNonRigidRouteFields

/-- The minimal W11 source fields are exactly the direct flexible payload:
candidate, period equations, and cross-block metric data, with no remembered
strong role-hinge or concrete four-target provenance. -/
theorem nonempty_sourceFields_iff_directFlexibleSourcePayload :
    Nonempty NonRigidRouteSourceFields <->
      Nonempty DirectFlexibleSourcePayload := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro S =>
        exact
          Nonempty.intro
            (DirectFlexibleSourcePayload.ofSourceFields S)
  case mpr =>
    intro H
    cases H with
    | intro D =>
        exact
          Nonempty.intro
            D.toSourceFields

/-- A nonempty minimal W11 source package is enough to inhabit the final
flexible lower-table family. -/
theorem nonempty_flexiblePeriodLowerTableFamily_of_sourceFields
    (H : Nonempty NonRigidRouteSourceFields) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toFlexiblePeriodLowerTableFamily

/-- A nonempty minimal W11 source package is enough to inhabit the flexible
generated-closure family. -/
theorem nonempty_flexibleGeneratedClosureFamily_of_sourceFields
    (H : Nonempty NonRigidRouteSourceFields) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toFlexibleGeneratedClosureFamily

/-- A nonempty direct flexible payload is enough to inhabit the flexible
generated-closure family.  This is the current live W11 route to the
generated-closure source, without detouring through the blocked concrete
role-hinge table aliases. -/
theorem nonempty_flexibleGeneratedClosureFamily_of_directFlexibleSourcePayload
    (H : Nonempty DirectFlexibleSourcePayload) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily :=
  nonempty_flexibleGeneratedClosureFamily_of_sourceFields
    (nonempty_sourceFields_iff_directFlexibleSourcePayload.2 H)

/-- A nonempty dependent W11 source package is enough to inhabit the final
flexible lower-table family. -/
theorem nonempty_flexiblePeriodLowerTableFamily_of_sourcePackage
    (H : Nonempty NonRigidRouteSourcePackage) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toFlexiblePeriodLowerTableFamily

/-- A nonempty dependent W11 source package also inhabits the flexible
generated-closure family. -/
theorem nonempty_flexibleGeneratedClosureFamily_of_sourcePackage
    (H : Nonempty NonRigidRouteSourcePackage) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toFlexibleGeneratedClosureFamily

/-- A nonempty W11 route is the exact missing source needed to inhabit the
final flexible lower-table family. -/
theorem nonempty_flexiblePeriodLowerTableFamily_of_nonRigidRouteFields
    (H : Nonempty NonRigidRouteFields) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  cases H with
  | intro F =>
      exact Nonempty.intro F.toFlexiblePeriodLowerTableFamily

/-- A nonempty W11 route also inhabits the flexible generated-closure family
used by the large-tail closed-placement rows. -/
theorem nonempty_flexibleGeneratedClosureFamily_of_nonRigidRouteFields
    (H : Nonempty NonRigidRouteFields) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily := by
  cases H with
  | intro F =>
      exact Nonempty.intro F.toFlexibleGeneratedClosureFamily

/-! ## Exact period/metric source reductions -/

/-- For a fixed same/opposite candidate, the remaining W11 route fields are
exactly a period-data choice together with cross-block metric data for that
period data. -/
theorem nonempty_remainingFields_iff_exists_period_metric
    (T : SameOppositeCandidate) :
    Nonempty (NonRigidCandidateRemainingFields T) <->
      Exists fun P : PeriodSearchData T =>
        Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P) := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro R =>
        exact Exists.intro R.periodData (Nonempty.intro R.metricData)
  case mpr =>
    intro H
    cases H with
    | intro P HM =>
        cases HM with
        | intro M =>
            exact Nonempty.intro
              { periodData := P
                metricData := M }

/-- The minimal W11 source is exactly a same/opposite candidate, period
fields for it, and cross-block metric fields for those periods. -/
theorem nonempty_sourceFields_iff_exists_candidate_period_metric :
    Nonempty NonRigidRouteSourceFields <->
      Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P) := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro S =>
        exact
          Exists.intro S.candidate
            (Exists.intro S.periodData (Nonempty.intro S.metricData))
  case mpr =>
    intro H
    cases H with
    | intro T Hrest =>
        cases Hrest with
        | intro P HM =>
            cases HM with
            | intro M =>
                exact Nonempty.intro
                  { candidate := T
                    periodData := P
                    metricData := M }

/-- A direct W11 source inhabitant from actual non-rigid candidate, period,
and cross-block metric data. -/
theorem nonempty_sourceFields_of_candidate_period_metric
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (M : RoleHingeCandidateSearchSurface.CrossBlockMetricData P) :
    Nonempty NonRigidRouteSourceFields :=
  Nonempty.intro
    { candidate := T
      periodData := P
      metricData := M }

/-- The direct flexible payload is exactly a same/opposite candidate, period
fields for it, and cross-block metric fields for those periods. -/
theorem nonempty_directFlexibleSourcePayload_iff_exists_candidate_period_metric :
    Nonempty DirectFlexibleSourcePayload <->
      Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P) := by
  constructor
  case mp =>
    intro H
    exact
      nonempty_sourceFields_iff_exists_candidate_period_metric.1
        (nonempty_sourceFields_iff_directFlexibleSourcePayload.2 H)
  case mpr =>
    intro H
    exact
      nonempty_sourceFields_iff_directFlexibleSourcePayload.1
        (nonempty_sourceFields_iff_exists_candidate_period_metric.2 H)

/-- A direct W11 source inhabitant from actual flexible candidate, period, and
cross-block metric data, stated at the provenance-free payload level. -/
theorem nonempty_directFlexibleSourcePayload_of_candidate_period_metric
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (M : RoleHingeCandidateSearchSurface.CrossBlockMetricData P) :
    Nonempty DirectFlexibleSourcePayload :=
  nonempty_sourceFields_iff_directFlexibleSourcePayload.1
    (nonempty_sourceFields_of_candidate_period_metric P M)

/-- Candidate, all-positive period equations, and cross-block metric data
are exactly the payload needed by the current W11 route to produce a flexible
generated-closure family. -/
theorem nonempty_flexibleGeneratedClosureFamily_of_candidate_period_metric
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (M : RoleHingeCandidateSearchSurface.CrossBlockMetricData P) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily :=
  nonempty_flexibleGeneratedClosureFamily_of_directFlexibleSourcePayload
    (nonempty_directFlexibleSourcePayload_of_candidate_period_metric P M)

/-- If the direct W11 source cannot be inhabited, the exact missing package is
a same/opposite candidate, all-positive period fields for that candidate, and
cross-block metric fields for those periods. -/
theorem no_sourceFields_without_candidate_period_metric
    (hmissing :
      Not
        (Exists fun T : SameOppositeCandidate =>
          Exists fun P : PeriodSearchData T =>
            Nonempty
              (RoleHingeCandidateSearchSurface.CrossBlockMetricData P))) :
    Not (Nonempty NonRigidRouteSourceFields) := by
  intro H
  exact hmissing
    (nonempty_sourceFields_iff_exists_candidate_period_metric.1 H)

/-- If the provenance-free direct flexible payload is absent, then the W11
minimal source fields are absent.  This is the checked blocker for the direct
route after the concrete table/value shortcuts have been ruled out. -/
theorem no_sourceFields_without_directFlexibleSourcePayload
    (hmissing : Not (Nonempty DirectFlexibleSourcePayload)) :
    Not (Nonempty NonRigidRouteSourceFields) := by
  intro H
  exact hmissing
    (nonempty_sourceFields_iff_directFlexibleSourcePayload.1 H)

/-- Equivalently, if the minimal W11 source fields are absent, the direct
flexible payload is absent. -/
theorem no_directFlexibleSourcePayload_without_sourceFields
    (hmissing : Not (Nonempty NonRigidRouteSourceFields)) :
    Not (Nonempty DirectFlexibleSourcePayload) := by
  intro H
  exact hmissing
    (nonempty_sourceFields_iff_directFlexibleSourcePayload.2 H)

/-- If the provenance-free direct flexible payload is missing, then the
current W11 route to the flexible generated-closure family has no source
fields, route record, or dependent source package.  This blocks only this
checked route; it does not assert that no unrelated direct
`GeneratedClosureFamily` could be supplied. -/
theorem currentGeneratedClosureRoute_blocked_without_directFlexibleSourcePayload
    (hmissing : Not (Nonempty DirectFlexibleSourcePayload)) :
    Not (Nonempty NonRigidRouteSourceFields) /\
      Not (Nonempty NonRigidRouteFields) /\
        Not (Nonempty NonRigidRouteSourcePackage) := by
  have hsource : Not (Nonempty NonRigidRouteSourceFields) :=
    no_sourceFields_without_directFlexibleSourcePayload hmissing
  have hroute : Not (Nonempty NonRigidRouteFields) := by
    intro H
    exact hsource (nonempty_nonRigidRouteFields_iff_sourceFields.1 H)
  have hpackage : Not (Nonempty NonRigidRouteSourcePackage) := by
    intro H
    exact hroute (nonempty_nonRigidRouteFields_iff_sourcePackage.2 H)
  exact And.intro hsource (And.intro hroute hpackage)

/-! ## Adapters from existing role-hinge period/cross-block data -/

/-- A flexible exact-local branch is already a W11 branch candidate after
forgetting the packaging of its connector and exact-local fields. -/
def branchCandidateOfFlexibleBranch
    (T : FlexibleExactLocalTransition.Branch) :
    BranchCandidate where
  placeNext := T.placeNext
  roleAngle := T.roleAngle
  realizes_role := by
    intro source u v role hrole
    exact T.connector.realizes_role source u v role hrole
  preserves_exactLocal_sqDistances :=
    T.preserves_exact_local_sq_distances

@[simp]
theorem branchCandidateOfFlexibleBranch_placeNext
    (T : FlexibleExactLocalTransition.Branch) :
    (branchCandidateOfFlexibleBranch T).placeNext = T.placeNext :=
  rfl

/-- Flexible same/opposite transition data forgets to the W11 non-rigid
candidate surface. -/
def sameOppositeCandidateOfFlexibleSameOpposite
    (T : FlexibleExactLocalTransition.SameOpposite) :
    SameOppositeCandidate where
  same := branchCandidateOfFlexibleBranch T.same
  opposite := branchCandidateOfFlexibleBranch T.opposite

@[simp]
theorem sameOppositeCandidateOfFlexibleSameOpposite_toFigure2
    (T : FlexibleExactLocalTransition.SameOpposite) :
    (sameOppositeCandidateOfFlexibleSameOpposite T).toFigure2TransitionObligations =
      T.toFigure2TransitionObligations :=
  rfl

/-- A strong role-hinge transition is a W11 branch candidate after forgetting
arbitrary-source same-block preservation to exact-local preservation. -/
def branchCandidateOfRoleHingeTransition
    (T : BaseTransitionRealization.RoleHingeTransition) :
    BranchCandidate where
  placeNext := T.placeNext
  roleAngle := T.roleAngle
  realizes_role := T.realizes_role
  preserves_exactLocal_sqDistances :=
    RoleHingeSameBlockAlgebra.preservesExactLocalSqDistances_of_preservesSameBlockDistances
      T.preserves_same_block_distances

@[simp]
theorem branchCandidateOfRoleHingeTransition_placeNext
    (T : BaseTransitionRealization.RoleHingeTransition) :
    (branchCandidateOfRoleHingeTransition T).placeNext = T.placeNext :=
  rfl

/-- Strong same/opposite role-hinge transitions forget to the W11 candidate
surface. -/
def sameOppositeCandidateOfRoleHingeTransitions
    (T : GeneratedMetricClosure.RoleHingeTransitions) :
    SameOppositeCandidate where
  same := branchCandidateOfRoleHingeTransition T.same
  opposite := branchCandidateOfRoleHingeTransition T.opposite

@[simp]
theorem sameOppositeCandidateOfRoleHingeTransitions_toFigure2
    (T : GeneratedMetricClosure.RoleHingeTransitions) :
    (sameOppositeCandidateOfRoleHingeTransitions T).toFigure2TransitionObligations =
      T.toFigure2TransitionObligations :=
  rfl

/-- Concrete role-hinge period-search data, once its strong transitions are
forgotten to the W11 candidate surface, supplies the W11 period fields. -/
def periodSearchDataOfConcretePeriodSearchData
    (P : ConcretePeriodSearchFamily.PeriodSearchData) :
    PeriodSearchData (sameOppositeCandidateOfRoleHingeTransitions P.transitions) where
  word := P.word
  equation := by
    intro k hk i
    simpa [sameOppositeCandidateOfRoleHingeTransitions,
      branchCandidateOfRoleHingeTransition,
      PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord] using
        P.equation k hk i

@[simp]
theorem periodSearchDataOfConcretePeriodSearchData_word
    (P : ConcretePeriodSearchFamily.PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (periodSearchDataOfConcretePeriodSearchData P).word k hk =
      P.word k hk :=
  rfl

/-- Existing concrete non-connector lower tables supply the W11 cross-block
metric fields for the period data obtained by forgetting their strong
role-hinge transitions. -/
def crossBlockMetricDataOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData
      (periodSearchDataOfConcretePeriodSearchData C.periodSearch) where
  lower := C.toCrossBlockLowerBounds.lower
  lower_ge_one := C.crossBlockLower_ge_one
  lower_bound := by
    intro k hk
    simpa [periodSearchDataOfConcretePeriodSearchData,
      sameOppositeCandidateOfRoleHingeTransitions,
      branchCandidateOfRoleHingeTransition,
      RoleHingeCandidateSearchSurface.PeriodSearchData.orientation,
      ConcretePeriodSearchFamily.PeriodSearchData.orientation] using
        C.crossBlockDistanceLowerBounds k hk

/-- Existing concrete non-connector lower-table families repackage directly
as the minimal W11 non-rigid route source fields. -/
def sourceFieldsOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    NonRigidRouteSourceFields where
  candidate := sameOppositeCandidateOfRoleHingeTransitions C.periodSearch.transitions
  periodData := periodSearchDataOfConcretePeriodSearchData C.periodSearch
  metricData := crossBlockMetricDataOfConcreteNonConnectorLowerTableFamily C

/-- Existing concrete non-connector lower-table families also repackage
directly as the dependent W11 non-rigid route source package. -/
def sourcePackageOfConcreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    NonRigidRouteSourcePackage :=
  Sigma.mk
    (sameOppositeCandidateOfRoleHingeTransitions C.periodSearch.transitions)
    { periodData := periodSearchDataOfConcretePeriodSearchData C.periodSearch
      metricData := crossBlockMetricDataOfConcreteNonConnectorLowerTableFamily C }

theorem nonempty_sourceFields_of_concreteNonConnectorLowerTableFamily
    (H :
      Nonempty
        ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    Nonempty NonRigidRouteSourceFields := by
  cases H with
  | intro C =>
      exact Nonempty.intro (sourceFieldsOfConcreteNonConnectorLowerTableFamily C)

/-- Decomposed concrete period data plus non-connector lower tables are the
same concrete source consumed by the W11 flexible route. -/
theorem nonempty_sourceFields_of_exists_concretePeriodSearch_tables
    (H :
      Exists fun periodSearch : ConcreteCrossBlockLowerTable.PeriodSearchData =>
        Nonempty
          (ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily
            periodSearch.toRoleHingedPeriodSearchFamily)) :
    Nonempty NonRigidRouteSourceFields :=
  nonempty_sourceFields_of_concreteNonConnectorLowerTableFamily
    (ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily.nonempty_iff_exists_periodSearch_tables.2
      H)

/-- Existing concrete value-matrix families repackage through their induced
concrete non-connector lower-table family. -/
def sourceFieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    NonRigidRouteSourceFields :=
  sourceFieldsOfConcreteNonConnectorLowerTableFamily
    C.toConcreteNonConnectorLowerTableFamily

theorem nonempty_sourceFields_of_concreteValueMatrixFamily
    (H : Nonempty ConcreteValueMatrixFamily) :
    Nonempty NonRigidRouteSourceFields := by
  cases H with
  | intro C =>
      exact Nonempty.intro (sourceFieldsOfConcreteValueMatrixFamily C)

/-- Decomposed concrete period data plus value matrices also feed the W11
flexible route through the lower-table projection. -/
theorem nonempty_sourceFields_of_exists_concretePeriodSearch_matrices
    (H :
      Exists fun periodSearch : ConcreteNonConnectorValueMatrix.PeriodSearchData =>
        Nonempty
          (ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily
            periodSearch.toRoleHingedPeriodSearchFamily)) :
    Nonempty NonRigidRouteSourceFields :=
  nonempty_sourceFields_of_concreteValueMatrixFamily
    (ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily.nonempty_iff_exists_periodSearch_matrices.2
      H)

/-! ## Direct flexible lower-table source lift -/

/-- The source-facing indexed algebraic period-equation field attached to a
final flexible lower-table route.  The lower table stores generated period
equations and metric bounds; W11 source fields phrase the period side as
indexed algebraic equations. -/
abbrev FlexibleLowerTableAlgebraicPeriodEquations
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    RoleHingeCandidateSearchSurface.ExactPeriodEquations
      (sameOppositeCandidateOfFlexibleSameOpposite F.transitions)
      hk (F.word k hk)

/-- The generated period equations already stored by a final flexible
lower-table family imply the indexed algebraic period equations required by
the W11 source surface. -/
theorem flexibleLowerTableAlgebraicPeriodEquations
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) :
    FlexibleLowerTableAlgebraicPeriodEquations F := by
  intro k hk i
  have hclosure :
      PeriodInterface.GeneratedClosureEquation
        F.transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((F.word k hk).toFin) :=
    PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      ((F.word k hk).toFin)
      (F.period k hk)
  simpa [FlexibleLowerTableAlgebraicPeriodEquations,
    RoleHingeCandidateSearchSurface.ExactPeriodEquations,
    PeriodWordCertificates.AlgebraicEquationsForWord,
    PeriodWordCertificates.finiteOrientationWordOfWord,
    PeriodSearchInterface.AlgebraicVertexPeriodEquation,
    PeriodSearchInterface.FiniteOrientationWord.iteratedTransitionBlock,
    sameOppositeCandidateOfFlexibleSameOpposite] using
      PeriodInterface.generatedClosureEquation_apply
        F.transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((F.word k hk).toFin)
        hclosure
        (BlockPartition.localVertexEquivFin16.symm i)

/-- Repackage a final flexible lower-table family as W11 period-search data
using indexed algebraic period equations. -/
def periodSearchDataOfFlexibleLowerTableFamily
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily)
    (equations : FlexibleLowerTableAlgebraicPeriodEquations F) :
    PeriodSearchData
      (sameOppositeCandidateOfFlexibleSameOpposite F.transitions) where
  word := F.word
  equation := equations

/-- Repackage the final flexible lower-table metric fields as W11 cross-block
metric data over the supplied algebraic period data. -/
def crossBlockMetricDataOfFlexibleLowerTableFamily
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily)
    (equations : FlexibleLowerTableAlgebraicPeriodEquations F) :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData
      (periodSearchDataOfFlexibleLowerTableFamily F equations) where
  lower := F.lower
  lower_ge_one := F.lower_ge_one
  lower_bound := by
    intro k hk
    simpa [periodSearchDataOfFlexibleLowerTableFamily,
      RoleHingeCandidateSearchSurface.PeriodSearchData.orientation,
      PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily.orientation] using
        F.lower_bound k hk

/-- A final flexible lower-table family plus indexed algebraic period
equations is exactly a W11 source-field inhabitant. -/
def sourceFieldsOfFlexibleLowerTableFamily
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily)
    (equations : FlexibleLowerTableAlgebraicPeriodEquations F) :
    NonRigidRouteSourceFields where
  candidate := sameOppositeCandidateOfFlexibleSameOpposite F.transitions
  periodData := periodSearchDataOfFlexibleLowerTableFamily F equations
  metricData := crossBlockMetricDataOfFlexibleLowerTableFamily F equations

/-- Source-facing lift of the final flexible lower-table route.  The named
algebraic field is derived from the stored generated period equations; all
metric data is already part of the lower-table family. -/
structure FlexibleLowerTableSourceLift where
  lowerTable : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily
  algebraicPeriodEquations :
    FlexibleLowerTableAlgebraicPeriodEquations lowerTable

namespace FlexibleLowerTableSourceLift

/-- Forget the lower-table lift to the minimal W11 source fields. -/
def toSourceFields
    (L : FlexibleLowerTableSourceLift) :
    NonRigidRouteSourceFields :=
  sourceFieldsOfFlexibleLowerTableFamily
    L.lowerTable L.algebraicPeriodEquations

/-- Any final flexible lower-table family has the source-facing lift: the
indexed algebraic equations are recovered from its stored generated period
equations. -/
def ofFlexibleLowerTableFamily
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) :
    FlexibleLowerTableSourceLift where
  lowerTable := F
  algebraicPeriodEquations :=
    flexibleLowerTableAlgebraicPeriodEquations F

/-- The W11 source fields produce the lower-table lift; the lower-table
metric fields are already projected by `toFlexiblePeriodLowerTableFamily`,
and the stored `periodData.equation` is the extra algebraic field. -/
def ofSourceFields
    (S : NonRigidRouteSourceFields) :
    FlexibleLowerTableSourceLift where
  lowerTable := S.toFlexiblePeriodLowerTableFamily
  algebraicPeriodEquations := by
    intro k hk
    simpa [NonRigidRouteSourceFields.toFlexiblePeriodLowerTableFamily,
      NonRigidRouteFields.toFlexiblePeriodLowerTableFamily,
      NonRigidCandidateRemainingFields.toFlexiblePeriodLowerTableFamily,
      FlexibleLowerTableAlgebraicPeriodEquations,
      sameOppositeCandidateOfFlexibleSameOpposite,
      branchCandidateOfFlexibleBranch] using
        S.periodData.equation k hk

end FlexibleLowerTableSourceLift

/-- A final flexible lower-table family directly gives the W11 minimal source
fields. -/
def sourceFieldsOfExistingFlexibleLowerTableFamily
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) :
    NonRigidRouteSourceFields :=
  (FlexibleLowerTableSourceLift.ofFlexibleLowerTableFamily F).toSourceFields

/-- A nonempty final flexible lower-table family closes the W11 lower-table
source lift. -/
theorem nonempty_flexibleLowerTableSourceLift_of_flexibleLowerTableFamily
    (H : Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) :
    Nonempty FlexibleLowerTableSourceLift := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (FlexibleLowerTableSourceLift.ofFlexibleLowerTableFamily F)

/-- A nonempty final flexible lower-table family directly inhabits the W11
minimal source fields. -/
theorem nonempty_sourceFields_of_flexibleLowerTableFamily
    (H : Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) :
    Nonempty NonRigidRouteSourceFields := by
  cases H with
  | intro F =>
      exact Nonempty.intro (sourceFieldsOfExistingFlexibleLowerTableFamily F)

/-- The W11 minimal source fields are equivalent to an existing final
flexible lower-table family.  The reverse direction uses the generated-period
equation stored by the lower table to recover the indexed algebraic period
equations. -/
theorem nonempty_sourceFields_iff_flexibleLowerTableFamily :
    Nonempty NonRigidRouteSourceFields <->
      Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  constructor
  case mp =>
    exact nonempty_flexiblePeriodLowerTableFamily_of_sourceFields
  case mpr =>
    exact nonempty_sourceFields_of_flexibleLowerTableFamily

/-- The lower-table source lift is equivalent to an existing final flexible
lower-table family, since the algebraic period-equation field is derived from
the stored generated period equations. -/
theorem nonempty_flexibleLowerTableSourceLift_iff_flexibleLowerTableFamily :
    Nonempty FlexibleLowerTableSourceLift <->
      Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro L =>
        exact Nonempty.intro L.lowerTable
  case mpr =>
    exact nonempty_flexibleLowerTableSourceLift_of_flexibleLowerTableFamily

/-- The direct flexible payload is equivalent to an existing final flexible
lower-table family. -/
theorem nonempty_directFlexibleSourcePayload_iff_flexibleLowerTableFamily :
    Nonempty DirectFlexibleSourcePayload <->
      Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  constructor
  case mp =>
    intro H
    exact
      nonempty_sourceFields_iff_flexibleLowerTableFamily.1
        (nonempty_sourceFields_iff_directFlexibleSourcePayload.2 H)
  case mpr =>
    intro H
    exact
      nonempty_sourceFields_iff_directFlexibleSourcePayload.1
        (nonempty_sourceFields_of_flexibleLowerTableFamily H)

/-- A nonempty final flexible lower-table family directly provides the W11
direct flexible payload. -/
theorem nonempty_directFlexibleSourcePayload_of_nonempty_flexibleLowerTableFamily
    (H : Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) :
    Nonempty DirectFlexibleSourcePayload :=
  nonempty_directFlexibleSourcePayload_iff_flexibleLowerTableFamily.2 H

/-- The final flexible lower-table family is inhabited exactly when the
provenance-free direct W11 payload is inhabited. -/
theorem nonempty_flexiblePeriodLowerTableFamily_iff_directFlexibleSourcePayload :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily <->
      Nonempty DirectFlexibleSourcePayload := by
  constructor
  case mp =>
    exact nonempty_directFlexibleSourcePayload_iff_flexibleLowerTableFamily.2
  case mpr =>
    exact nonempty_directFlexibleSourcePayload_iff_flexibleLowerTableFamily.1

/-- The exact remaining source for the final flexible lower-table family:
a flexible same/opposite candidate, all-positive period data for it, and
cross-block metric data for those periods. -/
theorem nonempty_flexiblePeriodLowerTableFamily_iff_exists_candidate_period_metric :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily <->
      Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P) := by
  constructor
  case mp =>
    intro H
    exact
      nonempty_sourceFields_iff_exists_candidate_period_metric.1
        (nonempty_sourceFields_iff_flexibleLowerTableFamily.2 H)
  case mpr =>
    intro H
    exact
      nonempty_sourceFields_iff_flexibleLowerTableFamily.1
        (nonempty_sourceFields_iff_exists_candidate_period_metric.2 H)

/-- Positive constructor for the final lower-table family from actual
candidate, period, and cross-block metric data. -/
theorem nonempty_flexiblePeriodLowerTableFamily_of_candidate_period_metric
    {T : SameOppositeCandidate}
    (P : PeriodSearchData T)
    (M : RoleHingeCandidateSearchSurface.CrossBlockMetricData P) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  nonempty_flexiblePeriodLowerTableFamily_iff_exists_candidate_period_metric.2
    (Exists.intro T (Exists.intro P (Nonempty.intro M)))

/-- The unpacked finite/metric source for the final flexible lower-table
family: a same/opposite candidate, all-positive period data for that
candidate, and the cross-block metric lower-table data for those periods. -/
abbrev CandidatePeriodMetricData : Type :=
  Sigma fun T : SameOppositeCandidate =>
    Sigma fun P : PeriodSearchData T =>
      RoleHingeCandidateSearchSurface.CrossBlockMetricData P

namespace CandidatePeriodMetricData

/-- The unpacked candidate/period/metric source is exactly the W11 source
fields, without any concrete role-hinge lower-table or value-matrix detour. -/
def toSourceFields
    (D : CandidatePeriodMetricData) :
    NonRigidRouteSourceFields where
  candidate := D.1
  periodData := D.2.1
  metricData := D.2.2

/-- The unpacked source directly fills the final flexible lower-table
family. -/
def toFlexiblePeriodLowerTableFamily
    (D : CandidatePeriodMetricData) :
    PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  D.toSourceFields.toFlexiblePeriodLowerTableFamily

end CandidatePeriodMetricData

/-- Forget the W11 source-field wrapper to the unpacked candidate/period/
metric data. -/
def candidatePeriodMetricDataOfSourceFields
    (S : NonRigidRouteSourceFields) :
    CandidatePeriodMetricData :=
  Sigma.mk S.candidate (Sigma.mk S.periodData S.metricData)

/-- The W11 source fields are equivalent to the unpacked finite/metric
source data. -/
theorem nonempty_sourceFields_iff_candidatePeriodMetricData :
    Nonempty NonRigidRouteSourceFields <->
      Nonempty CandidatePeriodMetricData := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro S =>
        exact Nonempty.intro
          (candidatePeriodMetricDataOfSourceFields S)
  case mpr =>
    intro H
    cases H with
    | intro D =>
        exact Nonempty.intro D.toSourceFields

/-- The direct flexible payload is equivalent to the unpacked candidate,
period, and metric source data. -/
theorem nonempty_directFlexibleSourcePayload_iff_candidatePeriodMetricData :
    Nonempty DirectFlexibleSourcePayload <->
      Nonempty CandidatePeriodMetricData := by
  exact
    Iff.trans nonempty_sourceFields_iff_directFlexibleSourcePayload.symm
      nonempty_sourceFields_iff_candidatePeriodMetricData

/-- The final flexible lower-table family is inhabited exactly when the
unpacked candidate/period/metric source data is inhabited. -/
theorem nonempty_flexiblePeriodLowerTableFamily_iff_candidatePeriodMetricData :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily <->
      Nonempty CandidatePeriodMetricData := by
  constructor
  case mp =>
    intro H
    exact
      nonempty_sourceFields_iff_candidatePeriodMetricData.1
        (nonempty_sourceFields_iff_flexibleLowerTableFamily.2 H)
  case mpr =>
    intro H
    exact
      nonempty_flexiblePeriodLowerTableFamily_of_sourceFields
        (nonempty_sourceFields_iff_candidatePeriodMetricData.2 H)

/-- Positive lower-table constructor from the unpacked candidate/period/
metric source data. -/
theorem nonempty_flexiblePeriodLowerTableFamily_of_candidatePeriodMetricData
    (H : Nonempty CandidatePeriodMetricData) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily :=
  nonempty_flexiblePeriodLowerTableFamily_iff_candidatePeriodMetricData.2 H

/-- If the unpacked candidate/period/metric source is absent, then the final
flexible lower-table family is absent along this checked W11 source lane. -/
theorem no_flexiblePeriodLowerTableFamily_without_candidatePeriodMetricData
    (hmissing : Not (Nonempty CandidatePeriodMetricData)) :
    Not (Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily) := by
  intro H
  exact hmissing
    (nonempty_flexiblePeriodLowerTableFamily_iff_candidatePeriodMetricData.1 H)

/-- W11 source fields recover the algebraic period equations for their
projected flexible lower-table family. -/
theorem flexibleLowerTableAlgebraicPeriodEquations_of_sourceFields
    (S : NonRigidRouteSourceFields) :
    FlexibleLowerTableAlgebraicPeriodEquations
      S.toFlexiblePeriodLowerTableFamily :=
  (FlexibleLowerTableSourceLift.ofSourceFields S).algebraicPeriodEquations

/-- The minimal W11 source fields are equivalent to a final flexible
lower-table family together with its indexed algebraic period equations. -/
theorem nonempty_sourceFields_iff_flexibleLowerTableSourceLift :
    Nonempty NonRigidRouteSourceFields <->
      Nonempty FlexibleLowerTableSourceLift := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro S =>
        exact Nonempty.intro
          (FlexibleLowerTableSourceLift.ofSourceFields S)
  case mpr =>
    intro H
    cases H with
    | intro L =>
        exact Nonempty.intro L.toSourceFields

/-- A final flexible lower-table family plus its indexed algebraic period
equations gives the provenance-free direct W11 payload.  This is the
constructor that avoids the blocked concrete non-connector table/value routes:
the metric fields come from the flexible lower table, and the algebraic field
is `FlexibleLowerTableAlgebraicPeriodEquations`.
-/
def directFlexibleSourcePayloadOfFlexibleLowerTableFamily
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily)
    (equations : FlexibleLowerTableAlgebraicPeriodEquations F) :
    DirectFlexibleSourcePayload :=
  DirectFlexibleSourcePayload.ofSourceFields
    (sourceFieldsOfFlexibleLowerTableFamily F equations)

/-- Positive direct payload constructor from flexible lower-table data and
indexed algebraic period equations. -/
theorem nonempty_directFlexibleSourcePayload_of_flexibleLowerTableFamily
    (F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily)
    (equations : FlexibleLowerTableAlgebraicPeriodEquations F) :
    Nonempty DirectFlexibleSourcePayload :=
  Nonempty.intro
    (directFlexibleSourcePayloadOfFlexibleLowerTableFamily F equations)

/-- The lower-table lift is exactly a flexible lower-table family together
with the indexed algebraic period equations for its stored words. -/
theorem nonempty_flexibleLowerTableSourceLift_iff_exists_lowerTable_algebraicPeriodEquations :
    Nonempty FlexibleLowerTableSourceLift <->
      Exists fun F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily =>
        FlexibleLowerTableAlgebraicPeriodEquations F := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro L =>
        exact Exists.intro L.lowerTable L.algebraicPeriodEquations
  case mpr =>
    intro H
    cases H with
    | intro F equations =>
        exact
          Nonempty.intro
            { lowerTable := F
              algebraicPeriodEquations := equations }

/-- Narrow checked remaining-field theorem for the direct W11 payload:
inhabiting `DirectFlexibleSourcePayload` is equivalent to providing a final
flexible lower-table family plus indexed algebraic period equations for that
family's words. -/
theorem nonempty_directFlexibleSourcePayload_iff_exists_lowerTable_algebraicPeriodEquations :
    Nonempty DirectFlexibleSourcePayload <->
      Exists fun F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily =>
        FlexibleLowerTableAlgebraicPeriodEquations F := by
  constructor
  case mp =>
    intro H
    have hLift : Nonempty FlexibleLowerTableSourceLift :=
      nonempty_sourceFields_iff_flexibleLowerTableSourceLift.1
        (nonempty_sourceFields_iff_directFlexibleSourcePayload.2 H)
    exact
      nonempty_flexibleLowerTableSourceLift_iff_exists_lowerTable_algebraicPeriodEquations.1
        hLift
  case mpr =>
    intro H
    have hLift : Nonempty FlexibleLowerTableSourceLift :=
      nonempty_flexibleLowerTableSourceLift_iff_exists_lowerTable_algebraicPeriodEquations.2
        H
    exact
      nonempty_sourceFields_iff_directFlexibleSourcePayload.1
        (nonempty_sourceFields_iff_flexibleLowerTableSourceLift.2
          hLift)

/-- Precise direct-flexible blocker: without the lower-table source lift, the
W11 minimal source fields cannot be inhabited. -/
theorem no_sourceFields_without_flexibleLowerTableSourceLift
    (hmissing : Not (Nonempty FlexibleLowerTableSourceLift)) :
    Not (Nonempty NonRigidRouteSourceFields) := by
  intro H
  exact hmissing
    (nonempty_sourceFields_iff_flexibleLowerTableSourceLift.1 H)

/-- Existing concrete non-connector lower-table families inhabit the
dependent W11 route source package, with no residual exact-local rows. -/
theorem nonempty_sourcePackage_of_concreteNonConnectorLowerTableFamily
    (H :
      Nonempty
        ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    Nonempty NonRigidRouteSourcePackage := by
  cases H with
  | intro C =>
      exact Nonempty.intro (sourcePackageOfConcreteNonConnectorLowerTableFamily C)

/-- The concrete period/non-connector source with a transition equality
inhabits the dependent W11 route source package after forgetting the equality
field, which is only needed by the exact-target spelling. -/
def sourcePackageOfConcreteNonConnectorLowerTableFamilyWithTransition
    (C : ConcreteSourceWithTransition) :
    NonRigidRouteSourcePackage :=
  sourcePackageOfConcreteNonConnectorLowerTableFamily C.1

theorem nonempty_sourcePackage_of_concreteNonConnectorLowerTableFamilyWithTransition
    (H : Nonempty ConcreteSourceWithTransition) :
    Nonempty NonRigidRouteSourcePackage := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (sourcePackageOfConcreteNonConnectorLowerTableFamilyWithTransition C)

/-- The partial period/non-connector/transition route source from
`PeriodCandidateTargetRoute` feeds the W11 dependent source package without
adding the blocked full exact-local residual rows. -/
theorem nonempty_sourcePackage_of_periodCandidatePartialLowerTableData
    (H : Nonempty PeriodCandidatePartialLowerTableData) :
    Nonempty NonRigidRouteSourcePackage := by
  exact
    nonempty_sourcePackage_of_concreteNonConnectorLowerTableFamilyWithTransition
      (nonempty_iff_concreteNonConnectorLowerTableFamilyWithTransition.1 H)

/-! ## Projections from W10 fields -/

/-- W10 complete non-rigid family fields forget to the smaller W11 route
interface. -/
def ofW10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    NonRigidRouteFields where
  candidate := F.candidateFields.toCandidate
  remaining :=
    { periodData := F.periodData
      metricData := F.metricData }

/-- W10 complete non-rigid fields contain exactly the W11 minimal source
fields, with no concrete lower-table detour. -/
def sourceFieldsOfW10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    NonRigidRouteSourceFields :=
  (ofW10CompleteNonRigidFamilyFields F).toNonRigidRouteSourceFields

/-- W10 complete non-rigid fields package as a flexible lower-table lift: the
lower-table data is the W11 projection, and the algebraic period equations are
the original W10 period fields. -/
def flexibleLowerTableSourceLiftOfW10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    FlexibleLowerTableSourceLift :=
  FlexibleLowerTableSourceLift.ofSourceFields
    (sourceFieldsOfW10CompleteNonRigidFamilyFields F)

/-- The projected flexible lower-table family from W10 complete non-rigid
fields carries the required indexed algebraic period equations. -/
theorem flexibleLowerTableAlgebraicPeriodEquations_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    FlexibleLowerTableAlgebraicPeriodEquations
      (sourceFieldsOfW10CompleteNonRigidFamilyFields F).toFlexiblePeriodLowerTableFamily :=
  flexibleLowerTableAlgebraicPeriodEquations_of_sourceFields
    (sourceFieldsOfW10CompleteNonRigidFamilyFields F)

@[simp]
theorem ofW10CompleteNonRigidFamilyFields_candidate
    (F : W10CompleteNonRigidFamilyFields) :
    (ofW10CompleteNonRigidFamilyFields F).candidate =
      F.candidateFields.toCandidate :=
  rfl

@[simp]
theorem ofW10CompleteNonRigidFamilyFields_same_placeNext
    (F : W10CompleteNonRigidFamilyFields) :
    (ofW10CompleteNonRigidFamilyFields F).candidate.same.placeNext =
      F.candidateFields.same.parameters.placeNext :=
  rfl

@[simp]
theorem ofW10CompleteNonRigidFamilyFields_opposite_placeNext
    (F : W10CompleteNonRigidFamilyFields) :
    (ofW10CompleteNonRigidFamilyFields F).candidate.opposite.placeNext =
      F.candidateFields.opposite.parameters.placeNext :=
  rfl

/-- Exact target theorem projected through the smaller W11 route interface. -/
theorem targetUpperConstructionFiveSixteen_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (ofW10CompleteNonRigidFamilyFields F).targetUpperConstructionFiveSixteen

/-- Arbitrary-size target theorem projected through the smaller W11 route
interface. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (ofW10CompleteNonRigidFamilyFields F).targetUpperConstructionFiveSixteenArbitrary

/-- Nonempty W10 complete non-rigid data is a direct W11 source inhabitant.
The remaining exact gate is therefore the W10 `metricData` field over a
candidate and all-positive period data, not any blocked role-hinge concrete
lower-table package. -/
theorem nonempty_sourceFields_of_w10CompleteNonRigidFamilyFields
    (H : Nonempty W10CompleteNonRigidFamilyFields) :
    Nonempty NonRigidRouteSourceFields := by
  cases H with
  | intro F =>
      exact Nonempty.intro
        (sourceFieldsOfW10CompleteNonRigidFamilyFields F)

/-- Nonempty W10 complete non-rigid fields inhabit the precise flexible
lower-table lift gate, including the indexed algebraic period equations. -/
theorem nonempty_flexibleLowerTableSourceLift_of_w10CompleteNonRigidFamilyFields
    (H : Nonempty W10CompleteNonRigidFamilyFields) :
    Nonempty FlexibleLowerTableSourceLift :=
  nonempty_sourceFields_iff_flexibleLowerTableSourceLift.1
    (nonempty_sourceFields_of_w10CompleteNonRigidFamilyFields H)

/-- Nonempty W10 complete non-rigid fields give a flexible lower-table family
equipped with the exact algebraic period equations required by W11. -/
theorem nonempty_exists_lowerTable_algebraicPeriodEquations_of_w10CompleteNonRigidFamilyFields
    (H : Nonempty W10CompleteNonRigidFamilyFields) :
    Exists fun F : PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily =>
      FlexibleLowerTableAlgebraicPeriodEquations F :=
  nonempty_flexibleLowerTableSourceLift_iff_exists_lowerTable_algebraicPeriodEquations.1
    (nonempty_flexibleLowerTableSourceLift_of_w10CompleteNonRigidFamilyFields H)

/-- Nonempty W10 complete non-rigid fields inhabit the direct W11 payload
gate, via the same source-field projection and without concrete table/value
shortcuts. -/
theorem nonempty_directFlexibleSourcePayload_of_w10CompleteNonRigidFamilyFields
    (H : Nonempty W10CompleteNonRigidFamilyFields) :
    Nonempty DirectFlexibleSourcePayload :=
  nonempty_sourceFields_iff_directFlexibleSourcePayload.1
    (nonempty_sourceFields_of_w10CompleteNonRigidFamilyFields H)

/-- W10 complete non-rigid fields reduce to the final flexible lower-table
source through the smaller W11 route interface. -/
theorem nonempty_flexiblePeriodLowerTableFamily_of_w10CompleteNonRigidFamilyFields
    (H : Nonempty W10CompleteNonRigidFamilyFields) :
    Nonempty PachTothFinalDataAssembly.FlexiblePeriodLowerTableFamily := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          ((ofW10CompleteNonRigidFamilyFields F)
            |>.toFlexiblePeriodLowerTableFamily)

/-- W10 complete non-rigid fields also reduce to the flexible
generated-closure family. -/
theorem nonempty_flexibleGeneratedClosureFamily_of_w10CompleteNonRigidFamilyFields
    (H : Nonempty W10CompleteNonRigidFamilyFields) :
    Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          ((ofW10CompleteNonRigidFamilyFields F)
            |>.toFlexibleGeneratedClosureFamily)

/-! ## Completed filtered branches also project to the smaller route -/

/-- A filtered branch surface plus full exact-local completion, period fields,
and metric fields.  This is intentionally stronger than the W11 route because
it remembers how the candidate was obtained. -/
structure CompletedFilteredRouteFields
    (F : FilteredSameOpposite) where
  completion : FilteredCompletionFields F
  periodData : PeriodSearchData completion.toCandidate
  metricData :
    RoleHingeCandidateSearchSurface.CrossBlockMetricData periodData

namespace CompletedFilteredRouteFields

/-- Forget the completed filtered origin to the smaller W11 route. -/
def toNonRigidRouteFields
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    NonRigidRouteFields where
  candidate := R.completion.toCandidate
  remaining :=
    { periodData := R.periodData
      metricData := R.metricData }

@[simp]
theorem toNonRigidRouteFields_candidate
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    R.toNonRigidRouteFields.candidate = R.completion.toCandidate :=
  rfl

/-- Exact target theorem for a completed filtered route, via the smaller
interface. -/
theorem targetUpperConstructionFiveSixteen
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.toNonRigidRouteFields.targetUpperConstructionFiveSixteen

end CompletedFilteredRouteFields

/-! ## Concrete four-target checked rows and obstructions -/

/-- Checked row data for the concrete four-target surface. -/
structure ConcreteFourTargetCheckedRows where
  filtered : FilteredSameOpposite
  samePossibleRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      RoleHingeConcreteSearch.samePlaceNext
  oppositePossibleRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      RoleHingeConcreteSearch.oppositePlaceNext
  t11rNotPossible :
    Not (ExactLocalBranchSolverSurface.PossibleRow T1_1 LocalVertex.r)
  sameT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r
  oppositeT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r
  possibleRowCount :
    ExactLocalObstructionExpansionW10.possibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.possibleExactLocalRowExpectedCard
  impossibleRowCount :
    ExactLocalObstructionExpansionW10.impossibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.impossibleExactLocalRowExpectedCard

/-- The concrete four-target surface has checked possible rows and named
blocked rows, but not full exact-local completion. -/
def concreteFourTargetCheckedRows :
    ConcreteFourTargetCheckedRows where
  filtered :=
    FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite
  samePossibleRows :=
    ExactLocalBranchSolverSurface.samePlaceNext_preservesPossibleExactLocalRows
  oppositePossibleRows :=
    ExactLocalBranchSolverSurface.oppositePlaceNext_preservesPossibleExactLocalRows
  t11rNotPossible :=
    ExactLocalBranchSolverSurface.not_possible_T1_1_r
  sameT11RExactBase :=
    ExactLocalBranchSolverSurface.samePlaceNext_T1_1_r_exactBaseContradiction
  oppositeT11RExactBase :=
    ExactLocalBranchSolverSurface.oppositePlaceNext_T1_1_r_exactBaseContradiction
  possibleRowCount :=
    ExactLocalObstructionExpansionW10.possibleRowEntries_card
  impossibleRowCount :=
    ExactLocalObstructionExpansionW10.impossibleRowEntries_card

/-- A concrete four-target route claim is the over-strong assertion that the
smaller W11 candidate can use the current concrete same/opposite maps. -/
structure ConcreteFourTargetRouteClaim extends NonRigidRouteFields where
  same_placeNext :
    candidate.same.placeNext = RoleHingeConcreteSearch.samePlaceNext
  opposite_placeNext :
    candidate.opposite.placeNext = RoleHingeConcreteSearch.oppositePlaceNext

/-- The same over-strong concrete claim, stated at the minimal source-field
level rather than the nested W11 route level. -/
structure ConcreteFourTargetSourceClaim extends NonRigidRouteSourceFields where
  same_placeNext :
    candidate.same.placeNext = RoleHingeConcreteSearch.samePlaceNext
  opposite_placeNext :
    candidate.opposite.placeNext = RoleHingeConcreteSearch.oppositePlaceNext

/-- The concrete same branch cannot be a W11 branch candidate. -/
theorem not_sameConcreteBranchCandidate :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.samePlaceNext) := by
  intro h
  cases h with
  | intro T hplace =>
      exact
        ExactLocalBranchSolverSurface.samePlaceNext_not_preservesExactLocalSqDistances
          (by
            simpa [hplace] using T.preserves_exactLocal_sqDistances)

/-- The concrete opposite branch cannot be a W11 branch candidate. -/
theorem not_oppositeConcreteBranchCandidate :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) := by
  intro h
  cases h with
  | intro T hplace =>
      exact
        ExactLocalBranchSolverSurface.oppositePlaceNext_not_preservesExactLocalSqDistances
          (by
            simpa [hplace] using T.preserves_exactLocal_sqDistances)

/-- The current concrete four-target maps cannot inhabit the smaller W11 route
candidate interface. -/
theorem not_concreteFourTargetRouteClaim :
    ConcreteFourTargetRouteClaim -> False := by
  intro C
  exact
    not_sameConcreteBranchCandidate
      (Exists.intro C.candidate.same C.same_placeNext)

/-- The current concrete four-target maps cannot inhabit the minimal W11
source fields either; the obstruction is already the same exact-local
same-branch row. -/
theorem not_concreteFourTargetSourceClaim :
    ConcreteFourTargetSourceClaim -> False := by
  intro C
  exact
    not_sameConcreteBranchCandidate
      (Exists.intro C.candidate.same C.same_placeNext)

/-- The concrete filtered four-target surface cannot be promoted to a
completed filtered route. -/
theorem not_concreteFourTargetCompletedFilteredRouteFields :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False := by
  intro R
  exact
    FlexibleTransitionSearchW10.not_concreteFourTargetFilteredCompletion
      R.completion

/-- W11 summary package: checked concrete rows, blocked over-strong concrete
routes, and the smaller viable route type kept separate. -/
structure RemainingFieldPackage where
  routeFields : Type
  sourceFields : Type
  sourceFieldsEquiv :
    Nonempty routeFields <-> Nonempty sourceFields
  directPayload : Type
  directPayloadEquiv :
    Nonempty sourceFields <-> Nonempty directPayload
  directPayloadCandidatePeriodMetric :
    Nonempty directPayload <->
      Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P)
  missingDirectPayloadBlocksSource :
    Not (Nonempty directPayload) -> Not (Nonempty sourceFields)
  checkedRows : ConcreteFourTargetCheckedRows
  blockedConcreteRoute : ConcreteFourTargetRouteClaim -> False
  blockedConcreteSource : ConcreteFourTargetSourceClaim -> False
  blockedConcreteFilteredRoute :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False

/-- Public W11 remaining-field package. -/
def remainingFieldPackage : RemainingFieldPackage where
  routeFields := NonRigidRouteFields
  sourceFields := NonRigidRouteSourceFields
  sourceFieldsEquiv := nonempty_nonRigidRouteFields_iff_sourceFields
  directPayload := DirectFlexibleSourcePayload
  directPayloadEquiv :=
    nonempty_sourceFields_iff_directFlexibleSourcePayload
  directPayloadCandidatePeriodMetric :=
    nonempty_directFlexibleSourcePayload_iff_exists_candidate_period_metric
  missingDirectPayloadBlocksSource :=
    no_sourceFields_without_directFlexibleSourcePayload
  checkedRows := concreteFourTargetCheckedRows
  blockedConcreteRoute := not_concreteFourTargetRouteClaim
  blockedConcreteSource := not_concreteFourTargetSourceClaim
  blockedConcreteFilteredRoute :=
    not_concreteFourTargetCompletedFilteredRouteFields

/-- Projection of the checked same-branch possible-row theorem from the W11
package. -/
theorem concreteSamePossibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : ExactLocalBranchSolverSurface.PossibleRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  remainingFieldPackage.checkedRows.samePossibleRows source hsource u v hrow

/-- Projection of the checked opposite-branch possible-row theorem from the
W11 package. -/
theorem concreteOppositePossibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : ExactLocalBranchSolverSurface.PossibleRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  remainingFieldPackage.checkedRows.oppositePossibleRows source hsource u v hrow

/-- Projection of the concrete route obstruction from the W11 package. -/
theorem concreteFourTargetRouteClaim_blocked :
    ConcreteFourTargetRouteClaim -> False :=
  remainingFieldPackage.blockedConcreteRoute

/-- Projection of the concrete source-field obstruction from the W11
package. -/
theorem concreteFourTargetSourceClaim_blocked :
    ConcreteFourTargetSourceClaim -> False :=
  remainingFieldPackage.blockedConcreteSource

/-- Projection of the concrete completed-filtered-route obstruction from the
W11 package. -/
theorem concreteFourTargetCompletedFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  remainingFieldPackage.blockedConcreteFilteredRoute

/-- Public W11 equivalence between minimal source fields and the direct
flexible payload. -/
theorem directFlexibleSourcePayload_equiv_sourceFields :
    Nonempty NonRigidRouteSourceFields <->
      Nonempty DirectFlexibleSourcePayload :=
  remainingFieldPackage.directPayloadEquiv

/-- Public W11 equivalence naming the remaining flexible
candidate/period/metric payload. -/
theorem directFlexibleSourcePayload_equiv_candidate_period_metric :
    Nonempty DirectFlexibleSourcePayload <->
      Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P) :=
  remainingFieldPackage.directPayloadCandidatePeriodMetric

/-- Public W11 blocker: without the direct flexible payload, the minimal
non-rigid route source cannot be inhabited. -/
theorem sourceFields_blocked_without_directFlexibleSourcePayload
    (hmissing : Not (Nonempty DirectFlexibleSourcePayload)) :
    Not (Nonempty NonRigidRouteSourceFields) :=
  remainingFieldPackage.missingDirectPayloadBlocksSource hmissing

/-- Checked status of the current W11 flexible generated-closure route.

The positive direction is the only live construction route found here:
provide the direct flexible payload, equivalently a same/opposite candidate
with all-positive period equations and cross-block metric data, and W11
produces `GeneratedClosureFamily`.  If that direct payload is absent, the
current W11 source/route packages are absent too; the concrete four-target
table routes remain blocked separately. -/
structure FlexibleGeneratedClosureCurrentRouteStatus : Prop where
  directPayload_to_generatedClosure :
    Nonempty DirectFlexibleSourcePayload ->
      Nonempty FlexibleExactLocalTransition.GeneratedClosureFamily
  exactRemainingPayload :
    Nonempty DirectFlexibleSourcePayload <->
      Exists fun T : SameOppositeCandidate =>
        Exists fun P : PeriodSearchData T =>
          Nonempty (RoleHingeCandidateSearchSurface.CrossBlockMetricData P)
  missingDirectPayload_blocks_currentRoute :
    Not (Nonempty DirectFlexibleSourcePayload) ->
      Not (Nonempty NonRigidRouteSourceFields) /\
        Not (Nonempty NonRigidRouteFields) /\
          Not (Nonempty NonRigidRouteSourcePackage)
  concreteFourTargetRoute_blocked :
    ConcreteFourTargetRouteClaim -> False
  concreteFourTargetSource_blocked :
    ConcreteFourTargetSourceClaim -> False
  concreteFourTargetFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False

/-- Public W11 certificate for the flexible generated-closure route status. -/
theorem flexibleGeneratedClosureCurrentRouteStatus :
    FlexibleGeneratedClosureCurrentRouteStatus where
  directPayload_to_generatedClosure :=
    nonempty_flexibleGeneratedClosureFamily_of_directFlexibleSourcePayload
  exactRemainingPayload :=
    directFlexibleSourcePayload_equiv_candidate_period_metric
  missingDirectPayload_blocks_currentRoute :=
    currentGeneratedClosureRoute_blocked_without_directFlexibleSourcePayload
  concreteFourTargetRoute_blocked :=
    concreteFourTargetRouteClaim_blocked
  concreteFourTargetSource_blocked :=
    concreteFourTargetSourceClaim_blocked
  concreteFourTargetFilteredRoute_blocked :=
    concreteFourTargetCompletedFilteredRoute_blocked

end FlexibleTransitionSearchW11
end PachToth
end ErdosProblems1066

end
