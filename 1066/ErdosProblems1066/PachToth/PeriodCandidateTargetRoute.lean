import ErdosProblems1066.PachToth.ConcretePeriodWordSearch
import ErdosProblems1066.PachToth.ConcreteCrossBlockLowerTable
import ErdosProblems1066.PachToth.ExactTargetCandidateClosure
import ErdosProblems1066.PachToth.ArbitraryNClosureCandidate

set_option autoImplicit false

/-!
# Period-candidate target route

This module connects the search-facing period-candidate data and the reduced
non-connector square-distance tables to the exact-target candidate closure.

The route is deliberately conditional and field-explicit.  It does not claim
that a search has succeeded; it records how the checked period-word equations,
the concrete exact-local residual fields, and a family of non-connector lower
tables assemble into the existing exact `16 * k` target and then into the
arbitrary-`n` target.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodCandidateTargetRoute

open FiniteGraph
open ConcreteCrossBlockLowerTable
open ExactTargetCandidateClosure
open NonRigidConnectorSeparationFacts

noncomputable section

abbrev R2 := Prod Real Real
abbrev LocalVertexIndex := CrossBlockLowerBoundsInterface.LocalVertexIndex

/-- The concrete two-letter period-word candidate exposed by the small-word
search module. -/
abbrev twoStepCandidateWord : OrientationWord.Word 2 :=
  ConcretePeriodWordSearch.candidateWord

/-- Exact-base closure equation for the concrete two-step period candidate,
spelled against the transition obligations used by the exact-target route. -/
abbrev TwoStepCandidateClosureEquation : Prop :=
  ConcretePeriodWordSearch.ExactBaseCandidateClosureEquation
    ExactTargetCandidateClosure.concreteObligations

/-- A two-step closure equation supplies the sixteen algebraic period fields
for the concrete two-letter candidate. -/
theorem twoStepCandidate_equations
    (hclose : TwoStepCandidateClosureEquation) :
    PeriodWordCertificates.AlgebraicEquationsForWord
      ExactTargetCandidateClosure.concreteObligations
      PeriodCertificateExamples.twoPositiveLength
      BaseTransitionRealization.exactBase
      twoStepCandidateWord := by
  intro i
  exact
    ConcretePeriodWordSearch.candidateAlgebraicEquations_of_twoStepClosesBase
      ExactTargetCandidateClosure.concreteObligations
      BaseTransitionRealization.exactBase hclose i

/-- The checked period-word and non-connector lower-table inputs needed for
the partial exact-target candidate certificate.

This deliberately excludes the residual exact-local same/opposite fields.  It
is the portion already supplied by period-equation and cross-block table
searches. -/
structure PeriodCandidatePartialLowerTableData where
  periodSearch : PeriodSearchData
  transition_eq :
    periodSearch.transitions.toFigure2TransitionObligations =
      ExactTargetCandidateClosure.concreteObligations
  tables :
    NonConnectorLowerTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace PeriodCandidatePartialLowerTableData

/-- The exact concrete source package for the partial route: concrete
non-connector lower tables together with the transition equality needed to
specialize them to the exact-target obligations. -/
abbrev ConcreteNonConnectorLowerTableFamilyWithTransition : Type :=
  { C : ConcreteNonConnectorLowerTableFamily //
    C.periodSearch.transitions.toFigure2TransitionObligations =
      ExactTargetCandidateClosure.concreteObligations }

/-- Build the partial route input from the dependent concrete lower-table
package exported by `ConcreteCrossBlockLowerTable`. -/
def ofConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily)
    (transition_eq :
      C.periodSearch.transitions.toFigure2TransitionObligations =
        ExactTargetCandidateClosure.concreteObligations) :
    PeriodCandidatePartialLowerTableData where
  periodSearch := C.periodSearch
  transition_eq := transition_eq
  tables := C.tables

/-- The checked partial exact-target certificate assembled from explicit
period fields and reduced non-connector square-distance tables. -/
def toMinimalExactTargetPartialCertificate
    (D : PeriodCandidatePartialLowerTableData) :
    ExactTargetCandidateClosure.MinimalExactTargetPartialCertificate where
  word := D.periodSearch.word
  equation := by
    intro k hk i
    have h := D.periodSearch.equation k hk i
    simpa [D.transition_eq,
      PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord] using h
  nonConnectorSqDist_ge_one := by
    intro k hk i u j v hij hnot
    have hsq :
        1 <=
          CrossBlockDistanceSqReduction.indexedGeneratedSqDist
            D.periodSearch.toRoleHingedPeriodSearchFamily hk i u j v :=
      (D.tables.table k hk).sqTable.sqDist_ge_one i u j v hij hnot
    simpa [ExactTargetCandidateClosure.concreteIndexedGeneratedSqDist,
      ExactTargetCandidateClosure.concreteGeneratedPoint,
      CrossBlockDistanceSqReduction.indexedGeneratedSqDist,
      CrossBlockLowerBoundsInterface.indexedGeneratedPoint,
      ConcretePeriodSearchFamily.PeriodSearchData.toRoleHingedPeriodSearchFamily,
      ConcretePeriodSearchFamily.PeriodSearchData.orientation,
      D.transition_eq] using hsq

/-- Forget the exact-target transition equality and retain the concrete
period/non-connector lower-table package used by the flexible route. -/
def toConcreteNonConnectorLowerTableFamily
    (D : PeriodCandidatePartialLowerTableData) :
    ConcreteNonConnectorLowerTableFamily where
  periodSearch := D.periodSearch
  tables := D.tables

/-- The exact concrete source package for the partial route: concrete
non-connector lower tables together with the transition equality needed to
specialize them to the exact-target obligations. -/
def toConcreteNonConnectorLowerTableFamilyWithTransition
    (D : PeriodCandidatePartialLowerTableData) :
    ConcreteNonConnectorLowerTableFamilyWithTransition :=
  ⟨D.toConcreteNonConnectorLowerTableFamily, D.transition_eq⟩

/-- Reconstruct the partial route input from the named concrete source
package. -/
def ofConcreteNonConnectorLowerTableFamilyWithTransition
    (C : ConcreteNonConnectorLowerTableFamilyWithTransition) :
    PeriodCandidatePartialLowerTableData :=
  ofConcreteNonConnectorLowerTableFamily C.1 C.2

/-- The partial route is inhabited exactly when the concrete non-connector
lower-table source is inhabited with the required transition equality.  This
keeps the source away from the blocked residual exact-local fields. -/
theorem nonempty_iff_concreteNonConnectorLowerTableFamilyWithTransition :
    Nonempty PeriodCandidatePartialLowerTableData <->
      Nonempty ConcreteNonConnectorLowerTableFamilyWithTransition := by
  constructor
  case mp =>
    intro H
    cases H with
    | intro D =>
        exact
          Nonempty.intro
            D.toConcreteNonConnectorLowerTableFamilyWithTransition
  case mpr =>
    intro H
    cases H with
    | intro C =>
        exact
          Nonempty.intro
            (ofConcreteNonConnectorLowerTableFamilyWithTransition C)

/-- The smaller source field already present inside the partial package:
any partial period/lower-table record contains a role-hinged period-search
family, before any residual exact-local fields enter the discussion. -/
def toRoleHingedPeriodSearchFamily
    (D : PeriodCandidatePartialLowerTableData) :
    ConcreteCrossBlockLowerTable.RoleHingedPeriodSearchFamily :=
  D.periodSearch.toRoleHingedPeriodSearchFamily

theorem nonempty_roleHingedPeriodSearchFamily_of_partial
    (H : Nonempty PeriodCandidatePartialLowerTableData) :
    Nonempty ConcreteCrossBlockLowerTable.RoleHingedPeriodSearchFamily := by
  cases H with
  | intro D => exact Nonempty.intro D.toRoleHingedPeriodSearchFamily

end PeriodCandidatePartialLowerTableData

/-- Search-facing all-positive period data together with reduced
non-connector square-distance tables, specialized to the concrete connector
transition obligations used by `ExactTargetCandidateClosure`.

The equality field is intentionally explicit: lower-table families are built
over a role-hinged period-search family, while the exact-target closure fixes
the concrete connector-only transition obligations.  The record only bridges
those two presentations when the caller supplies their equality. -/
structure PeriodCandidateLowerTableData where
  periodSearch : PeriodSearchData
  transition_eq :
    periodSearch.transitions.toFigure2TransitionObligations =
      ExactTargetCandidateClosure.concreteObligations
  same_rest :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.samePlaceNext source u)
                (RoleHingeConcreteSearch.samePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4
  opposite_rest :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.oppositePlaceNext source u)
                (RoleHingeConcreteSearch.oppositePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4
  tables :
    NonConnectorLowerTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace PeriodCandidateLowerTableData

/-- Forget the residual exact-local rows, retaining the checked period and
non-connector lower-table portion. -/
def toPartialLowerTableData
    (D : PeriodCandidateLowerTableData) :
    PeriodCandidatePartialLowerTableData where
  periodSearch := D.periodSearch
  transition_eq := D.transition_eq
  tables := D.tables

/-- Build the route input from the dependent concrete lower-table package
exported by `ConcreteCrossBlockLowerTable`. -/
def ofConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily)
    (transition_eq :
      C.periodSearch.transitions.toFigure2TransitionObligations =
        ExactTargetCandidateClosure.concreteObligations)
    (same_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.samePlaceNext source u)
                  (RoleHingeConcreteSearch.samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)
    (opposite_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.oppositePlaceNext source u)
                  (RoleHingeConcreteSearch.oppositePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    PeriodCandidateLowerTableData where
  periodSearch := C.periodSearch
  transition_eq := transition_eq
  same_rest := same_rest
  opposite_rest := opposite_rest
  tables := C.tables

/-- The checked partial exact-target certificate obtained from the period and
non-connector table fields, before adding residual exact-local rows. -/
def toMinimalExactTargetPartialCertificate
    (D : PeriodCandidateLowerTableData) :
    ExactTargetCandidateClosure.MinimalExactTargetPartialCertificate :=
  D.toPartialLowerTableData.toMinimalExactTargetPartialCertificate

/-- The exact-target minimal certificate assembled from the explicit period
fields and the reduced non-connector square-distance table family. -/
def toMinimalExactTargetCertificate
    (D : PeriodCandidateLowerTableData) :
    ExactTargetCandidateClosure.MinimalExactTargetCertificate :=
  D.toMinimalExactTargetPartialCertificate.withExactLocalResiduals
    D.same_rest D.opposite_rest

/-- The residual exact-local fields carried by the old full exact-target
route, isolated so the checked blocker can point to the precise missing
surface. -/
def toExactLocalResidualFields
    (D : PeriodCandidateLowerTableData) :
    ExactTargetCandidateClosure.ExactLocalResidualFields where
  same_rest := D.same_rest
  opposite_rest := D.opposite_rest

/-- The full period-candidate lower-table record is uninhabited for the
current concrete exact-target route: it includes the impossible same-branch
residual exact-local row family. -/
theorem not_nonempty :
    Not (Nonempty PeriodCandidateLowerTableData) := by
  intro h
  cases h with
  | intro D =>
      exact ExactTargetCandidateClosure.not_exactLocalResidualFields
        (Nonempty.intro D.toExactLocalResidualFields)

/-- Exact-block target at one positive block count through the assembled
exact-target candidate closure. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (D : PeriodCandidateLowerTableData)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  D.toMinimalExactTargetCertificate.targetUpperConstructionFiveSixteenAt_exactBlock
    k hk

/-- Exact Pach--Toth target from period-candidate data plus reduced
non-connector lower-table families. -/
theorem targetUpperConstructionFiveSixteen
    (D : PeriodCandidateLowerTableData) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toMinimalExactTargetCertificate.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target, routed through the existing exact-target
to arbitrary-`n` candidate closure. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (D : PeriodCandidateLowerTableData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ArbitraryNClosureCandidate.arbitrary_of_exactTarget
    D.targetUpperConstructionFiveSixteen

/-- The same exact target exposed with the lower tables first, for callers
that already hold a `ConcreteNonConnectorLowerTableFamily`. -/
theorem targetUpperConstructionFiveSixteen_of_concreteNonConnectorLowerTables
    (D : PeriodCandidateLowerTableData) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.targetUpperConstructionFiveSixteen

/-- The same arbitrary target exposed with the lower tables first, for callers
that already hold a `ConcreteNonConnectorLowerTableFamily`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteNonConnectorLowerTables
    (D : PeriodCandidateLowerTableData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  D.targetUpperConstructionFiveSixteenArbitrary

/-- Exact Pach--Toth target directly from the dependent concrete
non-connector lower-table package plus the remaining concrete exact-local
fields. -/
theorem targetUpperConstructionFiveSixteen_ofConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily)
    (transition_eq :
      C.periodSearch.transitions.toFigure2TransitionObligations =
        ExactTargetCandidateClosure.concreteObligations)
    (same_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.samePlaceNext source u)
                  (RoleHingeConcreteSearch.samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)
    (opposite_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.oppositePlaceNext source u)
                  (RoleHingeConcreteSearch.oppositePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (ofConcreteNonConnectorLowerTableFamily
    C transition_eq same_rest opposite_rest).targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target directly from the dependent concrete
non-connector lower-table package plus the remaining concrete exact-local
fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary_ofConcreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily)
    (transition_eq :
      C.periodSearch.transitions.toFigure2TransitionObligations =
        ExactTargetCandidateClosure.concreteObligations)
    (same_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.samePlaceNext source u)
                  (RoleHingeConcreteSearch.samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)
    (opposite_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.oppositePlaceNext source u)
                  (RoleHingeConcreteSearch.oppositePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (ofConcreteNonConnectorLowerTableFamily
    C transition_eq same_rest opposite_rest)
      |>.targetUpperConstructionFiveSixteenArbitrary

end PeriodCandidateLowerTableData

end

end PeriodCandidateTargetRoute
end PachToth
end ErdosProblems1066
