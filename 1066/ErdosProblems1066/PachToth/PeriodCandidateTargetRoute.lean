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

/-- The exact-target minimal certificate assembled from the explicit period
fields and the reduced non-connector square-distance table family. -/
def toMinimalExactTargetCertificate
    (D : PeriodCandidateLowerTableData) :
    ExactTargetCandidateClosure.MinimalExactTargetCertificate where
  word := D.periodSearch.word
  equation := by
    intro k hk i
    have h := D.periodSearch.equation k hk i
    simpa [D.transition_eq,
      PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord] using h
  same_rest := D.same_rest
  opposite_rest := D.opposite_rest
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
