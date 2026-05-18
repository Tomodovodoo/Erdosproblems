import ErdosProblems1066.PachToth.FlexibleBranchCoordinateSearch
import ErdosProblems1066.PachToth.ExactLocalBranchSolverSurface
import ErdosProblems1066.PachToth.UnitVectorParameterizationSearch
import ErdosProblems1066.PachToth.RoleHingeCandidateSearchSurface
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition

set_option autoImplicit false

/-!
# W10 flexible transition search surface

This file is an honest assembly surface for non-rigid transition searches
beyond the blocked concrete same/opposite four-target ansatz.

It exposes:

* unit-vector branch fields that construct `SameOppositeCandidate` data;
* filtered exact-local branches whose full exact-local completion remains an
  explicit field;
* a complete generated-family payload whose target theorem is available only
  after candidate, period, and metric fields have all been supplied; and
* named contradictions showing that the current concrete four-target
  same/opposite maps cannot fill those exact-local completion fields.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleTransitionSearchW10

open FiniteGraph
open ExactLocalBranchSolverSurface
open FlexibleBranchCoordinateSearch

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev UnitVectorBranchParameters :=
  UnitVectorParameterizationSearch.UnitVectorBranchParameters
abbrev BranchCandidate :=
  RoleHingeCandidateSearchSurface.BranchCandidate
abbrev SameOppositeCandidate :=
  RoleHingeCandidateSearchSurface.SameOppositeCandidate
abbrev FilteredBranch :=
  ExactLocalBranchSolverSurface.FilteredBranch
abbrev FilteredSameOpposite :=
  ExactLocalBranchSolverSurface.FilteredSameOpposite

/-! ## Candidate construction from unit-vector fields -/

/-- Honest fields for one branch of a flexible transition candidate.

The exact-local field is deliberately the explicit non-angle row table from
the unit-vector search surface; the role-angle port rows are then derived from
the supplied angle equations. -/
structure BranchCandidateFields where
  parameters : UnitVectorBranchParameters
  angleEquations :
    RoleHingeAngleCertificates.RoleHingeAngleEquations
      parameters.roleAngle
  nonAngleRows :
    UnitVectorParameterizationSearch.UnitVectorBranchParameters.NonAngleExactLocalRowHypotheses
      parameters

namespace BranchCandidateFields

/-- Connector data extracted from the unit-vector parameterization. -/
def toConnectorUnitRoleData
    (B : BranchCandidateFields) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData :=
  B.parameters.toConnectorUnitRoleData

@[simp]
theorem toConnectorUnitRoleData_placeNext
    (B : BranchCandidateFields) :
    B.toConnectorUnitRoleData.placeNext = B.parameters.placeNext :=
  rfl

/-- Full exact-local preservation obtained from the explicit row fields. -/
theorem preservesExactLocalSqDistances
    (B : BranchCandidateFields) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      B.parameters.placeNext :=
  B.parameters.preservesExactLocalSqDistances_of_angleEquations_and_nonAngleRows
    B.angleEquations B.nonAngleRows

/-- One flexible exact-local branch built from the explicit unit-vector
fields. -/
def toFlexibleBranch
    (B : BranchCandidateFields) :
    FlexibleExactLocalTransition.Branch :=
  B.parameters.toFlexibleBranch B.angleEquations B.nonAngleRows

@[simp]
theorem toFlexibleBranch_placeNext
    (B : BranchCandidateFields) :
    B.toFlexibleBranch.placeNext = B.parameters.placeNext :=
  rfl

/-- One role-hinge search candidate built from the explicit unit-vector
fields. -/
def toBranchCandidate
    (B : BranchCandidateFields) :
    BranchCandidate where
  placeNext := B.parameters.placeNext
  roleAngle := B.parameters.roleAngle
  realizes_role := B.parameters.realizes_role
  preserves_exactLocal_sqDistances := B.preservesExactLocalSqDistances

@[simp]
theorem toBranchCandidate_placeNext
    (B : BranchCandidateFields) :
    B.toBranchCandidate.placeNext = B.parameters.placeNext :=
  rfl

@[simp]
theorem toBranchCandidate_roleAngle
    (B : BranchCandidateFields) :
    B.toBranchCandidate.roleAngle = B.parameters.roleAngle :=
  rfl

/-- Connector-unit edges are derived from the unit-vector role equations. -/
theorem connector_unit_edges
    (B : BranchCandidateFields) :
    HingedTransitionInterface.ConnectorUnitEdges
      B.parameters.placeNext :=
  B.parameters.connector_unit_edges

end BranchCandidateFields

/-- Honest fields for a same/opposite pair of flexible transition candidates. -/
structure SameOppositeCandidateFields where
  same : BranchCandidateFields
  opposite : BranchCandidateFields

namespace SameOppositeCandidateFields

/-- Same/opposite candidate constructed from explicit branch fields. -/
def toCandidate
    (F : SameOppositeCandidateFields) :
    SameOppositeCandidate where
  same := F.same.toBranchCandidate
  opposite := F.opposite.toBranchCandidate

@[simp]
theorem toCandidate_same_placeNext
    (F : SameOppositeCandidateFields) :
    F.toCandidate.same.placeNext = F.same.parameters.placeNext :=
  rfl

@[simp]
theorem toCandidate_opposite_placeNext
    (F : SameOppositeCandidateFields) :
    F.toCandidate.opposite.placeNext =
      F.opposite.parameters.placeNext :=
  rfl

/-- Same/opposite flexible exact-local transition data from explicit branch
fields. -/
def toFlexibleSameOpposite
    (F : SameOppositeCandidateFields) :
    FlexibleExactLocalTransition.SameOpposite where
  same := F.same.toFlexibleBranch
  opposite := F.opposite.toFlexibleBranch

@[simp]
theorem toFlexibleSameOpposite_same_placeNext
    (F : SameOppositeCandidateFields) :
    F.toFlexibleSameOpposite.same.placeNext =
      F.same.parameters.placeNext :=
  rfl

@[simp]
theorem toFlexibleSameOpposite_opposite_placeNext
    (F : SameOppositeCandidateFields) :
    F.toFlexibleSameOpposite.opposite.placeNext =
      F.opposite.parameters.placeNext :=
  rfl

/-- Candidate exact-local fields give the generated-transition invariant used
by generated chains. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (F : SameOppositeCandidateFields) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      F.toCandidate.toFigure2TransitionObligations :=
  F.toCandidate.generatedTransitionsPreserveExactLocalSqDistances

end SameOppositeCandidateFields

/-! ## Exact-local completion fields for filtered solver surfaces -/

/-- Full exact-local completion fields for a solver-facing filtered
same/opposite surface. -/
structure FilteredSameOppositeCompletionFields
    (F : FilteredSameOpposite) where
  same_exactLocal :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      F.same.placeNext
  opposite_exactLocal :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      F.opposite.placeNext

/-- A filtered branch becomes a candidate branch only after full exact-local
preservation is supplied. -/
def branchCandidateOfFilteredBranch
    (B : FilteredBranch)
    (hfull :
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        B.placeNext) :
    BranchCandidate where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector.realizes_role
  preserves_exactLocal_sqDistances := hfull

@[simp]
theorem branchCandidateOfFilteredBranch_placeNext
    (B : FilteredBranch)
    (hfull :
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        B.placeNext) :
    (branchCandidateOfFilteredBranch B hfull).placeNext =
      B.placeNext :=
  rfl

namespace FilteredSameOppositeCompletionFields

/-- Promote a filtered same/opposite surface to flexible exact-local
transition data after both full exact-local fields are supplied. -/
def toFlexibleSameOpposite
    {F : FilteredSameOpposite}
    (C : FilteredSameOppositeCompletionFields F) :
    FlexibleExactLocalTransition.SameOpposite :=
  F.toFlexibleSameOpposite
    C.same_exactLocal C.opposite_exactLocal

/-- Promote a filtered same/opposite surface to the candidate search surface
after both full exact-local fields are supplied. -/
def toCandidate
    {F : FilteredSameOpposite}
    (C : FilteredSameOppositeCompletionFields F) :
    SameOppositeCandidate where
  same :=
    branchCandidateOfFilteredBranch F.same C.same_exactLocal
  opposite :=
    branchCandidateOfFilteredBranch F.opposite C.opposite_exactLocal

@[simp]
theorem toCandidate_same_placeNext
    {F : FilteredSameOpposite}
    (C : FilteredSameOppositeCompletionFields F) :
    C.toCandidate.same.placeNext = F.same.placeNext :=
  rfl

@[simp]
theorem toCandidate_opposite_placeNext
    {F : FilteredSameOpposite}
    (C : FilteredSameOppositeCompletionFields F) :
    C.toCandidate.opposite.placeNext = F.opposite.placeNext :=
  rfl

end FilteredSameOppositeCompletionFields

/-! ## Concrete four-target route: named blocked remainder fields -/

/-- The exact-local remainder fields for the current concrete same/opposite
four-target coordinate ansatz. -/
abbrev ConcreteFourTargetRemainingExactLocalEquations :=
  ConcreteSameOppositeRemainingExactLocalEquations

/-- Those concrete four-target exact-local remainder fields are inconsistent. -/
theorem not_concreteFourTargetRemainingExactLocalEquations :
    Not ConcreteFourTargetRemainingExactLocalEquations :=
  not_concreteSameOppositeRemainingExactLocalEquations

/-- The concrete four-target maps still form a filtered possible-row surface. -/
def concreteFourTargetFilteredSameOpposite :
    FilteredSameOpposite :=
  ExactLocalBranchSolverSurface.concreteFilteredSameOpposite

/-- The filtered concrete four-target surface cannot be completed to full
exact-local same/opposite candidate fields. -/
theorem not_concreteFourTargetFilteredCompletion :
    Not
      (FilteredSameOppositeCompletionFields
        concreteFourTargetFilteredSameOpposite) := by
  intro C
  have hsame :
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.samePlaceNext := by
    simpa [concreteFourTargetFilteredSameOpposite,
      ExactLocalBranchSolverSurface.concreteFilteredSameOpposite,
      ExactLocalBranchSolverSurface.concreteSameFilteredBranch,
      ExactLocalBranchSolverSurface.concreteSameConnector,
      ExactLocalBranchSolverSurface.FilteredBranch.placeNext] using
        C.same_exactLocal
  exact
    samePlaceNext_not_preservesExactLocalSqDistances
      hsame

/-- No unit-vector branch candidate fields can reuse the concrete same
four-target map. -/
theorem not_sameFourTargetBranchCandidateFields :
    Not
      (exists B : BranchCandidateFields,
        B.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext) := by
  rintro h
  cases h with
  | intro B hplace =>
    exact
      samePlaceNext_not_preservesExactLocalSqDistances
        (by
          simpa [BranchCandidateFields.toBranchCandidate, hplace] using
            B.toBranchCandidate.preserves_exactLocal_sqDistances)

/-- No unit-vector branch candidate fields can reuse the concrete opposite
four-target map. -/
theorem not_oppositeFourTargetBranchCandidateFields :
    Not
      (exists B : BranchCandidateFields,
        B.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) := by
  rintro h
  cases h with
  | intro B hplace =>
    exact
      oppositePlaceNext_not_preservesExactLocalSqDistances
        (by
          simpa [BranchCandidateFields.toBranchCandidate, hplace] using
            B.toBranchCandidate.preserves_exactLocal_sqDistances)

/-- A same/opposite unit-vector candidate pair cannot be exactly the blocked
concrete same/opposite four-target pair. -/
theorem not_sameOppositeCandidateFields_for_concreteFourTarget :
    Not
      (exists F : SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) := by
  rintro ⟨F, hsame, _hopposite⟩
  exact
    not_sameFourTargetBranchCandidateFields
      ⟨F.same, hsame⟩

/-! ## Complete family data and exact remaining fields -/

/-- Candidate plus all-positive algebraic period data, before metric fields
are supplied. -/
structure CandidatePeriodFields where
  candidateFields : SameOppositeCandidateFields
  periodData :
    RoleHingeCandidateSearchSurface.PeriodSearchData
      candidateFields.toCandidate

namespace CandidatePeriodFields

/-- The constructed same/opposite candidate. -/
def candidate
    (F : CandidatePeriodFields) :
    SameOppositeCandidate :=
  F.candidateFields.toCandidate

/-- The exact metric field still needed to reach the generated-chain target
route. -/
abbrev RemainingMetricFields
    (F : CandidatePeriodFields) : Type :=
  RoleHingeCandidateSearchSurface.CrossBlockMetricData
    F.periodData

/-- Generated-chain family before metric hypotheses are supplied. -/
def toGeneratedChainFamily
    (F : CandidatePeriodFields) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  F.periodData.toGeneratedChainFamily

/-- Period hypotheses already supplied by the period data. -/
theorem periods
    (F : CandidatePeriodFields) :
    F.toGeneratedChainFamily.Periods :=
  F.periodData.periods

end CandidatePeriodFields

/-- Complete non-rigid search-family data: explicit candidate fields, period
equations, and cross-block metric data. -/
structure CompleteNonRigidFamilyFields extends CandidatePeriodFields where
  metricData : toCandidatePeriodFields.RemainingMetricFields

namespace CompleteNonRigidFamilyFields

/-- Full family metric hypotheses projected from the supplied cross-block
metric fields. -/
def toFamilyMetricHypotheses
    (F : CompleteNonRigidFamilyFields) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      F.toGeneratedChainFamily :=
  F.metricData.toFamilyMetricHypotheses

/-- Exact target theorem, conditional on every field in
`CompleteNonRigidFamilyFields`. -/
theorem targetUpperConstructionFiveSixteen
    (F : CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.metricData.targetUpperConstructionFiveSixteen

end CompleteNonRigidFamilyFields

end FlexibleTransitionSearchW10
end PachToth
end ErdosProblems1066

end
