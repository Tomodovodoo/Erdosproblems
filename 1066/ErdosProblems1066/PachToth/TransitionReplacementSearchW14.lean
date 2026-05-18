import ErdosProblems1066.PachToth.TransitionAlternativeW13
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.UnitVectorParameterizationSearch

set_option autoImplicit false

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace TransitionReplacementSearchW14

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real
abbrev UVBranchParameters :=
  UnitVectorParameterizationSearch.UnitVectorBranchParameters
abbrev UVNonAngleRows :=
  UnitVectorParameterizationSearch.UnitVectorBranchParameters.NonAngleExactLocalRowHypotheses
abbrev UVSameOppositeParameters :=
  UnitVectorParameterizationSearch.UnitVectorBranchParameters.SameOppositeParameters
abbrev UVSameOppositeHypotheses :=
  UnitVectorParameterizationSearch.UnitVectorBranchParameters.SameOppositeAlgebraicHypotheses
abbrev BranchCandidate :=
  RoleHingeCandidateSearchSurface.BranchCandidate
abbrev SameOppositeCandidate :=
  RoleHingeCandidateSearchSurface.SameOppositeCandidate

def branchCandidateOfUnitVector
    (P : UVBranchParameters)
    (A : RoleHingeAngleCertificates.RoleHingeAngleEquations P.roleAngle)
    (H : UVNonAngleRows P) :
    BranchCandidate where
  placeNext := P.placeNext
  roleAngle := P.roleAngle
  realizes_role := P.realizes_role
  preserves_exactLocal_sqDistances :=
    UnitVectorParameterizationSearch.UnitVectorBranchParameters.preservesExactLocalSqDistances_of_angleEquations_and_nonAngleRows
      P A H

def sameOppositeCandidateOfUnitVector
    (P : UVSameOppositeParameters)
    (H : UVSameOppositeHypotheses P) :
    SameOppositeCandidate where
  same :=
    branchCandidateOfUnitVector P.same H.same_angle H.same_rows
  opposite :=
    branchCandidateOfUnitVector
      P.opposite H.opposite_angle H.opposite_rows

theorem sameOppositeCandidateOfUnitVector_same_placeNext
    (P : UVSameOppositeParameters)
    (H : UVSameOppositeHypotheses P) :
    (sameOppositeCandidateOfUnitVector P H).same.placeNext =
      P.same.placeNext :=
  rfl

theorem sameOppositeCandidateOfUnitVector_opposite_placeNext
    (P : UVSameOppositeParameters)
    (H : UVSameOppositeHypotheses P) :
    (sameOppositeCandidateOfUnitVector P H).opposite.placeNext =
      P.opposite.placeNext :=
  rfl

theorem unitVectorReplacement_orbitSqDistances
    (P : UVSameOppositeParameters)
    (H : UVSameOppositeHypotheses P)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      (sameOppositeCandidateOfUnitVector P H).toFigure2TransitionObligations
      hk BaseTransitionRealization.exactBase orientation :=
  (sameOppositeCandidateOfUnitVector P H).orbitSqDistances
    hk orientation

theorem unitVectorReplacement_generatedSameBlockIsometry
    (P : UVSameOppositeParameters)
    (H : UVSameOppositeHypotheses P)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      (sameOppositeCandidateOfUnitVector P H).toFigure2TransitionObligations
      hk BaseTransitionRealization.exactBase orientation :=
  (sameOppositeCandidateOfUnitVector P H).generatedSameBlockIsometry
    hk orientation

theorem not_roleAnglePortPair_T1_1_r :
    Not
      (RoleHingeAngleCertificates.IsRoleAnglePortPair
        T1_1 LocalVertex.r) := by
  decide

theorem not_unitVectorNonAngleRows_with_concreteSamePlace
    (P : UVBranchParameters)
    (hplace : P.placeNext = RoleHingeConcreteSearch.samePlaceNext) :
    Not (UVNonAngleRows P) := by
  intro H
  have hrow :=
    H.row_sqDist ExactLocalGeometry.localPoint
      RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
      T1_1 LocalVertex.r not_roleAnglePortPair_T1_1_r
  exact
    ExactLocalTransitionObligationMatrix.samePlaceNext_exactBase_T1_1_r_forces_contradiction
      (by simpa [hplace] using hrow)

theorem not_unitVectorNonAngleRows_with_concreteOppositePlace
    (P : UVBranchParameters)
    (hplace : P.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) :
    Not (UVNonAngleRows P) := by
  intro H
  have hrow :=
    H.row_sqDist ExactLocalGeometry.localPoint
      RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
      T1_1 LocalVertex.r not_roleAnglePortPair_T1_1_r
  exact
    ExactLocalTransitionObligationMatrix.oppositePlaceNext_exactBase_T1_1_r_forces_contradiction
      (by simpa [hplace] using hrow)

theorem not_unitVectorSameOppositeHypotheses_with_concreteSamePlace
    (P : UVSameOppositeParameters)
    (hplace : P.same.placeNext = RoleHingeConcreteSearch.samePlaceNext) :
    Not (UVSameOppositeHypotheses P) := by
  intro H
  exact
    not_unitVectorNonAngleRows_with_concreteSamePlace
      P.same hplace H.same_rows

theorem not_unitVectorSameOppositeHypotheses_with_concreteOppositePlace
    (P : UVSameOppositeParameters)
    (hplace :
      P.opposite.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) :
    Not (UVSameOppositeHypotheses P) := by
  intro H
  exact
    not_unitVectorNonAngleRows_with_concreteOppositePlace
      P.opposite hplace H.opposite_rows

def concreteSameUnitVectorParameters : UVBranchParameters where
  placeNext := RoleHingeConcreteSearch.samePlaceNext
  roleAngle := RoleHingeConcreteSearch.sameRoleAngle
  unit_vector_formula := by
    intro source u v role hrole
    simpa [RoleHingeConcreteSearch.samePlaceNext,
      UnitVectorGeometry.hingePoint] using
      RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
        RoleHingeConcreteSearch.sameRoleAngle source u v role hrole

def concreteOppositeUnitVectorParameters : UVBranchParameters where
  placeNext := RoleHingeConcreteSearch.oppositePlaceNext
  roleAngle := RoleHingeConcreteSearch.oppositeRoleAngle
  unit_vector_formula := by
    intro source u v role hrole
    simpa [RoleHingeConcreteSearch.oppositePlaceNext,
      UnitVectorGeometry.hingePoint] using
      RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
        RoleHingeConcreteSearch.oppositeRoleAngle source u v role hrole

def concreteSameOppositeUnitVectorParameters :
    UVSameOppositeParameters where
  same := concreteSameUnitVectorParameters
  opposite := concreteOppositeUnitVectorParameters

theorem not_concreteSameUnitVectorNonAngleRows :
    Not (UVNonAngleRows concreteSameUnitVectorParameters) :=
  not_unitVectorNonAngleRows_with_concreteSamePlace
    concreteSameUnitVectorParameters rfl

theorem not_concreteOppositeUnitVectorNonAngleRows :
    Not (UVNonAngleRows concreteOppositeUnitVectorParameters) :=
  not_unitVectorNonAngleRows_with_concreteOppositePlace
    concreteOppositeUnitVectorParameters rfl

theorem not_concreteSameOppositeUnitVectorHypotheses :
    Not
      (UVSameOppositeHypotheses
        concreteSameOppositeUnitVectorParameters) :=
  not_unitVectorSameOppositeHypotheses_with_concreteSamePlace
    concreteSameOppositeUnitVectorParameters rfl

end TransitionReplacementSearchW14
end PachToth
end ErdosProblems1066

end
