import ErdosProblems1066.PachToth.RoleHingeCandidateSearchSurface
import ErdosProblems1066.PachToth.RoleHingeExactLocalFinite

set_option autoImplicit false

/-!
# Flexible branch coordinate search surface

This file instantiates the concrete same/opposite role-angle coordinate data
at the flexible connector level, proves the exact-local rows that are forced
by the current four-target coordinate ansatz, and names the remaining
exact-local row equations needed to promote the coordinate data to the
`RoleHingeCandidateSearchSurface` branch interface.

The current same-branch ansatz is also sharply constrained: the row
`(T1_1, r)` on the exact base already contradicts the exact-local table, so
the remaining-equation package is intentionally not inhabited here.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleBranchCoordinateSearch

open FiniteGraph
open FiniteGraph.LocalVertex
open Figure2EdgeTable

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole

/-! ## Coordinate and role-angle data -/

/-- One branch of explicit coordinate data, without the exact-local
same-block field. -/
structure BranchCoordinateData where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)
  angleEquations :
    RoleHingeAngleCertificates.RoleHingeAngleEquations roleAngle

namespace BranchCoordinateData

/-- Connector-only projection to the flexible exact-local transition layer. -/
def toFlexibleConnectorData
    (B : BranchCoordinateData) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.realizes_role

@[simp]
theorem toFlexibleConnectorData_placeNext
    (B : BranchCoordinateData) :
    B.toFlexibleConnectorData.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toFlexibleConnectorData_roleAngle
    (B : BranchCoordinateData) :
    B.toFlexibleConnectorData.roleAngle = B.roleAngle :=
  rfl

/-- Connector-level role facts projected from raw coordinate data. -/
def toConnectorFacts
    (B : BranchCoordinateData) :
    RoleHingeCandidateSearchSurface.ConnectorTransitionFacts :=
  B.toFlexibleConnectorData.toConnectorTransitionFacts

@[simp]
theorem toConnectorFacts_placeNext
    (B : BranchCoordinateData) :
    B.toConnectorFacts.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toConnectorFacts_roleAngle
    (B : BranchCoordinateData) :
    B.toConnectorFacts.roleAngle = B.roleAngle :=
  rfl

/-- Connector-unit edges are a theorem of the role table and the hinge
formula, not an extra same-block assumption. -/
theorem connector_unit_edges
    (B : BranchCoordinateData) :
    HingedTransitionInterface.ConnectorUnitEdges B.placeNext :=
  B.toFlexibleConnectorData.connector_unit_edges

end BranchCoordinateData

/-- Concrete same-branch coordinate/role-angle data. -/
def sameBranchCoordinates : BranchCoordinateData where
  placeNext := RoleHingeConcreteSearch.samePlaceNext
  roleAngle := RoleHingeConcreteSearch.sameRoleAngle
  realizes_role :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.sameRoleAngle
  angleEquations := RoleHingeConcreteSearch.sameRoleAngle_angleEquations

/-- Concrete opposite-branch coordinate/role-angle data. -/
def oppositeBranchCoordinates : BranchCoordinateData where
  placeNext := RoleHingeConcreteSearch.oppositePlaceNext
  roleAngle := RoleHingeConcreteSearch.oppositeRoleAngle
  realizes_role :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.oppositeRoleAngle
  angleEquations := RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations

@[simp]
theorem sameBranchCoordinates_placeNext :
    sameBranchCoordinates.placeNext =
      RoleHingeConcreteSearch.samePlaceNext :=
  rfl

@[simp]
theorem oppositeBranchCoordinates_placeNext :
    oppositeBranchCoordinates.placeNext =
      RoleHingeConcreteSearch.oppositePlaceNext :=
  rfl

/-- Same/opposite coordinate data before exact-local same-block promotion. -/
structure SameOppositeCoordinateData where
  same : BranchCoordinateData
  opposite : BranchCoordinateData

namespace SameOppositeCoordinateData

/-- Connector-only same/opposite transition facts. -/
def toConnectorFacts
    (D : SameOppositeCoordinateData) :
    RoleHingeCandidateSearchSurface.SameOppositeConnectorTransitionFacts where
  same := D.same.toConnectorFacts
  opposite := D.opposite.toConnectorFacts

/-- Figure 2 connector obligations projected from the coordinate data. -/
def toFigure2TransitionObligations
    (D : SameOppositeCoordinateData) :
    RoleHingeCandidateSearchSurface.TransitionObligations :=
  D.toConnectorFacts.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (D : SameOppositeCoordinateData) :
    D.toFigure2TransitionObligations.samePlaceNext =
      D.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (D : SameOppositeCoordinateData) :
    D.toFigure2TransitionObligations.oppositePlaceNext =
      D.opposite.placeNext :=
  rfl

theorem same_connector_unit_edges
    (D : SameOppositeCoordinateData) :
    HingedTransitionInterface.ConnectorUnitEdges D.same.placeNext :=
  D.same.connector_unit_edges

theorem opposite_connector_unit_edges
    (D : SameOppositeCoordinateData) :
    HingedTransitionInterface.ConnectorUnitEdges D.opposite.placeNext :=
  D.opposite.connector_unit_edges

end SameOppositeCoordinateData

/-- The concrete same/opposite coordinate data. -/
def concreteSameOppositeCoordinates : SameOppositeCoordinateData where
  same := sameBranchCoordinates
  opposite := oppositeBranchCoordinates

/-! ## Rows already forced by the concrete ansatz -/

/-- Exact-local rows already discharged by diagonal triviality, the two
role-angle port pairs, or labels left unchanged by the four-target ansatz. -/
def DerivableExactLocalRow (u v : LocalVertex) : Prop :=
  u = v \/
    RoleHingeAngleCertificates.IsRoleAnglePortPair u v \/
      (Not (RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget u) /\
        Not (RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget v))

/-- The remaining exact-local equations for a branch are precisely the rows
not covered by `DerivableExactLocalRow`. -/
def ExactLocalRemainingRows
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (DerivableExactLocalRow u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (placeNext source u) (placeNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- Same-branch rows discharged without any remaining-row assumption. -/
theorem same_sqDist_of_derivable_row
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : DerivableExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hrow with hdiag | hrow
  · subst v
    exact
      RoleHingeExactLocalFinite.concreteRoleHingePlace_self_sqDist
        RoleHingeConcreteSearch.sameRoleAngle source u
  rcases hrow with hpair | hfree
  · rcases hpair with h | h | h | h
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.p_ports_exactLocalSqDist_of_angleEquations_realizes
          RoleHingeConcreteSearch.samePlaceNext
          RoleHingeConcreteSearch.sameRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.sameRoleAngle)
          RoleHingeConcreteSearch.sameRoleAngle_angleEquations source
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.p_ports_exactLocalSqDist_symm_of_angleEquations_realizes
          RoleHingeConcreteSearch.samePlaceNext
          RoleHingeConcreteSearch.sameRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.sameRoleAngle)
          RoleHingeConcreteSearch.sameRoleAngle_angleEquations source
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.q_ports_exactLocalSqDist_of_angleEquations_realizes
          RoleHingeConcreteSearch.samePlaceNext
          RoleHingeConcreteSearch.sameRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.sameRoleAngle)
          RoleHingeConcreteSearch.sameRoleAngle_angleEquations source
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.q_ports_exactLocalSqDist_symm_of_angleEquations_realizes
          RoleHingeConcreteSearch.samePlaceNext
          RoleHingeConcreteSearch.sameRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.sameRoleAngle)
          RoleHingeConcreteSearch.sameRoleAngle_angleEquations source
  · exact
      RoleHingeExactLocalFinite.samePlaceNext_unmoved_sqDist
        hsource hfree.left hfree.right

/-- Opposite-branch rows discharged without any remaining-row assumption. -/
theorem opposite_sqDist_of_derivable_row
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : DerivableExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hrow with hdiag | hrow
  · subst v
    exact
      RoleHingeExactLocalFinite.concreteRoleHingePlace_self_sqDist
        RoleHingeConcreteSearch.oppositeRoleAngle source u
  rcases hrow with hpair | hfree
  · rcases hpair with h | h | h | h
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.p_ports_exactLocalSqDist_of_angleEquations_realizes
          RoleHingeConcreteSearch.oppositePlaceNext
          RoleHingeConcreteSearch.oppositeRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.oppositeRoleAngle)
          RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations source
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.p_ports_exactLocalSqDist_symm_of_angleEquations_realizes
          RoleHingeConcreteSearch.oppositePlaceNext
          RoleHingeConcreteSearch.oppositeRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.oppositeRoleAngle)
          RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations source
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.q_ports_exactLocalSqDist_of_angleEquations_realizes
          RoleHingeConcreteSearch.oppositePlaceNext
          RoleHingeConcreteSearch.oppositeRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.oppositeRoleAngle)
          RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations source
    · cases h.left
      cases h.right
      exact
        RoleHingeAngleCertificates.q_ports_exactLocalSqDist_symm_of_angleEquations_realizes
          RoleHingeConcreteSearch.oppositePlaceNext
          RoleHingeConcreteSearch.oppositeRoleAngle
          (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
            RoleHingeConcreteSearch.oppositeRoleAngle)
          RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations source
  · exact
      RoleHingeExactLocalFinite.oppositePlaceNext_unmoved_sqDist
        hsource hfree.left hfree.right

/-! ## Conditional promotion to branch candidates -/

theorem same_preservesExactLocalSqDistances_of_remaining_rows
    (hremaining :
      ExactLocalRemainingRows RoleHingeConcreteSearch.samePlaceNext) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      RoleHingeConcreteSearch.samePlaceNext := by
  intro source hsource u v
  by_cases hrow : DerivableExactLocalRow u v
  · exact same_sqDist_of_derivable_row hsource hrow
  · exact hremaining source hsource u v hrow

theorem opposite_preservesExactLocalSqDistances_of_remaining_rows
    (hremaining :
      ExactLocalRemainingRows RoleHingeConcreteSearch.oppositePlaceNext) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      RoleHingeConcreteSearch.oppositePlaceNext := by
  intro source hsource u v
  by_cases hrow : DerivableExactLocalRow u v
  · exact opposite_sqDist_of_derivable_row hsource hrow
  · exact hremaining source hsource u v hrow

/-- The exact remaining equations for the concrete same/opposite coordinate
ansatz.  These are the only fields needed to promote the connector-level
coordinate data to the candidate interface. -/
structure ConcreteSameOppositeRemainingExactLocalEquations where
  same_remaining :
    ExactLocalRemainingRows RoleHingeConcreteSearch.samePlaceNext
  opposite_remaining :
    ExactLocalRemainingRows RoleHingeConcreteSearch.oppositePlaceNext

/-- Conditional same-branch candidate from the named remaining row equations. -/
def sameBranchCandidateOfRemainingRows
    (hremaining :
      ExactLocalRemainingRows RoleHingeConcreteSearch.samePlaceNext) :
    RoleHingeCandidateSearchSurface.BranchCandidate where
  placeNext := RoleHingeConcreteSearch.samePlaceNext
  roleAngle := RoleHingeConcreteSearch.sameRoleAngle
  realizes_role :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.sameRoleAngle
  preserves_exactLocal_sqDistances :=
    same_preservesExactLocalSqDistances_of_remaining_rows hremaining

/-- Conditional opposite-branch candidate from the named remaining row
equations. -/
def oppositeBranchCandidateOfRemainingRows
    (hremaining :
      ExactLocalRemainingRows RoleHingeConcreteSearch.oppositePlaceNext) :
    RoleHingeCandidateSearchSurface.BranchCandidate where
  placeNext := RoleHingeConcreteSearch.oppositePlaceNext
  roleAngle := RoleHingeConcreteSearch.oppositeRoleAngle
  realizes_role :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.oppositeRoleAngle
  preserves_exactLocal_sqDistances :=
    opposite_preservesExactLocalSqDistances_of_remaining_rows hremaining

/-- Conditional same/opposite candidate from the exact remaining equations. -/
def sameOppositeCandidateOfRemainingRows
    (R : ConcreteSameOppositeRemainingExactLocalEquations) :
    RoleHingeCandidateSearchSurface.SameOppositeCandidate where
  same := sameBranchCandidateOfRemainingRows R.same_remaining
  opposite := oppositeBranchCandidateOfRemainingRows R.opposite_remaining

@[simp]
theorem sameOppositeCandidateOfRemainingRows_same_placeNext
    (R : ConcreteSameOppositeRemainingExactLocalEquations) :
    (sameOppositeCandidateOfRemainingRows R).same.placeNext =
      RoleHingeConcreteSearch.samePlaceNext :=
  rfl

@[simp]
theorem sameOppositeCandidateOfRemainingRows_opposite_placeNext
    (R : ConcreteSameOppositeRemainingExactLocalEquations) :
    (sameOppositeCandidateOfRemainingRows R).opposite.placeNext =
      RoleHingeConcreteSearch.oppositePlaceNext :=
  rfl

/-! ## Sharp obstruction for the current same-branch ansatz -/

theorem not_derivable_T1_1_r :
    Not (DerivableExactLocalRow T1_1 LocalVertex.r) := by
  intro hrow
  rcases hrow with hdiag | hrow
  · cases hdiag
  rcases hrow with hpair | hfree
  · exact RoleHingeExactLocalFinite.not_isRoleAnglePortPair_T1_1_r hpair
  · exact hfree.left (Or.inl rfl)

theorem not_same_exactLocal_remaining_rows :
    Not (ExactLocalRemainingRows RoleHingeConcreteSearch.samePlaceNext) := by
  intro hremaining
  have hrow :=
    hremaining ExactLocalGeometry.localPoint
      RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
      T1_1 LocalVertex.r not_derivable_T1_1_r
  exact
    RoleHingeExactLocalFinite.samePlaceNext_exactBase_T1_1_r_sqDist_ne_exactLocal
      hrow

theorem not_concreteSameOppositeRemainingExactLocalEquations :
    Not ConcreteSameOppositeRemainingExactLocalEquations := by
  intro R
  exact not_same_exactLocal_remaining_rows R.same_remaining

theorem not_sameBranchCandidate_for_current_coordinates :
    Not
      (exists T : RoleHingeCandidateSearchSurface.BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.samePlaceNext) := by
  rintro ⟨T, hplace⟩
  have hrow :=
    T.preserves_exactLocal_sqDistances ExactLocalGeometry.localPoint
      RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
      T1_1 LocalVertex.r
  exact
    RoleHingeExactLocalFinite.samePlaceNext_exactBase_T1_1_r_sqDist_ne_exactLocal
      (by simpa [hplace] using hrow)

end FlexibleBranchCoordinateSearch
end PachToth
end ErdosProblems1066

end
