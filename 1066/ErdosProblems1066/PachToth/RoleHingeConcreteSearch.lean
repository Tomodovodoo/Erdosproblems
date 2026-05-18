import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.HingeAlgebra
import ErdosProblems1066.PachToth.RoleHingeAngleCertificates
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch
import ErdosProblems1066.PachToth.UnitVectorGeometry

set_option autoImplicit false

/-!
# Concrete role-hinged transition search

This file records a direct, non-translated role-hinge attempt.  The four
successor-connector targets are placed as unit hinge endpoints with fixed role
angles; all connector-unit obligations are therefore discharged by the role
table and unit-vector geometry.

The remaining metric condition is made algebraic: each branch must preserve
all same-block squared distances.  For the concrete four-target override below
we also prove that the current `forall source` same-block preservation
interface is too strong: no choice of the fixed role angles can satisfy it.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeConcreteSearch

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole

/-- Same-branch test angles for the four proof-used successor-connector roles. -/
def sameRoleAngle : ConnectorRole -> Real
  | .pToUpper => 0
  | .pToLower => Real.pi / 3
  | .qToUpper => 2 * Real.pi / 3
  | .qToLower => Real.pi

/-- Opposite-branch test angles, mirrored across the horizontal axis. -/
def oppositeRoleAngle : ConnectorRole -> Real
  | .pToUpper => 0
  | .pToLower => -Real.pi / 3
  | .qToUpper => -2 * Real.pi / 3
  | .qToLower => -Real.pi

/-- A concrete role-hinged next-block map: the four proof-used connector
targets are put at fixed unit-hinge endpoints, and all other labels are left
at their source locations. -/
def concreteRoleHingePlace
    (angle : ConnectorRole -> Real)
    (source : LocalVertex -> R2) : LocalVertex -> R2
  | .tri 1 1 =>
      UnitVectorGeometry.hingePoint (source T2_2) (angle .pToUpper)
  | .tri 1 2 =>
      UnitVectorGeometry.hingePoint (source T2_2) (angle .pToLower)
  | .tri 0 0 =>
      UnitVectorGeometry.hingePoint (source T4_0) (angle .qToUpper)
  | .tri 0 2 =>
      UnitVectorGeometry.hingePoint (source T4_0) (angle .qToLower)
  | v => source v

def samePlaceNext : (LocalVertex -> R2) -> LocalVertex -> R2 :=
  concreteRoleHingePlace sameRoleAngle

def oppositePlaceNext : (LocalVertex -> R2) -> LocalVertex -> R2 :=
  concreteRoleHingePlace oppositeRoleAngle

/-- The same-block preservation equations left by the concrete hinge ansatz,
written without square roots. -/
def AlgebraicSameBlockEquations
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  forall (source : LocalVertex -> R2) (u v : LocalVertex),
    HingeAlgebra.distSq (placeNext source u) (placeNext source v) =
      HingeAlgebra.distSq (source u) (source v)

/-- The exact remaining equations for the concrete same/opposite ansatz. -/
structure ConcreteSameOppositeRemainingEquations where
  same_sameBlock :
    AlgebraicSameBlockEquations samePlaceNext
  opposite_sameBlock :
    AlgebraicSameBlockEquations oppositePlaceNext

theorem root_eucDist_eq_of_distSq_eq
    {p q r s : R2}
    (h : HingeAlgebra.distSq p q = HingeAlgebra.distSq r s) :
    _root_.eucDist p q = _root_.eucDist r s := by
  simpa [_root_.eucDist, HingeAlgebra.distSq] using congrArg Real.sqrt h

theorem preservesSameBlockDistances_of_algebraic
    {placeNext : (LocalVertex -> R2) -> LocalVertex -> R2}
    (h : AlgebraicSameBlockEquations placeNext) :
    HingedTransitionInterface.PreservesSameBlockDistances placeNext := by
  intro source u v
  exact root_eucDist_eq_of_distSq_eq (h source u v)

/-- The concrete map realizes every named role directly as a hinge endpoint. -/
theorem concreteRoleHingePlace_realizes_role
    (angle : ConnectorRole -> Real) :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        concreteRoleHingePlace angle source v =
          UnitVectorGeometry.hingePoint (source u) (angle role) := by
  intro source u v role hrole
  have hconn :=
    Figure2EdgeTable.nextConnectorRole_nextConnector u v role hrole
  rcases HingeAlgebra.nextConnector_cases hconn with h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    cases role <;>
      simp [Figure2EdgeTable.nextConnectorRole, concreteRoleHingePlace,
        T, T1_1, T2_2] at hrole ⊢
  · rcases h with ⟨rfl, rfl⟩
    cases role <;>
      simp [Figure2EdgeTable.nextConnectorRole, concreteRoleHingePlace,
        T, T1_2, T2_2] at hrole ⊢
  · rcases h with ⟨rfl, rfl⟩
    cases role <;>
      simp [Figure2EdgeTable.nextConnectorRole, concreteRoleHingePlace,
        T, T0_0, T4_0] at hrole ⊢
  · rcases h with ⟨rfl, rfl⟩
    cases role <;>
      simp [Figure2EdgeTable.nextConnectorRole, concreteRoleHingePlace,
        T, T0_2, T4_0] at hrole ⊢

/-- The same-branch concrete angles are the existing equilateral role angles. -/
theorem sameRoleAngle_eq_sameEquilateralRoleAngle :
    sameRoleAngle =
      RoleHingeAngleCertificates.sameEquilateralRoleAngle := by
  funext role
  cases role <;> rfl

/-- The opposite-branch concrete angles are the existing equilateral role
angles. -/
theorem oppositeRoleAngle_eq_oppositeEquilateralRoleAngle :
    oppositeRoleAngle =
      RoleHingeAngleCertificates.oppositeEquilateralRoleAngle := by
  funext role
  cases role <;> rfl

/-- The same-branch concrete angles satisfy the two port-pair angle equations. -/
theorem sameRoleAngle_angleEquations :
    RoleHingeAngleCertificates.RoleHingeAngleEquations sameRoleAngle :=
  RoleHingeAngleCertificates.angleEquations_of_eq_sameEquilateralRoleAngle
    sameRoleAngle_eq_sameEquilateralRoleAngle

/-- The opposite-branch concrete angles satisfy the two port-pair angle
equations. -/
theorem oppositeRoleAngle_angleEquations :
    RoleHingeAngleCertificates.RoleHingeAngleEquations oppositeRoleAngle :=
  RoleHingeAngleCertificates.angleEquations_of_eq_oppositeEquilateralRoleAngle
    oppositeRoleAngle_eq_oppositeEquilateralRoleAngle

/-- The same-branch concrete map has both same-source connector-port pair unit
edges. -/
theorem same_port_pair_unit_edges :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (samePlaceNext source T1_1) (samePlaceNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (samePlaceNext source T0_0) (samePlaceNext source T0_2) = 1) := by
  exact
    RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
      samePlaceNext sameRoleAngle
      (concreteRoleHingePlace_realizes_role sameRoleAngle)
      sameRoleAngle_angleEquations

/-- The opposite-branch concrete map has both same-source connector-port pair
unit edges. -/
theorem opposite_port_pair_unit_edges :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (oppositePlaceNext source T1_1)
          (oppositePlaceNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (oppositePlaceNext source T0_0)
          (oppositePlaceNext source T0_2) = 1) := by
  exact
    RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
      oppositePlaceNext oppositeRoleAngle
      (concreteRoleHingePlace_realizes_role oppositeRoleAngle)
      oppositeRoleAngle_angleEquations

/-- Same/opposite concrete maps have all four same-source connector-port pair
unit-edge facts. -/
theorem sameOpposite_port_pair_unit_edges :
    And
      (And
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (samePlaceNext source T1_1) (samePlaceNext source T1_2) = 1)
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (samePlaceNext source T0_0) (samePlaceNext source T0_2) = 1))
      (And
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (oppositePlaceNext source T1_1)
            (oppositePlaceNext source T1_2) = 1)
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (oppositePlaceNext source T0_0)
            (oppositePlaceNext source T0_2) = 1)) := by
  exact And.intro same_port_pair_unit_edges opposite_port_pair_unit_edges

/-- Any concrete role-hinge map realizes every successor connector as a unit
edge, independently of the same-block field. -/
theorem concreteRoleHingePlace_connector_unit_edges
    (angle : ConnectorRole -> Real) :
    HingedTransitionInterface.ConnectorUnitEdges
      (concreteRoleHingePlace angle) := by
  intro source u v hconn
  rcases Figure2EdgeTable.nextConnector_has_role u v hconn with ⟨role, hrole⟩
  exact
    RoleHingeConnectorAlgebra.role_port_unit_of_realizes
      (concreteRoleHingePlace angle) angle
      (concreteRoleHingePlace_realizes_role angle)
      source u v role hrole

/-- One concrete branch, reduced to the algebraic same-block equations. -/
def concreteRoleHingeTransitionFacts
    (angle : ConnectorRole -> Real)
    (hSameBlock :
      AlgebraicSameBlockEquations (concreteRoleHingePlace angle)) :
    RoleHingeTransitionSearch.RoleHingeTransitionFacts where
  placeNext := concreteRoleHingePlace angle
  roleAngle := angle
  realizes_role := concreteRoleHingePlace_realizes_role angle
  preserves_same_block_distances :=
    preservesSameBlockDistances_of_algebraic hSameBlock

def sameRoleHingeTransitionFacts
    (hSameBlock : AlgebraicSameBlockEquations samePlaceNext) :
    RoleHingeTransitionSearch.RoleHingeTransitionFacts :=
  concreteRoleHingeTransitionFacts sameRoleAngle hSameBlock

def oppositeRoleHingeTransitionFacts
    (hSameBlock : AlgebraicSameBlockEquations oppositePlaceNext) :
    RoleHingeTransitionSearch.RoleHingeTransitionFacts :=
  concreteRoleHingeTransitionFacts oppositeRoleAngle hSameBlock

/-- If the two explicit squared-distance equation families are supplied, the
search-facing same/opposite role-hinged transition facts follow. -/
def concreteSameOppositeRoleHingeTransitionFacts
    (R : ConcreteSameOppositeRemainingEquations) :
    RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts where
  same := sameRoleHingeTransitionFacts R.same_sameBlock
  opposite := oppositeRoleHingeTransitionFacts R.opposite_sameBlock

/-- The same conditional data also projects to the base transition
realization package. -/
def concreteBaseSameOppositeTransitionRealization
    (R : ConcreteSameOppositeRemainingEquations) :
    BaseTransitionRealization.BaseSameOppositeTransitionRealization where
  same :=
    (sameRoleHingeTransitionFacts R.same_sameBlock).toRoleHingeTransition
  opposite :=
    (oppositeRoleHingeTransitionFacts R.opposite_sameBlock).toRoleHingeTransition

@[simp]
theorem concreteSameOppositeRoleHingeTransitionFacts_same_placeNext
    (R : ConcreteSameOppositeRemainingEquations) :
    (concreteSameOppositeRoleHingeTransitionFacts R).same.placeNext =
      samePlaceNext :=
  rfl

@[simp]
theorem concreteSameOppositeRoleHingeTransitionFacts_opposite_placeNext
    (R : ConcreteSameOppositeRemainingEquations) :
    (concreteSameOppositeRoleHingeTransitionFacts R).opposite.placeNext =
      oppositePlaceNext :=
  rfl

@[simp]
theorem concreteBaseSameOppositeTransitionRealization_same_placeNext
    (R : ConcreteSameOppositeRemainingEquations) :
    (concreteBaseSameOppositeTransitionRealization R).same.placeNext =
      samePlaceNext :=
  rfl

@[simp]
theorem concreteBaseSameOppositeTransitionRealization_opposite_placeNext
    (R : ConcreteSameOppositeRemainingEquations) :
    (concreteBaseSameOppositeTransitionRealization R).opposite.placeNext =
      oppositePlaceNext :=
  rfl

theorem same_connector_unit_edges :
    HingedTransitionInterface.ConnectorUnitEdges samePlaceNext :=
  concreteRoleHingePlace_connector_unit_edges sameRoleAngle

theorem opposite_connector_unit_edges :
    HingedTransitionInterface.ConnectorUnitEdges oppositePlaceNext :=
  concreteRoleHingePlace_connector_unit_edges oppositeRoleAngle

/-- The unconditional connector-only transition obligations for the concrete
same/opposite role-hinge maps. -/
def concreteSameOppositeTransitionObligations :
    Figure2Certificate.SameOppositeTransitionObligations where
  samePlaceNext := samePlaceNext
  oppositePlaceNext := oppositePlaceNext
  same_connector_unit_edges := same_connector_unit_edges
  opposite_connector_unit_edges := opposite_connector_unit_edges

@[simp]
theorem concreteSameOppositeTransitionObligations_samePlaceNext :
    concreteSameOppositeTransitionObligations.samePlaceNext =
      samePlaceNext :=
  rfl

@[simp]
theorem concreteSameOppositeTransitionObligations_oppositePlaceNext :
    concreteSameOppositeTransitionObligations.oppositePlaceNext =
      oppositePlaceNext :=
  rfl

def collapsedSource : LocalVertex -> R2 :=
  fun _ => (0, 0)

def separatedSource : LocalVertex -> R2
  | .tri 1 2 => (2, 0)
  | _ => (0, 0)

theorem eucDist_origin_two_zero :
    _root_.eucDist ((0, 0) : R2) ((2, 0) : R2) = 2 := by
  norm_num [_root_.eucDist]

/-- The concrete four-target override cannot satisfy the current
`forall source` preservation interface for any fixed role-angle assignment.

The obstruction uses only the pair `T1_1, T1_2`: two sources with the same
hinge center but different original distance would force the same produced
distance to be both `0` and `2`. -/
theorem not_preservesSameBlockDistances_concreteRoleHingePlace
    (angle : ConnectorRole -> Real) :
    Not
      (HingedTransitionInterface.PreservesSameBlockDistances
        (concreteRoleHingePlace angle)) := by
  intro hpres
  let produced : R2 :=
    UnitVectorGeometry.hingePoint ((0, 0) : R2) (angle .pToUpper)
  let produced' : R2 :=
    UnitVectorGeometry.hingePoint ((0, 0) : R2) (angle .pToLower)
  have hcollapsed := hpres collapsedSource T1_1 T1_2
  have hseparated := hpres separatedSource T1_1 T1_2
  have hzero : _root_.eucDist produced produced' = 0 := by
    simpa [produced, produced', collapsedSource, concreteRoleHingePlace,
      T, T1_1, T1_2, T2_2] using hcollapsed
  have htwo : _root_.eucDist produced produced' = 2 := by
    simpa [produced, produced', separatedSource, concreteRoleHingePlace,
      T, T1_1, T1_2, T2_2, eucDist_origin_two_zero] using hseparated
  linarith

theorem not_algebraicSameBlockEquations_concreteRoleHingePlace
    (angle : ConnectorRole -> Real) :
    Not (AlgebraicSameBlockEquations (concreteRoleHingePlace angle)) := by
  intro h
  exact
    not_preservesSameBlockDistances_concreteRoleHingePlace angle
      (preservesSameBlockDistances_of_algebraic h)

/-- No strong search-facing role-hinge transition fact can use this concrete
place map, because the strong same-block field would require arbitrary-source
distance preservation. -/
theorem not_roleHingeTransitionFacts_concreteRoleHingePlace
    (angle : ConnectorRole -> Real) :
    Not
      (exists F : RoleHingeTransitionSearch.RoleHingeTransitionFacts,
        F.placeNext = concreteRoleHingePlace angle) := by
  rintro ⟨F, hplace⟩
  exact
    not_preservesSameBlockDistances_concreteRoleHingePlace angle
      (by simpa [hplace] using F.preserves_same_block_distances)

/-- Consequently the concrete same/opposite maps cannot inhabit the old strong
same/opposite role-hinge search interface. -/
theorem not_sameOppositeRoleHingeTransitionFacts_for_concrete_places :
    Not
      (exists F :
        RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts,
        F.same.placeNext = samePlaceNext ∧
          F.opposite.placeNext = oppositePlaceNext) := by
  rintro ⟨F, hsame, _hopposite⟩
  exact
    not_roleHingeTransitionFacts_concreteRoleHingePlace sameRoleAngle
      ⟨F.same, by simpa [samePlaceNext] using hsame⟩

theorem no_concreteSameOppositeRemainingEquations :
    Not ConcreteSameOppositeRemainingEquations := by
  intro R
  exact
    not_algebraicSameBlockEquations_concreteRoleHingePlace sameRoleAngle
      R.same_sameBlock

end

end RoleHingeConcreteSearch
end PachToth
end ErdosProblems1066
