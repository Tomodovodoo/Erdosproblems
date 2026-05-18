import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.HingeAlgebra
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

theorem same_connector_unit_edges
    (R : ConcreteSameOppositeRemainingEquations) :
    HingedTransitionInterface.ConnectorUnitEdges samePlaceNext := by
  simpa using
    (concreteSameOppositeRoleHingeTransitionFacts R).same_connector_unit_edges

theorem opposite_connector_unit_edges
    (R : ConcreteSameOppositeRemainingEquations) :
    HingedTransitionInterface.ConnectorUnitEdges oppositePlaceNext := by
  simpa using
    (concreteSameOppositeRoleHingeTransitionFacts R).opposite_connector_unit_edges

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
