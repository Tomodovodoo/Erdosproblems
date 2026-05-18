import ErdosProblems1066.PachToth.ExactLocalTransitionObligationMatrix
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition

set_option autoImplicit false

/-!
# Exact-local branch solver surface

This module packages the exact-local row filter from
`ExactLocalTransitionObligationMatrix` as a small solver-facing transition
surface.

The concrete same/opposite role-hinge maps satisfy every row in
`IsPossibleExactLocalRow`, but the blocked row `T1_1,r` is a genuine exact-base
contradiction.  The filtered interface below lets search code consume the
possible-row facts without pretending that the concrete four-target maps
preserve the full exact-local table.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalBranchSolverSurface

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev PossibleRow :=
  ExactLocalTransitionObligationMatrix.IsPossibleExactLocalRow
abbrev ConnectorUnitRoleData :=
  FlexibleExactLocalTransition.ConnectorUnitRoleData
abbrev ConnectorTransitionFacts :=
  RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts
abbrev SameOppositeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations

/-! ## Filtered exact-local row obligations -/

/-- A branch preserves the exact-local squared-distance table only on the rows
selected by `row`. -/
def PreservesExactLocalRows
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (row : LocalVertex -> LocalVertex -> Prop) : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        row u v ->
          RoleHingeSameBlockAlgebra.sqDist
              (placeNext source u) (placeNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- The concrete finite matrix of rows that a solver may request from the
current exact-local branch surface. -/
def PreservesPossibleExactLocalRows
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  PreservesExactLocalRows placeNext PossibleRow

/-- Full exact-local preservation implies the filtered possible-row surface. -/
theorem preservesPossibleRows_of_preservesExactLocalSqDistances
    {placeNext : (LocalVertex -> R2) -> LocalVertex -> R2}
    (hpres :
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances placeNext) :
    PreservesPossibleExactLocalRows placeNext := by
  intro source hsource u v _hrow
  exact hpres source hsource u v

/-! ## Branch packages -/

/-- Connector role data plus filtered exact-local row preservation. -/
structure FilteredBranch where
  connector : ConnectorUnitRoleData
  possibleRows : PreservesPossibleExactLocalRows connector.placeNext

namespace FilteredBranch

def placeNext
    (B : FilteredBranch) :
    (LocalVertex -> R2) -> LocalVertex -> R2 :=
  B.connector.placeNext

def roleAngle
    (B : FilteredBranch) :
    ConnectorRole -> Real :=
  B.connector.roleAngle

@[simp]
theorem placeNext_eq
    (B : FilteredBranch) :
    B.placeNext = B.connector.placeNext :=
  rfl

@[simp]
theorem roleAngle_eq
    (B : FilteredBranch) :
    B.roleAngle = B.connector.roleAngle :=
  rfl

/-- Forget the filtered exact-local rows and retain connector transition facts. -/
def toConnectorFacts
    (B : FilteredBranch) :
    ConnectorTransitionFacts :=
  B.connector.toConnectorTransitionFacts

@[simp]
theorem toConnectorFacts_placeNext
    (B : FilteredBranch) :
    B.toConnectorFacts.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toConnectorFacts_roleAngle
    (B : FilteredBranch) :
    B.toConnectorFacts.roleAngle = B.roleAngle :=
  rfl

/-- Connector-unit edges are available from the connector role table alone. -/
theorem connector_unit_edges
    (B : FilteredBranch) :
    HingedTransitionInterface.ConnectorUnitEdges B.placeNext :=
  B.connector.connector_unit_edges

/-- Row-level access to the filtered exact-local obligation. -/
theorem possibleRow_sqDist
    (B : FilteredBranch)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : PossibleRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (B.placeNext source u) (B.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  B.possibleRows source hsource u v hrow

/-- A completed full exact-local branch can be consumed as a filtered branch. -/
def ofFlexibleBranch
    (B : FlexibleExactLocalTransition.Branch) :
    FilteredBranch where
  connector := B.connector
  possibleRows :=
    preservesPossibleRows_of_preservesExactLocalSqDistances
      B.preserves_exact_local_sq_distances

/-- If a filtered branch is later completed on all exact-local rows, it
projects to the existing flexible transition interface. -/
def toFlexibleBranch
    (B : FilteredBranch)
    (hall :
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances B.placeNext) :
    FlexibleExactLocalTransition.Branch where
  connector := B.connector
  exactLocal :=
    { preserves_exact_local_sq_distances := hall }

end FilteredBranch

/-- Same/opposite connector branches with filtered exact-local row facts. -/
structure FilteredSameOpposite where
  same : FilteredBranch
  opposite : FilteredBranch

namespace FilteredSameOpposite

/-- Connector-only same/opposite transition facts. -/
def toConnectorFacts
    (F : FilteredSameOpposite) :
    SameOppositeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.sameOppositeRoleHingeConnectorTransitionFacts
    F.same.toConnectorFacts F.opposite.toConnectorFacts

@[simp]
theorem toConnectorFacts_same
    (F : FilteredSameOpposite) :
    F.toConnectorFacts.same = F.same.toConnectorFacts :=
  rfl

@[simp]
theorem toConnectorFacts_opposite
    (F : FilteredSameOpposite) :
    F.toConnectorFacts.opposite = F.opposite.toConnectorFacts :=
  rfl

/-- Figure 2 transition obligations projected from connector facts. -/
def toFigure2TransitionObligations
    (F : FilteredSameOpposite) :
    TransitionObligations :=
  F.toConnectorFacts.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (F : FilteredSameOpposite) :
    F.toFigure2TransitionObligations.samePlaceNext =
      F.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (F : FilteredSameOpposite) :
    F.toFigure2TransitionObligations.oppositePlaceNext =
      F.opposite.placeNext :=
  rfl

/-- A completed same/opposite pair projects to the existing flexible
same/opposite transition interface. -/
def toFlexibleSameOpposite
    (F : FilteredSameOpposite)
    (hsame :
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        F.same.placeNext)
    (hopposite :
      RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        F.opposite.placeNext) :
    FlexibleExactLocalTransition.SameOpposite where
  same := F.same.toFlexibleBranch hsame
  opposite := F.opposite.toFlexibleBranch hopposite

end FilteredSameOpposite

/-! ## Concrete same/opposite possible-row witnesses -/

/-- Concrete same-branch connector data. -/
def concreteSameConnector : ConnectorUnitRoleData where
  placeNext := RoleHingeConcreteSearch.samePlaceNext
  roleAngle := RoleHingeConcreteSearch.sameRoleAngle
  realizes_role :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.sameRoleAngle

/-- Concrete opposite-branch connector data. -/
def concreteOppositeConnector : ConnectorUnitRoleData where
  placeNext := RoleHingeConcreteSearch.oppositePlaceNext
  roleAngle := RoleHingeConcreteSearch.oppositeRoleAngle
  realizes_role :=
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
      RoleHingeConcreteSearch.oppositeRoleAngle

/-- Same branch: the concrete map satisfies every possible exact-local row. -/
theorem samePlaceNext_preservesPossibleExactLocalRows :
    PreservesPossibleExactLocalRows RoleHingeConcreteSearch.samePlaceNext := by
  intro source hsource u v hrow
  exact
    ExactLocalTransitionObligationMatrix.samePlaceNext_possibleRow_sqDist
      hsource hrow

/-- Opposite branch: the concrete map satisfies every possible exact-local row. -/
theorem oppositePlaceNext_preservesPossibleExactLocalRows :
    PreservesPossibleExactLocalRows
      RoleHingeConcreteSearch.oppositePlaceNext := by
  intro source hsource u v hrow
  exact
    ExactLocalTransitionObligationMatrix.oppositePlaceNext_possibleRow_sqDist
      hsource hrow

/-- Concrete same branch packaged for solvers that request only possible rows. -/
def concreteSameFilteredBranch : FilteredBranch where
  connector := concreteSameConnector
  possibleRows := samePlaceNext_preservesPossibleExactLocalRows

/-- Concrete opposite branch packaged for solvers that request only possible
rows. -/
def concreteOppositeFilteredBranch : FilteredBranch where
  connector := concreteOppositeConnector
  possibleRows := oppositePlaceNext_preservesPossibleExactLocalRows

/-- Concrete same/opposite filtered exact-local branch surface. -/
def concreteFilteredSameOpposite : FilteredSameOpposite where
  same := concreteSameFilteredBranch
  opposite := concreteOppositeFilteredBranch

/-! ## Blocked-row contradictions -/

/-- A single exact-base row contradiction for a branch. -/
def ExactBaseRowContradiction
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (u v : LocalVertex) : Prop :=
  Not
    (RoleHingeSameBlockAlgebra.sqDist
        (placeNext ExactLocalGeometry.localPoint u)
        (placeNext ExactLocalGeometry.localPoint v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)

/-- A row contradiction at the exact base rules out any row filter that
contains that row. -/
theorem not_preservesRows_of_exactBaseRowContradiction
    {placeNext : (LocalVertex -> R2) -> LocalVertex -> R2}
    {row : LocalVertex -> LocalVertex -> Prop}
    {u v : LocalVertex}
    (hrow : row u v)
    (hcontr : ExactBaseRowContradiction placeNext u v) :
    Not (PreservesExactLocalRows placeNext row) := by
  intro hpres
  exact
    hcontr
      (hpres ExactLocalGeometry.localPoint
        RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
        u v hrow)

/-- The row `T1_1,r` is outside the possible-row matrix. -/
theorem not_possible_T1_1_r :
    Not (PossibleRow T1_1 LocalVertex.r) :=
  ExactLocalTransitionObligationMatrix.not_possible_T1_1_r

/-- Same branch: the blocked row `T1_1,r` contradicts the exact-local table on
the exact base. -/
theorem samePlaceNext_T1_1_r_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r :=
  ExactLocalTransitionObligationMatrix.samePlaceNext_exactBase_T1_1_r_forces_contradiction

/-- Opposite branch: the same blocked row contradicts the exact-local table on
the exact base. -/
theorem oppositePlaceNext_T1_1_r_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r :=
  ExactLocalTransitionObligationMatrix.oppositePlaceNext_exactBase_T1_1_r_forces_contradiction

/-- Any same-branch row filter containing `T1_1,r` is inconsistent. -/
theorem samePlaceNext_not_preservesRows_containing_T1_1_r
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T1_1 LocalVertex.r) :
    Not (PreservesExactLocalRows
      RoleHingeConcreteSearch.samePlaceNext row) :=
  not_preservesRows_of_exactBaseRowContradiction
    hrow samePlaceNext_T1_1_r_exactBaseContradiction

/-- Any opposite-branch row filter containing `T1_1,r` is inconsistent. -/
theorem oppositePlaceNext_not_preservesRows_containing_T1_1_r
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T1_1 LocalVertex.r) :
    Not (PreservesExactLocalRows
      RoleHingeConcreteSearch.oppositePlaceNext row) :=
  not_preservesRows_of_exactBaseRowContradiction
    hrow oppositePlaceNext_T1_1_r_exactBaseContradiction

/-- The concrete same branch cannot satisfy the full exact-local preservation
field required by flexible transitions. -/
theorem samePlaceNext_not_preservesExactLocalSqDistances :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.samePlaceNext) := by
  intro hpres
  exact
    samePlaceNext_T1_1_r_exactBaseContradiction
      (hpres ExactLocalGeometry.localPoint
        RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
        T1_1 LocalVertex.r)

/-- The concrete opposite branch cannot satisfy the full exact-local
preservation field required by flexible transitions. -/
theorem oppositePlaceNext_not_preservesExactLocalSqDistances :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.oppositePlaceNext) := by
  intro hpres
  exact
    oppositePlaceNext_T1_1_r_exactBaseContradiction
      (hpres ExactLocalGeometry.localPoint
        RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
        T1_1 LocalVertex.r)

/-- The concrete same connector data cannot be completed to a flexible
exact-local same-block branch. -/
theorem not_concreteSameConnector_exactLocalSameBlockData :
    Not
      (FlexibleExactLocalTransition.ExactLocalSameBlockData
        concreteSameConnector) := by
  intro hdata
  exact
    samePlaceNext_not_preservesExactLocalSqDistances
      hdata.preserves_exact_local_sq_distances

/-- The concrete opposite connector data cannot be completed to a flexible
exact-local same-block branch. -/
theorem not_concreteOppositeConnector_exactLocalSameBlockData :
    Not
      (FlexibleExactLocalTransition.ExactLocalSameBlockData
        concreteOppositeConnector) := by
  intro hdata
  exact
    oppositePlaceNext_not_preservesExactLocalSqDistances
      hdata.preserves_exact_local_sq_distances

end ExactLocalBranchSolverSurface
end PachToth
end ErdosProblems1066

end
