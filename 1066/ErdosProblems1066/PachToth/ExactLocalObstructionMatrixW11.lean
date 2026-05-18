import ErdosProblems1066.PachToth.ExactLocalObstructionExpansionW10

set_option autoImplicit false
set_option maxRecDepth 4096

/-!
# W11 exact-local obstruction matrix

This module extends the W10 exact-local row surface with named row classes for
root/moved-target rows and connector-source/target endpoint rows.  It also
packages a small candidate-row interface: a candidate may request any subset of
the W10 possible matrix, and the concrete same/opposite branches discharge
that subset.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalObstructionMatrixW11

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real
abbrev PossibleRow := ExactLocalTransitionObligationMatrix.IsPossibleExactLocalRow
abbrev W10PossibleRow := ExactLocalObstructionExpansionW10.PossibleRow
abbrev IsMovedTarget := RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget
abbrev ExactBaseRowContradiction :=
  ExactLocalBranchSolverSurface.ExactBaseRowContradiction
abbrev PreservesRows := ExactLocalBranchSolverSurface.PreservesExactLocalRows

/-! ## Projection back to the W10 matrix -/

theorem possibleRow_iff_w10
    (u v : LocalVertex) :
    PossibleRow u v <-> W10PossibleRow u v :=
  Iff.rfl

theorem possibleRow_of_w10
    {u v : LocalVertex}
    (h : W10PossibleRow u v) :
    PossibleRow u v :=
  h

theorem w10_of_possibleRow
    {u v : LocalVertex}
    (h : PossibleRow u v) :
    W10PossibleRow u v :=
  h

theorem possibleRowBool_iff
    (u v : LocalVertex) :
    ExactLocalTransitionObligationMatrix.possibleExactLocalRowBool u v = true <->
      PossibleRow u v :=
  ExactLocalObstructionExpansionW10.possibleRowBool_iff u v

def possibleRowEntries : Finset (Prod LocalVertex LocalVertex) :=
  ExactLocalObstructionExpansionW10.possibleRowEntries

def impossibleRowEntries : Finset (Prod LocalVertex LocalVertex) :=
  ExactLocalObstructionExpansionW10.impossibleRowEntries

theorem possibleRowEntries_to_w10 :
    possibleRowEntries =
      ExactLocalObstructionExpansionW10.possibleRowEntries :=
  rfl

theorem impossibleRowEntries_to_w10 :
    impossibleRowEntries =
      ExactLocalObstructionExpansionW10.impossibleRowEntries :=
  rfl

theorem possibleRowEntries_card :
    possibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.possibleExactLocalRowExpectedCard :=
  ExactLocalObstructionExpansionW10.possibleRowEntries_card

theorem impossibleRowEntries_card :
    impossibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.impossibleExactLocalRowExpectedCard :=
  ExactLocalObstructionExpansionW10.impossibleRowEntries_card

/-! ## A smaller exact-local candidate interface -/

structure ExactLocalCandidateRows where
  row : LocalVertex -> LocalVertex -> Prop
  projects_to_w10 :
    forall {u v : LocalVertex}, row u v -> W10PossibleRow u v

namespace ExactLocalCandidateRows

theorem possible
    (C : ExactLocalCandidateRows)
    {u v : LocalVertex}
    (hrow : C.row u v) :
    PossibleRow u v :=
  possibleRow_of_w10 (C.projects_to_w10 hrow)

theorem samePlaceNext_preservesRows
    (C : ExactLocalCandidateRows) :
    PreservesRows RoleHingeConcreteSearch.samePlaceNext C.row := by
  intro source hsource u v hrow
  exact
    ExactLocalTransitionObligationMatrix.samePlaceNext_possibleRow_sqDist
      hsource (C.possible hrow)

theorem oppositePlaceNext_preservesRows
    (C : ExactLocalCandidateRows) :
    PreservesRows RoleHingeConcreteSearch.oppositePlaceNext C.row := by
  intro source hsource u v hrow
  exact
    ExactLocalTransitionObligationMatrix.oppositePlaceNext_possibleRow_sqDist
      hsource (C.possible hrow)

def possibleRows : ExactLocalCandidateRows where
  row := PossibleRow
  projects_to_w10 := fun h => h

@[simp]
theorem possibleRows_row :
    possibleRows.row = PossibleRow :=
  rfl

end ExactLocalCandidateRows

/-! ## Root and moved-target rows -/

def IsRootMovedTargetRow (u v : LocalVertex) : Prop :=
  (u = LocalVertex.r /\ IsMovedTarget v) \/
    (IsMovedTarget u /\ v = LocalVertex.r)

theorem not_possible_T1_1_r :
    Not (PossibleRow T1_1 LocalVertex.r) :=
  ExactLocalTransitionObligationMatrix.not_possible_T1_1_r

theorem not_possible_T1_2_r :
    Not (PossibleRow T1_2 LocalVertex.r) :=
  ExactLocalObstructionExpansionW10.not_possible_T1_2_r

theorem not_possible_T0_0_r :
    Not (PossibleRow T0_0 LocalVertex.r) :=
  ExactLocalObstructionExpansionW10.not_possible_T0_0_r

theorem not_possible_T0_2_r :
    Not (PossibleRow T0_2 LocalVertex.r) :=
  ExactLocalObstructionExpansionW10.not_possible_T0_2_r

theorem not_possible_r_T1_1 :
    Not (PossibleRow LocalVertex.r T1_1) :=
  ExactLocalObstructionExpansionW10.not_possible_r_T1_1

theorem not_possible_r_T1_2 :
    Not (PossibleRow LocalVertex.r T1_2) :=
  ExactLocalObstructionExpansionW10.not_possible_r_T1_2

theorem not_possible_r_T0_0 :
    Not (PossibleRow LocalVertex.r T0_0) :=
  ExactLocalObstructionExpansionW10.not_possible_r_T0_0

theorem not_possible_r_T0_2 :
    Not (PossibleRow LocalVertex.r T0_2) :=
  ExactLocalObstructionExpansionW10.not_possible_r_T0_2

theorem rootMovedTargetRow_not_possible
    {u v : LocalVertex}
    (hrow : IsRootMovedTargetRow u v) :
    Not (PossibleRow u v) := by
  match hrow with
  | Or.inl hroot =>
      match hroot with
      | And.intro hu htarget =>
          subst u
          match htarget with
          | Or.inl hv =>
              subst v
              exact not_possible_r_T1_1
          | Or.inr (Or.inl hv) =>
              subst v
              exact not_possible_r_T1_2
          | Or.inr (Or.inr (Or.inl hv)) =>
              subst v
              exact not_possible_r_T0_0
          | Or.inr (Or.inr (Or.inr hv)) =>
              subst v
              exact not_possible_r_T0_2
  | Or.inr hroot =>
      match hroot with
      | And.intro htarget hv =>
          subst v
          match htarget with
          | Or.inl hu =>
              subst u
              exact not_possible_T1_1_r
          | Or.inr (Or.inl hu) =>
              subst u
              exact not_possible_T1_2_r
          | Or.inr (Or.inr (Or.inl hu)) =>
              subst u
              exact not_possible_T0_0_r
          | Or.inr (Or.inr (Or.inr hu)) =>
              subst u
              exact not_possible_T0_2_r

/-! ## Connector endpoint interactions -/

def IsPConnectorEndpointRow (u v : LocalVertex) : Prop :=
  (u = T2_2 /\ (v = T1_1 \/ v = T1_2)) \/
    ((u = T1_1 \/ u = T1_2) /\ v = T2_2)

def IsQConnectorEndpointRow (u v : LocalVertex) : Prop :=
  (u = T4_0 /\ (v = T0_0 \/ v = T0_2)) \/
    ((u = T0_0 \/ u = T0_2) /\ v = T4_0)

def IsConnectorEndpointRow (u v : LocalVertex) : Prop :=
  IsPConnectorEndpointRow u v \/ IsQConnectorEndpointRow u v

theorem not_possible_T2_2_T1_1 :
    Not (PossibleRow T2_2 T1_1) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem not_possible_T1_1_T2_2 :
    Not (PossibleRow T1_1 T2_2) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem not_possible_T2_2_T1_2 :
    Not (PossibleRow T2_2 T1_2) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem not_possible_T1_2_T2_2 :
    Not (PossibleRow T1_2 T2_2) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem not_possible_T4_0_T0_0 :
    Not (PossibleRow T4_0 T0_0) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem not_possible_T0_0_T4_0 :
    Not (PossibleRow T0_0 T4_0) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem not_possible_T4_0_T0_2 :
    Not (PossibleRow T4_0 T0_2) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem not_possible_T0_2_T4_0 :
    Not (PossibleRow T0_2 T4_0) :=
  ExactLocalObstructionExpansionW10.impossibleRow_of_bool_false rfl

theorem connectorEndpointRow_not_possible
    {u v : LocalVertex}
    (hrow : IsConnectorEndpointRow u v) :
    Not (PossibleRow u v) := by
  match hrow with
  | Or.inl hp =>
      match hp with
      | Or.inl hforward =>
          match hforward with
          | And.intro hu hv =>
              subst u
              match hv with
              | Or.inl hv1 =>
                  subst v
                  exact not_possible_T2_2_T1_1
              | Or.inr hv2 =>
                  subst v
                  exact not_possible_T2_2_T1_2
      | Or.inr hreverse =>
          match hreverse with
          | And.intro hu hv =>
              subst v
              match hu with
              | Or.inl hu1 =>
                  subst u
                  exact not_possible_T1_1_T2_2
              | Or.inr hu2 =>
                  subst u
                  exact not_possible_T1_2_T2_2
  | Or.inr hq =>
      match hq with
      | Or.inl hforward =>
          match hforward with
          | And.intro hu hv =>
              subst u
              match hv with
              | Or.inl hv1 =>
                  subst v
                  exact not_possible_T4_0_T0_0
              | Or.inr hv2 =>
                  subst v
                  exact not_possible_T4_0_T0_2
      | Or.inr hreverse =>
          match hreverse with
          | And.intro hu hv =>
              subst v
              match hu with
              | Or.inl hu1 =>
                  subst u
                  exact not_possible_T0_0_T4_0
              | Or.inr hu2 =>
                  subst u
                  exact not_possible_T0_2_T4_0

def IsW11BlockedEndpointRow (u v : LocalVertex) : Prop :=
  IsRootMovedTargetRow u v \/ IsConnectorEndpointRow u v

theorem blockedEndpointRow_not_possible
    {u v : LocalVertex}
    (hrow : IsW11BlockedEndpointRow u v) :
    Not (PossibleRow u v) := by
  match hrow with
  | Or.inl hroot => exact rootMovedTargetRow_not_possible hroot
  | Or.inr hconn => exact connectorEndpointRow_not_possible hconn

theorem candidateRows_exclude_blockedEndpointRow
    (C : ExactLocalCandidateRows)
    {u v : LocalVertex}
    (hblocked : IsW11BlockedEndpointRow u v) :
    Not (C.row u v) := by
  intro hrow
  exact blockedEndpointRow_not_possible hblocked (C.possible hrow)

/-! ## Exact-base connector endpoint obstructions -/

theorem not_moved_T2_2 :
    Not (IsMovedTarget T2_2) := by
  intro h
  rcases h with h | h | h | h <;> cases h

theorem not_moved_T4_0 :
    Not (IsMovedTarget T4_0) := by
  intro h
  rcases h with h | h | h | h <;> cases h

theorem samePlaceNext_exactBase_connector_forward_sqDist_one
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u)) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint u)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint v) =
      1 := by
  have hunit :=
    RoleHingeConcreteSearch.same_connector_unit_edges
      ExactLocalGeometry.localPoint u v hconn
  have hu_eq :
      RoleHingeConcreteSearch.samePlaceNext ExactLocalGeometry.localPoint u =
        ExactLocalGeometry.localPoint u :=
    RoleHingeExactLocalFinite.concreteRoleHingePlace_eq_source_of_not_portTarget
      RoleHingeConcreteSearch.sameRoleAngle ExactLocalGeometry.localPoint hu
  have hunit' :
      _root_.eucDist
          (RoleHingeConcreteSearch.samePlaceNext
            ExactLocalGeometry.localPoint u)
          (RoleHingeConcreteSearch.samePlaceNext
            ExactLocalGeometry.localPoint v) =
        1 := by
    simpa [hu_eq] using hunit
  exact RoleHingeAngleCertificates.sqDist_eq_one_of_eucDist_eq_one hunit'

theorem oppositePlaceNext_exactBase_connector_forward_sqDist_one
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u)) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint u)
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint v) =
      1 := by
  have hunit :=
    RoleHingeConcreteSearch.opposite_connector_unit_edges
      ExactLocalGeometry.localPoint u v hconn
  have hu_eq :
      RoleHingeConcreteSearch.oppositePlaceNext ExactLocalGeometry.localPoint u =
        ExactLocalGeometry.localPoint u :=
    RoleHingeExactLocalFinite.concreteRoleHingePlace_eq_source_of_not_portTarget
      RoleHingeConcreteSearch.oppositeRoleAngle ExactLocalGeometry.localPoint hu
  have hunit' :
      _root_.eucDist
          (RoleHingeConcreteSearch.oppositePlaceNext
            ExactLocalGeometry.localPoint u)
          (RoleHingeConcreteSearch.oppositePlaceNext
            ExactLocalGeometry.localPoint v) =
        1 := by
    simpa [hu_eq] using hunit
  exact RoleHingeAngleCertificates.sqDist_eq_one_of_eucDist_eq_one hunit'

theorem samePlaceNext_exactBase_connector_reverse_sqDist_one
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u)) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint v)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint u) =
      1 := by
  calc
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint v)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint u) =
      RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint u)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint v) := by
        exact RoleHingeAngleCertificates.sqDist_comm _ _
    _ = 1 :=
      samePlaceNext_exactBase_connector_forward_sqDist_one hconn hu

theorem oppositePlaceNext_exactBase_connector_reverse_sqDist_one
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u)) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint v)
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint u) =
      1 := by
  calc
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint v)
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint u) =
      RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint u)
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint v) := by
        exact RoleHingeAngleCertificates.sqDist_comm _ _
    _ = 1 :=
      oppositePlaceNext_exactBase_connector_forward_sqDist_one hconn hu

theorem samePlaceNext_connector_forward_exactBaseContradiction
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u))
    (hlocal :
      Not
        ((((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) = 1)) :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext u v := by
  intro h
  have hs :=
    samePlaceNext_exactBase_connector_forward_sqDist_one hconn hu
  rw [hs] at h
  exact hlocal h.symm

theorem oppositePlaceNext_connector_forward_exactBaseContradiction
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u))
    (hlocal :
      Not
        ((((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) = 1)) :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext u v := by
  intro h
  have hs :=
    oppositePlaceNext_exactBase_connector_forward_sqDist_one hconn hu
  rw [hs] at h
  exact hlocal h.symm

theorem samePlaceNext_connector_reverse_exactBaseContradiction
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u))
    (hlocal :
      Not
        ((((ExactLocalGeometry.localNorm4 v u : Int) : Real) / 4) = 1)) :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext v u := by
  intro h
  have hs :=
    samePlaceNext_exactBase_connector_reverse_sqDist_one hconn hu
  rw [hs] at h
  exact hlocal h.symm

theorem oppositePlaceNext_connector_reverse_exactBaseContradiction
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v)
    (hu : Not (IsMovedTarget u))
    (hlocal :
      Not
        ((((ExactLocalGeometry.localNorm4 v u : Int) : Real) / 4) = 1)) :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext v u := by
  intro h
  have hs :=
    oppositePlaceNext_exactBase_connector_reverse_sqDist_one hconn hu
  rw [hs] at h
  exact hlocal h.symm

theorem nextConnector_T2_2_T1_1 :
    CrossBlock.NextConnector T2_2 T1_1 :=
  Figure2EdgeTable.nextConnectorRole_nextConnector
    T2_2 T1_1 Figure2EdgeTable.NextConnectorRole.pToUpper rfl

theorem nextConnector_T2_2_T1_2 :
    CrossBlock.NextConnector T2_2 T1_2 :=
  Figure2EdgeTable.nextConnectorRole_nextConnector
    T2_2 T1_2 Figure2EdgeTable.NextConnectorRole.pToLower rfl

theorem nextConnector_T4_0_T0_0 :
    CrossBlock.NextConnector T4_0 T0_0 :=
  Figure2EdgeTable.nextConnectorRole_nextConnector
    T4_0 T0_0 Figure2EdgeTable.NextConnectorRole.qToUpper rfl

theorem nextConnector_T4_0_T0_2 :
    CrossBlock.NextConnector T4_0 T0_2 :=
  Figure2EdgeTable.nextConnectorRole_nextConnector
    T4_0 T0_2 Figure2EdgeTable.NextConnectorRole.qToLower rfl

theorem exactLocalNorm4_T2_2_T1_1_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T2_2 T1_1 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T2_2, T1_1]

theorem exactLocalNorm4_T1_1_T2_2_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T1_1 T2_2 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T2_2, T1_1]

theorem exactLocalNorm4_T2_2_T1_2_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T2_2 T1_2 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T2_2, T1_2]

theorem exactLocalNorm4_T1_2_T2_2_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T1_2 T2_2 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T2_2, T1_2]

theorem exactLocalNorm4_T4_0_T0_0_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T4_0 T0_0 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T4_0, T0_0]

theorem exactLocalNorm4_T0_0_T4_0_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T0_0 T4_0 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T4_0, T0_0]

theorem exactLocalNorm4_T4_0_T0_2_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T4_0 T0_2 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T4_0, T0_2]

theorem exactLocalNorm4_T0_2_T4_0_ne_one :
    Not
      ((((ExactLocalGeometry.localNorm4 T0_2 T4_0 : Int) : Real) / 4) = 1) := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T4_0, T0_2]

theorem samePlaceNext_T2_2_T1_1_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T2_2 T1_1 :=
  samePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T2_2_T1_1 not_moved_T2_2
    exactLocalNorm4_T2_2_T1_1_ne_one

theorem oppositePlaceNext_T2_2_T1_1_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T2_2 T1_1 :=
  oppositePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T2_2_T1_1 not_moved_T2_2
    exactLocalNorm4_T2_2_T1_1_ne_one

theorem samePlaceNext_T1_1_T2_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 T2_2 :=
  samePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T2_2_T1_1 not_moved_T2_2
    exactLocalNorm4_T1_1_T2_2_ne_one

theorem oppositePlaceNext_T1_1_T2_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 T2_2 :=
  oppositePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T2_2_T1_1 not_moved_T2_2
    exactLocalNorm4_T1_1_T2_2_ne_one

theorem samePlaceNext_T2_2_T1_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T2_2 T1_2 :=
  samePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T2_2_T1_2 not_moved_T2_2
    exactLocalNorm4_T2_2_T1_2_ne_one

theorem oppositePlaceNext_T2_2_T1_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T2_2 T1_2 :=
  oppositePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T2_2_T1_2 not_moved_T2_2
    exactLocalNorm4_T2_2_T1_2_ne_one

theorem samePlaceNext_T1_2_T2_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_2 T2_2 :=
  samePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T2_2_T1_2 not_moved_T2_2
    exactLocalNorm4_T1_2_T2_2_ne_one

theorem oppositePlaceNext_T1_2_T2_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_2 T2_2 :=
  oppositePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T2_2_T1_2 not_moved_T2_2
    exactLocalNorm4_T1_2_T2_2_ne_one

theorem samePlaceNext_T4_0_T0_0_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T4_0 T0_0 :=
  samePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T4_0_T0_0 not_moved_T4_0
    exactLocalNorm4_T4_0_T0_0_ne_one

theorem oppositePlaceNext_T4_0_T0_0_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T4_0 T0_0 :=
  oppositePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T4_0_T0_0 not_moved_T4_0
    exactLocalNorm4_T4_0_T0_0_ne_one

theorem samePlaceNext_T0_0_T4_0_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T0_0 T4_0 :=
  samePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T4_0_T0_0 not_moved_T4_0
    exactLocalNorm4_T0_0_T4_0_ne_one

theorem oppositePlaceNext_T0_0_T4_0_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T0_0 T4_0 :=
  oppositePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T4_0_T0_0 not_moved_T4_0
    exactLocalNorm4_T0_0_T4_0_ne_one

theorem samePlaceNext_T4_0_T0_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T4_0 T0_2 :=
  samePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T4_0_T0_2 not_moved_T4_0
    exactLocalNorm4_T4_0_T0_2_ne_one

theorem oppositePlaceNext_T4_0_T0_2_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T4_0 T0_2 :=
  oppositePlaceNext_connector_forward_exactBaseContradiction
    nextConnector_T4_0_T0_2 not_moved_T4_0
    exactLocalNorm4_T4_0_T0_2_ne_one

theorem samePlaceNext_T0_2_T4_0_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T0_2 T4_0 :=
  samePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T4_0_T0_2 not_moved_T4_0
    exactLocalNorm4_T0_2_T4_0_ne_one

theorem oppositePlaceNext_T0_2_T4_0_exactBaseContradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T0_2 T4_0 :=
  oppositePlaceNext_connector_reverse_exactBaseContradiction
    nextConnector_T4_0_T0_2 not_moved_T4_0
    exactLocalNorm4_T0_2_T4_0_ne_one

theorem samePlaceNext_not_preservesRows_containing_T2_2_T1_1
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T2_2 T1_1) :
    Not (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  ExactLocalBranchSolverSurface.not_preservesRows_of_exactBaseRowContradiction
    hrow samePlaceNext_T2_2_T1_1_exactBaseContradiction

theorem oppositePlaceNext_not_preservesRows_containing_T2_2_T1_1
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T2_2 T1_1) :
    Not (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  ExactLocalBranchSolverSurface.not_preservesRows_of_exactBaseRowContradiction
    hrow oppositePlaceNext_T2_2_T1_1_exactBaseContradiction

theorem samePlaceNext_not_preservesRows_containing_T4_0_T0_0
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T4_0 T0_0) :
    Not (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  ExactLocalBranchSolverSurface.not_preservesRows_of_exactBaseRowContradiction
    hrow samePlaceNext_T4_0_T0_0_exactBaseContradiction

theorem oppositePlaceNext_not_preservesRows_containing_T4_0_T0_0
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T4_0 T0_0) :
    Not (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  ExactLocalBranchSolverSurface.not_preservesRows_of_exactBaseRowContradiction
    hrow oppositePlaceNext_T4_0_T0_0_exactBaseContradiction

end ExactLocalObstructionMatrixW11
end PachToth
end ErdosProblems1066

end
