import ErdosProblems1066.PachToth.ExactLocalTransitionObligationMatrix
import ErdosProblems1066.PachToth.ExactLocalBranchSolverSurface
import ErdosProblems1066.PachToth.FlexibleBranchCoordinateSearch
import ErdosProblems1066.PachToth.RoleHingeExactLocalFinite
import ErdosProblems1066.PachToth.RoleHingeConnectorConcrete

set_option autoImplicit false
set_option maxRecDepth 4096

/-!
# W10 exact-local obstruction expansion

This module expands the W9 exact-local row obstruction surface.  It keeps the
Prop-level possible-row API, adds a checked Boolean transport layer for the
finite matrix, records the matrix counts, and names additional blocked rows
beyond the original `T1_1,r` witness.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalObstructionExpansionW10

open FiniteGraph
open FiniteGraph.LocalVertex
open ExactLocalTransitionObligationMatrix

abbrev R2 := Prod Real Real
abbrev PossibleRow := IsPossibleExactLocalRow
abbrev DerivableRow := FlexibleBranchCoordinateSearch.DerivableExactLocalRow
abbrev PreservesRows := ExactLocalBranchSolverSurface.PreservesExactLocalRows
abbrev ExactBaseRowContradiction :=
  ExactLocalBranchSolverSurface.ExactBaseRowContradiction

instance instDecidableConcretePortTarget (v : LocalVertex) :
    Decidable (RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget v) := by
  unfold RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget
  infer_instance

instance instDecidableRoleAnglePortPair (u v : LocalVertex) :
    Decidable (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) := by
  unfold RoleHingeAngleCertificates.IsRoleAnglePortPair
  infer_instance

instance instDecidableInheritedPair (u v : LocalVertex) :
    Decidable (IsInheritedPair u v) := by
  unfold IsInheritedPair
  infer_instance

instance instDecidablePossibleRow (u v : LocalVertex) :
    Decidable (PossibleRow u v) := by
  unfold PossibleRow IsPossibleExactLocalRow
  infer_instance

/-! ## Checked Boolean matrix transport -/

/-- The Boolean row matrix is equivalent to the Prop-level possible-row API. -/
theorem possibleRowBool_iff
    (u v : LocalVertex) :
    possibleExactLocalRowBool u v = true <-> PossibleRow u v := by
  cases u with
  | r =>
      cases v with
      | r => decide
      | tri t c => fin_cases t <;> fin_cases c <;> decide
  | tri t c =>
      fin_cases t <;> fin_cases c <;>
        cases v with
        | r => decide
        | tri t' c' => fin_cases t' <;> fin_cases c' <;> decide

theorem possibleRow_of_bool
    {u v : LocalVertex}
    (h : possibleExactLocalRowBool u v = true) :
    PossibleRow u v :=
  (possibleRowBool_iff u v).1 h

theorem bool_of_possibleRow
    {u v : LocalVertex}
    (h : PossibleRow u v) :
    possibleExactLocalRowBool u v = true :=
  (possibleRowBool_iff u v).2 h

theorem impossibleRow_of_bool_false
    {u v : LocalVertex}
    (h : possibleExactLocalRowBool u v = false) :
    Not (PossibleRow u v) := by
  intro hrow
  have htrue := bool_of_possibleRow hrow
  rw [h] at htrue
  cases htrue

theorem bool_false_of_impossibleRow
    {u v : LocalVertex}
    (h : Not (PossibleRow u v)) :
    possibleExactLocalRowBool u v = false := by
  cases hbool : possibleExactLocalRowBool u v
  · rfl
  · exact False.elim (h (possibleRow_of_bool hbool))

/-- Boolean possible entries in the exact-local row matrix. -/
def possibleRowEntries : Finset (Prod LocalVertex LocalVertex) :=
  localPairMatrix.filter fun p => possibleExactLocalRowBool p.1 p.2

/-- Boolean impossible entries in the exact-local row matrix. -/
def impossibleRowEntries : Finset (Prod LocalVertex LocalVertex) :=
  localPairMatrix.filter fun p => !possibleExactLocalRowBool p.1 p.2

theorem mem_possibleRowEntries
    {p : Prod LocalVertex LocalVertex} :
    p ∈ possibleRowEntries <-> p ∈ localPairMatrix /\ PossibleRow p.1 p.2 := by
  rw [possibleRowEntries, Finset.mem_filter]
  constructor
  · intro hp
    exact And.intro hp.1 (possibleRow_of_bool hp.2)
  · intro hp
    exact And.intro hp.1 (bool_of_possibleRow hp.2)

theorem mem_impossibleRowEntries
    {p : Prod LocalVertex LocalVertex} :
    p ∈ impossibleRowEntries <->
      p ∈ localPairMatrix /\ Not (PossibleRow p.1 p.2) := by
  rw [impossibleRowEntries, Finset.mem_filter]
  constructor
  · intro hp
    exact And.intro hp.1 (impossibleRow_of_bool_false (by
      simpa using hp.2))
  · intro hp
    exact And.intro hp.1 (by
      rw [bool_false_of_impossibleRow hp.2]
      rfl)

theorem possibleRowEntries_card :
    possibleRowEntries.card = possibleExactLocalRowExpectedCard := by
  decide

theorem impossibleRowEntries_card :
    impossibleRowEntries.card = impossibleExactLocalRowExpectedCard := by
  decide

/-! ## Possible-row transport across W9 surfaces -/

theorem derivableRow_of_possibleRow
    {u v : LocalVertex}
    (h : PossibleRow u v) :
    DerivableRow u v := by
  rcases h with hdiag | hinherited | hpair
  · exact Or.inl hdiag
  · exact Or.inr (Or.inr hinherited)
  · exact Or.inr (Or.inl hpair)

theorem possibleRow_of_derivableRow
    {u v : LocalVertex}
    (h : DerivableRow u v) :
    PossibleRow u v := by
  rcases h with hdiag | hrow
  · exact Or.inl hdiag
  rcases hrow with hpair | hinherited
  · exact Or.inr (Or.inr hpair)
  · exact Or.inr (Or.inl hinherited)

theorem derivableRow_iff_possibleRow
    (u v : LocalVertex) :
    DerivableRow u v <-> PossibleRow u v :=
  ⟨possibleRow_of_derivableRow, derivableRow_of_possibleRow⟩

theorem derivableRow_of_bool
    {u v : LocalVertex}
    (h : possibleExactLocalRowBool u v = true) :
    DerivableRow u v :=
  derivableRow_of_possibleRow (possibleRow_of_bool h)

theorem not_derivableRow_of_bool_false
    {u v : LocalVertex}
    (h : possibleExactLocalRowBool u v = false) :
    Not (DerivableRow u v) := by
  intro hrow
  exact impossibleRow_of_bool_false h (possibleRow_of_derivableRow hrow)

theorem filteredBranch_sqDist_of_possibleRowBool
    (B : ExactLocalBranchSolverSurface.FilteredBranch)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : possibleExactLocalRowBool u v = true) :
    RoleHingeSameBlockAlgebra.sqDist
        (B.placeNext source u) (B.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  B.possibleRow_sqDist hsource (possibleRow_of_bool hrow)

theorem same_sqDist_of_possibleRowBool
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : possibleExactLocalRowBool u v = true) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  ExactLocalTransitionObligationMatrix.samePlaceNext_possibleRow_sqDist
    hsource (possibleRow_of_bool hrow)

theorem opposite_sqDist_of_possibleRowBool
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : possibleExactLocalRowBool u v = true) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  ExactLocalTransitionObligationMatrix.oppositePlaceNext_possibleRow_sqDist
    hsource (possibleRow_of_bool hrow)

theorem same_sqDist_of_possibleRowBool_via_coordinateSearch
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : possibleExactLocalRowBool u v = true) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  FlexibleBranchCoordinateSearch.same_sqDist_of_derivable_row
    hsource (derivableRow_of_bool hrow)

theorem opposite_sqDist_of_possibleRowBool_via_coordinateSearch
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : possibleExactLocalRowBool u v = true) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  FlexibleBranchCoordinateSearch.opposite_sqDist_of_derivable_row
    hsource (derivableRow_of_bool hrow)

/-! ## Connector-concrete transport -/

theorem connectorConcrete_samePlaceNext_eq :
    RoleHingeConnectorConcrete.samePlaceNext =
      RoleHingeConcreteSearch.samePlaceNext := by
  funext source v
  simp [RoleHingeConnectorConcrete.samePlaceNext,
    RoleHingeConnectorConcrete.concretePlaceNext,
    RoleHingeConcreteSearch.samePlaceNext,
    RoleHingeConcreteSearch.sameRoleAngle_eq_sameEquilateralRoleAngle]

theorem connectorConcrete_oppositePlaceNext_eq :
    RoleHingeConnectorConcrete.oppositePlaceNext =
      RoleHingeConcreteSearch.oppositePlaceNext := by
  funext source v
  simp [RoleHingeConnectorConcrete.oppositePlaceNext,
    RoleHingeConnectorConcrete.concretePlaceNext,
    RoleHingeConcreteSearch.oppositePlaceNext,
    RoleHingeConcreteSearch.oppositeRoleAngle_eq_oppositeEquilateralRoleAngle]

theorem connectorConcrete_same_preservesPossibleExactLocalRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      RoleHingeConnectorConcrete.samePlaceNext := by
  rw [connectorConcrete_samePlaceNext_eq]
  exact ExactLocalBranchSolverSurface.samePlaceNext_preservesPossibleExactLocalRows

theorem connectorConcrete_opposite_preservesPossibleExactLocalRows :
    ExactLocalBranchSolverSurface.PreservesPossibleExactLocalRows
      RoleHingeConnectorConcrete.oppositePlaceNext := by
  rw [connectorConcrete_oppositePlaceNext_eq]
  exact
    ExactLocalBranchSolverSurface.oppositePlaceNext_preservesPossibleExactLocalRows

/-! ## Expanded blocked root rows -/

theorem not_possible_T1_2_r :
    Not (PossibleRow T1_2 LocalVertex.r) :=
  impossibleRow_of_bool_false rfl

theorem not_possible_T0_0_r :
    Not (PossibleRow T0_0 LocalVertex.r) :=
  impossibleRow_of_bool_false rfl

theorem not_possible_T0_2_r :
    Not (PossibleRow T0_2 LocalVertex.r) :=
  impossibleRow_of_bool_false rfl

theorem not_possible_r_T1_1 :
    Not (PossibleRow LocalVertex.r T1_1) :=
  impossibleRow_of_bool_false rfl

theorem not_possible_r_T1_2 :
    Not (PossibleRow LocalVertex.r T1_2) :=
  impossibleRow_of_bool_false rfl

theorem not_possible_r_T0_0 :
    Not (PossibleRow LocalVertex.r T0_0) :=
  impossibleRow_of_bool_false rfl

theorem not_possible_r_T0_2 :
    Not (PossibleRow LocalVertex.r T0_2) :=
  impossibleRow_of_bool_false rfl

theorem not_derivable_T1_2_r :
    Not (DerivableRow T1_2 LocalVertex.r) :=
  not_derivableRow_of_bool_false rfl

theorem exactLocalNorm4_T1_2_r :
    (((ExactLocalGeometry.localNorm4 T1_2 LocalVertex.r : Int) : Real) / 4) =
      1 := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T1_2]

/-- Same branch: a second exact-base blocked row, beyond the W9 `T1_1,r`
witness. -/
theorem samePlaceNext_exactBase_T1_2_r_sqDist :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint T1_2)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint LocalVertex.r) =
      10 := by
  norm_num [RoleHingeConcreteSearch.samePlaceNext,
    RoleHingeConcreteSearch.concreteRoleHingePlace,
    RoleHingeConcreteSearch.sameRoleAngle,
    RoleHingeSameBlockAlgebra.sqDist,
    UnitVectorGeometry.hingePoint, UnitVectorGeometry.add,
    UnitVectorGeometry.unitVec,
    ExactLocalGeometry.localPoint, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.toPoint, ExactLocalGeometry.h,
    T, T1_2, T2_2]
  ring_nf
  rw [Real.sq_sqrt]
  · norm_num
  · norm_num

theorem samePlaceNext_exactBase_T1_2_r_forces_contradiction :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_2 LocalVertex.r := by
  unfold ExactBaseRowContradiction
  unfold ExactLocalBranchSolverSurface.ExactBaseRowContradiction
  rw [samePlaceNext_exactBase_T1_2_r_sqDist,
    exactLocalNorm4_T1_2_r]
  norm_num

theorem samePlaceNext_not_preservesRows_containing_T1_2_r
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T1_2 LocalVertex.r) :
    Not (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  ExactLocalBranchSolverSurface.not_preservesRows_of_exactBaseRowContradiction
    hrow samePlaceNext_exactBase_T1_2_r_forces_contradiction

end ExactLocalObstructionExpansionW10
end PachToth
end ErdosProblems1066

end
