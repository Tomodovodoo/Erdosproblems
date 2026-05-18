import ErdosProblems1066.PachToth.RoleHingeExactLocalFinite

set_option autoImplicit false

/-!
# Exact-local transition obligation matrix

The concrete role-hinge ansatz overrides four local labels and leaves the
other twelve labels unchanged.  The old all-non-port-pair "rest" obligation is
therefore too strong: a moved label paired with most local labels already
contradicts the exact local squared-distance table on the exact base block.

This file records the finite matrix of rows that still can be discharged by
the current concrete same/opposite maps:

* diagonal rows;
* rows whose two labels are both unchanged by the concrete map;
* the two same-source role-angle port pairs, in both orders.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalTransitionObligationMatrix

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real

/-- A row inherited directly from the source block because neither endpoint is
one of the four concrete role-hinge target labels. -/
def IsInheritedPair (u v : LocalVertex) : Prop :=
  Not (RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget u) /\
    Not (RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget v)

/-- The exact-local rows still available to the concrete role-hinge ansatz. -/
def IsPossibleExactLocalRow (u v : LocalVertex) : Prop :=
  u = v \/
    IsInheritedPair u v \/
      RoleHingeAngleCertificates.IsRoleAnglePortPair u v

/-- Boolean version of the four moved labels. -/
def isConcreteRoleHingePortTargetBool : LocalVertex -> Bool
  | .tri 1 1 => true
  | .tri 1 2 => true
  | .tri 0 0 => true
  | .tri 0 2 => true
  | _ => false

/-- Boolean version of the two role-angle port pairs, in both orders. -/
def isRoleAnglePortPairBool : LocalVertex -> LocalVertex -> Bool
  | .tri 1 1, .tri 1 2 => true
  | .tri 1 2, .tri 1 1 => true
  | .tri 0 0, .tri 0 2 => true
  | .tri 0 2, .tri 0 0 => true
  | _, _ => false

/-- Computable Boolean matrix entry for possible exact-local rows. -/
def possibleExactLocalRowBool (u v : LocalVertex) : Bool :=
  decide (u = v) ||
    (!isConcreteRoleHingePortTargetBool u &&
      !isConcreteRoleHingePortTargetBool v) ||
        isRoleAnglePortPairBool u v

/-- The finite set of all local-vertex matrix entries. -/
def localPairMatrix : Finset (LocalVertex × LocalVertex) :=
  (Finset.univ : Finset LocalVertex).product
    (Finset.univ : Finset LocalVertex)

/-- Expected count of possible rows in the concrete matrix. -/
def possibleExactLocalRowExpectedCard : Nat := 152

/-- Expected count of rows blocked by the concrete matrix. -/
def impossibleExactLocalRowExpectedCard : Nat := 104

theorem possible_of_eq {u v : LocalVertex} (h : u = v) :
    IsPossibleExactLocalRow u v :=
  Or.inl h

theorem possible_of_inherited {u v : LocalVertex}
    (h : IsInheritedPair u v) :
    IsPossibleExactLocalRow u v :=
  Or.inr (Or.inl h)

theorem possible_of_roleAnglePortPair {u v : LocalVertex}
    (h : RoleHingeAngleCertificates.IsRoleAnglePortPair u v) :
    IsPossibleExactLocalRow u v :=
  Or.inr (Or.inr h)

/-- A moved/unmoved classification for every ordered row. -/
theorem row_eq_or_inherited_or_moved
    (u v : LocalVertex) :
    u = v \/
      IsInheritedPair u v \/
        RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget u \/
          RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget v := by
  by_cases hdiag : u = v
  · exact Or.inl hdiag
  · right
    by_cases hu :
        RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget u
    · exact Or.inr (Or.inl hu)
    · by_cases hv :
        RoleHingeExactLocalFinite.IsConcreteRoleHingePortTarget v
      · exact Or.inr (Or.inr hv)
      · exact Or.inl ⟨hu, hv⟩

theorem not_possible_of_not_eq_not_inherited_not_portPair
    {u v : LocalVertex}
    (hneq : u ≠ v)
    (hnotInherited : Not (IsInheritedPair u v))
    (hnotPort :
      Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v)) :
    Not (IsPossibleExactLocalRow u v) := by
  intro hpossible
  rcases hpossible with hdiag | hinherited | hport
  · exact hneq hdiag
  · exact hnotInherited hinherited
  · exact hnotPort hport

theorem samePlaceNext_roleAnglePortPair_sqDist
    (source : LocalVertex -> R2)
    {u v : LocalVertex}
    (hpair : RoleHingeAngleCertificates.IsRoleAnglePortPair u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hpair with h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.p_ports_exactLocalSqDist_of_angleEquations_realizes
        RoleHingeConcreteSearch.samePlaceNext
        RoleHingeConcreteSearch.sameRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.sameRoleAngle)
        RoleHingeConcreteSearch.sameRoleAngle_angleEquations
        source
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.p_ports_exactLocalSqDist_symm_of_angleEquations_realizes
        RoleHingeConcreteSearch.samePlaceNext
        RoleHingeConcreteSearch.sameRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.sameRoleAngle)
        RoleHingeConcreteSearch.sameRoleAngle_angleEquations
        source
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.q_ports_exactLocalSqDist_of_angleEquations_realizes
        RoleHingeConcreteSearch.samePlaceNext
        RoleHingeConcreteSearch.sameRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.sameRoleAngle)
        RoleHingeConcreteSearch.sameRoleAngle_angleEquations
        source
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.q_ports_exactLocalSqDist_symm_of_angleEquations_realizes
        RoleHingeConcreteSearch.samePlaceNext
        RoleHingeConcreteSearch.sameRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.sameRoleAngle)
        RoleHingeConcreteSearch.sameRoleAngle_angleEquations
        source

theorem oppositePlaceNext_roleAnglePortPair_sqDist
    (source : LocalVertex -> R2)
    {u v : LocalVertex}
    (hpair : RoleHingeAngleCertificates.IsRoleAnglePortPair u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hpair with h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.p_ports_exactLocalSqDist_of_angleEquations_realizes
        RoleHingeConcreteSearch.oppositePlaceNext
        RoleHingeConcreteSearch.oppositeRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.oppositeRoleAngle)
        RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations
        source
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.p_ports_exactLocalSqDist_symm_of_angleEquations_realizes
        RoleHingeConcreteSearch.oppositePlaceNext
        RoleHingeConcreteSearch.oppositeRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.oppositeRoleAngle)
        RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations
        source
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.q_ports_exactLocalSqDist_of_angleEquations_realizes
        RoleHingeConcreteSearch.oppositePlaceNext
        RoleHingeConcreteSearch.oppositeRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.oppositeRoleAngle)
        RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations
        source
  · rcases h with ⟨rfl, rfl⟩
    exact
      RoleHingeAngleCertificates.q_ports_exactLocalSqDist_symm_of_angleEquations_realizes
        RoleHingeConcreteSearch.oppositePlaceNext
        RoleHingeConcreteSearch.oppositeRoleAngle
        (RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role
          RoleHingeConcreteSearch.oppositeRoleAngle)
        RoleHingeConcreteSearch.oppositeRoleAngle_angleEquations
        source

/-- Same branch: every possible matrix row is discharged by the concrete map on
any exact-local source block. -/
theorem samePlaceNext_possibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hpossible : IsPossibleExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hpossible with hdiag | hinherited | hpair
  · exact
      RoleHingeExactLocalFinite.samePlaceNext_eq_or_unmoved_sqDist
        hsource (Or.inl hdiag)
  · exact
      RoleHingeExactLocalFinite.samePlaceNext_eq_or_unmoved_sqDist
        hsource (Or.inr hinherited)
  · exact samePlaceNext_roleAnglePortPair_sqDist source hpair

/-- Opposite branch: every possible matrix row is discharged by the concrete
map on any exact-local source block. -/
theorem oppositePlaceNext_possibleRow_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hpossible : IsPossibleExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hpossible with hdiag | hinherited | hpair
  · exact
      RoleHingeExactLocalFinite.oppositePlaceNext_eq_or_unmoved_sqDist
        hsource (Or.inl hdiag)
  · exact
      RoleHingeExactLocalFinite.oppositePlaceNext_eq_or_unmoved_sqDist
        hsource (Or.inr hinherited)
  · exact oppositePlaceNext_roleAnglePortPair_sqDist source hpair

/-- The row `T1_1,r` is outside the possible matrix. -/
theorem not_possible_T1_1_r :
    Not (IsPossibleExactLocalRow T1_1 LocalVertex.r) := by
  intro hpossible
  rcases hpossible with hdiag | hinherited | hpair
  · cases hdiag
  · exact hinherited.left (Or.inl rfl)
  · exact
      RoleHingeExactLocalFinite.not_isRoleAnglePortPair_T1_1_r hpair

/-- Same branch: the row `T1_1,r` forces the concrete exact-base
contradiction used by the older non-port-pair obstruction. -/
theorem samePlaceNext_exactBase_T1_1_r_forces_contradiction :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint T1_1)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint LocalVertex.r) ≠
      ((ExactLocalGeometry.localNorm4 T1_1 LocalVertex.r : Int) : Real) / 4 :=
  RoleHingeExactLocalFinite.samePlaceNext_exactBase_T1_1_r_sqDist_ne_exactLocal

/-- Opposite branch: the same row is also an exact-base obstruction, because
both concrete branches place `T1_1` with the same `pToUpper` arm. -/
theorem oppositePlaceNext_exactBase_T1_1_r_forces_contradiction :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint T1_1)
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint LocalVertex.r) ≠
      ((ExactLocalGeometry.localNorm4 T1_1 LocalVertex.r : Int) : Real) / 4 := by
  simpa [RoleHingeConcreteSearch.samePlaceNext,
    RoleHingeConcreteSearch.oppositePlaceNext,
    RoleHingeConcreteSearch.concreteRoleHingePlace,
    RoleHingeConcreteSearch.sameRoleAngle,
    RoleHingeConcreteSearch.oppositeRoleAngle,
    T, T1_1, T2_2] using
      RoleHingeExactLocalFinite.samePlaceNext_exactBase_T1_1_r_sqDist_ne_exactLocal

/-- The same branch satisfies every possible row on the exact base. -/
theorem samePlaceNext_exactBase_possibleRow_sqDist
    {u v : LocalVertex}
    (hpossible : IsPossibleExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint u)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  samePlaceNext_possibleRow_sqDist
    RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
    hpossible

/-- The opposite branch satisfies every possible row on the exact base. -/
theorem oppositePlaceNext_exactBase_possibleRow_sqDist
    {u v : LocalVertex}
    (hpossible : IsPossibleExactLocalRow u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint u)
        (RoleHingeConcreteSearch.oppositePlaceNext
          ExactLocalGeometry.localPoint v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  oppositePlaceNext_possibleRow_sqDist
    RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
    hpossible

end ExactLocalTransitionObligationMatrix
end PachToth
end ErdosProblems1066

end
