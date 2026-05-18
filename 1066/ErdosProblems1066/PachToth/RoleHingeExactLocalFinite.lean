import ErdosProblems1066.PachToth.RoleHingeAngleCertificates
import ErdosProblems1066.PachToth.RoleHingeConcreteSearch
import ErdosProblems1066.PachToth.RoleHingeSameBlockAlgebra

set_option autoImplicit false

/-!
# Finite exact-local rows for the concrete role-hinge maps

The equilateral role-angle reducer in `RoleHingeAngleCertificates` leaves a
finite same-block squared-distance obligation for every non-port-pair row.
This file records the concrete rows that are forced immediately by the
four-target shape of `RoleHingeConcreteSearch.concreteRoleHingePlace`, and it
also exposes a concrete row obstruction for the current placeholder map.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeExactLocalFinite

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole

/-- The four labels moved by `concreteRoleHingePlace`. -/
def IsConcreteRoleHingePortTarget (v : LocalVertex) : Prop :=
  v = T1_1 \/ v = T1_2 \/ v = T0_0 \/ v = T0_2

theorem not_isRoleAnglePortPair_of_not_portTarget_left
    {u v : LocalVertex}
    (hu : Not (IsConcreteRoleHingePortTarget u)) :
    Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) := by
  intro hpair
  rcases hpair with h | h | h | h
  · exact hu (Or.inl h.left)
  · exact hu (Or.inr (Or.inl h.left))
  · exact hu (Or.inr (Or.inr (Or.inl h.left)))
  · exact hu (Or.inr (Or.inr (Or.inr h.left)))

theorem not_isRoleAnglePortPair_of_not_portTarget_right
    {u v : LocalVertex}
    (hv : Not (IsConcreteRoleHingePortTarget v)) :
    Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) := by
  intro hpair
  rcases hpair with h | h | h | h
  · exact hv (Or.inr (Or.inl h.right))
  · exact hv (Or.inl h.right)
  · exact hv (Or.inr (Or.inr (Or.inr h.right)))
  · exact hv (Or.inr (Or.inr (Or.inl h.right)))

/-- Diagonal rows are never one of the angle-controlled port pairs. -/
theorem not_isRoleAnglePortPair_self
    (u : LocalVertex) :
    Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u u) := by
  intro hpair
  rcases hpair with h | h | h | h
  · cases h.left
    cases h.right
  · cases h.left
    cases h.right
  · cases h.left
    cases h.right
  · cases h.left
    cases h.right

/-- A non-target label is copied unchanged by the concrete role-hinge map. -/
theorem concreteRoleHingePlace_eq_source_of_not_portTarget
    (angle : ConnectorRole -> Real) (source : LocalVertex -> R2)
    {v : LocalVertex}
    (hv : Not (IsConcreteRoleHingePortTarget v)) :
    RoleHingeConcreteSearch.concreteRoleHingePlace angle source v =
      source v := by
  cases v with
  | r =>
      rfl
  | tri t c =>
      fin_cases t <;> fin_cases c <;>
        simp [IsConcreteRoleHingePortTarget,
          RoleHingeConcreteSearch.concreteRoleHingePlace,
          T, T0_0, T0_2, T1_1, T1_2] at hv ⊢

/-- The exact local integer squared-distance table has zero diagonal. -/
theorem exactLocalNorm4_self
    (u : LocalVertex) :
    (((ExactLocalGeometry.localNorm4 u u : Int) : Real) / 4) = 0 := by
  simp [ExactLocalGeometry.localNorm4, ExactLocalGeometry.GridPoint.norm4]

/-- Every diagonal row of a concrete role-hinge output block is exact-local. -/
theorem concreteRoleHingePlace_self_sqDist
    (angle : ConnectorRole -> Real) (source : LocalVertex -> R2)
    (u : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.concreteRoleHingePlace angle source u)
        (RoleHingeConcreteSearch.concreteRoleHingePlace angle source u) =
      ((ExactLocalGeometry.localNorm4 u u : Int) : Real) / 4 := by
  rw [exactLocalNorm4_self]
  simp [RoleHingeSameBlockAlgebra.sqDist]

/-- Non-port-target rows are inherited from any exact-local source block. -/
theorem concreteRoleHingePlace_unmoved_sqDist
    (angle : ConnectorRole -> Real) {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hu : Not (IsConcreteRoleHingePortTarget u))
    (hv : Not (IsConcreteRoleHingePortTarget v)) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.concreteRoleHingePlace angle source u)
        (RoleHingeConcreteSearch.concreteRoleHingePlace angle source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rw [concreteRoleHingePlace_eq_source_of_not_portTarget angle source hu,
    concreteRoleHingePlace_eq_source_of_not_portTarget angle source hv]
  exact hsource u v

/-- Same-branch inherited non-port-target rows. -/
theorem samePlaceNext_unmoved_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hu : Not (IsConcreteRoleHingePortTarget u))
    (hv : Not (IsConcreteRoleHingePortTarget v)) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  exact
    concreteRoleHingePlace_unmoved_sqDist
      RoleHingeConcreteSearch.sameRoleAngle hsource hu hv

/-- Opposite-branch inherited non-port-target rows. -/
theorem oppositePlaceNext_unmoved_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hu : Not (IsConcreteRoleHingePortTarget u))
    (hv : Not (IsConcreteRoleHingePortTarget v)) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  exact
    concreteRoleHingePlace_unmoved_sqDist
      RoleHingeConcreteSearch.oppositeRoleAngle hsource hu hv

/-- Same-branch rows covered by either diagonal triviality or unchanged labels. -/
theorem samePlaceNext_eq_or_unmoved_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow :
      u = v \/
        (Not (IsConcreteRoleHingePortTarget u) /\
          Not (IsConcreteRoleHingePortTarget v))) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hrow with hdiag | hfree
  · subst v
    exact
      concreteRoleHingePlace_self_sqDist
        RoleHingeConcreteSearch.sameRoleAngle source u
  · exact samePlaceNext_unmoved_sqDist hsource hfree.left hfree.right

/-- Opposite-branch rows covered by either diagonal triviality or unchanged labels. -/
theorem oppositePlaceNext_eq_or_unmoved_sqDist
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow :
      u = v \/
        (Not (IsConcreteRoleHingePortTarget u) /\
          Not (IsConcreteRoleHingePortTarget v))) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 := by
  rcases hrow with hdiag | hfree
  · subst v
    exact
      concreteRoleHingePlace_self_sqDist
        RoleHingeConcreteSearch.oppositeRoleAngle source u
  · exact oppositePlaceNext_unmoved_sqDist hsource hfree.left hfree.right

/-- The row `T1_1,r` is not angle-controlled. -/
theorem not_isRoleAnglePortPair_T1_1_r :
    Not (RoleHingeAngleCertificates.IsRoleAnglePortPair T1_1 LocalVertex.r) := by
  intro hpair
  rcases hpair with h | h | h | h
  · cases h.right
  · cases h.right
  · cases h.right
  · cases h.right

theorem exactLocalNorm4_T1_1_r :
    (((ExactLocalGeometry.localNorm4 T1_1 LocalVertex.r : Int) : Real) / 4) =
      3 := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T1_1]

/-- On the exact base, the current same-branch four-target map gives a concrete
non-port-pair row value different from the exact-local table. -/
theorem samePlaceNext_exactBase_T1_1_r_sqDist :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint T1_1)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint LocalVertex.r) =
      10 + 3 * Real.sqrt 3 := by
  norm_num [RoleHingeConcreteSearch.samePlaceNext,
    RoleHingeConcreteSearch.concreteRoleHingePlace,
    RoleHingeConcreteSearch.sameRoleAngle,
    RoleHingeSameBlockAlgebra.sqDist,
    UnitVectorGeometry.hingePoint, UnitVectorGeometry.add,
    UnitVectorGeometry.unitVec,
    ExactLocalGeometry.localPoint, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.toPoint, ExactLocalGeometry.h,
    T, T1_1, T2_2]
  ring_nf
  rw [Real.sq_sqrt]
  · ring_nf
  · norm_num

theorem samePlaceNext_exactBase_T1_1_r_sqDist_ne_exactLocal :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint T1_1)
        (RoleHingeConcreteSearch.samePlaceNext
          ExactLocalGeometry.localPoint LocalVertex.r) ≠
      ((ExactLocalGeometry.localNorm4 T1_1 LocalVertex.r : Int) : Real) / 4 := by
  rw [samePlaceNext_exactBase_T1_1_r_sqDist,
    exactLocalNorm4_T1_1_r]
  intro h
  nlinarith [Real.sqrt_nonneg (3 : Real)]

/-- The exact `same_rest` argument required by
`sameOppositeExactLocal_of_equilateralRoleAngles_obligations_eq` cannot be
supplied by the current concrete same-branch four-target map. -/
theorem not_samePlaceNext_full_nonPortPair_rest :
    Not
      (forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (RoleHingeConcreteSearch.samePlaceNext source u)
                  (RoleHingeConcreteSearch.samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) := by
  intro hrest
  have hrow :=
    hrest ExactLocalGeometry.localPoint
      RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
      T1_1 LocalVertex.r not_isRoleAnglePortPair_T1_1_r
  exact samePlaceNext_exactBase_T1_1_r_sqDist_ne_exactLocal hrow

end RoleHingeExactLocalFinite
end PachToth
end ErdosProblems1066

end
