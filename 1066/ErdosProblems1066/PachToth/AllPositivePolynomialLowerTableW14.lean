import ErdosProblems1066.PachToth.AllPositiveFiniteFieldsW14
import ErdosProblems1066.PachToth.NonConnectorTableConcreteW14

set_option autoImplicit false

/-!
# W14 all-positive polynomial lower table

This file is the replacement concrete-table surface for the all-positive
route.  It does not assert an endpoint theorem.  Instead it exposes checked
row-family reducers for the exact remaining polynomial lower-bound fields:
every consumed row is still a concrete `polynomial >= 1` obligation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AllPositivePolynomialLowerTableW14

noncomputable section

abbrev PeriodCandidateFamily :=
  AllPositiveFiniteFieldsW14.PeriodCandidateFamily

abbrev ExactMissingConcreteTableFields :=
  AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields

abbrev UpperTrianglePosition :=
  NonConnectorPolynomialCertificates.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  NonConnectorPolynomialCertificates.PositionNonConnector hk p

abbrev MissingNonConnectorRows :=
  NonConnectorTableConcreteW14.MissingNonConnectorRows

abbrev NonConnectorRow :=
  NonConnectorTableConcreteW14.NonConnectorRow

def onePositive : 0 < 1 :=
  NonConnectorTableConcreteW14.onePositive

/-! ## Exact row-family reducer -/

/-- Row-local version of `ExactMissingConcreteTableFields`.

For each positive `k`, the remaining obligations are exactly the packed
upper-triangle non-connector rows, each asking for its polynomial to be at
least `1`. -/
structure ExactMissingConcreteRowFamily
    (F : PeriodCandidateFamily) where
  rows :
    forall (k : Nat) (hk : 0 < k),
      MissingNonConnectorRows F.toRoleHingedPeriodSearchFamily k hk

namespace ExactMissingConcreteRowFamily

/-- Convert row-local obligations into the W14 exact missing table fields. -/
def toFields
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F) :
    ExactMissingConcreteTableFields F where
  polynomial_ge_one := by
    intro k hk p hp
    exact ((R.rows k hk).toPositionPolynomialCertificate).polynomial_ge_one p hp

theorem toFields_polynomial_ge_one
    {F : PeriodCandidateFamily}
    (R : ExactMissingConcreteRowFamily F)
    (k : Nat) (hk : 0 < k)
    (p : UpperTrianglePosition k)
    (hp : PositionNonConnector hk p) :
    1 <= p.polynomial F.toRoleHingedPeriodSearchFamily hk :=
  R.toFields.polynomial_ge_one k hk p hp

end ExactMissingConcreteRowFamily

/-- Any existing exact missing table fields can be read back as row-local
obligations.  This proves that the reducer does not widen the search target. -/
def rowFamilyOfFields
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    ExactMissingConcreteRowFamily F where
  rows := by
    intro k hk
    exact
      { inequality := by
          intro row
          exact D.polynomial_ge_one
            k hk row.toUpperTrianglePosition row.positionNonConnector }

@[simp]
theorem rowFamilyOfFields_toFields
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F)
    (k : Nat) (hk : 0 < k)
    (p : UpperTrianglePosition k)
    (hp : PositionNonConnector hk p) :
    (rowFamilyOfFields D).toFields.polynomial_ge_one k hk p hp =
      D.polynomial_ge_one k hk p hp :=
  rfl

/-! ## Concrete rows already closed by finite shape -/

/-- The `k = 1` row family is vacuous: there is no strict upper-triangle block
pair. -/
def lengthOneRows
    (F : PeriodCandidateFamily) :
    MissingNonConnectorRows
      F.toRoleHingedPeriodSearchFamily 1 onePositive where
  inequality := by
    intro row
    exact False.elim
      (NonConnectorTableConcreteW14.finOne_not_lt
        row.left row.right row.left_lt_right)

def lengthOnePositionPolynomialCertificate
    (F : PeriodCandidateFamily) :
    NonConnectorPolynomialCertificates.PositionPolynomialCertificate
      F.toRoleHingedPeriodSearchFamily 1 onePositive :=
  (lengthOneRows F).toPositionPolynomialCertificate

theorem lengthOne_polynomial_ge_one
    (F : PeriodCandidateFamily)
    (p : UpperTrianglePosition 1)
    (hp : PositionNonConnector onePositive p) :
    1 <= p.polynomial F.toRoleHingedPeriodSearchFamily onePositive :=
  (lengthOnePositionPolynomialCertificate F).polynomial_ge_one p hp

/-! ## Existing small-length row adapters -/

def lengthTwoRowsOfMissingInequalities
    (F : PeriodCandidateFamily)
    (H :
      LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily) :
    MissingNonConnectorRows
      F.toRoleHingedPeriodSearchFamily 2
        ConcreteValueCertificateExamples.twoPositive :=
  NonConnectorTableConcreteW14.lengthTwoRowsOfMissingInequalities
    F.toRoleHingedPeriodSearchFamily H

def lengthThreeRowsOfMissingInequalities
    (F : PeriodCandidateFamily)
    (H :
      LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily) :
    MissingNonConnectorRows
      F.toRoleHingedPeriodSearchFamily 3
        LengthTwoThreeCaseW10.threePositive :=
  NonConnectorTableConcreteW14.lengthThreeRowsOfMissingInequalities
    F.toRoleHingedPeriodSearchFamily H

def lengthFourRowsOfMissingInequalities
    (F : PeriodCandidateFamily)
    (H :
      LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily) :
    MissingNonConnectorRows
      F.toRoleHingedPeriodSearchFamily 4
        LengthFourFiveCaseW11.fourPositive :=
  NonConnectorTableConcreteW14.lengthFourRowsOfMissingInequalities
    F.toRoleHingedPeriodSearchFamily H

def lengthFiveRowsOfMissingInequalities
    (F : PeriodCandidateFamily)
    (H :
      LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily) :
    MissingNonConnectorRows
      F.toRoleHingedPeriodSearchFamily 5
        LengthFourFiveCaseW11.fivePositive :=
  NonConnectorTableConcreteW14.lengthFiveRowsOfMissingInequalities
    F.toRoleHingedPeriodSearchFamily H

/-! ## Small rows plus an exact tail -/

/-- Data needed after the existing concrete reducers have handled
`k = 1, 2, 3, 4, 5`.  The `tail` field is precisely the remaining family of
row-local polynomial inequalities for `5 < k`. -/
structure SmallLengthRowsWithTail
    (F : PeriodCandidateFamily) where
  lengthTwo :
    LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily
  lengthThree :
    LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily
  lengthFour :
    LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily
  lengthFive :
    LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily
  tail :
    forall (k : Nat) (hk : 0 < k),
      5 < k ->
        MissingNonConnectorRows F.toRoleHingedPeriodSearchFamily k hk

namespace SmallLengthRowsWithTail

/-- Assemble the exact all-positive row family from closed `k = 1`, existing
small-length reducers for `2 <= k <= 5`, and the explicit `5 < k` tail. -/
def toRowFamily
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    ExactMissingConcreteRowFamily F where
  rows := by
    intro k hk
    rcases k with _ | k
    · exact False.elim (Nat.not_lt_zero 0 hk)
    rcases k with _ | k
    · exact lengthOneRows F
    rcases k with _ | k
    · exact lengthTwoRowsOfMissingInequalities F H.lengthTwo
    rcases k with _ | k
    · exact lengthThreeRowsOfMissingInequalities F H.lengthThree
    rcases k with _ | k
    · exact lengthFourRowsOfMissingInequalities F H.lengthFour
    rcases k with _ | k
    · exact lengthFiveRowsOfMissingInequalities F H.lengthFive
    · exact H.tail _ hk (by omega)

/-- The checked finite row-family reducer for the W14 exact missing fields. -/
def toFields
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F) :
    ExactMissingConcreteTableFields F :=
  H.toRowFamily.toFields

theorem tail_polynomial_ge_one
    {F : PeriodCandidateFamily}
    (H : SmallLengthRowsWithTail F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k)
    (row : NonConnectorRow k hk) :
    1 <= row.polynomial F.toRoleHingedPeriodSearchFamily :=
  (H.tail k hk hgt).inequality row

end SmallLengthRowsWithTail

end

end AllPositivePolynomialLowerTableW14
end PachToth
end ErdosProblems1066
