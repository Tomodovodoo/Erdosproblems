import ErdosProblems1066.PachToth.AllPositivePolynomialLowerTableW14
import ErdosProblems1066.PachToth.GeneratedPolynomialLowerTableRoute
import ErdosProblems1066.PachToth.GeneratedPointPolynomialFacts

set_option autoImplicit false

/-!
# W15 tail polynomial lower-proof surface

This file owns only the `5 < k` tail interface.  It does not assert an
endpoint theorem.  Instead it records checked adapters from explicit
upper-triangle, non-connector generated-point polynomial inequalities to the
row-local `MissingNonConnectorRows` consumed by the W14 all-positive table.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TailPolynomialLowerProofW15

noncomputable section

abbrev PeriodCandidateFamily :=
  AllPositivePolynomialLowerTableW14.PeriodCandidateFamily

abbrev RoleHingedPeriodSearchFamily :=
  NonConnectorTableConcreteW14.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  NonConnectorTableConcreteW14.LocalVertexIndex

abbrev UpperTrianglePosition :=
  NonConnectorTableConcreteW14.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  NonConnectorTableConcreteW14.PositionNonConnector hk p

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  NonConnectorTableConcreteW14.IndexedCyclicConnectorPair hk i u j v

abbrev NonConnectorRow :=
  NonConnectorTableConcreteW14.NonConnectorRow

abbrev MissingNonConnectorRows :=
  NonConnectorTableConcreteW14.MissingNonConnectorRows

abbrev SmallLengthRowsWithTail :=
  AllPositivePolynomialLowerTableW14.SmallLengthRowsWithTail

/-! ## Tail row spellings -/

/-- Generated-point spelling of the polynomial attached to a packed row. -/
def rowGeneratedPointPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (row : NonConnectorRow k hk) : Real :=
  GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
    F hk row.left row.leftVertex row.right row.rightVertex

@[simp]
theorem rowGeneratedPointPolynomial_eq_polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (row : NonConnectorRow k hk) :
    rowGeneratedPointPolynomial F hk row = row.polynomial F := by
  rfl

/-- Tail rows stated directly in the packed-row generated-point spelling.

Every field is still an explicit algebraic lower-bound obligation; this
structure only records that the obligations are needed for block counts
strictly larger than five. -/
structure TailGeneratedPointRowInequalities
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one :
    forall (k : Nat) (hk : 0 < k), 5 < k ->
      forall row : NonConnectorRow k hk,
        1 <= rowGeneratedPointPolynomial F hk row

namespace TailGeneratedPointRowInequalities

/-- Checked adapter from packed generated-point tail rows to the exact W14
tail row family. -/
def toMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (T : TailGeneratedPointRowInequalities F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    MissingNonConnectorRows F k hk where
  inequality := by
    intro row
    simpa using T.polynomial_ge_one k hk hgt row

theorem row_polynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (T : TailGeneratedPointRowInequalities F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k)
    (row : NonConnectorRow k hk) :
    1 <= row.polynomial F := by
  simpa using T.polynomial_ge_one k hk hgt row

end TailGeneratedPointRowInequalities

/-! ## Block-pair algebraic inequality form -/

/-- Tail obligations expanded to the concrete block-pair and local-vertex
indices.  This is the smallest generated-point algebraic target for the
`5 < k` part: strict upper-triangle block pairs only, and only when the pair
is not a cyclic connector pair. -/
structure TailBlockPairGeneratedPointInequalities
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one_lt :
    forall (k : Nat) (hk : 0 < k), 5 < k ->
      forall (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                  F hk i u j v

namespace TailBlockPairGeneratedPointInequalities

/-- Repack the explicit block-pair algebraic inequalities as packed row
inequalities. -/
def toRowInequalities
    {F : RoleHingedPeriodSearchFamily}
    (T : TailBlockPairGeneratedPointInequalities F) :
    TailGeneratedPointRowInequalities F where
  polynomial_ge_one := by
    intro k hk hgt row
    exact T.polynomial_ge_one_lt k hk hgt
      row.left row.leftVertex row.right row.rightVertex
      row.left_lt_right row.not_connector

/-- Checked adapter from explicit block-pair algebraic tail inequalities to
the exact W14 tail row family. -/
def toMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (T : TailBlockPairGeneratedPointInequalities F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    MissingNonConnectorRows F k hk :=
  T.toRowInequalities.toMissingRows k hk hgt

/-- The same tail facts in the generated-polynomial route table spelling for
one fixed tail block count. -/
def toGeneratedPointTable
    {F : RoleHingedPeriodSearchFamily}
    (T : TailBlockPairGeneratedPointInequalities F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable
      F k hk where
  polynomial_ge_one_lt := T.polynomial_ge_one_lt k hk hgt

theorem row_polynomial_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (T : TailBlockPairGeneratedPointInequalities F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k)
    (row : NonConnectorRow k hk) :
    1 <= row.polynomial F := by
  exact T.toRowInequalities.row_polynomial_ge_one k hk hgt row

end TailBlockPairGeneratedPointInequalities

/-! ## Candidate-family tail handoff -/

/-- Tail algebraic inequalities for an all-positive period candidate. -/
abbrev CandidateTailBlockPairInequalities
    (F : PeriodCandidateFamily) : Prop :=
  TailBlockPairGeneratedPointInequalities
    F.toRoleHingedPeriodSearchFamily

/-- Candidate-tail rows in the exact `SmallLengthRowsWithTail.tail` shape
expected by `AllPositivePolynomialLowerTableW14`. -/
def candidateTailRowsOfBlockPairInequalities
    {F : PeriodCandidateFamily}
    (T : CandidateTailBlockPairInequalities F) :
    forall (k : Nat) (hk : 0 < k), 5 < k ->
      MissingNonConnectorRows F.toRoleHingedPeriodSearchFamily k hk :=
  fun k hk hgt => T.toMissingRows k hk hgt

/-- Assemble W14's small-length-plus-tail reducer from existing small-length
rows and explicit tail algebraic inequalities.  This stops at the checked W14
field adapter and deliberately makes no endpoint claim. -/
def smallLengthRowsWithTailOfBlockPairInequalities
    {F : PeriodCandidateFamily}
    (lengthTwo :
      LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthThree :
      LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFour :
      LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFive :
      LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (tail : CandidateTailBlockPairInequalities F) :
    SmallLengthRowsWithTail F where
  lengthTwo := lengthTwo
  lengthThree := lengthThree
  lengthFour := lengthFour
  lengthFive := lengthFive
  tail := candidateTailRowsOfBlockPairInequalities tail

/-- The checked W14 exact-missing field adapter obtained from the small rows
and the explicit `5 < k` algebraic tail inequalities. -/
def exactMissingFieldsOfBlockPairInequalities
    {F : PeriodCandidateFamily}
    (lengthTwo :
      LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthThree :
      LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFour :
      LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFive :
      LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (tail : CandidateTailBlockPairInequalities F) :
    AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields F :=
  (smallLengthRowsWithTailOfBlockPairInequalities
    lengthTwo lengthThree lengthFour lengthFive tail).toFields

end

end TailPolynomialLowerProofW15
end PachToth
end ErdosProblems1066
