import ErdosProblems1066.PachToth.TailPolynomialLowerProofW15
import ErdosProblems1066.PachToth.GeneratedPointPolynomialFacts

set_option autoImplicit false

/-!
# W16 tail polynomial rows

This module keeps the `5 < k` row work in one place.  It proves the W15
tail block-pair field from three checked sources: packed W14 row families,
generated-point metric facts, and explicit computed-value rows.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TailPolynomialRowsW16

noncomputable section

open GeneratedPointPolynomialFacts

abbrev RoleHingedPeriodSearchFamily :=
  TailPolynomialLowerProofW15.RoleHingedPeriodSearchFamily

abbrev PeriodCandidateFamily :=
  TailPolynomialLowerProofW15.PeriodCandidateFamily

abbrev LocalVertexIndex :=
  TailPolynomialLowerProofW15.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  TailPolynomialLowerProofW15.IndexedCyclicConnectorPair hk i u j v

abbrev NonConnectorRow :=
  TailPolynomialLowerProofW15.NonConnectorRow

abbrev MissingNonConnectorRows :=
  TailPolynomialLowerProofW15.MissingNonConnectorRows

abbrev TailBlockPairGeneratedPointInequalities :=
  TailPolynomialLowerProofW15.TailBlockPairGeneratedPointInequalities

abbrev CandidateTailBlockPairInequalities :=
  TailPolynomialLowerProofW15.CandidateTailBlockPairInequalities

abbrev SmallLengthRowsWithTail :=
  TailPolynomialLowerProofW15.SmallLengthRowsWithTail

abbrev TailPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
    F hk i u j v

abbrev TailPolynomialLowerTarget
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  forall (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex),
      i.val < j.val ->
        Not (IndexedCyclicConnectorPair hk i u j v) ->
          1 <= TailPolynomial F hk i u j v

/-! ## Generated-point normal forms -/

theorem tailPolynomial_eq_normalizedGeneratedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    TailPolynomial F hk i u j v =
      GeneratedPointPolynomialFacts.normalizedGeneratedPointSqPolynomial
        F.transitions.toFigure2TransitionObligations
        hk BaseTransitionRealization.exactBase (F.orientation k hk)
        i (CrossBlockLowerBoundsInterface.localVertexOfIndex u)
        j (CrossBlockLowerBoundsInterface.localVertexOfIndex v) := by
  rw [TailPolynomial]
  rw [(GeneratedPolynomialLowerTableRoute.indexedGeneratedSqPolynomial_eq_generatedPoint
    F hk i u j v).symm]
  exact
    GeneratedPointPolynomialFacts.indexedGeneratedSqPolynomial_eq_normalizedGeneratedPoint
      F hk i u j v

theorem indexedEucDist_ge_one_iff_tailPolynomial_ge_one
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    1 <=
        _root_.eucDist
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v) <->
      1 <= TailPolynomial F hk i u j v := by
  rw [tailPolynomial_eq_normalizedGeneratedPoint F hk i u j v]
  exact one_le_indexedGenerated_eucDist_iff_one_le_normalizedGeneratedPoint
    F hk i u j v

theorem polynomial_ge_one_lt_of_indexedEucDist
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertexIndex}
    {j : Fin k} {v : LocalVertexIndex}
    (h :
      1 <=
        _root_.eucDist
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk i u)
          (CrossBlockLowerBoundsInterface.indexedGeneratedPoint F hk j v)) :
    1 <= TailPolynomial F hk i u j v :=
  (indexedEucDist_ge_one_iff_tailPolynomial_ge_one F hk i u j v).1 h

/-! ## Adapters from W14 packed rows -/

theorem polynomial_ge_one_lt_of_missingRows
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (R : MissingNonConnectorRows F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= TailPolynomial F hk i u j v := by
  have hrow :=
    R.inequality
      ({ left := i
         leftVertex := u
         right := j
         rightVertex := v
         left_lt_right := hlt
         not_connector := hnot } :
        NonConnectorTableConcreteW14.NonConnectorRow k hk)
  simpa [TailPolynomial, NonConnectorTableConcreteW14.NonConnectorRow.polynomial,
    NonConnectorTableConcreteW14.NonConnectorRow.toUpperTrianglePosition]
    using hrow

def blockPairInequalitiesOfMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (R :
      forall (k : Nat) (hk : 0 < k), 5 < k ->
        MissingNonConnectorRows F k hk) :
    TailBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact polynomial_ge_one_lt_of_missingRows
      (R k hk hgt) i u j v hlt hnot

def generatedPointTableOfMissingRows
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (R : MissingNonConnectorRows F k hk) :
    GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable
      F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    exact polynomial_ge_one_lt_of_missingRows R i u j v hlt hnot

def tailGeneratedPointTableOfMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (R :
      forall (k : Nat) (hk : 0 < k), 5 < k ->
        MissingNonConnectorRows F k hk)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable
      F k hk :=
  generatedPointTableOfMissingRows (R k hk hgt)

/-! ## Explicit value-row target -/

structure TailValueRows
    (F : RoleHingedPeriodSearchFamily) where
  value :
    forall (k : Nat) (_hk : 0 < k), 5 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k) (hgt : 5 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            value k hk hgt i u j v = TailPolynomial F hk i u j v
  value_ge_one_lt :
    forall (k : Nat) (hk : 0 < k) (hgt : 5 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= value k hk hgt i u j v

namespace TailValueRows

theorem polynomial_ge_one_lt
    {F : RoleHingedPeriodSearchFamily}
    (V : TailValueRows F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= TailPolynomial F hk i u j v := by
  have hvalue := V.value_ge_one_lt k hk hgt i u j v hlt hnot
  have hpoly := V.value_eq_polynomial_lt k hk hgt i u j v hlt hnot
  simpa [hpoly] using hvalue

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (V : TailValueRows F) :
    TailBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro k hk hgt i u j v hlt hnot
    exact V.polynomial_ge_one_lt k hk hgt i u j v hlt hnot

def toGeneratedPointTable
    {F : RoleHingedPeriodSearchFamily}
    (V : TailValueRows F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable
      F k hk where
  polynomial_ge_one_lt := V.polynomial_ge_one_lt k hk hgt

def toMissingRows
    {F : RoleHingedPeriodSearchFamily}
    (V : TailValueRows F)
    (k : Nat) (hk : 0 < k) (hgt : 5 < k) :
    MissingNonConnectorRows F k hk :=
  V.toBlockPairInequalities.toMissingRows k hk hgt

end TailValueRows

/-! ## Candidate handoff through W15 and W14 -/

def candidateTailRowsOfMissingRows
    {F : PeriodCandidateFamily}
    (R :
      forall (k : Nat) (hk : 0 < k), 5 < k ->
        MissingNonConnectorRows F.toRoleHingedPeriodSearchFamily k hk) :
    CandidateTailBlockPairInequalities F :=
  blockPairInequalitiesOfMissingRows R

def smallLengthRowsWithTailOfMissingRows
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
    (tail :
      forall (k : Nat) (hk : 0 < k), 5 < k ->
        MissingNonConnectorRows F.toRoleHingedPeriodSearchFamily k hk) :
    SmallLengthRowsWithTail F :=
  TailPolynomialLowerProofW15.smallLengthRowsWithTailOfBlockPairInequalities
    lengthTwo lengthThree lengthFour lengthFive
    (candidateTailRowsOfMissingRows tail)

def exactMissingFieldsOfMissingRows
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
    (tail :
      forall (k : Nat) (hk : 0 < k), 5 < k ->
        MissingNonConnectorRows F.toRoleHingedPeriodSearchFamily k hk) :
    AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields F :=
  (smallLengthRowsWithTailOfMissingRows
    lengthTwo lengthThree lengthFour lengthFive tail).toFields

end

end TailPolynomialRowsW16
end PachToth
end ErdosProblems1066
