import ErdosProblems1066.PachToth.TailPolynomialLowerProofW15

set_option autoImplicit false

/-!
# W16 small row two and three adapters

This file packages the length-two and length-three rows in the same
generated-point block-pair spelling used by the tail route, then repacks them
as the existing W10 small-row ledgers consumed by W15.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallRowsTwoThreeW16

noncomputable section

abbrev PeriodCandidateFamily :=
  TailPolynomialLowerProofW15.PeriodCandidateFamily

abbrev RoleHingedPeriodSearchFamily :=
  TailPolynomialLowerProofW15.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  TailPolynomialLowerProofW15.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  TailPolynomialLowerProofW15.IndexedCyclicConnectorPair hk i u j v

def twoPositive : 0 < 2 :=
  ConcreteValueCertificateExamples.twoPositive

def threePositive : 0 < 3 :=
  LengthTwoThreeCaseW10.threePositive

/-! ## Generated-point block-pair small rows -/

structure LengthTwoBlockPairGeneratedPointInequalities
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one_lt :
    forall (i : Fin 2) (u : LocalVertexIndex)
      (j : Fin 2) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair twoPositive i u j v) ->
            1 <=
              GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                F twoPositive i u j v

structure LengthThreeBlockPairGeneratedPointInequalities
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one_lt :
    forall (i : Fin 3) (u : LocalVertexIndex)
      (j : Fin 3) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair threePositive i u j v) ->
            1 <=
              GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
                F threePositive i u j v

structure LengthTwoThreeBlockPairGeneratedPointInequalities
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwo : LengthTwoBlockPairGeneratedPointInequalities F
  lengthThree : LengthThreeBlockPairGeneratedPointInequalities F

/-! ## Adapters to the W10 row ledgers -/

def lengthTwoMissingOfBlockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthTwoBlockPairGeneratedPointInequalities F) :
    LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities F where
  inequality := by
    intro u v hnot_connector
    have hge := H.polynomial_ge_one_lt
      (0 : Fin 2) u (1 : Fin 2) v (by norm_num) hnot_connector
    simpa [ConcreteValueCertificateExamples.lengthTwoPosition,
      GeneratedPolynomialLowerTableRoute.indexedGeneratedSqPolynomial_eq_generatedPoint]
      using hge

def lengthThreeMissingOfBlockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthThreeBlockPairGeneratedPointInequalities F) :
    LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities F where
  inequality01 := by
    intro u v hnot_connector
    have hge := H.polynomial_ge_one_lt
      (0 : Fin 3) u (1 : Fin 3) v (by norm_num) hnot_connector
    simpa [LengthTwoThreeCaseW10.lengthThreePosition01,
      GeneratedPolynomialLowerTableRoute.indexedGeneratedSqPolynomial_eq_generatedPoint]
      using hge
  inequality02 := by
    intro u v hnot_connector
    have hge := H.polynomial_ge_one_lt
      (0 : Fin 3) u (2 : Fin 3) v (by norm_num) hnot_connector
    simpa [LengthTwoThreeCaseW10.lengthThreePosition02,
      GeneratedPolynomialLowerTableRoute.indexedGeneratedSqPolynomial_eq_generatedPoint]
      using hge
  inequality12 := by
    intro u v hnot_connector
    have hge := H.polynomial_ge_one_lt
      (1 : Fin 3) u (2 : Fin 3) v (by norm_num) hnot_connector
    simpa [LengthTwoThreeCaseW10.lengthThreePosition12,
      GeneratedPolynomialLowerTableRoute.indexedGeneratedSqPolynomial_eq_generatedPoint]
      using hge

def lengthTwoThreeMissingOfBlockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthTwoThreeBlockPairGeneratedPointInequalities F) :
    LengthTwoThreeCaseW10.LengthTwoThreeMissingNonConnectorInequalities F where
  lengthTwo :=
    lengthTwoMissingOfBlockPairGeneratedPointInequalities H.lengthTwo
  lengthThree :=
    lengthThreeMissingOfBlockPairGeneratedPointInequalities H.lengthThree

theorem lengthTwo_polynomial_ge_one_of_blockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthTwoBlockPairGeneratedPointInequalities F)
    (p : LengthTwoThreeCaseW10.UpperTrianglePosition 2)
    (hp : LengthTwoThreeCaseW10.PositionNonConnector twoPositive p) :
    1 <= p.polynomial F twoPositive :=
  LengthTwoThreeCaseW10.lengthTwo_polynomial_ge_one_of_missing F
    (lengthTwoMissingOfBlockPairGeneratedPointInequalities H) p hp

theorem lengthThree_polynomial_ge_one_of_blockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthThreeBlockPairGeneratedPointInequalities F)
    (p : LengthTwoThreeCaseW10.UpperTrianglePosition 3)
    (hp : LengthTwoThreeCaseW10.PositionNonConnector threePositive p) :
    1 <= p.polynomial F threePositive :=
  LengthTwoThreeCaseW10.lengthThree_polynomial_ge_one_of_missing F
    (lengthThreeMissingOfBlockPairGeneratedPointInequalities H) p hp

/-! ## Candidate-family handoff to W15 -/

abbrev CandidateLengthTwoBlockPairGeneratedPointInequalities
    (F : PeriodCandidateFamily) : Prop :=
  LengthTwoBlockPairGeneratedPointInequalities
    F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthThreeBlockPairGeneratedPointInequalities
    (F : PeriodCandidateFamily) : Prop :=
  LengthThreeBlockPairGeneratedPointInequalities
    F.toRoleHingedPeriodSearchFamily

structure CandidateLengthTwoThreeBlockPairGeneratedPointInequalities
    (F : PeriodCandidateFamily) where
  lengthTwo : CandidateLengthTwoBlockPairGeneratedPointInequalities F
  lengthThree : CandidateLengthThreeBlockPairGeneratedPointInequalities F

def candidateLengthTwoMissingOfBlockPairGeneratedPointInequalities
    {F : PeriodCandidateFamily}
    (H : CandidateLengthTwoBlockPairGeneratedPointInequalities F) :
    LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  lengthTwoMissingOfBlockPairGeneratedPointInequalities H

def candidateLengthThreeMissingOfBlockPairGeneratedPointInequalities
    {F : PeriodCandidateFamily}
    (H : CandidateLengthThreeBlockPairGeneratedPointInequalities F) :
    LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  lengthThreeMissingOfBlockPairGeneratedPointInequalities H

def candidateLengthTwoThreeMissingOfBlockPairGeneratedPointInequalities
    {F : PeriodCandidateFamily}
    (H : CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F) :
    LengthTwoThreeCaseW10.LengthTwoThreeMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily where
  lengthTwo :=
    candidateLengthTwoMissingOfBlockPairGeneratedPointInequalities H.lengthTwo
  lengthThree :=
    candidateLengthThreeMissingOfBlockPairGeneratedPointInequalities H.lengthThree

def exactMissingFieldsOfSmallRowsTwoThreeAndBlockPairInequalities
    {F : PeriodCandidateFamily}
    (smallRows :
      CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F)
    (lengthFour :
      LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthFive :
      LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (tail : TailPolynomialLowerProofW15.CandidateTailBlockPairInequalities F) :
    AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields F :=
  TailPolynomialLowerProofW15.exactMissingFieldsOfBlockPairInequalities
    (candidateLengthTwoMissingOfBlockPairGeneratedPointInequalities
      smallRows.lengthTwo)
    (candidateLengthThreeMissingOfBlockPairGeneratedPointInequalities
      smallRows.lengthThree)
    lengthFour lengthFive tail

end

end SmallRowsTwoThreeW16
end PachToth
end ErdosProblems1066
