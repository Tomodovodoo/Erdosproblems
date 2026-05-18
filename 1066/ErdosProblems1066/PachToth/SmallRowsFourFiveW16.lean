import ErdosProblems1066.PachToth.TailPolynomialLowerProofW15

set_option autoImplicit false

/-!
# W16 small rows four and five

This file packages the `k = 4` and `k = 5` non-connector rows in the same
generated-point block-pair spelling used by the W15 tail handoff.  The checked
adapters below convert those compact block-pair inequalities into the W11
enumerated length-four and length-five ledgers consumed by
`TailPolynomialLowerProofW15.exactMissingFieldsOfBlockPairInequalities`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallRowsFourFiveW16

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

abbrev LengthFourMissingNonConnectorInequalities :=
  LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities

abbrev LengthFiveMissingNonConnectorInequalities :=
  LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities

abbrev LengthTwoMissingNonConnectorInequalities :=
  LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities

abbrev LengthThreeMissingNonConnectorInequalities :=
  LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities

abbrev CandidateTailBlockPairInequalities :=
  TailPolynomialLowerProofW15.CandidateTailBlockPairInequalities

abbrev ExactMissingConcreteTableFields :=
  AllPositiveFiniteFieldsW14.ExactMissingConcreteTableFields

def generatedPointPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
    F hk i u j v

structure LengthFourBlockPairGeneratedPointInequalities
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one_lt :
    forall (i : Fin 4) (u : LocalVertexIndex)
      (j : Fin 4) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair
            LengthFourFiveCaseW11.fourPositive i u j v) ->
            1 <= generatedPointPolynomial
              F LengthFourFiveCaseW11.fourPositive i u j v

structure LengthFiveBlockPairGeneratedPointInequalities
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one_lt :
    forall (i : Fin 5) (u : LocalVertexIndex)
      (j : Fin 5) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair
            LengthFourFiveCaseW11.fivePositive i u j v) ->
            1 <= generatedPointPolynomial
              F LengthFourFiveCaseW11.fivePositive i u j v

structure LengthFourFiveBlockPairGeneratedPointInequalities
    (F : RoleHingedPeriodSearchFamily) where
  lengthFour : LengthFourBlockPairGeneratedPointInequalities F
  lengthFive : LengthFiveBlockPairGeneratedPointInequalities F

namespace LengthFourBlockPairGeneratedPointInequalities

def toMissingInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFourBlockPairGeneratedPointInequalities F) :
    LengthFourMissingNonConnectorInequalities F where
  inequality01 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFourPosition01,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 0 u 1 v (by norm_num) hp
  inequality02 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFourPosition02,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 0 u 2 v (by norm_num) hp
  inequality03 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFourPosition03,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 0 u 3 v (by norm_num) hp
  inequality12 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFourPosition12,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 1 u 2 v (by norm_num) hp
  inequality13 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFourPosition13,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 1 u 3 v (by norm_num) hp
  inequality23 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFourPosition23,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 2 u 3 v (by norm_num) hp

theorem polynomial_ge_one_of_position
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFourBlockPairGeneratedPointInequalities F)
    (p : LengthFourFiveCaseW11.UpperTrianglePosition 4)
    (hp :
      LengthFourFiveCaseW11.PositionNonConnector
        LengthFourFiveCaseW11.fourPositive p) :
    1 <= p.polynomial F LengthFourFiveCaseW11.fourPositive :=
  LengthFourFiveCaseW11.lengthFour_polynomial_ge_one_of_missing
    F H.toMissingInequalities p hp

end LengthFourBlockPairGeneratedPointInequalities

namespace LengthFiveBlockPairGeneratedPointInequalities

def toMissingInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFiveBlockPairGeneratedPointInequalities F) :
    LengthFiveMissingNonConnectorInequalities F where
  inequality01 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition01,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 0 u 1 v (by norm_num) hp
  inequality02 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition02,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 0 u 2 v (by norm_num) hp
  inequality03 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition03,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 0 u 3 v (by norm_num) hp
  inequality04 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition04,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 0 u 4 v (by norm_num) hp
  inequality12 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition12,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 1 u 2 v (by norm_num) hp
  inequality13 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition13,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 1 u 3 v (by norm_num) hp
  inequality14 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition14,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 1 u 4 v (by norm_num) hp
  inequality23 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition23,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 2 u 3 v (by norm_num) hp
  inequality24 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition24,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 2 u 4 v (by norm_num) hp
  inequality34 := by
    intro u v hp
    simpa [LengthFourFiveCaseW11.lengthFivePosition34,
      generatedPointPolynomial] using
      H.polynomial_ge_one_lt 3 u 4 v (by norm_num) hp

theorem polynomial_ge_one_of_position
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFiveBlockPairGeneratedPointInequalities F)
    (p : LengthFourFiveCaseW11.UpperTrianglePosition 5)
    (hp :
      LengthFourFiveCaseW11.PositionNonConnector
        LengthFourFiveCaseW11.fivePositive p) :
    1 <= p.polynomial F LengthFourFiveCaseW11.fivePositive :=
  LengthFourFiveCaseW11.lengthFive_polynomial_ge_one_of_missing
    F H.toMissingInequalities p hp

end LengthFiveBlockPairGeneratedPointInequalities

namespace LengthFourFiveBlockPairGeneratedPointInequalities

def lengthFourMissing
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFourFiveBlockPairGeneratedPointInequalities F) :
    LengthFourMissingNonConnectorInequalities F :=
  H.lengthFour.toMissingInequalities

def lengthFiveMissing
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFourFiveBlockPairGeneratedPointInequalities F) :
    LengthFiveMissingNonConnectorInequalities F :=
  H.lengthFive.toMissingInequalities

end LengthFourFiveBlockPairGeneratedPointInequalities

abbrev CandidateLengthFourBlockPairInequalities
    (F : PeriodCandidateFamily) :=
  LengthFourBlockPairGeneratedPointInequalities
    F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthFiveBlockPairInequalities
    (F : PeriodCandidateFamily) :=
  LengthFiveBlockPairGeneratedPointInequalities
    F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthFourFiveBlockPairInequalities
    (F : PeriodCandidateFamily) :=
  LengthFourFiveBlockPairGeneratedPointInequalities
    F.toRoleHingedPeriodSearchFamily

def candidateLengthFourMissing
    {F : PeriodCandidateFamily}
    (H : CandidateLengthFourBlockPairInequalities F) :
    LengthFourMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  H.toMissingInequalities

def candidateLengthFiveMissing
    {F : PeriodCandidateFamily}
    (H : CandidateLengthFiveBlockPairInequalities F) :
    LengthFiveMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  H.toMissingInequalities

def candidateLengthFourFiveMissing
    {F : PeriodCandidateFamily}
    (H : CandidateLengthFourFiveBlockPairInequalities F) :
    LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily where
  lengthFour := H.lengthFourMissing
  lengthFive := H.lengthFiveMissing

def exactMissingFieldsOfSmallRowsFourFiveAndTail
    {F : PeriodCandidateFamily}
    (lengthTwo :
      LengthTwoMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (lengthThree :
      LengthThreeMissingNonConnectorInequalities
        F.toRoleHingedPeriodSearchFamily)
    (smallRows : CandidateLengthFourFiveBlockPairInequalities F)
    (tail : CandidateTailBlockPairInequalities F) :
    ExactMissingConcreteTableFields F :=
  TailPolynomialLowerProofW15.exactMissingFieldsOfBlockPairInequalities
    lengthTwo lengthThree
    smallRows.lengthFourMissing
    smallRows.lengthFiveMissing
    tail

end

end SmallRowsFourFiveW16
end PachToth
end ErdosProblems1066
