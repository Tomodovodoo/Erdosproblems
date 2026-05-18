import ErdosProblems1066.PachToth.SmallRowsTwoThreeW16
import ErdosProblems1066.PachToth.SmallRowsFourFiveW16

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace SmallRowValueCertificatesW17

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

structure SmallBlockPairValueRows
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  value :
    Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            value i u j v = generatedPointPolynomial F hk i u j v
  value_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= value i u j v

namespace SmallBlockPairValueRows

theorem polynomial_ge_one_lt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (V : SmallBlockPairValueRows F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= generatedPointPolynomial F hk i u j v := by
  have hvalue := V.value_ge_one_lt i u j v hlt hnot
  have hpoly := V.value_eq_polynomial_lt i u j v hlt hnot
  simpa [hpoly] using hvalue

def toGeneratedPointTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (V : SmallBlockPairValueRows F k hk) :
    GeneratedPolynomialLowerTableRoute.GeneratedPointNonConnectorPolynomialTable
      F k hk where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    exact V.polynomial_ge_one_lt i u j v hlt hnot

end SmallBlockPairValueRows

abbrev LengthTwoValueRows
    (F : RoleHingedPeriodSearchFamily) :=
  SmallBlockPairValueRows F 2 SmallRowsTwoThreeW16.twoPositive

abbrev LengthThreeValueRows
    (F : RoleHingedPeriodSearchFamily) :=
  SmallBlockPairValueRows F 3 SmallRowsTwoThreeW16.threePositive

abbrev LengthFourValueRows
    (F : RoleHingedPeriodSearchFamily) :=
  SmallBlockPairValueRows F 4 LengthFourFiveCaseW11.fourPositive

abbrev LengthFiveValueRows
    (F : RoleHingedPeriodSearchFamily) :=
  SmallBlockPairValueRows F 5 LengthFourFiveCaseW11.fivePositive

def lengthTwoBlockPairInequalitiesOfValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthTwoValueRows F) :
    SmallRowsTwoThreeW16.LengthTwoBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    exact V.polynomial_ge_one_lt i u j v hlt hnot

def lengthThreeBlockPairInequalitiesOfValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthThreeValueRows F) :
    SmallRowsTwoThreeW16.LengthThreeBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    exact V.polynomial_ge_one_lt i u j v hlt hnot

def lengthFourBlockPairInequalitiesOfValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthFourValueRows F) :
    SmallRowsFourFiveW16.LengthFourBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    exact V.polynomial_ge_one_lt i u j v hlt hnot

def lengthFiveBlockPairInequalitiesOfValueRows
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthFiveValueRows F) :
    SmallRowsFourFiveW16.LengthFiveBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    exact V.polynomial_ge_one_lt i u j v hlt hnot

structure LengthTwoThreeValueRows
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwo : LengthTwoValueRows F
  lengthThree : LengthThreeValueRows F

namespace LengthTwoThreeValueRows

def toBlockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthTwoThreeValueRows F) :
    SmallRowsTwoThreeW16.LengthTwoThreeBlockPairGeneratedPointInequalities F
    where
  lengthTwo := lengthTwoBlockPairInequalitiesOfValueRows V.lengthTwo
  lengthThree := lengthThreeBlockPairInequalitiesOfValueRows V.lengthThree

def toMissingInequalities
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthTwoThreeValueRows F) :
    LengthTwoThreeCaseW10.LengthTwoThreeMissingNonConnectorInequalities F :=
  SmallRowsTwoThreeW16.lengthTwoThreeMissingOfBlockPairGeneratedPointInequalities
    V.toBlockPairGeneratedPointInequalities

end LengthTwoThreeValueRows

structure LengthFourFiveValueRows
    (F : RoleHingedPeriodSearchFamily) where
  lengthFour : LengthFourValueRows F
  lengthFive : LengthFiveValueRows F

namespace LengthFourFiveValueRows

def toBlockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthFourFiveValueRows F) :
    SmallRowsFourFiveW16.LengthFourFiveBlockPairGeneratedPointInequalities F
    where
  lengthFour := lengthFourBlockPairInequalitiesOfValueRows V.lengthFour
  lengthFive := lengthFiveBlockPairInequalitiesOfValueRows V.lengthFive

def toMissingInequalities
    {F : RoleHingedPeriodSearchFamily}
    (V : LengthFourFiveValueRows F) :
    LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities F
    where
  lengthFour := V.toBlockPairGeneratedPointInequalities.lengthFourMissing
  lengthFive := V.toBlockPairGeneratedPointInequalities.lengthFiveMissing

end LengthFourFiveValueRows

abbrev CandidateLengthTwoValueRows
    (F : PeriodCandidateFamily) :=
  LengthTwoValueRows F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthThreeValueRows
    (F : PeriodCandidateFamily) :=
  LengthThreeValueRows F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthFourValueRows
    (F : PeriodCandidateFamily) :=
  LengthFourValueRows F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthFiveValueRows
    (F : PeriodCandidateFamily) :=
  LengthFiveValueRows F.toRoleHingedPeriodSearchFamily

structure CandidateLengthTwoThreeValueRows
    (F : PeriodCandidateFamily) where
  lengthTwo : CandidateLengthTwoValueRows F
  lengthThree : CandidateLengthThreeValueRows F

namespace CandidateLengthTwoThreeValueRows

def toBlockPairGeneratedPointInequalities
    {F : PeriodCandidateFamily}
    (V : CandidateLengthTwoThreeValueRows F) :
    SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F
    where
  lengthTwo := lengthTwoBlockPairInequalitiesOfValueRows V.lengthTwo
  lengthThree := lengthThreeBlockPairInequalitiesOfValueRows V.lengthThree

def toMissingInequalities
    {F : PeriodCandidateFamily}
    (V : CandidateLengthTwoThreeValueRows F) :
    LengthTwoThreeCaseW10.LengthTwoThreeMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  SmallRowsTwoThreeW16.candidateLengthTwoThreeMissingOfBlockPairGeneratedPointInequalities
    V.toBlockPairGeneratedPointInequalities

end CandidateLengthTwoThreeValueRows

structure CandidateLengthFourFiveValueRows
    (F : PeriodCandidateFamily) where
  lengthFour : CandidateLengthFourValueRows F
  lengthFive : CandidateLengthFiveValueRows F

namespace CandidateLengthFourFiveValueRows

def toBlockPairGeneratedPointInequalities
    {F : PeriodCandidateFamily}
    (V : CandidateLengthFourFiveValueRows F) :
    SmallRowsFourFiveW16.CandidateLengthFourFiveBlockPairInequalities F
    where
  lengthFour := lengthFourBlockPairInequalitiesOfValueRows V.lengthFour
  lengthFive := lengthFiveBlockPairInequalitiesOfValueRows V.lengthFive

def toMissingInequalities
    {F : PeriodCandidateFamily}
    (V : CandidateLengthFourFiveValueRows F) :
    LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  SmallRowsFourFiveW16.candidateLengthFourFiveMissing
    V.toBlockPairGeneratedPointInequalities

end CandidateLengthFourFiveValueRows

structure CandidateSmallRowValueRows
    (F : PeriodCandidateFamily) where
  lengthTwoThree : CandidateLengthTwoThreeValueRows F
  lengthFourFive : CandidateLengthFourFiveValueRows F

namespace CandidateSmallRowValueRows

def lengthTwoThreeMissing
    {F : PeriodCandidateFamily}
    (V : CandidateSmallRowValueRows F) :
    LengthTwoThreeCaseW10.LengthTwoThreeMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  V.lengthTwoThree.toMissingInequalities

def lengthFourFiveMissing
    {F : PeriodCandidateFamily}
    (V : CandidateSmallRowValueRows F) :
    LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  V.lengthFourFive.toMissingInequalities

def exactMissingFieldsWithTail
    {F : PeriodCandidateFamily}
    (V : CandidateSmallRowValueRows F)
    (tail : CandidateTailBlockPairInequalities F) :
    ExactMissingConcreteTableFields F :=
  SmallRowsFourFiveW16.exactMissingFieldsOfSmallRowsFourFiveAndTail
    V.lengthTwoThreeMissing.lengthTwo
    V.lengthTwoThreeMissing.lengthThree
    V.lengthFourFive.toBlockPairGeneratedPointInequalities
    tail

end CandidateSmallRowValueRows

end

end SmallRowValueCertificatesW17
end PachToth
end ErdosProblems1066
