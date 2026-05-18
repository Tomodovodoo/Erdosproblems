import ErdosProblems1066.PachToth.SmallRowValueCertificatesW17

set_option autoImplicit false

/-!
# W18 value producers for the length-four and length-five small rows

This file gives the `k = 4` and `k = 5` producer surface for the W16/W17
small-row handoff.  The values are the generated-point polynomials themselves;
the remaining obligations are exactly the finite upper-triangle
non-connector lower bounds for lengths four and five.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallRowsFourFiveValueProducerW18

noncomputable section

abbrev PeriodCandidateFamily :=
  SmallRowValueCertificatesW17.PeriodCandidateFamily

abbrev RoleHingedPeriodSearchFamily :=
  SmallRowValueCertificatesW17.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  SmallRowValueCertificatesW17.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  SmallRowValueCertificatesW17.IndexedCyclicConnectorPair hk i u j v

abbrev generatedPointPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  SmallRowValueCertificatesW17.generatedPointPolynomial F hk i u j v

abbrev LengthFourBlockPairGeneratedPointInequalities :=
  SmallRowsFourFiveW16.LengthFourBlockPairGeneratedPointInequalities

abbrev LengthFiveBlockPairGeneratedPointInequalities :=
  SmallRowsFourFiveW16.LengthFiveBlockPairGeneratedPointInequalities

abbrev LengthFourFiveBlockPairGeneratedPointInequalities :=
  SmallRowsFourFiveW16.LengthFourFiveBlockPairGeneratedPointInequalities

abbrev CandidateLengthFourFiveBlockPairInequalities :=
  SmallRowsFourFiveW16.CandidateLengthFourFiveBlockPairInequalities

abbrev LengthFourValueRows :=
  SmallRowValueCertificatesW17.LengthFourValueRows

abbrev LengthFiveValueRows :=
  SmallRowValueCertificatesW17.LengthFiveValueRows

abbrev LengthFourFiveValueRows :=
  SmallRowValueCertificatesW17.LengthFourFiveValueRows

abbrev CandidateLengthFourValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthFourValueRows

abbrev CandidateLengthFiveValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthFiveValueRows

abbrev CandidateLengthFourFiveValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthFourFiveValueRows

abbrev CandidateLengthTwoThreeValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthTwoThreeValueRows

abbrev CandidateTailBlockPairInequalities :=
  SmallRowsFourFiveW16.CandidateTailBlockPairInequalities

abbrev ExactMissingConcreteTableFields :=
  SmallRowsFourFiveW16.ExactMissingConcreteTableFields

abbrev fourPositive : 0 < 4 :=
  LengthFourFiveCaseW11.fourPositive

abbrev fivePositive : 0 < 5 :=
  LengthFourFiveCaseW11.fivePositive

def lengthFourValueRowsOfBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFourBlockPairGeneratedPointInequalities F) :
    LengthFourValueRows F where
  value := fun i u j v => generatedPointPolynomial F fourPositive i u j v
  value_eq_polynomial_lt := by
    intro _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro i u j v hlt hnot
    exact H.polynomial_ge_one_lt i u j v hlt hnot

def lengthFiveValueRowsOfBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFiveBlockPairGeneratedPointInequalities F) :
    LengthFiveValueRows F where
  value := fun i u j v => generatedPointPolynomial F fivePositive i u j v
  value_eq_polynomial_lt := by
    intro _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := by
    intro i u j v hlt hnot
    exact H.polynomial_ge_one_lt i u j v hlt hnot

def lengthFourFiveValueRowsOfBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : LengthFourFiveBlockPairGeneratedPointInequalities F) :
    LengthFourFiveValueRows F where
  lengthFour := lengthFourValueRowsOfBlockPairInequalities H.lengthFour
  lengthFive := lengthFiveValueRowsOfBlockPairInequalities H.lengthFive

def candidateLengthFourFiveValueRowsOfBlockPairInequalities
    {F : PeriodCandidateFamily}
    (H : CandidateLengthFourFiveBlockPairInequalities F) :
    CandidateLengthFourFiveValueRows F where
  lengthFour := lengthFourValueRowsOfBlockPairInequalities H.lengthFour
  lengthFive := lengthFiveValueRowsOfBlockPairInequalities H.lengthFive

def candidateLengthFourFiveBlockPairInequalitiesOfValueRows
    {F : PeriodCandidateFamily}
    (V : CandidateLengthFourFiveValueRows F) :
    CandidateLengthFourFiveBlockPairInequalities F :=
  V.toBlockPairGeneratedPointInequalities

/-! ## Exact finite obligations for `k = 4` -/

structure LengthFourFiniteValueObligations
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one01 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fourPositive
        (0 : Fin 4) u (1 : Fin 4) v) ->
        1 <= generatedPointPolynomial F fourPositive
          (0 : Fin 4) u (1 : Fin 4) v
  polynomial_ge_one02 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fourPositive
        (0 : Fin 4) u (2 : Fin 4) v) ->
        1 <= generatedPointPolynomial F fourPositive
          (0 : Fin 4) u (2 : Fin 4) v
  polynomial_ge_one03 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fourPositive
        (0 : Fin 4) u (3 : Fin 4) v) ->
        1 <= generatedPointPolynomial F fourPositive
          (0 : Fin 4) u (3 : Fin 4) v
  polynomial_ge_one12 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fourPositive
        (1 : Fin 4) u (2 : Fin 4) v) ->
        1 <= generatedPointPolynomial F fourPositive
          (1 : Fin 4) u (2 : Fin 4) v
  polynomial_ge_one13 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fourPositive
        (1 : Fin 4) u (3 : Fin 4) v) ->
        1 <= generatedPointPolynomial F fourPositive
          (1 : Fin 4) u (3 : Fin 4) v
  polynomial_ge_one23 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fourPositive
        (2 : Fin 4) u (3 : Fin 4) v) ->
        1 <= generatedPointPolynomial F fourPositive
          (2 : Fin 4) u (3 : Fin 4) v

namespace LengthFourFiniteValueObligations

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthFourFiniteValueObligations F) :
    LengthFourBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    fin_cases i <;> fin_cases j <;> norm_num at hlt
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one01 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one02 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one03 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one12 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one13 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one23 u v hnot

def toValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthFourFiniteValueObligations F) :
    LengthFourValueRows F :=
  lengthFourValueRowsOfBlockPairInequalities C.toBlockPairInequalities

end LengthFourFiniteValueObligations

/-! ## Exact finite obligations for `k = 5` -/

structure LengthFiveFiniteValueObligations
    (F : RoleHingedPeriodSearchFamily) where
  polynomial_ge_one01 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (0 : Fin 5) u (1 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (0 : Fin 5) u (1 : Fin 5) v
  polynomial_ge_one02 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (0 : Fin 5) u (2 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (0 : Fin 5) u (2 : Fin 5) v
  polynomial_ge_one03 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (0 : Fin 5) u (3 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (0 : Fin 5) u (3 : Fin 5) v
  polynomial_ge_one04 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (0 : Fin 5) u (4 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (0 : Fin 5) u (4 : Fin 5) v
  polynomial_ge_one12 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (1 : Fin 5) u (2 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (1 : Fin 5) u (2 : Fin 5) v
  polynomial_ge_one13 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (1 : Fin 5) u (3 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (1 : Fin 5) u (3 : Fin 5) v
  polynomial_ge_one14 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (1 : Fin 5) u (4 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (1 : Fin 5) u (4 : Fin 5) v
  polynomial_ge_one23 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (2 : Fin 5) u (3 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (2 : Fin 5) u (3 : Fin 5) v
  polynomial_ge_one24 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (2 : Fin 5) u (4 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (2 : Fin 5) u (4 : Fin 5) v
  polynomial_ge_one34 :
    forall u v : LocalVertexIndex,
      Not (IndexedCyclicConnectorPair fivePositive
        (3 : Fin 5) u (4 : Fin 5) v) ->
        1 <= generatedPointPolynomial F fivePositive
          (3 : Fin 5) u (4 : Fin 5) v

namespace LengthFiveFiniteValueObligations

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthFiveFiniteValueObligations F) :
    LengthFiveBlockPairGeneratedPointInequalities F where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot
    fin_cases i <;> fin_cases j <;> norm_num at hlt
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one01 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one02 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one03 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one04 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one12 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one13 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one14 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one23 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one24 u v hnot
    · simpa [generatedPointPolynomial] using
        C.polynomial_ge_one34 u v hnot

def toValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthFiveFiniteValueObligations F) :
    LengthFiveValueRows F :=
  lengthFiveValueRowsOfBlockPairInequalities C.toBlockPairInequalities

end LengthFiveFiniteValueObligations

structure LengthFourFiveFiniteValueObligations
    (F : RoleHingedPeriodSearchFamily) where
  lengthFour : LengthFourFiniteValueObligations F
  lengthFive : LengthFiveFiniteValueObligations F

namespace LengthFourFiveFiniteValueObligations

def toBlockPairInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthFourFiveFiniteValueObligations F) :
    LengthFourFiveBlockPairGeneratedPointInequalities F where
  lengthFour := C.lengthFour.toBlockPairInequalities
  lengthFive := C.lengthFive.toBlockPairInequalities

def toValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthFourFiveFiniteValueObligations F) :
    LengthFourFiveValueRows F where
  lengthFour := C.lengthFour.toValueRows
  lengthFive := C.lengthFive.toValueRows

end LengthFourFiveFiniteValueObligations

abbrev CandidateLengthFourFiniteValueObligations
    (F : PeriodCandidateFamily) :=
  LengthFourFiniteValueObligations F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthFiveFiniteValueObligations
    (F : PeriodCandidateFamily) :=
  LengthFiveFiniteValueObligations F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthFourFiveFiniteValueObligations
    (F : PeriodCandidateFamily) :=
  LengthFourFiveFiniteValueObligations F.toRoleHingedPeriodSearchFamily

def candidateLengthFourFiveBlockPairInequalitiesOfFiniteObligations
    {F : PeriodCandidateFamily}
    (C : CandidateLengthFourFiveFiniteValueObligations F) :
    CandidateLengthFourFiveBlockPairInequalities F :=
  C.toBlockPairInequalities

def candidateLengthFourFiveValueRowsOfFiniteObligations
    {F : PeriodCandidateFamily}
    (C : CandidateLengthFourFiveFiniteValueObligations F) :
    CandidateLengthFourFiveValueRows F where
  lengthFour := C.lengthFour.toValueRows
  lengthFive := C.lengthFive.toValueRows

structure CandidateLengthFourFiveValueProducer
    (F : PeriodCandidateFamily) where
  finiteObligations : CandidateLengthFourFiveFiniteValueObligations F

namespace CandidateLengthFourFiveValueProducer

def blockPairInequalities
    {F : PeriodCandidateFamily}
    (P : CandidateLengthFourFiveValueProducer F) :
    CandidateLengthFourFiveBlockPairInequalities F :=
  candidateLengthFourFiveBlockPairInequalitiesOfFiniteObligations
    P.finiteObligations

def valueRows
    {F : PeriodCandidateFamily}
    (P : CandidateLengthFourFiveValueProducer F) :
    CandidateLengthFourFiveValueRows F :=
  candidateLengthFourFiveValueRowsOfFiniteObligations P.finiteObligations

def missingInequalities
    {F : PeriodCandidateFamily}
    (P : CandidateLengthFourFiveValueProducer F) :
    LengthFourFiveCaseW11.LengthFourFiveMissingNonConnectorInequalities
      F.toRoleHingedPeriodSearchFamily :=
  SmallRowsFourFiveW16.candidateLengthFourFiveMissing
    P.blockPairInequalities

def exactMissingFieldsWithTail
    {F : PeriodCandidateFamily}
    (smallTwoThree : CandidateLengthTwoThreeValueRows F)
    (P : CandidateLengthFourFiveValueProducer F)
    (tail : CandidateTailBlockPairInequalities F) :
    ExactMissingConcreteTableFields F :=
  SmallRowValueCertificatesW17.CandidateSmallRowValueRows.exactMissingFieldsWithTail
    { lengthTwoThree := smallTwoThree
      lengthFourFive := P.valueRows }
    tail

end CandidateLengthFourFiveValueProducer

end

end SmallRowsFourFiveValueProducerW18
end PachToth
end ErdosProblems1066
