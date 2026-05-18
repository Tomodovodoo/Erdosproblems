import ErdosProblems1066.PachToth.SmallRowValueCertificatesW17
import ErdosProblems1066.PachToth.FiniteCertificateSearchSurface

set_option autoImplicit false

/-!
# W18 small-row value producer for lengths two and three

This file owns the `k = 2` and `k = 3` value-certificate production layer.
It introduces no unchecked numeric data: vector and list certificates still
carry the exact value-to-polynomial equalities and lower-bound proofs for each
upper-triangle non-connector entry.  The definitions below only repackage
those finite certificates into the W17 value-row interface and the W16
candidate block-pair inequality interface.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallRowsTwoThreeValueProducerW18

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

abbrev SmallBlockPairValueRows :=
  SmallRowValueCertificatesW17.SmallBlockPairValueRows

abbrev LengthTwoValueRows :=
  SmallRowValueCertificatesW17.LengthTwoValueRows

abbrev LengthThreeValueRows :=
  SmallRowValueCertificatesW17.LengthThreeValueRows

abbrev LengthTwoThreeValueRows :=
  SmallRowValueCertificatesW17.LengthTwoThreeValueRows

abbrev CandidateLengthTwoValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthTwoValueRows

abbrev CandidateLengthThreeValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthThreeValueRows

abbrev CandidateLengthTwoThreeValueRows :=
  SmallRowValueCertificatesW17.CandidateLengthTwoThreeValueRows

abbrev UpperTriangleNonConnectorSqValueVectorCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificate

abbrev UpperTriangleNonConnectorSqValueListCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificate

/-! ## Generic finite-certificate adapters -/

def valueRowsOfPolynomialInequalities
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (polynomial_ge_one_lt :
      forall (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= generatedPointPolynomial F hk i u j v) :
    SmallBlockPairValueRows F k hk where
  value := fun i u j v => generatedPointPolynomial F hk i u j v
  value_eq_polynomial_lt := by
    intro _i _u _j _v _hlt _hnot
    rfl
  value_ge_one_lt := polynomial_ge_one_lt

def valueRowsOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F k hk) :
    SmallBlockPairValueRows F k hk where
  value := C.value
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot
    simpa [generatedPointPolynomial] using
      C.value_eq_polynomial_lt i u j v hlt hnot
  value_ge_one_lt := by
    intro i u j v hlt hnot
    exact C.value_ge_one_lt i u j v hlt hnot

def valueRowsOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (C : UpperTriangleNonConnectorSqValueListCertificate F k hk) :
    SmallBlockPairValueRows F k hk where
  value := C.value
  value_eq_polynomial_lt := by
    intro i u j v hlt hnot
    simpa [generatedPointPolynomial] using
      C.value_eq_polynomial_lt i u j v hlt hnot
  value_ge_one_lt := by
    intro i u j v hlt hnot
    exact C.value_ge_one_lt i u j v hlt hnot

/-! ## Length-two rows -/

abbrev LengthTwoVectorCertificate (F : RoleHingedPeriodSearchFamily) :=
  UpperTriangleNonConnectorSqValueVectorCertificate
    F 2 SmallRowsTwoThreeW16.twoPositive

abbrev LengthTwoListCertificate (F : RoleHingedPeriodSearchFamily) :=
  UpperTriangleNonConnectorSqValueListCertificate
    F 2 SmallRowsTwoThreeW16.twoPositive

def lengthTwoValueRowsOfPolynomialInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : SmallRowsTwoThreeW16.LengthTwoBlockPairGeneratedPointInequalities F) :
    LengthTwoValueRows F :=
  valueRowsOfPolynomialInequalities H.polynomial_ge_one_lt

def lengthTwoValueRowsOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoVectorCertificate F) :
    LengthTwoValueRows F :=
  valueRowsOfVectorCertificate C

def lengthTwoValueRowsOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoListCertificate F) :
    LengthTwoValueRows F :=
  valueRowsOfListCertificate C

def lengthTwoBlockPairInequalitiesOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoVectorCertificate F) :
    SmallRowsTwoThreeW16.LengthTwoBlockPairGeneratedPointInequalities F :=
  SmallRowValueCertificatesW17.lengthTwoBlockPairInequalitiesOfValueRows
    (lengthTwoValueRowsOfVectorCertificate C)

def lengthTwoBlockPairInequalitiesOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoListCertificate F) :
    SmallRowsTwoThreeW16.LengthTwoBlockPairGeneratedPointInequalities F :=
  SmallRowValueCertificatesW17.lengthTwoBlockPairInequalitiesOfValueRows
    (lengthTwoValueRowsOfListCertificate C)

/-! ## Length-three rows -/

abbrev LengthThreeVectorCertificate (F : RoleHingedPeriodSearchFamily) :=
  UpperTriangleNonConnectorSqValueVectorCertificate
    F 3 SmallRowsTwoThreeW16.threePositive

abbrev LengthThreeListCertificate (F : RoleHingedPeriodSearchFamily) :=
  UpperTriangleNonConnectorSqValueListCertificate
    F 3 SmallRowsTwoThreeW16.threePositive

def lengthThreeValueRowsOfPolynomialInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : SmallRowsTwoThreeW16.LengthThreeBlockPairGeneratedPointInequalities F) :
    LengthThreeValueRows F :=
  valueRowsOfPolynomialInequalities H.polynomial_ge_one_lt

def lengthThreeValueRowsOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthThreeVectorCertificate F) :
    LengthThreeValueRows F :=
  valueRowsOfVectorCertificate C

def lengthThreeValueRowsOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthThreeListCertificate F) :
    LengthThreeValueRows F :=
  valueRowsOfListCertificate C

def lengthThreeBlockPairInequalitiesOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthThreeVectorCertificate F) :
    SmallRowsTwoThreeW16.LengthThreeBlockPairGeneratedPointInequalities F :=
  SmallRowValueCertificatesW17.lengthThreeBlockPairInequalitiesOfValueRows
    (lengthThreeValueRowsOfVectorCertificate C)

def lengthThreeBlockPairInequalitiesOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthThreeListCertificate F) :
    SmallRowsTwoThreeW16.LengthThreeBlockPairGeneratedPointInequalities F :=
  SmallRowValueCertificatesW17.lengthThreeBlockPairInequalitiesOfValueRows
    (lengthThreeValueRowsOfListCertificate C)

/-! ## Paired length-two/length-three producers -/

structure LengthTwoThreeVectorCertificates
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwo : LengthTwoVectorCertificate F
  lengthThree : LengthThreeVectorCertificate F

namespace LengthTwoThreeVectorCertificates

def toValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoThreeVectorCertificates F) :
    LengthTwoThreeValueRows F where
  lengthTwo := lengthTwoValueRowsOfVectorCertificate C.lengthTwo
  lengthThree := lengthThreeValueRowsOfVectorCertificate C.lengthThree

def toBlockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoThreeVectorCertificates F) :
    SmallRowsTwoThreeW16.LengthTwoThreeBlockPairGeneratedPointInequalities F :=
  C.toValueRows.toBlockPairGeneratedPointInequalities

end LengthTwoThreeVectorCertificates

structure LengthTwoThreeListCertificates
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwo : LengthTwoListCertificate F
  lengthThree : LengthThreeListCertificate F

namespace LengthTwoThreeListCertificates

def toValueRows
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoThreeListCertificates F) :
    LengthTwoThreeValueRows F where
  lengthTwo := lengthTwoValueRowsOfListCertificate C.lengthTwo
  lengthThree := lengthThreeValueRowsOfListCertificate C.lengthThree

def toBlockPairGeneratedPointInequalities
    {F : RoleHingedPeriodSearchFamily}
    (C : LengthTwoThreeListCertificates F) :
    SmallRowsTwoThreeW16.LengthTwoThreeBlockPairGeneratedPointInequalities F :=
  C.toValueRows.toBlockPairGeneratedPointInequalities

end LengthTwoThreeListCertificates

def lengthTwoThreeValueRowsOfPolynomialInequalities
    {F : RoleHingedPeriodSearchFamily}
    (H : SmallRowsTwoThreeW16.LengthTwoThreeBlockPairGeneratedPointInequalities F) :
    LengthTwoThreeValueRows F where
  lengthTwo := lengthTwoValueRowsOfPolynomialInequalities H.lengthTwo
  lengthThree := lengthThreeValueRowsOfPolynomialInequalities H.lengthThree

/-! ## Candidate-family handoff -/

abbrev CandidateLengthTwoVectorCertificate
    (F : PeriodCandidateFamily) :=
  LengthTwoVectorCertificate F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthThreeVectorCertificate
    (F : PeriodCandidateFamily) :=
  LengthThreeVectorCertificate F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthTwoListCertificate
    (F : PeriodCandidateFamily) :=
  LengthTwoListCertificate F.toRoleHingedPeriodSearchFamily

abbrev CandidateLengthThreeListCertificate
    (F : PeriodCandidateFamily) :=
  LengthThreeListCertificate F.toRoleHingedPeriodSearchFamily

structure CandidateLengthTwoThreeVectorCertificates
    (F : PeriodCandidateFamily) where
  lengthTwo : CandidateLengthTwoVectorCertificate F
  lengthThree : CandidateLengthThreeVectorCertificate F

namespace CandidateLengthTwoThreeVectorCertificates

def toValueRows
    {F : PeriodCandidateFamily}
    (C : CandidateLengthTwoThreeVectorCertificates F) :
    CandidateLengthTwoThreeValueRows F where
  lengthTwo := lengthTwoValueRowsOfVectorCertificate C.lengthTwo
  lengthThree := lengthThreeValueRowsOfVectorCertificate C.lengthThree

def toBlockPairGeneratedPointInequalities
    {F : PeriodCandidateFamily}
    (C : CandidateLengthTwoThreeVectorCertificates F) :
    SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F :=
  C.toValueRows.toBlockPairGeneratedPointInequalities

end CandidateLengthTwoThreeVectorCertificates

structure CandidateLengthTwoThreeListCertificates
    (F : PeriodCandidateFamily) where
  lengthTwo : CandidateLengthTwoListCertificate F
  lengthThree : CandidateLengthThreeListCertificate F

namespace CandidateLengthTwoThreeListCertificates

def toValueRows
    {F : PeriodCandidateFamily}
    (C : CandidateLengthTwoThreeListCertificates F) :
    CandidateLengthTwoThreeValueRows F where
  lengthTwo := lengthTwoValueRowsOfListCertificate C.lengthTwo
  lengthThree := lengthThreeValueRowsOfListCertificate C.lengthThree

def toBlockPairGeneratedPointInequalities
    {F : PeriodCandidateFamily}
    (C : CandidateLengthTwoThreeListCertificates F) :
    SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F :=
  C.toValueRows.toBlockPairGeneratedPointInequalities

end CandidateLengthTwoThreeListCertificates

def candidateLengthTwoThreeValueRowsOfPolynomialInequalities
    {F : PeriodCandidateFamily}
    (H :
      SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F) :
    CandidateLengthTwoThreeValueRows F where
  lengthTwo := lengthTwoValueRowsOfPolynomialInequalities H.lengthTwo
  lengthThree := lengthThreeValueRowsOfPolynomialInequalities H.lengthThree

def candidateLengthTwoThreeRowsOfVectorCertificates
    {F : PeriodCandidateFamily}
    (C : CandidateLengthTwoThreeVectorCertificates F) :
    SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F :=
  C.toBlockPairGeneratedPointInequalities

def candidateLengthTwoThreeRowsOfListCertificates
    {F : PeriodCandidateFamily}
    (C : CandidateLengthTwoThreeListCertificates F) :
    SmallRowsTwoThreeW16.CandidateLengthTwoThreeBlockPairGeneratedPointInequalities F :=
  C.toBlockPairGeneratedPointInequalities

end

end SmallRowsTwoThreeValueProducerW18
end PachToth
end ErdosProblems1066
