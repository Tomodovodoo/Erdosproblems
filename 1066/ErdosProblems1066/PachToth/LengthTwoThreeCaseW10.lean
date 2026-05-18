import ErdosProblems1066.PachToth.Arithmetic
import ErdosProblems1066.PachToth.ConcreteValueCertificateExamples
import ErdosProblems1066.PachToth.FiniteCertificateSearchSurface
import ErdosProblems1066.PachToth.SmallCaseCertificates

set_option autoImplicit false

/-!
# W10 small length-two and length-three value-certificate surface

This module pushes the concrete small-k non-connector value-certificate
examples to `k = 2` and `k = 3`.

No numerical lower bound is invented here.  For each small length, the file
names the exact per-position polynomial inequalities still needed from a real
finite search, then proves that those inequalities are precisely enough to
build the existing non-connector value-matrix and position-value-certificate
interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LengthTwoThreeCaseW10

open ConcreteValueCertificateExamples

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  ConcreteValueCertificateExamples.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  ConcreteValueCertificateExamples.LocalVertexIndex

abbrev UpperTrianglePosition :=
  ConcreteValueCertificateExamples.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  ConcreteValueCertificateExamples.PositionNonConnector hk p

abbrev NonConnectorValueMatrix :=
  ConcreteValueCertificateExamples.NonConnectorValueMatrix

abbrev PositionValueCertificate :=
  ConcreteValueCertificateExamples.PositionValueCertificate

abbrev UpperTriangleNonConnectorSqValueTable :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueTable

abbrev UpperTriangleNonConnectorSqValueVectorCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificate

abbrev UpperTriangleNonConnectorSqValueListCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificate

def threePositive : 0 < 3 :=
  Nat.zero_lt_succ 2

/-! ## Length two -/

abbrev LengthTwoMissingNonConnectorInequality :=
  ConcreteValueCertificateExamples.LengthTwoMissingNonConnectorInequality

abbrev LengthTwoMissingNonConnectorInequalities :=
  ConcreteValueCertificateExamples.LengthTwoMissingNonConnectorInequalities

/-- The existing length-two ledger has one upper-triangle block pair and all
local-vertex pairs. -/
theorem lengthTwo_polynomial_ge_one_of_missing
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthTwoMissingNonConnectorInequalities F)
    (p : UpperTrianglePosition 2)
    (hp : PositionNonConnector twoPositive p) :
    1 <= p.polynomial F twoPositive := by
  cases p with
  | mk left leftVertex right rightVertex left_lt_right =>
      fin_cases left <;> fin_cases right
      all_goals simp at left_lt_right
      all_goals first
        | omega
        | exact H.inequality leftVertex rightVertex hp

/-- Length-two per-position inequalities build the checked value matrix whose
stored value is the polynomial itself. -/
def lengthTwoMatrixOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthTwoMissingNonConnectorInequalities F) :
    NonConnectorValueMatrix F 2 twoPositive :=
  matrixOfPerPositionPolynomialInequalities F 2 twoPositive
    (lengthTwo_polynomial_ge_one_of_missing F H)

def lengthTwoPositionValueCertificateOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthTwoMissingNonConnectorInequalities F) :
    PositionValueCertificate F 2 twoPositive :=
  (lengthTwoMatrixOfMissingInequalities F H).toPositionValueCertificate

def lengthTwoSqValueTableOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthTwoMissingNonConnectorInequalities F) :
    UpperTriangleNonConnectorSqValueTable F 2 twoPositive :=
  (lengthTwoMatrixOfMissingInequalities F H).toSqValueTable

def lengthTwoMatrixOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F 2 twoPositive) :
    NonConnectorValueMatrix F 2 twoPositive :=
  matrixOfVectorCertificate C

def lengthTwoMatrixOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificate F 2 twoPositive) :
    NonConnectorValueMatrix F 2 twoPositive :=
  matrixOfListCertificate C

/-! ## Length three -/

def lengthThreePosition01
    (u v : LocalVertexIndex) : UpperTrianglePosition 3 where
  left := 0
  leftVertex := u
  right := 1
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthThreePosition02
    (u v : LocalVertexIndex) : UpperTrianglePosition 3 where
  left := 0
  leftVertex := u
  right := 2
  rightVertex := v
  left_lt_right := by
    norm_num

def lengthThreePosition12
    (u v : LocalVertexIndex) : UpperTrianglePosition 3 where
  left := 1
  leftVertex := u
  right := 2
  rightVertex := v
  left_lt_right := by
    norm_num

/-- The exact missing inequality for the `(0, 1)` length-three block pair. -/
abbrev LengthThreeMissingNonConnectorInequality01
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector threePositive (lengthThreePosition01 u v) ->
    1 <= (lengthThreePosition01 u v).polynomial F threePositive

/-- The exact missing inequality for the `(0, 2)` length-three block pair. -/
abbrev LengthThreeMissingNonConnectorInequality02
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector threePositive (lengthThreePosition02 u v) ->
    1 <= (lengthThreePosition02 u v).polynomial F threePositive

/-- The exact missing inequality for the `(1, 2)` length-three block pair. -/
abbrev LengthThreeMissingNonConnectorInequality12
    (F : RoleHingedPeriodSearchFamily)
    (u v : LocalVertexIndex) : Prop :=
  PositionNonConnector threePositive (lengthThreePosition12 u v) ->
    1 <= (lengthThreePosition12 u v).polynomial F threePositive

/-- The full length-three ledger: three upper-triangle block pairs, each with
one inequality for every pair of local vertices. -/
structure LengthThreeMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) where
  inequality01 :
    forall u v : LocalVertexIndex,
      LengthThreeMissingNonConnectorInequality01 F u v
  inequality02 :
    forall u v : LocalVertexIndex,
      LengthThreeMissingNonConnectorInequality02 F u v
  inequality12 :
    forall u v : LocalVertexIndex,
      LengthThreeMissingNonConnectorInequality12 F u v

theorem lengthThree_polynomial_ge_one_of_missing
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthThreeMissingNonConnectorInequalities F)
    (p : UpperTrianglePosition 3)
    (hp : PositionNonConnector threePositive p) :
    1 <= p.polynomial F threePositive := by
  cases p with
  | mk left leftVertex right rightVertex left_lt_right =>
      fin_cases left <;> fin_cases right
      all_goals simp at left_lt_right
      all_goals first
        | omega
        | exact H.inequality01 leftVertex rightVertex hp
        | exact H.inequality02 leftVertex rightVertex hp
        | exact H.inequality12 leftVertex rightVertex hp

/-- Length-three per-position inequalities build the checked value matrix
whose stored value is the polynomial itself. -/
def lengthThreeMatrixOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthThreeMissingNonConnectorInequalities F) :
    NonConnectorValueMatrix F 3 threePositive :=
  matrixOfPerPositionPolynomialInequalities F 3 threePositive
    (lengthThree_polynomial_ge_one_of_missing F H)

def lengthThreePositionValueCertificateOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthThreeMissingNonConnectorInequalities F) :
    PositionValueCertificate F 3 threePositive :=
  (lengthThreeMatrixOfMissingInequalities F H).toPositionValueCertificate

def lengthThreeSqValueTableOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthThreeMissingNonConnectorInequalities F) :
    UpperTriangleNonConnectorSqValueTable F 3 threePositive :=
  (lengthThreeMatrixOfMissingInequalities F H).toSqValueTable

def lengthThreeMatrixOfVectorCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificate F 3 threePositive) :
    NonConnectorValueMatrix F 3 threePositive :=
  matrixOfVectorCertificate C

def lengthThreeMatrixOfListCertificate
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificate F 3 threePositive) :
    NonConnectorValueMatrix F 3 threePositive :=
  matrixOfListCertificate C

/-! ## Joint small-k bookkeeping -/

structure LengthTwoThreeMissingNonConnectorInequalities
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwo : LengthTwoMissingNonConnectorInequalities F
  lengthThree : LengthThreeMissingNonConnectorInequalities F

structure LengthTwoThreeValueMatrices
    (F : RoleHingedPeriodSearchFamily) where
  lengthTwo : NonConnectorValueMatrix F 2 twoPositive
  lengthThree : NonConnectorValueMatrix F 3 threePositive

def lengthTwoThreeMatricesOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthTwoThreeMissingNonConnectorInequalities F) :
    LengthTwoThreeValueMatrices F where
  lengthTwo := lengthTwoMatrixOfMissingInequalities F H.lengthTwo
  lengthThree := lengthThreeMatrixOfMissingInequalities F H.lengthThree

theorem lengthTwo_missing_localVertexPair_count :
    16 * 16 = 256 := by
  norm_num

theorem lengthThree_missing_localVertexPair_count :
    3 * 16 * 16 = 768 := by
  norm_num

theorem lengthTwoThree_remainder_arithmetic_sample :
    Arithmetic.ceilDiv (5 * (16 * 2 + 3)) 16 = 11 := by
  norm_num [Arithmetic.ceilDiv]

theorem smallCase_remainder_three :
    targetUpperConstructionFiveSixteenAt 3 :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenAt_r3

end

end LengthTwoThreeCaseW10
end PachToth
end ErdosProblems1066
