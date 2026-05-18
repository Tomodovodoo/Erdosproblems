import ErdosProblems1066.PachToth.NonConnectorInstantiationW13
import ErdosProblems1066.PachToth.LengthFourFiveCaseW11

set_option autoImplicit false

/-!
# W14 concrete non-connector table surface

This module is the concrete table handoff for the connector-separated
Pach--Toth route.  It does three small jobs:

* native upper-triangle non-connector tables, vector grids, and row lists are
  converted into the W13 indexed separation fields;
* the length-one case is inhabited concretely, since its upper triangle is
  empty; and
* the non-vacuous cases are exposed as exact packed row obligations, so a
  finite search can fill precisely the remaining rows without changing the
  downstream route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonConnectorTableConcreteW14

open CrossBlockSqTableSearch

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  NonConnectorInstantiationW13.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  NonConnectorInstantiationW13.LocalVertexIndex

abbrev IndexedValueFields :=
  NonConnectorInstantiationW13.IndexedValueFields

abbrev IndexedSqDistanceFields :=
  NonConnectorInstantiationW13.IndexedSqDistanceFields

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  NonConnectorInstantiationW13.IndexedCyclicConnectorPair hk i u j v

abbrev UpperTrianglePosition :=
  CrossBlockPolynomialNormalization.UpperTrianglePosition

abbrev PositionNonConnector
    {k : Nat} (hk : 0 < k) (p : UpperTrianglePosition k) : Prop :=
  CrossBlockPolynomialNormalization.upperTrianglePositionNonConnector hk p

abbrev UpperTriangleNonConnectorSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTable

abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily

abbrev UpperTriangleNonConnectorSqValueVectorCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificate

abbrev UpperTriangleNonConnectorSqValueListCertificate :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificate

abbrev UpperTriangleNonConnectorSqValueVectorCertificateFamily :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificateFamily

abbrev UpperTriangleNonConnectorSqValueListCertificateFamily :=
  FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificateFamily

abbrev NonConnectorValueMatrix :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrix

abbrev PositionPolynomialCertificate :=
  NonConnectorPolynomialCertificates.PositionPolynomialCertificate

abbrev PositionValueCertificate :=
  NonConnectorPolynomialCertificates.PositionValueCertificate

def onePositive : 0 < 1 :=
  Nat.zero_lt_succ 0

theorem finOne_not_lt (i j : Fin 1) : Not (i.val < j.val) := by
  omega

/-! ## W13 field inhabitants from concrete table formats -/

/-- Read a native upper-triangle table in the canonical endpoint order. -/
def normalizedTableValue
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} (hk : 0 < k)
    (T : UpperTriangleNonConnectorSqValueTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  if _hlt : i.val < j.val then
    T.value i u j v
  else if _hgt : j.val < i.val then
    T.value j v i u
  else
    0

@[simp]
theorem normalizedTableValue_of_lt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqValueTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    normalizedTableValue hk T i u j v = T.value i u j v := by
  simp [normalizedTableValue, hlt]

@[simp]
theorem normalizedTableValue_of_gt
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqValueTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hgt : j.val < i.val) :
    normalizedTableValue hk T i u j v = T.value j v i u := by
  have hnlt : Not (i.val < j.val) := by omega
  simp [normalizedTableValue, hnlt, hgt]

theorem normalizedTableValue_eq_sqDist
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqValueTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    normalizedTableValue hk T i u j v =
      CrossBlockDistanceSqReduction.indexedGeneratedSqDist
        F hk i u j v := by
  by_cases hlt : i.val < j.val
  · rw [normalizedTableValue_of_lt T i u j v hlt]
    have hvalue := T.value_eq_polynomial_lt
      i u j v hlt hnot_connector
    simpa [CrossBlockSqTableSearch.indexedGeneratedSqDist_eq_polynomial]
      using hvalue
  · have hgt : j.val < i.val := by
      have hne_val : Not (i.val = j.val) := by
        intro hval
        exact hij (Fin.ext hval)
      omega
    rw [normalizedTableValue_of_gt T i u j v hgt]
    have hnot_swap :
        Not (IndexedCyclicConnectorPair hk j v i u) :=
      CrossBlockSqTableSearch.not_indexedCyclicConnectorPair_comm
        hk i u j v hnot_connector
    have hvalue := T.value_eq_polynomial_lt
      j v i u hgt hnot_swap
    rw [← CrossBlockSqTableSearch.indexedGeneratedSqDist_eq_polynomial
      F hk j v i u] at hvalue
    rw [CrossBlockSqTableSearch.indexedGeneratedSqDist_comm F hk i u j v]
    exact hvalue

theorem normalizedTableValue_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : UpperTriangleNonConnectorSqValueTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot_connector : Not (IndexedCyclicConnectorPair hk i u j v)) :
    1 <= normalizedTableValue hk T i u j v := by
  by_cases hlt : i.val < j.val
  · rw [normalizedTableValue_of_lt T i u j v hlt]
    exact T.value_ge_one_lt i u j v hlt hnot_connector
  · have hgt : j.val < i.val := by
      have hne_val : Not (i.val = j.val) := by
        intro hval
        exact hij (Fin.ext hval)
      omega
    rw [normalizedTableValue_of_gt T i u j v hgt]
    have hnot_swap :
        Not (IndexedCyclicConnectorPair hk j v i u) :=
      CrossBlockSqTableSearch.not_indexedCyclicConnectorPair_comm
        hk i u j v hnot_connector
    exact T.value_ge_one_lt j v i u hgt hnot_swap

def indexedValueFieldsOfTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorSqValueTableFamily F) :
    IndexedValueFields F where
  value := fun k hk i u j v =>
    normalizedTableValue hk (T.table k hk) i u j v
  value_eq_sqDist := by
    intro k hk i u j v hij hnot_connector
    exact normalizedTableValue_eq_sqDist
      (T.table k hk) i u j v hij hnot_connector
  value_ge_one := by
    intro k hk i u j v hij hnot_connector
    exact normalizedTableValue_ge_one
      (T.table k hk) i u j v hij hnot_connector

def indexedSqDistanceFieldsOfTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorSqValueTableFamily F) :
    IndexedSqDistanceFields F :=
  (indexedValueFieldsOfTableFamily T).toSqDistanceFields

def indexedValueFieldsOfVectorCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    IndexedValueFields F :=
  indexedValueFieldsOfTableFamily C.toSqValueTableFamily

def indexedSqDistanceFieldsOfVectorCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    IndexedSqDistanceFields F :=
  (indexedValueFieldsOfVectorCertificateFamily C).toSqDistanceFields

def indexedValueFieldsOfListCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    IndexedValueFields F :=
  indexedValueFieldsOfTableFamily C.toSqValueTableFamily

def indexedSqDistanceFieldsOfListCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    IndexedSqDistanceFields F :=
  (indexedValueFieldsOfListCertificateFamily C).toSqDistanceFields

theorem targetUpperConstructionFiveSixteen_of_tableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorSqValueTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (indexedSqDistanceFieldsOfTableFamily T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_tableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : UpperTriangleNonConnectorSqValueTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (indexedSqDistanceFieldsOfTableFamily T)
    |>.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_vectorCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (indexedSqDistanceFieldsOfVectorCertificateFamily C)
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_vectorCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueVectorCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (indexedSqDistanceFieldsOfVectorCertificateFamily C)
    |>.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_listCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (indexedSqDistanceFieldsOfListCertificateFamily C)
    |>.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_listCertificateFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : UpperTriangleNonConnectorSqValueListCertificateFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (indexedSqDistanceFieldsOfListCertificateFamily C)
    |>.targetUpperConstructionFiveSixteenArbitrary

/-! ## Length-one concrete inhabitants -/

def lengthOneSqValueTable
    (F : RoleHingedPeriodSearchFamily) :
    UpperTriangleNonConnectorSqValueTable F 1 onePositive where
  value := fun _ _ _ _ => 0
  value_eq_polynomial_lt := by
    intro i _u j _v hlt _hnot_connector
    exact False.elim (finOne_not_lt i j hlt)
  value_ge_one_lt := by
    intro i _u j _v hlt _hnot_connector
    exact False.elim (finOne_not_lt i j hlt)

def lengthOneZeroGrid :
    FiniteCertificateSearchSurface.SqValueGrid 1 :=
  Vector.replicate 1
    (Vector.replicate 16
      (Vector.replicate 1
        (Vector.replicate 16 (0 : Real))))

def lengthOneVectorCertificate
    (F : RoleHingedPeriodSearchFamily) :
    UpperTriangleNonConnectorSqValueVectorCertificate F 1 onePositive where
  values := lengthOneZeroGrid
  value_eq_polynomial_lt := by
    intro i _u j _v hlt _hnot_connector
    exact False.elim (finOne_not_lt i j hlt)
  value_ge_one_lt := by
    intro i _u j _v hlt _hnot_connector
    exact False.elim (finOne_not_lt i j hlt)

def lengthOneListCertificate
    (F : RoleHingedPeriodSearchFamily) :
    UpperTriangleNonConnectorSqValueListCertificate F 1 onePositive where
  rows := []
  complete := by
    intro i _u j _v hlt _hnot_connector
    exact False.elim (finOne_not_lt i j hlt)

/-! ## Exact row surface for non-vacuous table generation -/

structure NonConnectorRow (k : Nat) (hk : 0 < k) where
  left : Fin k
  leftVertex : LocalVertexIndex
  right : Fin k
  rightVertex : LocalVertexIndex
  left_lt_right : left.val < right.val
  not_connector :
    Not (IndexedCyclicConnectorPair hk left leftVertex right rightVertex)

namespace NonConnectorRow

def toUpperTrianglePosition
    {k : Nat} {hk : 0 < k}
    (row : NonConnectorRow k hk) : UpperTrianglePosition k where
  left := row.left
  leftVertex := row.leftVertex
  right := row.right
  rightVertex := row.rightVertex
  left_lt_right := row.left_lt_right

theorem positionNonConnector
    {k : Nat} {hk : 0 < k}
    (row : NonConnectorRow k hk) :
    PositionNonConnector hk row.toUpperTrianglePosition :=
  row.not_connector

def polynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} {hk : 0 < k}
    (row : NonConnectorRow k hk) : Real :=
  row.toUpperTrianglePosition.polynomial F hk

end NonConnectorRow

abbrev MissingNonConnectorRowInequality
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} {hk : 0 < k}
    (row : NonConnectorRow k hk) : Prop :=
  1 <= row.polynomial F

structure MissingNonConnectorRows
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  inequality :
    forall row : NonConnectorRow k hk,
      MissingNonConnectorRowInequality F row

namespace MissingNonConnectorRows

def toPositionPolynomialCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (H : MissingNonConnectorRows F k hk) :
    PositionPolynomialCertificate F k hk where
  polynomial_ge_one := by
    intro p hp
    exact H.inequality
      { left := p.left
        leftVertex := p.leftVertex
        right := p.right
        rightVertex := p.rightVertex
        left_lt_right := p.left_lt_right
        not_connector := hp }

def toPositionValueCertificate
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (H : MissingNonConnectorRows F k hk) :
    PositionValueCertificate F k hk where
  value := fun p => p.polynomial F hk
  value_eq_polynomial := by
    intro _p _hp
    rfl
  value_ge_one := by
    intro p hp
    exact H.inequality
      { left := p.left
        leftVertex := p.leftVertex
        right := p.right
        rightVertex := p.rightVertex
        left_lt_right := p.left_lt_right
        not_connector := hp }

def toSqValueTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (H : MissingNonConnectorRows F k hk) :
    UpperTriangleNonConnectorSqValueTable F k hk :=
  H.toPositionValueCertificate.toUpperTriangleNonConnectorSqValueTable

def toValueMatrix
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (H : MissingNonConnectorRows F k hk) :
    NonConnectorValueMatrix F k hk where
  value := fun p => p.polynomial F hk
  value_eq_polynomial := by
    intro _p _hp
    rfl
  value_ge_one := by
    intro p hp
    exact H.inequality
      { left := p.left
        leftVertex := p.leftVertex
        right := p.right
        rightVertex := p.rightVertex
        left_lt_right := p.left_lt_right
        not_connector := hp }

end MissingNonConnectorRows

def lengthTwoRowsOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthTwoThreeCaseW10.LengthTwoMissingNonConnectorInequalities F) :
    MissingNonConnectorRows F 2 ConcreteValueCertificateExamples.twoPositive where
  inequality := by
    intro row
    exact
      LengthTwoThreeCaseW10.lengthTwo_polynomial_ge_one_of_missing
        F H row.toUpperTrianglePosition row.positionNonConnector

def lengthThreeRowsOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthTwoThreeCaseW10.LengthThreeMissingNonConnectorInequalities F) :
    MissingNonConnectorRows F 3 LengthTwoThreeCaseW10.threePositive where
  inequality := by
    intro row
    exact
      LengthTwoThreeCaseW10.lengthThree_polynomial_ge_one_of_missing
        F H row.toUpperTrianglePosition row.positionNonConnector

def lengthFourRowsOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourFiveCaseW11.LengthFourMissingNonConnectorInequalities F) :
    MissingNonConnectorRows F 4 LengthFourFiveCaseW11.fourPositive where
  inequality := by
    intro row
    exact
      LengthFourFiveCaseW11.lengthFour_polynomial_ge_one_of_missing
        F H row.toUpperTrianglePosition row.positionNonConnector

def lengthFiveRowsOfMissingInequalities
    (F : RoleHingedPeriodSearchFamily)
    (H : LengthFourFiveCaseW11.LengthFiveMissingNonConnectorInequalities F) :
    MissingNonConnectorRows F 5 LengthFourFiveCaseW11.fivePositive where
  inequality := by
    intro row
    exact
      LengthFourFiveCaseW11.lengthFive_polynomial_ge_one_of_missing
        F H row.toUpperTrianglePosition row.positionNonConnector

theorem lengthOne_missing_row_count :
    0 * 16 * 16 = 0 := by
  norm_num

end

end NonConnectorTableConcreteW14
end PachToth
end ErdosProblems1066
