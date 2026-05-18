import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.CrossBlockSqTableSearch

set_option autoImplicit false

/-!
# Non-rigid finite-certificate obligation summary

This module records the compact input package for the current non-rigid
finite-certificate route.  The remaining data are:

* role-hinged period-search data, including the transition metric package,
  one finite orientation word for each positive block count, and the indexed
  algebraic period equations; and
* upper-triangle square-distance value tables proving generated cross-block
  separation for each positive block count.

The proof below routes only through the role-hinged/generated-chain and
cross-block square-table bridges.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteCertificateObligationSummary

noncomputable section

abbrev PeriodSearchData :=
  ConcretePeriodSearchFamily.PeriodSearchData

abbrev RoleHingeTransitions :=
  ConcretePeriodSearchFamily.RoleHingeTransitions

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockSqTableSearch.LocalVertexIndex

abbrev UpperTriangleSqValueTable :=
  CrossBlockSqTableSearch.UpperTriangleSqValueTable

abbrev UpperTrianglePolynomialTableFamily :=
  CrossBlockSqTableSearch.UpperTrianglePolynomialTableFamily

abbrev UpperTriangleSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily

abbrev IndexedCrossBlockSqDistanceTableFamily :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTableFamily

/-- The square-value half of the finite-certificate checklist, once the
role-hinged period-search data has been fixed.

For every positive block count, generated scripts still need to provide an
upper-triangle value table, prove that each stored value is the generated
coordinate square polynomial, and prove that the stored value is at least
`1`. -/
structure SqValueCertificate (periodSearch : PeriodSearchData) where
  value :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  value_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          value k hk i u j v =
            CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
              periodSearch.toRoleHingedPeriodSearchFamily hk i u j v
  value_ge_one_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val -> 1 <= value k hk i u j v

namespace SqValueCertificate

/-- Project one block count of the checklist to the upper-triangle table
interface consumed by the square-distance reduction. -/
def toSqValueTable
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    UpperTriangleSqValueTable
      periodSearch.toRoleHingedPeriodSearchFamily k hk where
  value := S.value k hk
  value_eq_polynomial_lt := by
    intro i u j v hlt
    exact S.value_eq_polynomial_lt k hk i u j v hlt
  value_ge_one_lt := by
    intro i u j v hlt
    exact S.value_ge_one_lt k hk i u j v hlt

@[simp]
theorem toSqValueTable_value
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    (S.toSqValueTable k hk).value = S.value k hk :=
  rfl

/-- Project the checklist to the table family used by the all-positive
finite square-distance route. -/
def toSqValueTableFamily
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch) :
    UpperTriangleSqValueTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily where
  table := fun k hk => S.toSqValueTable k hk

@[simp]
theorem toSqValueTableFamily_table
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    S.toSqValueTableFamily.table k hk = S.toSqValueTable k hk :=
  rfl

/-- Coordinate-polynomial tables obtained from the checklist. -/
def toPolynomialTableFamily
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch) :
    UpperTrianglePolynomialTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily :=
  S.toSqValueTableFamily.toPolynomialTableFamily

/-- Square-distance table family obtained from the checklist. -/
def toSqDistanceTableFamily
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch) :
    IndexedCrossBlockSqDistanceTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily :=
  S.toSqValueTableFamily.toSqDistanceTableFamily

/-- Cross-block lower-bound facade obtained from the checklist. -/
def toCrossBlockLowerBounds
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      periodSearch.toRoleHingedPeriodSearchFamily :=
  S.toSqValueTableFamily.toCrossBlockLowerBounds

/-- Generated global separation obtained from the remaining square-value
checklist. -/
def separated
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (periodSearch.orientation k hk) :=
  S.toSqDistanceTableFamily.separated k hk

/-- Exact-multiple Pach--Toth target from period-search data plus the
square-value checklist. -/
theorem targetUpperConstructionFiveSixteen
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteen :=
  S.toSqValueTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target from period-search data plus the
square-value checklist. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {periodSearch : PeriodSearchData}
    (S : SqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  S.toSqValueTableFamily.targetUpperConstructionFiveSixteenArbitrary

end SqValueCertificate

/-- The exact remaining data for the current non-rigid finite-certificate
route to the arbitrary Pach--Toth target. -/
structure Obligations where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      PeriodSearchInterface.AlgebraicVertexPeriodEquation
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))
        (BlockPartition.localVertexEquivFin16.symm i)
  sqValue :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  sqValue_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          sqValue k hk i u j v =
            CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
              (ConcretePeriodSearchFamily.PeriodSearchData.toRoleHingedPeriodSearchFamily
                ({ transitions := transitions
                   word := word
                   equation := equation } : PeriodSearchData))
              hk i u j v
  sqValue_ge_one_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val -> 1 <= sqValue k hk i u j v

namespace Obligations

/-- Repackage the explicit transition, word, and period-equation fields as
the reusable concrete period-search data. -/
def toPeriodSearchData
    (O : Obligations) :
    PeriodSearchData where
  transitions := O.transitions
  word := O.word
  equation := O.equation

/-- Project the stored square-value fields to the checklist over the projected
period-search data. -/
def toSqValueCertificate
    (O : Obligations) :
    SqValueCertificate O.toPeriodSearchData where
  value := O.sqValue
  value_eq_polynomial_lt := by
    intro k hk i u j v hlt
    simpa [toPeriodSearchData] using
      O.sqValue_eq_polynomial_lt k hk i u j v hlt
  value_ge_one_lt := by
    intro k hk i u j v hlt
    exact O.sqValue_ge_one_lt k hk i u j v hlt

/-- Assemble the full obligation summary from the period-search checklist and
the remaining square-value checklist. -/
def ofPeriodSearchDataSqValueCertificate
    (periodSearch : PeriodSearchData)
    (sqValue : SqValueCertificate periodSearch) :
    Obligations where
  transitions := periodSearch.transitions
  word := periodSearch.word
  equation := periodSearch.equation
  sqValue := sqValue.value
  sqValue_eq_polynomial_lt := by
    intro k hk i u j v hlt
    simpa using sqValue.value_eq_polynomial_lt k hk i u j v hlt
  sqValue_ge_one_lt := by
    intro k hk i u j v hlt
    exact sqValue.value_ge_one_lt k hk i u j v hlt

@[simp]
theorem toPeriodSearchData_transitions
    (O : Obligations) :
    O.toPeriodSearchData.transitions = O.transitions :=
  rfl

@[simp]
theorem toPeriodSearchData_word
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    O.toPeriodSearchData.word k hk = O.word k hk :=
  rfl

@[simp]
theorem toPeriodSearchData_equation
    (O : Obligations)
    (k : Nat) (hk : 0 < k) (i : Fin 16) :
    O.toPeriodSearchData.equation k hk i =
      O.equation k hk i :=
  rfl

@[simp]
theorem toSqValueCertificate_value
    (O : Obligations) :
    O.toSqValueCertificate.value = O.sqValue :=
  rfl

@[simp]
theorem toSqValueCertificate_value_apply
    (O : Obligations)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    O.toSqValueCertificate.value k hk i u j v =
      O.sqValue k hk i u j v :=
  rfl

@[simp]
theorem ofPeriodSearchDataSqValueCertificate_toPeriodSearchData
    (periodSearch : PeriodSearchData)
    (sqValue : SqValueCertificate periodSearch) :
    (ofPeriodSearchDataSqValueCertificate periodSearch
      sqValue).toPeriodSearchData = periodSearch := by
  cases periodSearch
  rfl

/-- The generated-chain orientation projected from the stored finite word. -/
def orientation
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  O.toPeriodSearchData.orientation k hk

@[simp]
theorem orientation_apply
    (O : Obligations)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    O.orientation k hk i = O.word k hk i :=
  rfl

/-- The finite period-search word projected from the stored word field. -/
def finiteWord
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  O.toPeriodSearchData.finiteWord k hk

@[simp]
theorem finiteWord_length
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    (O.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    (O : Obligations)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (O.finiteWord k hk).letter i = O.orientation k hk i :=
  rfl

/-- The indexed algebraic period certificate obtained from the stored
equations. -/
def indexedCertificate
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (ExactFamilyClosure.finiteOrientationWord k hk
        (O.orientation k hk)) :=
  O.toPeriodSearchData.indexedCertificate k hk

/-- The generated closure equation projected from the indexed certificate. -/
def closure
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      O.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (O.orientation k hk) :=
  O.toPeriodSearchData.closure k hk

/-- The generated final-block period equation projected from the indexed
certificate. -/
def periodEquation
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      O.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (O.orientation k hk) :=
  O.toPeriodSearchData.periodEquation k hk

/-- The role-hinged period-search family exposed by the summary package. -/
def toRoleHingedPeriodSearchFamily
    (O : Obligations) :
    RoleHingedPeriodSearchFamily :=
  O.toPeriodSearchData.toRoleHingedPeriodSearchFamily

@[simp]
theorem toRoleHingedPeriodSearchFamily_eq
    (O : Obligations) :
    O.toRoleHingedPeriodSearchFamily =
      O.toPeriodSearchData.toRoleHingedPeriodSearchFamily :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_transitions
    (O : Obligations) :
    O.toRoleHingedPeriodSearchFamily.transitions = O.transitions :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_orientation
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    O.toRoleHingedPeriodSearchFamily.orientation k hk =
      O.orientation k hk :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_orientation_apply
    (O : Obligations)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    O.toRoleHingedPeriodSearchFamily.orientation k hk i =
      O.word k hk i :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_period
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    O.toRoleHingedPeriodSearchFamily.period k hk =
      O.indexedCertificate k hk :=
  rfl

/-- The upper-triangle square-value table for one positive block count,
rebuilt from the explicit stored value fields. -/
def toSqValueTable
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    UpperTriangleSqValueTable O.toRoleHingedPeriodSearchFamily k hk where
  value := O.sqValue k hk
  value_eq_polynomial_lt := by
    intro i u j v hlt
    simpa [toRoleHingedPeriodSearchFamily, toPeriodSearchData] using
      O.sqValue_eq_polynomial_lt k hk i u j v hlt
  value_ge_one_lt := by
    intro i u j v hlt
    exact O.sqValue_ge_one_lt k hk i u j v hlt

@[simp]
theorem toSqValueTable_value
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    (O.toSqValueTable k hk).value = O.sqValue k hk :=
  rfl

@[simp]
theorem toSqValueTable_value_apply
    (O : Obligations)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    (O.toSqValueTable k hk).value i u j v =
      O.sqValue k hk i u j v :=
  rfl

/-- Projection of the stored computed-value equality to the generated square
coordinate polynomial. -/
theorem sqValue_eq_indexedGeneratedSqPolynomial_lt
    (O : Obligations)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    O.sqValue k hk i u j v =
      CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
        O.toRoleHingedPeriodSearchFamily hk i u j v := by
  simpa [toRoleHingedPeriodSearchFamily, toPeriodSearchData] using
    O.sqValue_eq_polynomial_lt k hk i u j v hlt

/-- Projection of the stored upper-triangle lower bound. -/
theorem sqValue_ge_one_of_lt
    (O : Obligations)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hlt : i.val < j.val) :
    1 <= O.sqValue k hk i u j v :=
  O.sqValue_ge_one_lt k hk i u j v hlt

/-- The family of upper-triangle square-value tables rebuilt from the stored
per-block value fields. -/
def toSqValueTableFamily
    (O : Obligations) :
    UpperTriangleSqValueTableFamily
      O.toRoleHingedPeriodSearchFamily where
  table := fun k hk => O.toSqValueTable k hk

@[simp]
theorem toSqValueTableFamily_table
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    O.toSqValueTableFamily.table k hk =
      O.toSqValueTable k hk :=
  rfl

@[simp]
theorem toSqValueTableFamily_table_value
    (O : Obligations)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    (O.toSqValueTableFamily.table k hk).value i u j v =
      O.sqValue k hk i u j v :=
  rfl

@[simp]
theorem toSqValueCertificate_toSqValueTableFamily
    (O : Obligations) :
    O.toSqValueCertificate.toSqValueTableFamily =
      O.toSqValueTableFamily := by
  rfl

/-- The coordinate-polynomial table family obtained from the stored
upper-triangle value fields. -/
def toPolynomialTableFamily
    (O : Obligations) :
    UpperTrianglePolynomialTableFamily
      O.toRoleHingedPeriodSearchFamily :=
  O.toSqValueTableFamily.toPolynomialTableFamily

/-- The generated square-distance table family obtained from the stored
upper-triangle value tables. -/
def toSqDistanceTableFamily
    (O : Obligations) :
    IndexedCrossBlockSqDistanceTableFamily
      O.toRoleHingedPeriodSearchFamily :=
  O.toSqValueTableFamily.toSqDistanceTableFamily

/-- The cross-block lower-bound facade obtained from the stored finite
square-distance tables. -/
def toCrossBlockLowerBounds
    (O : Obligations) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      O.toRoleHingedPeriodSearchFamily :=
  O.toSqValueTableFamily.toCrossBlockLowerBounds

/-- Generated global separation obtained from the finite square-value
tables. -/
def separated
    (O : Obligations)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (O.orientation k hk) :=
  O.toSqDistanceTableFamily.separated k hk

/-- The role-hinged generated-closure family obtained from the summarized
period and cross-block fields. -/
def toRoleHingedGeneratedClosureFamily
    (O : Obligations) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  O.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

/-- The exact-multiple Pach--Toth target obtained from the summarized
non-rigid finite-certificate obligations. -/
theorem targetUpperConstructionFiveSixteen
    (O : Obligations) :
    PachToth.targetUpperConstructionFiveSixteen :=
  O.toSqValueTableFamily.targetUpperConstructionFiveSixteen

/-- The arbitrary-`n` Pach--Toth target obtained from the summarized
non-rigid finite-certificate obligations. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (O : Obligations) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  O.toSqValueTableFamily.targetUpperConstructionFiveSixteenArbitrary

end Obligations

/-- Exact target from an existing period-search package plus the remaining
square-value checklist. -/
theorem targetUpperConstructionFiveSixteen_of_periodSearchData_sqValueCertificate
    (periodSearch : PeriodSearchData)
    (sqValue : SqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (Obligations.ofPeriodSearchDataSqValueCertificate periodSearch
    sqValue).targetUpperConstructionFiveSixteen

/-- Arbitrary target from an existing period-search package plus the
remaining square-value checklist. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_sqValueCertificate
    (periodSearch : PeriodSearchData)
    (sqValue : SqValueCertificate periodSearch) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (Obligations.ofPeriodSearchDataSqValueCertificate periodSearch
    sqValue).targetUpperConstructionFiveSixteenArbitrary

/-- Arbitrary target from period-search data plus raw square-value facts.
This is the compact checklist theorem for callers that have already assembled
the period-search package and only need to discharge the table generator
facts. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_sqValueFacts
    (periodSearch : PeriodSearchData)
    (sqValue :
      forall (k : Nat), 0 < k ->
        Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real)
    (sqValue_eq_polynomial_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            sqValue k hk i u j v =
              CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                periodSearch.toRoleHingedPeriodSearchFamily hk i u j v)
    (sqValue_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val -> 1 <= sqValue k hk i u j v) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_sqValueCertificate
    periodSearch
    { value := sqValue
      value_eq_polynomial_lt := sqValue_eq_polynomial_lt
      value_ge_one_lt := sqValue_ge_one_lt }

/-- Top-level spelling of the final bridge from the finite-certificate
obligation summary to the arbitrary Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (O : Obligations) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  O.targetUpperConstructionFiveSixteenArbitrary

end

end FiniteCertificateObligationSummary
end PachToth
end ErdosProblems1066
