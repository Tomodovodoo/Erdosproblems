import ErdosProblems1066.PachToth.FiniteCertificateObligationsW12
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.ConcreteValueCertificateExamples
import ErdosProblems1066.PachToth.RemainderConstruction

set_option autoImplicit false

/-!
# W13 finite-certificate instantiation

This file is intentionally only an instantiation layer.  It projects the
concrete finite data shapes already present in the Pach--Toth directory into
the W12 finite-certificate facade, and it records the exact conditional routes
used once a finite table family is supplied.

Finite table data for the all-positive non-connector row should inhabit one
of these concrete surfaces:

* `ErdosProblems1066/PachToth/ConcreteNonConnectorValueMatrix.lean`:
  `ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily` or
  `ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily`.
* `ErdosProblems1066/PachToth/FiniteCertificateSearchSurface.lean`:
  `FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueVectorCertificateFamily`
  or
  `FiniteCertificateSearchSurface.UpperTriangleNonConnectorSqValueListCertificateFamily`.

The checked remainder construction used by the arbitrary-`n` route is
available in `ErdosProblems1066/PachToth/RemainderConstruction.lean` as
`RemainderConstruction.exists_remainder_config_mod_sixteen`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteCertificateInstantiationW13

namespace W12

abbrev PeriodEquationFields :=
  FiniteCertificateObligationsW12.PeriodEquationFields

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev AllPositiveNonConnectorSqValueCertificate :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorSqValueCertificate

abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  FiniteCertificateObligationsW12.UpperTriangleNonConnectorSqValueTableFamily

abbrev VectorTableFamily :=
  FiniteCertificateObligationsW12.VectorTableFamily

abbrev ListTableFamily :=
  FiniteCertificateObligationsW12.ListTableFamily

abbrev TableFamilyPackage :=
  FiniteCertificateObligationsW12.TableFamilyPackage

abbrev VectorPackage :=
  FiniteCertificateObligationsW12.VectorPackage

abbrev ListPackage :=
  FiniteCertificateObligationsW12.ListPackage

abbrev ExactTarget :=
  FiniteCertificateObligationsW12.ExactTarget

abbrev ArbitraryTarget :=
  FiniteCertificateObligationsW12.ArbitraryTarget

abbrev ExactBlockTarget :=
  FiniteCertificateObligationsW12.ExactBlockTarget

end W12

noncomputable section

/-! ## Period-field instantiations -/

/-- The concrete period-search family has exactly the raw W12 period-field
shape: one finite word and its exact `Fin 16` algebraic equations for every
positive block count. -/
def periodFieldsOfPeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    W12.PeriodEquationFields where
  transitions := F.transitions
  word := F.word
  equation := F.equation

@[simp]
theorem periodFieldsOfPeriodSearchData_transitions
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    (periodFieldsOfPeriodSearchData F).transitions = F.transitions :=
  rfl

@[simp]
theorem periodFieldsOfPeriodSearchData_word
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (periodFieldsOfPeriodSearchData F).word k hk = F.word k hk :=
  rfl

@[simp]
theorem periodFieldsOfPeriodSearchData_orientation
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (periodFieldsOfPeriodSearchData F).orientation k hk =
      F.orientation k hk :=
  rfl

@[simp]
theorem periodFieldsOfPeriodSearchData_equation
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (k : Nat) (hk : 0 < k) (i : Fin 16) :
    (periodFieldsOfPeriodSearchData F).equation k hk i =
      F.equation k hk i :=
  rfl

/-- Role-hinge period candidates also instantiate the W12 period-field row,
after forgetting the transition-fact wrapper to its transition obligations. -/
def periodFieldsOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :
    W12.PeriodEquationFields where
  transitions := F.transitions.toRoleHingeTransitions
  word := F.word
  equation := by
    intro k hk i
    simpa [ConcretePeriodCandidateSearch.transitionObligationsOfFacts]
      using (F.period k hk).equation i

@[simp]
theorem periodFieldsOfPeriodCandidateFamily_transitions
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :
    (periodFieldsOfPeriodCandidateFamily F).transitions =
      F.transitions.toRoleHingeTransitions :=
  rfl

@[simp]
theorem periodFieldsOfPeriodCandidateFamily_word
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) :
    (periodFieldsOfPeriodCandidateFamily F).word k hk = F.word k hk :=
  rfl

@[simp]
theorem periodFieldsOfPeriodCandidateFamily_orientation
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) :
    (periodFieldsOfPeriodCandidateFamily F).orientation k hk =
      F.orientation k hk :=
  rfl

/-! ## W12 table-package instantiations -/

/-- Native upper-triangle non-connector tables over concrete period data
instantiate the W12 native-table package. -/
def tableFamilyPackageOfPeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.UpperTriangleNonConnectorSqValueTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.TableFamilyPackage where
  period := periodFieldsOfPeriodSearchData F
  tableFamily := T

/-- Vector-grid tables over concrete period data instantiate the W12 vector
package. -/
def vectorPackageOfPeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.VectorTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.VectorPackage where
  period := periodFieldsOfPeriodSearchData F
  tables := T

/-- Row-list tables over concrete period data instantiate the W12 list
package. -/
def listPackageOfPeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.ListTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.ListPackage where
  period := periodFieldsOfPeriodSearchData F
  tables := T

/-- Native upper-triangle non-connector tables over role-hinge candidates
instantiate the W12 native-table package. -/
def tableFamilyPackageOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.UpperTriangleNonConnectorSqValueTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.TableFamilyPackage where
  period := periodFieldsOfPeriodCandidateFamily F
  tableFamily := T

/-- Vector-grid tables over role-hinge candidates instantiate the W12 vector
package. -/
def vectorPackageOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.VectorTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.VectorPackage where
  period := periodFieldsOfPeriodCandidateFamily F
  tables := T

/-- Row-list tables over role-hinge candidates instantiate the W12 list
package. -/
def listPackageOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.ListTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.ListPackage where
  period := periodFieldsOfPeriodCandidateFamily F
  tables := T

/-! ## Concrete value-matrix instantiations -/

/-- Concrete value matrices instantiate the raw W12 all-positive
non-connector fields. -/
def fieldsOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    W12.AllPositiveNonConnectorFields where
  period := periodFieldsOfPeriodSearchData C.periodSearch
  value := fun k hk => (C.matrices.matrix k hk).toSqValueTable.value
  value_eq_polynomial_lt := by
    intro k hk i u j v hlt hnot_connector
    exact
      (C.matrices.matrix k hk).toSqValueTable.value_eq_polynomial_lt
        i u j v hlt hnot_connector
  value_ge_one_lt := by
    intro k hk i u j v hlt hnot_connector
    exact
      (C.matrices.matrix k hk).toSqValueTable.value_ge_one_lt
        i u j v hlt hnot_connector

/-- Candidate value matrices instantiate the raw W12 all-positive
non-connector fields. -/
def fieldsOfCandidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    W12.AllPositiveNonConnectorFields where
  period := periodFieldsOfPeriodCandidateFamily C.period
  value := fun k hk => (C.matrices.matrix k hk).toSqValueTable.value
  value_eq_polynomial_lt := by
    intro k hk i u j v hlt hnot_connector
    exact
      (C.matrices.matrix k hk).toSqValueTable.value_eq_polynomial_lt
        i u j v hlt hnot_connector
  value_ge_one_lt := by
    intro k hk i u j v hlt hnot_connector
    exact
      (C.matrices.matrix k hk).toSqValueTable.value_ge_one_lt
        i u j v hlt hnot_connector

/-- Concrete value matrices as a compact W12 certificate. -/
def certificateOfConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  (fieldsOfConcreteValueMatrixFamily C).toCertificate

/-- Candidate value matrices as a compact W12 certificate. -/
def certificateOfCandidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  (fieldsOfCandidateValueMatrixFamily C).toCertificate

/-! ## Checked target routes -/

theorem targetUpperConstructionFiveSixteenAt_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  (fieldsOfConcreteValueMatrixFamily C).targetUpperConstructionFiveSixteenAt_exactBlock
    k hk

theorem targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    W12.ExactTarget :=
  (fieldsOfConcreteValueMatrixFamily C).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    W12.ArbitraryTarget :=
  (fieldsOfConcreteValueMatrixFamily C).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    W12.ExactBlockTarget k :=
  (fieldsOfCandidateValueMatrixFamily C).targetUpperConstructionFiveSixteenAt_exactBlock
    k hk

theorem targetUpperConstructionFiveSixteen_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    W12.ExactTarget :=
  (fieldsOfCandidateValueMatrixFamily C).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    W12.ArbitraryTarget :=
  (fieldsOfCandidateValueMatrixFamily C).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_periodSearchData_tableFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.UpperTriangleNonConnectorSqValueTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.ExactTarget :=
  (tableFamilyPackageOfPeriodSearchData F T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_tableFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.UpperTriangleNonConnectorSqValueTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.ArbitraryTarget :=
  (tableFamilyPackageOfPeriodSearchData F T).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_periodSearchData_vectorFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.VectorTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.ExactTarget :=
  (vectorPackageOfPeriodSearchData F T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_vectorFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.VectorTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.ArbitraryTarget :=
  (vectorPackageOfPeriodSearchData F T).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_periodSearchData_listFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.ListTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.ExactTarget :=
  (listPackageOfPeriodSearchData F T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchData_listFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (T :
      W12.ListTableFamily
        (periodFieldsOfPeriodSearchData F).toRoleHingedPeriodSearchFamily) :
    W12.ArbitraryTarget :=
  (listPackageOfPeriodSearchData F T).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_periodCandidateFamily_tableFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.UpperTriangleNonConnectorSqValueTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.ExactTarget :=
  (tableFamilyPackageOfPeriodCandidateFamily F T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCandidateFamily_tableFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.UpperTriangleNonConnectorSqValueTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.ArbitraryTarget :=
  (tableFamilyPackageOfPeriodCandidateFamily F T).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_periodCandidateFamily_vectorFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.VectorTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.ExactTarget :=
  (vectorPackageOfPeriodCandidateFamily F T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCandidateFamily_vectorFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.VectorTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.ArbitraryTarget :=
  (vectorPackageOfPeriodCandidateFamily F T).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_periodCandidateFamily_listFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.ListTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.ExactTarget :=
  (listPackageOfPeriodCandidateFamily F T).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCandidateFamily_listFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (T :
      W12.ListTableFamily
        (periodFieldsOfPeriodCandidateFamily F).toRoleHingedPeriodSearchFamily) :
    W12.ArbitraryTarget :=
  (listPackageOfPeriodCandidateFamily F T).targetUpperConstructionFiveSixteenArbitrary

/-! ## Remainder side recorded for the arbitrary-`n` split -/

theorem exists_remainder_config_mod_sixteen
    {r : Nat} (hr : r < 16) :
    Exists fun C : _root_.UDConfig r =>
      forall s : Finset (Fin r), C.IsIndep s -> s.card <= Arithmetic.ceilDiv r 3 :=
  RemainderConstruction.exists_remainder_config_mod_sixteen hr

/-! ## W13 route ledger -/

structure Matrix where
  periodSearchData :
    ConcretePeriodSearchFamily.PeriodSearchData -> W12.PeriodEquationFields
  periodCandidateFamily :
    ConcretePeriodCandidateSearch.PeriodCandidateFamily ->
      W12.PeriodEquationFields
  concreteValueMatrices :
    ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily ->
      W12.AllPositiveNonConnectorFields
  candidateValueMatrices :
    ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily ->
      W12.AllPositiveNonConnectorFields
  concreteValueMatrixExact :
    ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily -> W12.ExactTarget
  concreteValueMatrixArbitrary :
    ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily -> W12.ArbitraryTarget
  candidateValueMatrixExact :
    ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily -> W12.ExactTarget
  candidateValueMatrixArbitrary :
    ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily -> W12.ArbitraryTarget

def matrix : Matrix where
  periodSearchData := periodFieldsOfPeriodSearchData
  periodCandidateFamily := periodFieldsOfPeriodCandidateFamily
  concreteValueMatrices := fieldsOfConcreteValueMatrixFamily
  candidateValueMatrices := fieldsOfCandidateValueMatrixFamily
  concreteValueMatrixExact := targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily
  concreteValueMatrixArbitrary :=
    targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily
  candidateValueMatrixExact := targetUpperConstructionFiveSixteen_of_candidateValueMatrixFamily
  candidateValueMatrixArbitrary :=
    targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily

end

end FiniteCertificateInstantiationW13
end PachToth
end ErdosProblems1066
