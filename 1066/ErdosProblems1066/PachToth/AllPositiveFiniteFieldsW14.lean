import ErdosProblems1066.PachToth.FiniteCertificateInstantiationW13
import ErdosProblems1066.PachToth.NonConnectorInstantiationW13
import ErdosProblems1066.PachToth.NonConnectorPolynomialCertificates

set_option autoImplicit false

/-!
# W14 all-positive finite fields

This file isolates the honest all-positive finite-certificate input for the
role-hinged candidate route.  It does not expose a final Pach--Toth endpoint:
the declarations below only turn explicit polynomial lower-bound fields, for
every positive block count, into the W12 field/package surfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace AllPositiveFiniteFieldsW14

namespace W12

abbrev PeriodEquationFields :=
  FiniteCertificateObligationsW12.PeriodEquationFields

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev AllPositiveNonConnectorSqValueCertificate :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorSqValueCertificate

abbrev TableFamilyPackage :=
  FiniteCertificateObligationsW12.TableFamilyPackage

abbrev UpperTriangleNonConnectorSqValueTableFamily :=
  FiniteCertificateObligationsW12.UpperTriangleNonConnectorSqValueTableFamily

abbrev LocalVertexIndex :=
  FiniteCertificateObligationsW12.LocalVertexIndex

end W12

noncomputable section

abbrev PeriodCandidateFamily :=
  ConcretePeriodCandidateSearch.PeriodCandidateFamily

abbrev PositionPolynomialCertificateFamily :=
  NonConnectorPolynomialCertificates.PositionPolynomialCertificateFamily

abbrev CandidatePolynomialCertificateFamily :=
  NonConnectorPolynomialCertificates.CandidatePolynomialCertificateFamily

/-! ## Candidate period fields -/

/-- The W13 period-field adapter, with the W14 spelling used below. -/
def periodFieldsOfCandidateFamily
    (F : PeriodCandidateFamily) :
    W12.PeriodEquationFields :=
  FiniteCertificateInstantiationW13.periodFieldsOfPeriodCandidateFamily F

@[simp]
theorem periodFieldsOfCandidateFamily_toRoleHingedPeriodSearchFamily
    (F : PeriodCandidateFamily) :
    (periodFieldsOfCandidateFamily F).toRoleHingedPeriodSearchFamily =
      F.toRoleHingedPeriodSearchFamily :=
  rfl

/-! ## Polynomial-backed non-connector value fields -/

/-- The value table used by W12 when the generator proves the polynomial
inequality directly. -/
def polynomialSqValue
    (F : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : W12.LocalVertexIndex)
    (j : Fin k) (v : W12.LocalVertexIndex) : Real :=
  CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
    (periodFieldsOfCandidateFamily F).toRoleHingedPeriodSearchFamily
    hk i u j v

@[simp]
theorem polynomialSqValue_eq_polynomial
    (F : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : W12.LocalVertexIndex)
    (j : Fin k) (v : W12.LocalVertexIndex) :
    polynomialSqValue F k hk i u j v =
      CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
        (periodFieldsOfCandidateFamily F).toRoleHingedPeriodSearchFamily
        hk i u j v :=
  rfl

theorem fin_ne_of_val_lt
    {k : Nat} {i j : Fin k} (hlt : i.val < j.val) : Ne i j := by
  intro h
  subst j
  exact (Nat.lt_irrefl i.val) hlt

/-- A candidate-period family plus polynomial lower-bound certificates
instantiates the raw W12 all-positive non-connector fields. -/
def fieldsOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.AllPositiveNonConnectorFields where
  period := periodFieldsOfCandidateFamily C.period
  value := polynomialSqValue C.period
  value_eq_polynomial_lt := by
    intro _k _hk _i _u _j _v _hlt _hnot_connector
    rfl
  value_ge_one_lt := by
    intro k hk i u j v hlt hnot_connector
    exact
      (C.certificates.certificate k hk).orderedPolynomial_ge_one
        i u j v (fin_ne_of_val_lt hlt) hnot_connector

@[simp]
theorem fieldsOfCandidatePolynomialCertificateFamily_period
    (C : CandidatePolynomialCertificateFamily) :
    (fieldsOfCandidatePolynomialCertificateFamily C).period =
      periodFieldsOfCandidateFamily C.period :=
  rfl

@[simp]
theorem fieldsOfCandidatePolynomialCertificateFamily_value
    (C : CandidatePolynomialCertificateFamily)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : W12.LocalVertexIndex)
    (j : Fin k) (v : W12.LocalVertexIndex) :
    (fieldsOfCandidatePolynomialCertificateFamily C).value k hk i u j v =
      CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
        (periodFieldsOfCandidateFamily C.period).toRoleHingedPeriodSearchFamily
        hk i u j v :=
  rfl

theorem fieldsOfCandidatePolynomialCertificateFamily_value_ge_one_lt
    (C : CandidatePolynomialCertificateFamily)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : W12.LocalVertexIndex)
    (j : Fin k) (v : W12.LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector :
      Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair hk i u j v)) :
    1 <= (fieldsOfCandidatePolynomialCertificateFamily C).value k hk i u j v :=
  (fieldsOfCandidatePolynomialCertificateFamily C).value_ge_one_lt
    k hk i u j v hlt hnot_connector

/-- The native upper-triangle table family obtained from the polynomial
fields. -/
def sqValueTableFamilyOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.UpperTriangleNonConnectorSqValueTableFamily
      (periodFieldsOfCandidateFamily C.period).toRoleHingedPeriodSearchFamily :=
  (fieldsOfCandidatePolynomialCertificateFamily C).toSqValueTableFamily

/-- The W12 table-family package for the all-positive candidate route. -/
def tableFamilyPackageOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.TableFamilyPackage where
  period := periodFieldsOfCandidateFamily C.period
  tableFamily := sqValueTableFamilyOfCandidatePolynomialCertificateFamily C

/-- The compact W12 all-positive non-connector square-value certificate. -/
def certificateOfCandidatePolynomialCertificateFamily
    (C : CandidatePolynomialCertificateFamily) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  (fieldsOfCandidatePolynomialCertificateFamily C).toCertificate

/-! ## Exact remaining concrete table fields -/

/-- The exact remaining concrete table fields for one all-positive
period-candidate family: every positive block count and every non-connector
upper-triangle packed position has polynomial square-distance at least one. -/
structure ExactMissingConcreteTableFields
    (F : PeriodCandidateFamily) where
  polynomial_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (p : NonConnectorPolynomialCertificates.UpperTrianglePosition k),
        NonConnectorPolynomialCertificates.PositionNonConnector hk p ->
          1 <= p.polynomial F.toRoleHingedPeriodSearchFamily hk

namespace ExactMissingConcreteTableFields

def toPositionPolynomialCertificateFamily
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    PositionPolynomialCertificateFamily F.toRoleHingedPeriodSearchFamily where
  certificate := fun k hk =>
    { polynomial_ge_one := D.polynomial_ge_one k hk }

def toCandidatePolynomialCertificateFamily
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    CandidatePolynomialCertificateFamily where
  period := F
  certificates := D.toPositionPolynomialCertificateFamily

def toFields
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    W12.AllPositiveNonConnectorFields :=
  fieldsOfCandidatePolynomialCertificateFamily
    D.toCandidatePolynomialCertificateFamily

def toTableFamilyPackage
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    W12.TableFamilyPackage :=
  tableFamilyPackageOfCandidatePolynomialCertificateFamily
    D.toCandidatePolynomialCertificateFamily

def toCertificate
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F) :
    W12.AllPositiveNonConnectorSqValueCertificate :=
  certificateOfCandidatePolynomialCertificateFamily
    D.toCandidatePolynomialCertificateFamily

@[simp]
theorem toFields_value
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : W12.LocalVertexIndex)
    (j : Fin k) (v : W12.LocalVertexIndex) :
    D.toFields.value k hk i u j v =
      CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
        (periodFieldsOfCandidateFamily F).toRoleHingedPeriodSearchFamily
        hk i u j v :=
  rfl

theorem toFields_value_ge_one_lt
    {F : PeriodCandidateFamily}
    (D : ExactMissingConcreteTableFields F)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : W12.LocalVertexIndex)
    (j : Fin k) (v : W12.LocalVertexIndex)
    (hlt : i.val < j.val)
    (hnot_connector :
      Not (CrossBlockSqTableSearch.IndexedCyclicConnectorPair hk i u j v)) :
    1 <= D.toFields.value k hk i u j v :=
  D.toFields.value_ge_one_lt k hk i u j v hlt hnot_connector

end ExactMissingConcreteTableFields

end

end AllPositiveFiniteFieldsW14
end PachToth
end ErdosProblems1066
