import ErdosProblems1066.PachToth.ConcreteReducedMetricCertificatesW26
import ErdosProblems1066.PachToth.ConcreteCrossBlockFamilyInhabitationW23
import ErdosProblems1066.PachToth.PolynomialCertificateExtraction

set_option autoImplicit false

/-!
# W27 finite reduced-metric certificate adapters

This file is only a source-data handoff.  It routes the already finite
polynomial/value/table certificate surfaces into the W25 same-family reduced
metric fields and into the W26 concrete reduced-metric certificate package.

The concrete W26 route still requires an actual concrete finite value-row or
lower-table package.  The final section names that exact row package rather
than assuming it.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteReducedMetricCertificatesW27

open FiniteGraph

noncomputable section

abbrev RoleHingedPeriodSearchFamily : Type :=
  PolynomialCertificateExtraction.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex : Type :=
  PolynomialCertificateExtraction.LocalVertexIndex

abbrev GeneratedPointPolynomialCertificateFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  PolynomialCertificateExtraction.GeneratedPointPolynomialCertificateFamily F

abbrev GeneratedPointValueCertificateFamily
    (F : RoleHingedPeriodSearchFamily) : Type :=
  PolynomialCertificateExtraction.GeneratedPointValueCertificateFamily F

abbrev ConcreteGeneratedPointValueCertificateFamily : Type :=
  PolynomialCertificateExtraction.ConcreteGeneratedPointValueCertificateFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteReducedMetricCertificate : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteReducedMetricCertificate

abbrev RoleHingedGeneratedChainFamily
    (F : RoleHingedPeriodSearchFamily) :
    ReducedMetricFieldsSameFamilyW25.GeneratedChainFamily :=
  ReducedMetricFieldsSameFamilyW25.roleHingedGeneratedChainFamily F

abbrev W25ReducedMetricFields
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ReducedMetricFieldsSameFamilyW25.ReducedMetricFields
    (RoleHingedGeneratedChainFamily F)

abbrev W26ReducedMetricFields
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  ReducedMetricFieldsSameFamilyW25.ReducedMetricFields
    ((ConcreteReducedMetricCertificatesW26.directReducedSourceFieldsOfConcreteLowerTables
      C).toSourceFields.family)

abbrev GeneratedPointPolynomialInequalityRows
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex),
      i.val < j.val ->
        Not (PolynomialCertificateExtraction.IndexedCyclicConnectorPair
          hk i u j v) ->
          1 <=
            GeneratedPolynomialLowerTableRoute.indexedGeneratedPointSqPolynomial
              F hk i u j v

/-! ## Polynomial rows feed the W25 same-family reduced metric fields -/

def polynomialCertificateFamilyOfInequalityRows
    (F : RoleHingedPeriodSearchFamily)
    (rows : GeneratedPointPolynomialInequalityRows F) :
    GeneratedPointPolynomialCertificateFamily F :=
  PolynomialCertificateExtraction.polynomialCertificateFamilyOfGeneratedPointPolynomialFacts
    F rows

def w25FieldsOfGeneratedPointPolynomialInequalityRows
    (F : RoleHingedPeriodSearchFamily)
    (rows : GeneratedPointPolynomialInequalityRows F) :
    W25ReducedMetricFields F :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfGeneratedPointPolynomialFacts
    F rows

def w25FieldsOfGeneratedPointPolynomialCertificates
    {F : RoleHingedPeriodSearchFamily}
    (C : GeneratedPointPolynomialCertificateFamily F) :
    W25ReducedMetricFields F :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfGeneratedPointPolynomialCertificateFamily
    C

def w25FieldsOfGeneratedPointValueCertificates
    {F : RoleHingedPeriodSearchFamily}
    (C : GeneratedPointValueCertificateFamily F) :
    W25ReducedMetricFields F :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfGeneratedPointValueCertificateFamily
    C

@[simp]
theorem w25FieldsOfGeneratedPointPolynomialInequalityRows_eq_certificates
    (F : RoleHingedPeriodSearchFamily)
    (rows : GeneratedPointPolynomialInequalityRows F) :
    w25FieldsOfGeneratedPointPolynomialInequalityRows F rows =
      w25FieldsOfGeneratedPointPolynomialCertificates
        (polynomialCertificateFamilyOfInequalityRows F rows) := by
  rfl

/-! ## Concrete value/table certificates feed the W26 concrete package -/

def concreteLowerTablesOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockFamilyInhabitationW23.concreteLowerTableFamilyOfValueMatrixFamily
    C

def concreteLowerTablesOfConcreteValueMatrixRows
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockFamilyInhabitationW23.concreteLowerTableFamilyOfRowPackage
    P

def concreteLowerTablesOfConcreteGeneratedPointValueCertificates
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockFamilyInhabitationW23.concreteLowerTableFamilyOfGeneratedPointValueCertificates
    C

def w26CertificateOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ConcreteReducedMetricCertificate :=
  ConcreteReducedMetricCertificatesW26.concreteReducedMetricCertificateOfLowerTables
    C

def w26CertificateOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ConcreteReducedMetricCertificate :=
  w26CertificateOfConcreteLowerTables
    (concreteLowerTablesOfConcreteValueMatrixFamily C)

def w26CertificateOfConcreteValueMatrixRows
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteReducedMetricCertificate :=
  w26CertificateOfConcreteLowerTables
    (concreteLowerTablesOfConcreteValueMatrixRows P)

def w26CertificateOfConcreteGeneratedPointValueCertificates
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    ConcreteReducedMetricCertificate :=
  w26CertificateOfConcreteLowerTables
    (concreteLowerTablesOfConcreteGeneratedPointValueCertificates C)

def w26FieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    W26ReducedMetricFields C :=
  ConcreteReducedMetricCertificatesW26.reducedMetricFieldsOfConcreteLowerTables
    C

def w26FieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    W26ReducedMetricFields
      (concreteLowerTablesOfConcreteValueMatrixFamily C) :=
  w26FieldsOfConcreteLowerTables
    (concreteLowerTablesOfConcreteValueMatrixFamily C)

def w26FieldsOfConcreteValueMatrixRows
    (P : ConcreteValueMatrixRowPackage) :
    W26ReducedMetricFields
      (concreteLowerTablesOfConcreteValueMatrixRows P) :=
  w26FieldsOfConcreteLowerTables
    (concreteLowerTablesOfConcreteValueMatrixRows P)

def w26FieldsOfConcreteGeneratedPointValueCertificates
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    W26ReducedMetricFields
      (concreteLowerTablesOfConcreteGeneratedPointValueCertificates C) :=
  w26FieldsOfConcreteLowerTables
    (concreteLowerTablesOfConcreteGeneratedPointValueCertificates C)

/-! ## The same concrete finite data also feeds the W25 same-family route -/

def w25FieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    W25ReducedMetricFields C.toRoleHingedPeriodSearchFamily :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfConcreteLowerTableFamily C

def w25FieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    W25ReducedMetricFields C.toRoleHingedPeriodSearchFamily :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfConcreteValueMatrixFamily C

def w25FieldsOfConcreteValueMatrixRows
    (P : ConcreteValueMatrixRowPackage) :
    W25ReducedMetricFields
      P.periodSearch.toRoleHingedPeriodSearchFamily :=
  ReducedMetricFieldsSameFamilyW25.fieldsOfConcreteValueMatrixRows P

def w25FieldsOfConcreteGeneratedPointValueCertificates
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    W25ReducedMetricFields C.toRoleHingedPeriodSearchFamily :=
  w25FieldsOfGeneratedPointValueCertificates C.certificates

/-! ## Nonempty handoffs and the exact finite row still needed -/

theorem nonempty_w26Certificate_of_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      Nonempty ConcreteReducedMetricCertificate := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro (w26CertificateOfConcreteLowerTables C)

theorem nonempty_w26Certificate_of_concreteValueMatrixFamily :
    Nonempty ConcreteValueMatrixFamily ->
      Nonempty ConcreteReducedMetricCertificate := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro (w26CertificateOfConcreteValueMatrixFamily C)

theorem nonempty_w26Certificate_of_concreteValueMatrixRows :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty ConcreteReducedMetricCertificate := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (w26CertificateOfConcreteValueMatrixRows P)

theorem nonempty_w26Certificate_of_concreteGeneratedPointValueCertificates :
    Nonempty ConcreteGeneratedPointValueCertificateFamily ->
      Nonempty ConcreteReducedMetricCertificate := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro
        (w26CertificateOfConcreteGeneratedPointValueCertificates C)

/-- The finite value-row package whose inhabitant would give a concrete W26
reduced-metric certificate through this file.  Its fields are the concrete
period search data, the length `2`/`3` value rows, the length `4`/`5` value
rows, and the tail value rows. -/
abbrev ExactFiniteValueInequalityRowsStillNeeded : Type :=
  ConcreteValueMatrixRowPackage

theorem nonempty_exactFiniteValueInequalityRowsStillNeeded_iff_valueMatrix :
    Nonempty ExactFiniteValueInequalityRowsStillNeeded <->
      Nonempty ConcreteValueMatrixFamily :=
  (ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage).symm

theorem nonempty_w26Certificate_of_exactFiniteValueInequalityRowsStillNeeded :
    Nonempty ExactFiniteValueInequalityRowsStillNeeded ->
      Nonempty ConcreteReducedMetricCertificate :=
  nonempty_w26Certificate_of_concreteValueMatrixRows

end

end FiniteReducedMetricCertificatesW27
end PachToth

namespace Verified

abbrev PachTothW27ExactFiniteValueInequalityRowsStillNeeded : Type :=
  PachToth.FiniteReducedMetricCertificatesW27.ExactFiniteValueInequalityRowsStillNeeded

abbrev PachTothW27ConcreteReducedMetricCertificate : Type :=
  PachToth.FiniteReducedMetricCertificatesW27.ConcreteReducedMetricCertificate

theorem pachtoth_w27_nonempty_concreteReducedMetricCertificate_of_exactFiniteRows :
    Nonempty PachTothW27ExactFiniteValueInequalityRowsStillNeeded ->
      Nonempty PachTothW27ConcreteReducedMetricCertificate :=
  PachToth.FiniteReducedMetricCertificatesW27.nonempty_w26Certificate_of_exactFiniteValueInequalityRowsStillNeeded

end Verified
end ErdosProblems1066
