import ErdosProblems1066.PachToth.GeneratedClosureMetricPackageInhabitationW25
import ErdosProblems1066.PachToth.GeneratedClosureSourceSameFamilyW25
import ErdosProblems1066.PachToth.DirectReducedMetricInputW26
import ErdosProblems1066.PachToth.FiniteReducedMetricCertificatesW27
import ErdosProblems1066.PachToth.ConcreteLowerTableFamilyConstructionW27
import ErdosProblems1066.PachToth.PachTothW27RouteAudit

set_option autoImplicit false

/-!
# W28 generated-closure metric source handoff

This file keeps the generated-closure route separated from the blocked
role-hinged lower-table route.  Concrete value rows can be mapped directly to
the W23/W25 generated-closure metric package through source fields.  Metric
certificates and concrete lower tables also map to that package, but W27 proves
that those inhabitants are unavailable, so the corresponding routes are
recorded as blocked.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedClosureMetricSourceW28

noncomputable section

abbrev GeneratedClosureMetricRowPackage : Type :=
  GeneratedClosureMetricPackageInhabitationW25.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  Nonempty GeneratedClosureMetricRowPackage

abbrev RawSourceFields : Type :=
  GeneratedClosureMetricPackageInhabitationW25.RawSourceFields

abbrev ConcreteValueMatrixRowPackage : Type :=
  FiniteReducedMetricCertificatesW27.ConcreteValueMatrixRowPackage

abbrev ExactFiniteValueInequalityRowsStillNeeded : Type :=
  FiniteReducedMetricCertificatesW27.ExactFiniteValueInequalityRowsStillNeeded

abbrev ConcreteValueMatrixFamily : Type :=
  FiniteReducedMetricCertificatesW27.ConcreteValueMatrixFamily

abbrev ConcreteGeneratedPointValueCertificateFamily : Type :=
  FiniteReducedMetricCertificatesW27.ConcreteGeneratedPointValueCertificateFamily

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  FiniteReducedMetricCertificatesW27.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteReducedMetricCertificate : Type :=
  FiniteReducedMetricCertificatesW27.ConcreteReducedMetricCertificate

abbrev RoleHingedPeriodSearchFamily : Type :=
  FiniteReducedMetricCertificatesW27.RoleHingedPeriodSearchFamily

/-! ## Direct finite-row to generated-closure package path -/

def rawSourceFieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    RawSourceFields :=
  GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixFamily
    C

def rawSourceFieldsOfFiniteValueRows
    (P : ConcreteValueMatrixRowPackage) :
    RawSourceFields :=
  GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixRowPackage
    P

def generatedClosureMetricRowPackageOfRawSourceFields
    (S : RawSourceFields) :
    GeneratedClosureMetricRowPackage :=
  GeneratedClosureMetricPackageInhabitationW25.generatedClosureMetricRowPackageOfRawSourceFields
    S

def generatedClosureMetricRowPackageOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfRawSourceFields
    (rawSourceFieldsOfConcreteValueMatrixFamily C)

def generatedClosureMetricRowPackageOfFiniteValueRows
    (P : ConcreteValueMatrixRowPackage) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfRawSourceFields
    (rawSourceFieldsOfFiniteValueRows P)

def generatedClosureMetricRowPackageOfExactFiniteValueRows
    (P : ExactFiniteValueInequalityRowsStillNeeded) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfFiniteValueRows P

@[simp]
theorem generatedClosureMetricRowPackageOfFiniteValueRows_family
    (P : ConcreteValueMatrixRowPackage) :
    (generatedClosureMetricRowPackageOfFiniteValueRows P).family =
      (rawSourceFieldsOfFiniteValueRows P).family := by
  rfl

@[simp]
theorem generatedClosureMetricRowPackageOfConcreteValueMatrixFamily_family
    (C : ConcreteValueMatrixFamily) :
    (generatedClosureMetricRowPackageOfConcreteValueMatrixFamily C).family =
      (rawSourceFieldsOfConcreteValueMatrixFamily C).family := by
  rfl

theorem generatedClosureMetricGate_of_finiteValueRows :
    Nonempty ConcreteValueMatrixRowPackage -> GeneratedClosureMetricGate := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro
        (generatedClosureMetricRowPackageOfFiniteValueRows P)

theorem generatedClosureMetricGate_of_exactFiniteValueRows :
    Nonempty ExactFiniteValueInequalityRowsStillNeeded ->
      GeneratedClosureMetricGate :=
  generatedClosureMetricGate_of_finiteValueRows

theorem generatedClosureMetricGate_of_concreteValueMatrixFamily :
    Nonempty ConcreteValueMatrixFamily -> GeneratedClosureMetricGate := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro
        (generatedClosureMetricRowPackageOfConcreteValueMatrixFamily C)

/-! ## Certificate and lower-table handoffs, kept conditional -/

def concreteValueMatrixFamilyOfConcreteGeneratedPointValueCertificates
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    ConcreteValueMatrixFamily :=
  C.toConcreteValueMatrixFamily

def generatedClosureMetricRowPackageOfConcreteGeneratedPointValueCertificates
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfConcreteValueMatrixFamily
    (concreteValueMatrixFamilyOfConcreteGeneratedPointValueCertificates C)

def generatedClosureMetricRowPackageOfConcreteReducedMetricCertificate
    (P : ConcreteReducedMetricCertificate) :
    GeneratedClosureMetricRowPackage :=
  P.generatedClosureMetricRowPackage

def generatedClosureMetricRowPackageOfConcreteLowerTablesViaDirectReducedInput
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedClosureMetricRowPackage :=
  DirectReducedMetricInputW26.generatedClosureMetricRowPackageOfConcreteLowerTables
    C

def generatedClosureMetricRowPackageOfConcreteLowerTablesViaW26Certificate
    (C : ConcreteNonConnectorLowerTableFamily) :
    GeneratedClosureMetricRowPackage :=
  ConcreteReducedMetricCertificatesW26.generatedClosureMetricRowPackageOfConcreteLowerTables
    C

@[simp]
theorem generatedClosureMetricRowPackageOfConcreteLowerTablesViaDirectReducedInput_family
    (C : ConcreteNonConnectorLowerTableFamily) :
    (generatedClosureMetricRowPackageOfConcreteLowerTablesViaDirectReducedInput
      C).family =
        DirectReducedMetricInputW26.directReducedGeneratedChainFamily C := by
  rfl

theorem generatedClosureMetricGate_of_concreteGeneratedPointValueCertificates :
    Nonempty ConcreteGeneratedPointValueCertificateFamily ->
      GeneratedClosureMetricGate := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro
        (generatedClosureMetricRowPackageOfConcreteGeneratedPointValueCertificates
          C)

theorem generatedClosureMetricGate_of_concreteReducedMetricCertificate :
    Nonempty ConcreteReducedMetricCertificate -> GeneratedClosureMetricGate := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro
        (generatedClosureMetricRowPackageOfConcreteReducedMetricCertificate P)

theorem generatedClosureMetricGate_of_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      GeneratedClosureMetricGate := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro
        (generatedClosureMetricRowPackageOfConcreteLowerTablesViaDirectReducedInput
          C)

theorem concreteReducedMetricCertificateGate_iff_concreteLowerTableGate :
    Nonempty ConcreteReducedMetricCertificate <->
      Nonempty ConcreteNonConnectorLowerTableFamily :=
  PachTothW27RouteAudit.concreteReducedMetricCertificateGate_iff_concreteLowerTableGate

/-! ## Route wrappers and recorded obstructions -/

structure FiniteRowsGeneratedClosureRoute where
  rows : ConcreteValueMatrixRowPackage
  package : GeneratedClosureMetricRowPackage
  package_eq :
    package = generatedClosureMetricRowPackageOfFiniteValueRows rows

structure ConcreteValueCertificatesGeneratedClosureRoute where
  certificates : ConcreteGeneratedPointValueCertificateFamily
  package : GeneratedClosureMetricRowPackage
  package_eq :
    package =
      generatedClosureMetricRowPackageOfConcreteGeneratedPointValueCertificates
        certificates

structure ReducedMetricCertificateGeneratedClosureRoute where
  certificate : ConcreteReducedMetricCertificate
  package : GeneratedClosureMetricRowPackage
  package_eq :
    package =
      generatedClosureMetricRowPackageOfConcreteReducedMetricCertificate
        certificate

def finiteRowsGeneratedClosureRoute
    (P : ConcreteValueMatrixRowPackage) :
    FiniteRowsGeneratedClosureRoute where
  rows := P
  package := generatedClosureMetricRowPackageOfFiniteValueRows P
  package_eq := rfl

def concreteValueCertificatesGeneratedClosureRoute
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    ConcreteValueCertificatesGeneratedClosureRoute where
  certificates := C
  package :=
    generatedClosureMetricRowPackageOfConcreteGeneratedPointValueCertificates C
  package_eq := rfl

def reducedMetricCertificateGeneratedClosureRoute
    (P : ConcreteReducedMetricCertificate) :
    ReducedMetricCertificateGeneratedClosureRoute where
  certificate := P
  package := generatedClosureMetricRowPackageOfConcreteReducedMetricCertificate P
  package_eq := rfl

def roleHingedPeriodSearchFamilyOfFiniteValueRows
    (P : ConcreteValueMatrixRowPackage) :
    RoleHingedPeriodSearchFamily :=
  P.periodSearch.toRoleHingedPeriodSearchFamily

def roleHingedPeriodSearchFamilyOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    RoleHingedPeriodSearchFamily :=
  C.toRoleHingedPeriodSearchFamily

def roleHingedPeriodSearchFamilyOfConcreteGeneratedPointValueCertificates
    (C : ConcreteGeneratedPointValueCertificateFamily) :
    RoleHingedPeriodSearchFamily :=
  C.toRoleHingedPeriodSearchFamily

def roleHingedPeriodSearchFamilyOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    RoleHingedPeriodSearchFamily :=
  C.toRoleHingedPeriodSearchFamily

theorem finiteValueRows_imply_roleHingedPeriodSearchFamily :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty RoleHingedPeriodSearchFamily := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro
        (roleHingedPeriodSearchFamilyOfFiniteValueRows P)

theorem concreteValueMatrixFamily_imply_roleHingedPeriodSearchFamily :
    Nonempty ConcreteValueMatrixFamily ->
      Nonempty RoleHingedPeriodSearchFamily := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro
        (roleHingedPeriodSearchFamilyOfConcreteValueMatrixFamily C)

theorem concreteGeneratedPointValueCertificates_imply_roleHingedPeriodSearchFamily :
    Nonempty ConcreteGeneratedPointValueCertificateFamily ->
      Nonempty RoleHingedPeriodSearchFamily := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro
        (roleHingedPeriodSearchFamilyOfConcreteGeneratedPointValueCertificates
          C)

theorem concreteLowerTables_imply_roleHingedPeriodSearchFamily :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      Nonempty RoleHingedPeriodSearchFamily := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro
        (roleHingedPeriodSearchFamilyOfConcreteLowerTables C)

theorem no_roleHingedPeriodSearchFamily :
    Not (Nonempty RoleHingedPeriodSearchFamily) :=
  PachTothW26RouteAudit.no_roleHingedPeriodSearchFamily

theorem no_concreteFiniteValueRows :
    Not (Nonempty ConcreteValueMatrixRowPackage) := by
  intro h
  exact no_roleHingedPeriodSearchFamily
    (finiteValueRows_imply_roleHingedPeriodSearchFamily h)

theorem no_concreteValueMatrixFamily :
    Not (Nonempty ConcreteValueMatrixFamily) := by
  intro h
  exact no_roleHingedPeriodSearchFamily
    (concreteValueMatrixFamily_imply_roleHingedPeriodSearchFamily h)

theorem no_concreteGeneratedPointValueCertificates :
    Not (Nonempty ConcreteGeneratedPointValueCertificateFamily) := by
  intro h
  exact no_roleHingedPeriodSearchFamily
    (concreteGeneratedPointValueCertificates_imply_roleHingedPeriodSearchFamily
      h)

theorem no_concreteLowerTables :
    Not (Nonempty ConcreteNonConnectorLowerTableFamily) :=
  ConcreteLowerTableFamilyConstructionW27.no_concreteNonConnectorLowerTableFamily

theorem no_concreteReducedMetricCertificate :
    Not (Nonempty ConcreteReducedMetricCertificate) := by
  intro h
  exact no_concreteLowerTables
    (concreteReducedMetricCertificateGate_iff_concreteLowerTableGate.mp h)

theorem no_finiteRowsGeneratedClosureRoute :
    Not (Nonempty FiniteRowsGeneratedClosureRoute) := by
  intro h
  cases h with
  | intro R =>
      exact no_concreteFiniteValueRows (Nonempty.intro R.rows)

theorem no_concreteValueCertificatesGeneratedClosureRoute :
    Not (Nonempty ConcreteValueCertificatesGeneratedClosureRoute) := by
  intro h
  cases h with
  | intro R =>
      exact no_concreteGeneratedPointValueCertificates
        (Nonempty.intro R.certificates)

theorem no_reducedMetricCertificateGeneratedClosureRoute :
    Not (Nonempty ReducedMetricCertificateGeneratedClosureRoute) := by
  intro h
  cases h with
  | intro R =>
      exact no_concreteReducedMetricCertificate
        (Nonempty.intro R.certificate)

end

end GeneratedClosureMetricSourceW28
end PachToth

namespace Verified

abbrev PachTothW28GeneratedClosureMetricRowPackage : Type :=
  PachToth.GeneratedClosureMetricSourceW28.GeneratedClosureMetricRowPackage

abbrev PachTothW28FiniteRowsGeneratedClosureRoute : Type :=
  PachToth.GeneratedClosureMetricSourceW28.FiniteRowsGeneratedClosureRoute

abbrev PachTothW28ReducedMetricCertificateGeneratedClosureRoute : Type :=
  PachToth.GeneratedClosureMetricSourceW28.ReducedMetricCertificateGeneratedClosureRoute

theorem pachtoth_w28_generatedClosureMetricGate_of_exactFiniteValueRows :
    Nonempty
        PachToth.GeneratedClosureMetricSourceW28.ExactFiniteValueInequalityRowsStillNeeded ->
      Nonempty PachTothW28GeneratedClosureMetricRowPackage :=
  PachToth.GeneratedClosureMetricSourceW28.generatedClosureMetricGate_of_exactFiniteValueRows

theorem pachtoth_w28_no_finiteRowsGeneratedClosureRoute :
    Not (Nonempty PachTothW28FiniteRowsGeneratedClosureRoute) :=
  PachToth.GeneratedClosureMetricSourceW28.no_finiteRowsGeneratedClosureRoute

theorem pachtoth_w28_no_reducedMetricCertificateGeneratedClosureRoute :
    Not (Nonempty PachTothW28ReducedMetricCertificateGeneratedClosureRoute) :=
  PachToth.GeneratedClosureMetricSourceW28.no_reducedMetricCertificateGeneratedClosureRoute

end Verified
end ErdosProblems1066
