import ErdosProblems1066.PachToth.ConcreteLowerTableFamilyConstructionW27
import ErdosProblems1066.PachToth.DirectFullMetricSourceConstructionW27
import ErdosProblems1066.PachToth.FiniteReducedMetricCertificatesW27
import ErdosProblems1066.PachToth.NonRoleHingePeriodSourceW24
import ErdosProblems1066.PachToth.PachTothW27FinalAssembly

set_option autoImplicit false

/-!
# W28 finite-row no-go audit

This file records the precise boundary around the W27 finite-row and
lower-table routes.  The concrete finite rows and all lower-table wrappers
still carry concrete period-search data, so any unconditional inhabitant of
those packages would give a role-hinged period-search family.  That family is
already empty in the checked route audit.

The viable escape hatch is not another wrapper around those concrete rows.  It
is the non-role exact-base full-metric interface from W24, whose gate is stated
below without a role-hinged period-search field.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteRowsNoGoAuditW28

noncomputable section

/-! ## Role-hinged dependency shared by the finite-row route -/

abbrev PeriodSearchData : Type :=
  ConcreteLowerTableFamilyConstructionW27.PeriodSearchData

abbrev RoleHingedPeriodSearchFamily : Type :=
  ConcreteLowerTableFamilyConstructionW27.RoleHingedPeriodSearchFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteLowerTableFamilyConstructionW27.ConcreteValueMatrixRowPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteLowerTableFamilyConstructionW27.ConcreteValueMatrixFamily

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteLowerTableFamilyConstructionW27.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteReducedMetricCertificate : Type :=
  ConcreteLowerTableFamilyConstructionW27.ConcreteReducedMetricCertificate

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceConstructionW27.DirectFullMetricSourcePackage

abbrev DirectFullMetricSourceConstruction : Type :=
  DirectFullMetricSourceConstructionW27.DirectFullMetricSourceConstruction

abbrev ExactFiniteValueInequalityRowsStillNeeded : Type :=
  FiniteReducedMetricCertificatesW27.ExactFiniteValueInequalityRowsStillNeeded

abbrev FiniteTableCore (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteLowerTableFamilyConstructionW27.FiniteTableCore F

abbrev PolynomialFiniteTableCore
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ConcreteLowerTableFamilyConstructionW27.PolynomialFiniteTableCore F

abbrev RoleHingedPeriodSearchGate : Prop :=
  Nonempty RoleHingedPeriodSearchFamily

abbrev ConcreteValueMatrixRowGate : Prop :=
  Nonempty ConcreteValueMatrixRowPackage

abbrev ConcreteValueMatrixFamilyGate : Prop :=
  Nonempty ConcreteValueMatrixFamily

abbrev ConcreteLowerTableGate : Prop :=
  Nonempty ConcreteNonConnectorLowerTableFamily

abbrev ConcreteReducedMetricCertificateGate : Prop :=
  Nonempty ConcreteReducedMetricCertificate

abbrev DirectFullMetricSourcePackageGate : Prop :=
  Nonempty DirectFullMetricSourcePackage

abbrev DirectFullMetricSourceConstructionGate : Prop :=
  Nonempty DirectFullMetricSourceConstruction

abbrev ExactFiniteValueRowsGate : Prop :=
  Nonempty ExactFiniteValueInequalityRowsStillNeeded

theorem not_roleHingedPeriodSearchGate :
    Not RoleHingedPeriodSearchGate :=
  PachTothW26RouteAudit.no_roleHingedPeriodSearchFamily

def roleHingedPeriodSearchFamilyOfPeriodSearch
    (periodSearch : PeriodSearchData) :
    RoleHingedPeriodSearchFamily :=
  periodSearch.toRoleHingedPeriodSearchFamily

def roleHingedPeriodSearchFamilyOfRows
    (P : ConcreteValueMatrixRowPackage) :
    RoleHingedPeriodSearchFamily :=
  roleHingedPeriodSearchFamilyOfPeriodSearch P.periodSearch

def roleHingedPeriodSearchFamilyOfLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    RoleHingedPeriodSearchFamily :=
  ConcreteLowerTableFamilyConstructionW27.roleHingedPeriodSearchFamilyOfConcreteLowerTables
    C

theorem roleHingedPeriodSearchGate_of_periodSearchData :
    Nonempty PeriodSearchData -> RoleHingedPeriodSearchGate := by
  intro h
  cases h with
  | intro periodSearch =>
      exact
        Nonempty.intro
          (roleHingedPeriodSearchFamilyOfPeriodSearch periodSearch)

theorem roleHingedPeriodSearchGate_of_concreteValueMatrixRowGate :
    ConcreteValueMatrixRowGate -> RoleHingedPeriodSearchGate := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (roleHingedPeriodSearchFamilyOfRows P)

theorem roleHingedPeriodSearchGate_of_concreteValueMatrixFamilyGate :
    ConcreteValueMatrixFamilyGate -> RoleHingedPeriodSearchGate := by
  intro h
  exact
    roleHingedPeriodSearchGate_of_concreteValueMatrixRowGate
      ((ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage).mp
        h)

theorem roleHingedPeriodSearchGate_of_exactFiniteValueRowsGate :
    ExactFiniteValueRowsGate -> RoleHingedPeriodSearchGate :=
  roleHingedPeriodSearchGate_of_concreteValueMatrixRowGate

theorem roleHingedPeriodSearchGate_of_concreteLowerTableGate :
    ConcreteLowerTableGate -> RoleHingedPeriodSearchGate := by
  intro h
  cases h with
  | intro C =>
      exact Nonempty.intro (roleHingedPeriodSearchFamilyOfLowerTables C)

theorem roleHingedPeriodSearchGate_of_concreteReducedMetricCertificateGate :
    ConcreteReducedMetricCertificateGate -> RoleHingedPeriodSearchGate := by
  intro h
  exact
    roleHingedPeriodSearchGate_of_concreteLowerTableGate
      ((ConcreteReducedMetricCertificatesW26.nonempty_concreteReducedMetricCertificate_iff_lowerTables).mp
        h)

theorem roleHingedPeriodSearchGate_of_directFullMetricSourcePackageGate :
    DirectFullMetricSourcePackageGate -> RoleHingedPeriodSearchGate := by
  intro h
  exact
    roleHingedPeriodSearchGate_of_concreteLowerTableGate
      ((DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourcePackage_iff_concreteLowerTables).mp
        h)

theorem roleHingedPeriodSearchGate_of_directFullMetricSourceConstructionGate :
    DirectFullMetricSourceConstructionGate -> RoleHingedPeriodSearchGate := by
  intro h
  exact
    roleHingedPeriodSearchGate_of_concreteLowerTableGate
      ((DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourceConstruction_iff_concreteLowerTables).mp
        h)

/-! ## Concrete finite rows with their period-search data -/

structure ConcreteFiniteRowsWithPeriodSearch where
  periodSearch : PeriodSearchData
  rows : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily

namespace ConcreteFiniteRowsWithPeriodSearch

def toRowPackage
    (P : ConcreteFiniteRowsWithPeriodSearch) :
    ConcreteValueMatrixRowPackage :=
  P.rows.rowPackage

def toConcreteLowerTables
    (P : ConcreteFiniteRowsWithPeriodSearch) :
    ConcreteNonConnectorLowerTableFamily :=
  P.rows.concreteLowerTables

end ConcreteFiniteRowsWithPeriodSearch

def concreteFiniteRowsWithPeriodSearchOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteFiniteRowsWithPeriodSearch where
  periodSearch := P.periodSearch
  rows := ConcreteLowerTableFamilyConstructionW27.finiteTableCoreOfRowPackage P

theorem concreteFiniteRowsWithPeriodSearch_toRowPackage_periodSearch
    (P : ConcreteFiniteRowsWithPeriodSearch) :
    P.toRowPackage.periodSearch = P.periodSearch := by
  rfl

theorem nonempty_concreteFiniteRowsWithPeriodSearch_iff_rows :
    Nonempty ConcreteFiniteRowsWithPeriodSearch <->
      ConcreteValueMatrixRowGate := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toRowPackage
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (concreteFiniteRowsWithPeriodSearchOfRowPackage P)

theorem roleHingedPeriodSearchGate_of_concreteFiniteRowsWithPeriodSearch :
    Nonempty ConcreteFiniteRowsWithPeriodSearch ->
      RoleHingedPeriodSearchGate := by
  intro h
  exact
    roleHingedPeriodSearchGate_of_concreteValueMatrixRowGate
      (nonempty_concreteFiniteRowsWithPeriodSearch_iff_rows.mp h)

/-! ## Exact no-go statements for the W27 blocked route -/

theorem not_concreteValueMatrixRowGate :
    Not ConcreteValueMatrixRowGate := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_concreteValueMatrixRowGate h)

theorem not_exactFiniteValueRowsGate :
    Not ExactFiniteValueRowsGate :=
  not_concreteValueMatrixRowGate

theorem not_concreteValueMatrixFamilyGate :
    Not ConcreteValueMatrixFamilyGate := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_concreteValueMatrixFamilyGate h)

theorem not_concreteFiniteRowsWithPeriodSearch :
    Not (Nonempty ConcreteFiniteRowsWithPeriodSearch) := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_concreteFiniteRowsWithPeriodSearch h)

theorem not_concreteLowerTableGate :
    Not ConcreteLowerTableGate :=
  ConcreteLowerTableFamilyConstructionW27.no_concreteNonConnectorLowerTableFamily

theorem not_concreteReducedMetricCertificateGate :
    Not ConcreteReducedMetricCertificateGate := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_concreteReducedMetricCertificateGate h)

theorem not_directFullMetricSourcePackageGate :
    Not DirectFullMetricSourcePackageGate := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_directFullMetricSourcePackageGate h)

theorem not_directFullMetricSourceConstructionGate :
    Not DirectFullMetricSourceConstructionGate := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_directFullMetricSourceConstructionGate h)

/-! ## Iff map of equivalent blocked wrappers -/

theorem concreteValueMatrixFamilyGate_iff_concreteValueMatrixRowGate :
    ConcreteValueMatrixFamilyGate <-> ConcreteValueMatrixRowGate :=
  ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage

theorem exactFiniteValueRowsGate_iff_concreteValueMatrixRowGate :
    ExactFiniteValueRowsGate <-> ConcreteValueMatrixRowGate :=
  Iff.rfl

theorem concreteReducedMetricCertificateGate_iff_concreteLowerTableGate :
    ConcreteReducedMetricCertificateGate <-> ConcreteLowerTableGate :=
  ConcreteReducedMetricCertificatesW26.nonempty_concreteReducedMetricCertificate_iff_lowerTables

theorem directFullMetricSourcePackageGate_iff_concreteLowerTableGate :
    DirectFullMetricSourcePackageGate <-> ConcreteLowerTableGate :=
  DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourcePackage_iff_concreteLowerTables

theorem directFullMetricSourceConstructionGate_iff_concreteLowerTableGate :
    DirectFullMetricSourceConstructionGate <-> ConcreteLowerTableGate :=
  DirectFullMetricSourceConstructionW27.nonempty_directFullMetricSourceConstruction_iff_concreteLowerTables

theorem concreteLowerTableGate_of_concreteFiniteRowsWithPeriodSearch :
    Nonempty ConcreteFiniteRowsWithPeriodSearch -> ConcreteLowerTableGate := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.toConcreteLowerTables

theorem concreteLowerTableGate_of_concreteValueMatrixRowGate :
    ConcreteValueMatrixRowGate -> ConcreteLowerTableGate := by
  intro h
  cases h with
  | intro P =>
      exact
        concreteLowerTableGate_of_concreteFiniteRowsWithPeriodSearch
          (Nonempty.intro
            (concreteFiniteRowsWithPeriodSearchOfRowPackage P))

theorem blocked_finiteRows_lowerTables_certificate_directPackage_summary :
    Not RoleHingedPeriodSearchGate /\
      Not ConcreteValueMatrixRowGate /\
        Not ConcreteLowerTableGate /\
          Not ConcreteReducedMetricCertificateGate /\
            Not DirectFullMetricSourcePackageGate :=
  And.intro not_roleHingedPeriodSearchGate
    (And.intro not_concreteValueMatrixRowGate
      (And.intro not_concreteLowerTableGate
        (And.intro not_concreteReducedMetricCertificateGate
          not_directFullMetricSourcePackageGate)))

/-! ## Role-indexed cores are useful only after the role family is supplied -/

abbrev RoleIndexedFiniteTableCore : Type :=
  Sigma FiniteTableCore

structure RoleIndexedPolynomialFiniteTableCore where
  family : RoleHingedPeriodSearchFamily
  rows : PolynomialFiniteTableCore family

theorem roleHingedPeriodSearchGate_of_roleIndexedFiniteTableCore :
    Nonempty RoleIndexedFiniteTableCore -> RoleHingedPeriodSearchGate := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.1

theorem roleHingedPeriodSearchGate_of_roleIndexedPolynomialFiniteTableCore :
    Nonempty RoleIndexedPolynomialFiniteTableCore ->
      RoleHingedPeriodSearchGate := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.family

theorem not_roleIndexedFiniteTableCore :
    Not (Nonempty RoleIndexedFiniteTableCore) := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_roleIndexedFiniteTableCore h)

theorem not_roleIndexedPolynomialFiniteTableCore :
    Not (Nonempty RoleIndexedPolynomialFiniteTableCore) := by
  intro h
  exact not_roleHingedPeriodSearchGate
    (roleHingedPeriodSearchGate_of_roleIndexedPolynomialFiniteTableCore h)

/-! ## Non-role alternatives that remain viable targets -/

abbrev ExactBaseFullMetricSourceFields : Type :=
  NonRoleHingePeriodSourceW24.ExactBaseFullMetricSourceFields

abbrev ExactBaseFullMetricCoreFields : Type :=
  NonRoleHingePeriodSourceW24.ExactBaseFullMetricCoreFields

abbrev RemainingFullMetricField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  NonRoleHingePeriodSourceW24.RemainingFullMetricField C

abbrev RemainingSeparationField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  NonRoleHingePeriodSourceW24.RemainingSeparationField C

abbrev RemainingSameBlockField
    (C : ExactBaseFullMetricCoreFields) : Prop :=
  NonRoleHingePeriodSourceW24.RemainingSameBlockField C

abbrev NonRoleExactBaseGate : Prop :=
  Nonempty ExactBaseFullMetricSourceFields

theorem nonRoleExactBaseGate_iff_remainingFullMetric :
    NonRoleExactBaseGate <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        RemainingFullMetricField C :=
  NonRoleHingePeriodSourceW24.nonempty_exactBaseFullMetricSourceFields_iff_remainingFullMetric

theorem nonRoleExactBaseGate_iff_parts :
    NonRoleExactBaseGate <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        RemainingSeparationField C /\ RemainingSameBlockField C :=
  NonRoleHingePeriodSourceW24.nonempty_exactBaseFullMetricSourceFields_iff_parts

abbrev RoleHingedFullMetricSourceRoute : Type :=
  NonRoleHingePeriodSourceW24.RoleHingedFullMetricSourceRoute

abbrev RoleHingedFullMetricSourceRouteGate : Prop :=
  Nonempty RoleHingedFullMetricSourceRoute

theorem not_roleHingedFullMetricSourceRouteGate :
    Not RoleHingedFullMetricSourceRouteGate :=
  NonRoleHingePeriodSourceW24.not_nonempty_roleHingedFullMetricSourceRoute

theorem viable_nonRole_route_summary :
    (NonRoleExactBaseGate <->
      Exists fun C : ExactBaseFullMetricCoreFields =>
        RemainingSeparationField C /\ RemainingSameBlockField C) /\
      Not RoleHingedFullMetricSourceRouteGate :=
  And.intro nonRoleExactBaseGate_iff_parts
    not_roleHingedFullMetricSourceRouteGate

end

end FiniteRowsNoGoAuditW28
end PachToth

namespace Verified

abbrev PachTothW28FiniteRowsRoleHingedPeriodSearchGate : Prop :=
  PachToth.FiniteRowsNoGoAuditW28.RoleHingedPeriodSearchGate

abbrev PachTothW28FiniteRowsConcreteValueMatrixRowGate : Prop :=
  PachToth.FiniteRowsNoGoAuditW28.ConcreteValueMatrixRowGate

abbrev PachTothW28FiniteRowsConcreteLowerTableGate : Prop :=
  PachToth.FiniteRowsNoGoAuditW28.ConcreteLowerTableGate

abbrev PachTothW28FiniteRowsConcreteReducedMetricCertificateGate : Prop :=
  PachToth.FiniteRowsNoGoAuditW28.ConcreteReducedMetricCertificateGate

abbrev PachTothW28FiniteRowsDirectFullMetricSourcePackageGate : Prop :=
  PachToth.FiniteRowsNoGoAuditW28.DirectFullMetricSourcePackageGate

abbrev PachTothW28NonRoleExactBaseGate : Prop :=
  PachToth.FiniteRowsNoGoAuditW28.NonRoleExactBaseGate

theorem pachtoth_w28_finiteRows_blocked_route_summary :
    Not PachTothW28FiniteRowsRoleHingedPeriodSearchGate /\
      Not PachTothW28FiniteRowsConcreteValueMatrixRowGate /\
        Not PachTothW28FiniteRowsConcreteLowerTableGate /\
          Not PachTothW28FiniteRowsConcreteReducedMetricCertificateGate /\
            Not PachTothW28FiniteRowsDirectFullMetricSourcePackageGate :=
  PachToth.FiniteRowsNoGoAuditW28.blocked_finiteRows_lowerTables_certificate_directPackage_summary

theorem pachtoth_w28_concreteReducedMetricCertificateGate_iff_lowerTableGate :
    PachTothW28FiniteRowsConcreteReducedMetricCertificateGate <->
      PachTothW28FiniteRowsConcreteLowerTableGate :=
  PachToth.FiniteRowsNoGoAuditW28.concreteReducedMetricCertificateGate_iff_concreteLowerTableGate

theorem pachtoth_w28_directFullMetricSourcePackageGate_iff_lowerTableGate :
    PachTothW28FiniteRowsDirectFullMetricSourcePackageGate <->
      PachTothW28FiniteRowsConcreteLowerTableGate :=
  PachToth.FiniteRowsNoGoAuditW28.directFullMetricSourcePackageGate_iff_concreteLowerTableGate

theorem pachtoth_w28_nonRoleExactBaseGate_iff_parts :
    PachTothW28NonRoleExactBaseGate <->
      Exists fun C :
        PachToth.FiniteRowsNoGoAuditW28.ExactBaseFullMetricCoreFields =>
          PachToth.FiniteRowsNoGoAuditW28.RemainingSeparationField C /\
            PachToth.FiniteRowsNoGoAuditW28.RemainingSameBlockField C :=
  PachToth.FiniteRowsNoGoAuditW28.nonRoleExactBaseGate_iff_parts

end Verified
end ErdosProblems1066
