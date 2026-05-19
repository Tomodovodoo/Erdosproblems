import ErdosProblems1066.PachToth.ConcreteReducedMetricCertificatesW26
import ErdosProblems1066.PachToth.ConcreteValueMatrixRowPackageInhabitationW23
import ErdosProblems1066.PachToth.PachTothW26RouteAudit

set_option autoImplicit false

/-!
# W27 concrete lower-table family construction

The W26 route audit shows that the full concrete lower-table family is still
blocked by the empty role-hinged period-search surface.  This file therefore
records the obstruction explicitly and isolates the finite table core that is
available independently of that period-search inhabitant.

No target endpoint is used to build a source below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteLowerTableFamilyConstructionW27

noncomputable section

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteNonConnectorLowerTableFamily

abbrev PeriodSearchData : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.PeriodSearchData

abbrev RoleHingedPeriodSearchFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.RoleHingedPeriodSearchFamily

abbrev NonConnectorValueMatrixFamily
    (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.NonConnectorValueMatrixFamily F

abbrev NonConnectorLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily F

abbrev LengthTwoThreeValueRows
    (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.LengthTwoThreeValueRows F

abbrev LengthFourFiveValueRows
    (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.LengthFourFiveValueRows F

abbrev TailValueRows
    (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteValueMatrixRowPackageInhabitationW23.TailValueRows F

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily

abbrev DirectReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) :=
  DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C

abbrev DirectFullMetricSourcePackage : Type :=
  DirectFullMetricSourceInhabitationW25.DirectFullMetricSourcePackage

abbrev ConcreteReducedMetricCertificate : Type :=
  ConcreteReducedMetricCertificatesW26.ConcreteReducedMetricCertificate

/-! ## Full concrete lower-table obstruction -/

def roleHingedPeriodSearchFamilyOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    RoleHingedPeriodSearchFamily :=
  C.periodSearch.toRoleHingedPeriodSearchFamily

theorem no_concreteNonConnectorLowerTableFamily :
    Not (Nonempty ConcreteNonConnectorLowerTableFamily) := by
  intro h
  exact PachTothW26RouteAudit.no_roleHingedPeriodSearchFamily
    (h.elim fun C =>
      Nonempty.intro (roleHingedPeriodSearchFamilyOfConcreteLowerTables C))

theorem no_periodSearch_with_nonConnectorLowerTableFamily :
    Not
      (Exists fun periodSearch : PeriodSearchData =>
        Nonempty
          (NonConnectorLowerTableFamily
            periodSearch.toRoleHingedPeriodSearchFamily)) := by
  intro h
  exact no_concreteNonConnectorLowerTableFamily
    (ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily.nonempty_iff_exists_periodSearch_tables.2 h)

theorem no_periodSearch_with_nonConnectorValueMatrixFamily :
    Not
      (Exists fun periodSearch : PeriodSearchData =>
        Nonempty
          (NonConnectorValueMatrixFamily
            periodSearch.toRoleHingedPeriodSearchFamily)) := by
  intro h
  apply no_periodSearch_with_nonConnectorLowerTableFamily
  cases h with
  | intro periodSearch HM =>
      cases HM with
      | intro matrices =>
          exact Exists.intro periodSearch
            (Nonempty.intro matrices.toNonConnectorLowerTableFamily)

/-! ## Finite table core independent of the blocked period-search surface -/

structure FiniteTableCore (F : RoleHingedPeriodSearchFamily) where
  smallTwoThree : LengthTwoThreeValueRows F
  smallFourFive : LengthFourFiveValueRows F
  tail : TailValueRows F

namespace FiniteTableCore

def valueMatrixFamily
    {F : RoleHingedPeriodSearchFamily}
    (P : FiniteTableCore F) :
    NonConnectorValueMatrixFamily F :=
  ConcreteValueMatrixFamilyInhabitationW22.valueMatrixFamilyOfValueRows
    P.smallTwoThree P.smallFourFive P.tail

def lowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (P : FiniteTableCore F) :
    NonConnectorLowerTableFamily F :=
  P.valueMatrixFamily.toNonConnectorLowerTableFamily

def rowPackage
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteValueMatrixRowPackage where
  periodSearch := periodSearch
  smallTwoThree := P.smallTwoThree
  smallFourFive := P.smallFourFive
  tail := P.tail

def concreteValueMatrixFamily
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteValueMatrixFamily :=
  P.rowPackage.toConcreteValueMatrixFamily

def concreteLowerTables
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockFamilyInhabitationW23.concreteLowerTableFamilyOfValueMatrixFamily
    P.concreteValueMatrixFamily

def directReducedSourceFields
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    DirectReducedSourceFieldsOver P.concreteLowerTables :=
  ConcreteReducedMetricCertificatesW26.directReducedSourceFieldsOfConcreteLowerTables
    P.concreteLowerTables

def directFullMetricSourcePackage
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    DirectFullMetricSourcePackage :=
  DirectFullMetricSourceInhabitationW25.DirectFullMetricSourcePackage.ofConcreteLowerTables
    P.concreteLowerTables

def concreteReducedMetricCertificate
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteReducedMetricCertificate :=
  ConcreteReducedMetricCertificatesW26.concreteReducedMetricCertificateOfLowerTables
    P.concreteLowerTables

@[simp]
theorem concreteLowerTables_periodSearch
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    P.concreteLowerTables.periodSearch = periodSearch := by
  rfl

@[simp]
theorem concreteLowerTables_tables
    {periodSearch : PeriodSearchData}
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    P.concreteLowerTables.tables = P.lowerTableFamily := by
  rfl

end FiniteTableCore

/-! ## Polynomial lower-bound core for the finite rows -/

abbrev LengthTwoThreePolynomialInequalities
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  SmallRowsTwoThreeW16.LengthTwoThreeBlockPairGeneratedPointInequalities F

abbrev LengthFourFivePolynomialInequalities
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  SmallRowsFourFiveW16.LengthFourFiveBlockPairGeneratedPointInequalities F

abbrev TailPolynomialInequalities
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  TailValueRowsProducerW18.ExplicitTailPolynomialInequalities F

structure PolynomialFiniteTableCore (F : RoleHingedPeriodSearchFamily) where
  smallTwoThree : LengthTwoThreePolynomialInequalities F
  smallFourFive : LengthFourFivePolynomialInequalities F
  tail : TailPolynomialInequalities F

namespace PolynomialFiniteTableCore

def toFiniteTableCore
    {F : RoleHingedPeriodSearchFamily}
    (P : PolynomialFiniteTableCore F) :
    FiniteTableCore F where
  smallTwoThree :=
    SmallRowsTwoThreeValueProducerW18.lengthTwoThreeValueRowsOfPolynomialInequalities
      P.smallTwoThree
  smallFourFive :=
    SmallRowsFourFiveValueProducerW18.lengthFourFiveValueRowsOfBlockPairInequalities
      P.smallFourFive
  tail :=
    TailValueRowsProducerW18.tailValueRowsOfPolynomialInequalities P.tail

def lowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (P : PolynomialFiniteTableCore F) :
    NonConnectorLowerTableFamily F :=
  P.toFiniteTableCore.lowerTableFamily

end PolynomialFiniteTableCore

theorem nonempty_finiteTableCore_of_polynomialFiniteTableCore
    {F : RoleHingedPeriodSearchFamily}
    (P : PolynomialFiniteTableCore F) :
    Nonempty (FiniteTableCore F) :=
  Nonempty.intro P.toFiniteTableCore

def finiteTableCoreOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    FiniteTableCore P.periodSearch.toRoleHingedPeriodSearchFamily where
  smallTwoThree := P.smallTwoThree
  smallFourFive := P.smallFourFive
  tail := P.tail

theorem nonempty_finiteTableCore_of_rowPackage
    (P : ConcreteValueMatrixRowPackage) :
    Nonempty (FiniteTableCore P.periodSearch.toRoleHingedPeriodSearchFamily) :=
  Nonempty.intro (finiteTableCoreOfRowPackage P)

def concreteLowerTables_of_periodSearch_and_finiteTableCore
    (periodSearch : PeriodSearchData)
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteNonConnectorLowerTableFamily :=
  P.concreteLowerTables

theorem concreteLowerTables_blocked_before_finiteTables
    (periodSearch : PeriodSearchData)
    (P : FiniteTableCore periodSearch.toRoleHingedPeriodSearchFamily) :
    False :=
  no_concreteNonConnectorLowerTableFamily
    (Nonempty.intro
      (concreteLowerTables_of_periodSearch_and_finiteTableCore periodSearch P))

end

end ConcreteLowerTableFamilyConstructionW27
end PachToth

namespace Verified

abbrev PachTothW27FiniteTableCore
    (F : PachToth.ConcreteLowerTableFamilyConstructionW27.RoleHingedPeriodSearchFamily) :
    Type :=
  PachToth.ConcreteLowerTableFamilyConstructionW27.FiniteTableCore F

theorem pachtoth_w27_no_concreteNonConnectorLowerTableFamily :
    Not (Nonempty
      PachToth.ConcreteLowerTableFamilyConstructionW27.ConcreteNonConnectorLowerTableFamily) :=
  PachToth.ConcreteLowerTableFamilyConstructionW27.no_concreteNonConnectorLowerTableFamily

end Verified
end ErdosProblems1066
