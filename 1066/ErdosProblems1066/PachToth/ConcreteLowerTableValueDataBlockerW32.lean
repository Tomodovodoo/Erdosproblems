import ErdosProblems1066.PachToth.ConcreteCrossBlockLowerTable
import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22
import ErdosProblems1066.PachToth.FiniteRowsNoGoAuditW28

set_option autoImplicit false

/-!
# W32 blocker for the current concrete lower-table gate

The current concrete non-connector lower-table gate can be reached from
concrete value matrices, vector certificates, or list certificates only after
supplying concrete period-search data.  In this checkout that period-search
field projects to the checked empty role-hinged period-search surface.  The
value-matrix route is pinned to its exact row package so the blocker points to
the missing row family rather than to another endpoint facade.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteLowerTableValueDataBlockerW32

noncomputable section

abbrev ConcreteLowerTableFamily : Type :=
  ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteLowerTableGate : Prop :=
  Nonempty ConcreteLowerTableFamily

abbrev PeriodSearchData : Type :=
  ConcreteCrossBlockLowerTable.PeriodSearchData

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev ConcreteValueMatrixGate : Prop :=
  Nonempty ConcreteValueMatrixFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

abbrev ConcreteValueMatrixRowGate : Prop :=
  Nonempty ConcreteValueMatrixRowPackage

abbrev LowerTableVectorCertificateRowsGate : Prop :=
  Exists fun periodSearch : PeriodSearchData =>
    Nonempty
      (ConcreteCrossBlockLowerTable.UpperTriangleNonConnectorVectorCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily)

abbrev LowerTableListCertificateRowsGate : Prop :=
  Exists fun periodSearch : PeriodSearchData =>
    Nonempty
      (ConcreteCrossBlockLowerTable.UpperTriangleNonConnectorListCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily)

abbrev ValueMatrixVectorCertificateRowsGate : Prop :=
  Exists fun periodSearch : PeriodSearchData =>
    Nonempty
      (ConcreteNonConnectorValueMatrix.UpperTriangleNonConnectorSqValueVectorCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily)

abbrev ValueMatrixListCertificateRowsGate : Prop :=
  Exists fun periodSearch : PeriodSearchData =>
    Nonempty
      (ConcreteNonConnectorValueMatrix.UpperTriangleNonConnectorSqValueListCertificateFamily
        periodSearch.toRoleHingedPeriodSearchFamily)

theorem concreteValueMatrixGate_iff_exactRowPackage :
    ConcreteValueMatrixGate <-> ConcreteValueMatrixRowGate :=
  ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage

theorem concreteLowerTableGate_of_concreteValueMatrixGate
    (H : ConcreteValueMatrixGate) :
    ConcreteLowerTableGate := by
  cases H with
  | intro C =>
      exact Nonempty.intro C.toConcreteNonConnectorLowerTableFamily

theorem concreteLowerTableGate_of_lowerTableVectorCertificateRowsGate
    (H : LowerTableVectorCertificateRowsGate) :
    ConcreteLowerTableGate := by
  cases H with
  | intro periodSearch HC =>
      cases HC with
      | intro C =>
          exact
            Nonempty.intro
              (ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily.ofVectorCertificateFamily
                periodSearch C)

theorem concreteLowerTableGate_of_lowerTableListCertificateRowsGate
    (H : LowerTableListCertificateRowsGate) :
    ConcreteLowerTableGate := by
  cases H with
  | intro periodSearch HC =>
      cases HC with
      | intro C =>
          exact
            Nonempty.intro
              (ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily.ofListCertificateFamily
                periodSearch C)

theorem concreteValueMatrixGate_of_valueMatrixVectorCertificateRowsGate
    (H : ValueMatrixVectorCertificateRowsGate) :
    ConcreteValueMatrixGate := by
  cases H with
  | intro periodSearch HC =>
      cases HC with
      | intro C =>
          exact
            Nonempty.intro
              (ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily.ofVectorCertificateFamily
                periodSearch C)

theorem concreteValueMatrixGate_of_valueMatrixListCertificateRowsGate
    (H : ValueMatrixListCertificateRowsGate) :
    ConcreteValueMatrixGate := by
  cases H with
  | intro periodSearch HC =>
      cases HC with
      | intro C =>
          exact
            Nonempty.intro
              (ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily.ofListCertificateFamily
                periodSearch C)

theorem concreteLowerTableGate_of_valueMatrixVectorCertificateRowsGate
    (H : ValueMatrixVectorCertificateRowsGate) :
    ConcreteLowerTableGate :=
  concreteLowerTableGate_of_concreteValueMatrixGate
    (concreteValueMatrixGate_of_valueMatrixVectorCertificateRowsGate H)

theorem concreteLowerTableGate_of_valueMatrixListCertificateRowsGate
    (H : ValueMatrixListCertificateRowsGate) :
    ConcreteLowerTableGate :=
  concreteLowerTableGate_of_concreteValueMatrixGate
    (concreteValueMatrixGate_of_valueMatrixListCertificateRowsGate H)

theorem not_periodSearchDataGate :
    Not (Nonempty PeriodSearchData) := by
  intro H
  cases H with
  | intro periodSearch =>
      exact FiniteRowsNoGoAuditW28.not_roleHingedPeriodSearchGate
        (Nonempty.intro periodSearch.toRoleHingedPeriodSearchFamily)

theorem not_concreteValueMatrixRowGate :
    Not ConcreteValueMatrixRowGate :=
  FiniteRowsNoGoAuditW28.not_concreteValueMatrixRowGate

theorem not_concreteValueMatrixGate :
    Not ConcreteValueMatrixGate := by
  intro H
  exact not_concreteValueMatrixRowGate
    (concreteValueMatrixGate_iff_exactRowPackage.1 H)

theorem not_lowerTableVectorCertificateRowsGate :
    Not LowerTableVectorCertificateRowsGate := by
  intro H
  cases H with
  | intro periodSearch _ =>
      exact not_periodSearchDataGate (Nonempty.intro periodSearch)

theorem not_lowerTableListCertificateRowsGate :
    Not LowerTableListCertificateRowsGate := by
  intro H
  cases H with
  | intro periodSearch _ =>
      exact not_periodSearchDataGate (Nonempty.intro periodSearch)

theorem not_valueMatrixVectorCertificateRowsGate :
    Not ValueMatrixVectorCertificateRowsGate := by
  intro H
  cases H with
  | intro periodSearch _ =>
      exact not_periodSearchDataGate (Nonempty.intro periodSearch)

theorem not_valueMatrixListCertificateRowsGate :
    Not ValueMatrixListCertificateRowsGate := by
  intro H
  cases H with
  | intro periodSearch _ =>
      exact not_periodSearchDataGate (Nonempty.intro periodSearch)

theorem not_concreteLowerTableGate :
    Not ConcreteLowerTableGate :=
  FiniteRowsNoGoAuditW28.not_concreteLowerTableGate

end

end ConcreteLowerTableValueDataBlockerW32
end PachToth
end ErdosProblems1066
