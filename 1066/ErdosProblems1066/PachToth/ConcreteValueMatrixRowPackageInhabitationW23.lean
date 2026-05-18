import ErdosProblems1066.PachToth.ConcreteValueMatrixFamilyInhabitationW22
import ErdosProblems1066.PachToth.PeriodBaseFixingSameW16

set_option autoImplicit false

/-!
# W23 concrete value-matrix row-package inhabitation check

This file attacks the W22 row-package source directly.  The W18 value-row
producers assemble the package once a concrete period-search family and the
three row families are supplied.  In the current development the period-search
field is already blocked by the empty strong role-hinge transition package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteValueMatrixRowPackageInhabitationW23

noncomputable section

abbrev RowPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixRowPackage

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.ConcreteValueMatrixFamily

abbrev W21InputPackage : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.W21InputPackage

abbrev PeriodSearchData : Type :=
  ConcreteValueMatrixFamilyInhabitationW22.PeriodSearchData

abbrev RoleHingeTransitions : Type :=
  ConcretePeriodSearchFamily.RoleHingeTransitions

abbrev LengthTwoThreeValueRows
    (F : ConcreteValueMatrixFamilyInhabitationW22.RoleHingedPeriodSearchFamily) :
    Type :=
  SmallRowsTwoThreeValueProducerW18.LengthTwoThreeValueRows F

abbrev LengthFourFiveValueRows
    (F : ConcreteValueMatrixFamilyInhabitationW22.RoleHingedPeriodSearchFamily) :
    Type :=
  SmallRowsFourFiveValueProducerW18.LengthFourFiveValueRows F

abbrev TailValueRows
    (F : ConcreteValueMatrixFamilyInhabitationW22.RoleHingedPeriodSearchFamily) :
    Type :=
  TailValueRowsProducerW18.TailValueRows F

/-- The W18 row data needed after choosing the concrete period-search data. -/
structure W18RowFamilies (periodSearch : PeriodSearchData) where
  smallTwoThree :
    LengthTwoThreeValueRows periodSearch.toRoleHingedPeriodSearchFamily
  smallFourFive :
    LengthFourFiveValueRows periodSearch.toRoleHingedPeriodSearchFamily
  tail :
    TailValueRows periodSearch.toRoleHingedPeriodSearchFamily

namespace W18RowFamilies

def toRowPackage
    {periodSearch : PeriodSearchData}
    (R : W18RowFamilies periodSearch) :
    RowPackage where
  periodSearch := periodSearch
  smallTwoThree := R.smallTwoThree
  smallFourFive := R.smallFourFive
  tail := R.tail

def toConcreteValueMatrixFamily
    {periodSearch : PeriodSearchData}
    (R : W18RowFamilies periodSearch) :
    ConcreteValueMatrixFamily :=
  R.toRowPackage.toConcreteValueMatrixFamily

def toInputPackage
    {periodSearch : PeriodSearchData}
    (R : W18RowFamilies periodSearch) :
    W21InputPackage :=
  R.toRowPackage.toInputPackage

@[simp]
theorem toConcreteValueMatrixFamily_eq_w22
    {periodSearch : PeriodSearchData}
    (R : W18RowFamilies periodSearch) :
    R.toConcreteValueMatrixFamily =
      R.toRowPackage.toConcreteValueMatrixFamily :=
  rfl

@[simp]
theorem toInputPackage_eq_w22
    {periodSearch : PeriodSearchData}
    (R : W18RowFamilies periodSearch) :
    R.toInputPackage = R.toRowPackage.toInputPackage :=
  rfl

end W18RowFamilies

def rowPackageOfW18Rows
    (periodSearch : PeriodSearchData)
    (smallTwoThree :
      LengthTwoThreeValueRows periodSearch.toRoleHingedPeriodSearchFamily)
    (smallFourFive :
      LengthFourFiveValueRows periodSearch.toRoleHingedPeriodSearchFamily)
    (tail :
      TailValueRows periodSearch.toRoleHingedPeriodSearchFamily) :
    RowPackage :=
  (W18RowFamilies.mk smallTwoThree smallFourFive tail).toRowPackage

def concreteValueMatrixFamilyOfW18Rows
    (periodSearch : PeriodSearchData)
    (smallTwoThree :
      LengthTwoThreeValueRows periodSearch.toRoleHingedPeriodSearchFamily)
    (smallFourFive :
      LengthFourFiveValueRows periodSearch.toRoleHingedPeriodSearchFamily)
    (tail :
      TailValueRows periodSearch.toRoleHingedPeriodSearchFamily) :
    ConcreteValueMatrixFamily :=
  (rowPackageOfW18Rows periodSearch smallTwoThree smallFourFive tail)
    |>.toConcreteValueMatrixFamily

def inputPackageOfW18Rows
    (periodSearch : PeriodSearchData)
    (smallTwoThree :
      LengthTwoThreeValueRows periodSearch.toRoleHingedPeriodSearchFamily)
    (smallFourFive :
      LengthFourFiveValueRows periodSearch.toRoleHingedPeriodSearchFamily)
    (tail :
      TailValueRows periodSearch.toRoleHingedPeriodSearchFamily) :
    W21InputPackage :=
  (rowPackageOfW18Rows periodSearch smallTwoThree smallFourFive tail)
    |>.toInputPackage

theorem nonempty_rowPackage_iff_exists_w18RowFamilies :
    Nonempty RowPackage <->
      Exists fun periodSearch : PeriodSearchData =>
        Nonempty (W18RowFamilies periodSearch) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.periodSearch
            (Nonempty.intro
              { smallTwoThree := P.smallTwoThree
                smallFourFive := P.smallFourFive
                tail := P.tail })
  case mpr =>
    intro h
    cases h with
    | intro periodSearch hrows =>
        cases hrows with
        | intro R =>
            exact Nonempty.intro R.toRowPackage

def periodSearchDataOfRowPackage
    (P : RowPackage) :
    PeriodSearchData :=
  P.periodSearch

def roleHingeTransitionsOfPeriodSearchData
    (P : PeriodSearchData) :
    RoleHingeTransitions :=
  P.transitions

theorem rowPackage_requires_periodSearchData :
    Nonempty RowPackage -> Nonempty PeriodSearchData := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.periodSearch

theorem periodSearchData_requires_roleHingeTransitions :
    Nonempty PeriodSearchData -> Nonempty RoleHingeTransitions := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro P.transitions

theorem not_nonempty_roleHingeTransitions :
    Not (Nonempty RoleHingeTransitions) :=
  PeriodBaseFixingSameW16.not_nonempty_roleHingeTransitions

theorem not_nonempty_periodSearchData :
    Not (Nonempty PeriodSearchData) := by
  intro h
  exact not_nonempty_roleHingeTransitions
    (periodSearchData_requires_roleHingeTransitions h)

theorem not_nonempty_rowPackage :
    Not (Nonempty RowPackage) := by
  intro h
  exact not_nonempty_periodSearchData
    (rowPackage_requires_periodSearchData h)

theorem not_exists_w18RowFamilies :
    Not
      (Exists fun periodSearch : PeriodSearchData =>
        Nonempty (W18RowFamilies periodSearch)) := by
  intro h
  exact not_nonempty_rowPackage
    (nonempty_rowPackage_iff_exists_w18RowFamilies.2 h)

theorem no_concreteValueMatrixFamily_from_w18RowFamilies :
    Not (Nonempty ConcreteValueMatrixFamily) := by
  intro h
  exact not_nonempty_rowPackage
    (ConcreteValueMatrixFamilyInhabitationW22.nonempty_concreteValueMatrixFamily_iff_rowPackage.1
      h)

end

end ConcreteValueMatrixRowPackageInhabitationW23
end PachToth
end ErdosProblems1066
