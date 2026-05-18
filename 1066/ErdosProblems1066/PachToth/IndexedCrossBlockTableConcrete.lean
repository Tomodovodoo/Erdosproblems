import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily

set_option autoImplicit false

/-!
# Concrete finite indexed cross-block tables

This module is the concrete wrapper for finite-index cross-block lower tables.
The only remaining numerical obligations are the finite inequalities stored in
`IndexedCrossBlockLowerTable`: entries on distinct blocks are at least one, and
each entry is bounded above by the corresponding generated distance.
-/

namespace ErdosProblems1066
namespace PachToth
namespace IndexedCrossBlockTableConcrete

open CrossBlockLowerBoundsInterface
open ConcretePeriodSearchFamily
open FiniteGraph

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev IndexedCrossBlockLowerTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTable F k hk

abbrev IndexedCrossBlockLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTableFamily F

abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F

namespace IndexedCrossBlockLowerTableFamily

/-- Forget a finite-index table family to the lower-bound facade used by the
generated-family closure route. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    CrossBlockLowerBounds F :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.ofIndexedTables T

@[simp]
theorem toCrossBlockLowerBounds_lower
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    (T.toCrossBlockLowerBounds).lower k hk = T.lower k hk :=
  rfl

/-- The `>= 1` finite inequalities project through the concrete facade. -/
theorem toCrossBlockLowerBounds_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((T.toCrossBlockLowerBounds).lower k hk) :=
  (T.toCrossBlockLowerBounds).toLowerBoundsAtLeastOne k hk

/-- The finite metric inequalities project through the concrete facade. -/
theorem toCrossBlockLowerBounds_bound
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      ((T.toCrossBlockLowerBounds).lower k hk) :=
  (T.toCrossBlockLowerBounds).toDistanceLowerBounds k hk

/-- The projected `>= 1` facade is exactly the table-family projection. -/
theorem toCrossBlockLowerBounds_ge_one_eq
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    T.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk =
      T.lower_ge_one k hk :=
  rfl

/-- The projected metric facade is exactly the table-family projection. -/
theorem toCrossBlockLowerBounds_bound_eq
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    T.toCrossBlockLowerBounds.toDistanceLowerBounds k hk =
      T.lower_bound k hk :=
  rfl

/-- Generated global separation supplied by the finite indexed tables. -/
def separated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toCrossBlockLowerBounds.separated k hk

/-- The separation wrapper reduces to the one-table generated separation
projection. -/
theorem separated_eq_table
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    T.separated k hk = (T.table k hk).generatedGlobalSeparation := by
  exact CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.separated_ofIndexedTables
    T k hk

/-- Exact-multiple target obtained directly from finite indexed tables. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target obtained directly from finite indexed tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end IndexedCrossBlockLowerTableFamily

/-- Concrete period-search data plus finite indexed cross-block lower tables. -/
structure IndexedConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  tables :
    IndexedCrossBlockLowerTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace IndexedConcreteCrossBlockFamily

/-- Forget concrete words to the period-search family expected by the
cross-block lower-bound interface. -/
def toRoleHingedPeriodSearchFamily
    (F : IndexedConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  F.periodSearch.toRoleHingedPeriodSearchFamily

@[simp]
theorem toRoleHingedPeriodSearchFamily_eq
    (F : IndexedConcreteCrossBlockFamily) :
    F.toRoleHingedPeriodSearchFamily =
      F.periodSearch.toRoleHingedPeriodSearchFamily :=
  rfl

/-- The stored finite indexed table family, reindexed through the concrete
period-search facade. -/
def toIndexedCrossBlockLowerTableFamily
    (F : IndexedConcreteCrossBlockFamily) :
    IndexedCrossBlockLowerTableFamily F.toRoleHingedPeriodSearchFamily :=
  F.tables

@[simp]
theorem toIndexedCrossBlockLowerTableFamily_table
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    (F.toIndexedCrossBlockLowerTableFamily.table k hk) =
      F.tables.table k hk :=
  rfl

/-- Forget finite indexed tables to the downstream cross-block lower-bound
facade. -/
def toCrossBlockLowerBounds
    (F : IndexedConcreteCrossBlockFamily) :
    CrossBlockLowerBounds F.toRoleHingedPeriodSearchFamily :=
  F.toIndexedCrossBlockLowerTableFamily.toCrossBlockLowerBounds

@[simp]
theorem toCrossBlockLowerBounds_lower
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    (F.toCrossBlockLowerBounds).lower k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower k hk :=
  rfl

/-- The `>= 1` finite inequalities project to `CrossBlockLowerBounds`. -/
theorem toCrossBlockLowerBounds_ge_one
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((F.toCrossBlockLowerBounds).lower k hk) :=
  F.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk

/-- The finite metric inequalities project to `CrossBlockLowerBounds`. -/
theorem toCrossBlockLowerBounds_bound
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk)
      ((F.toCrossBlockLowerBounds).lower k hk) :=
  F.toCrossBlockLowerBounds.toDistanceLowerBounds k hk

/-- The concrete `>= 1` projection is the stored finite table-family
projection. -/
theorem toCrossBlockLowerBounds_ge_one_eq
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower_ge_one k hk :=
  rfl

/-- The concrete metric projection is the stored finite table-family
projection. -/
theorem toCrossBlockLowerBounds_bound_eq
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.toCrossBlockLowerBounds.toDistanceLowerBounds k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower_bound k hk :=
  rfl

/-- Generated global separation supplied by the finite indexed table family. -/
def separated
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk) :=
  F.toCrossBlockLowerBounds.separated k hk

/-- The concrete separation wrapper reduces to the one-table separation
projection. -/
theorem separated_eq_table
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.separated k hk =
      (F.toIndexedCrossBlockLowerTableFamily.table k hk).generatedGlobalSeparation :=
  F.toIndexedCrossBlockLowerTableFamily.separated_eq_table k hk

/-- The role-hinged generated-closure family obtained from concrete
period-search data and finite indexed cross-block tables. -/
def toRoleHingedGeneratedClosureFamily
    (F : IndexedConcreteCrossBlockFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  F.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

/-- Exact-multiple Pach-Toth target from concrete period-search data and finite
indexed cross-block tables. -/
theorem targetUpperConstructionFiveSixteen
    (F : IndexedConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toIndexedCrossBlockLowerTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach-Toth target from concrete period-search data, finite
indexed cross-block tables, and the checked small cases imported downstream. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : IndexedConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toIndexedCrossBlockLowerTableFamily.targetUpperConstructionFiveSixteenArbitrary

end IndexedConcreteCrossBlockFamily

end

end IndexedCrossBlockTableConcrete
end PachToth
end ErdosProblems1066
