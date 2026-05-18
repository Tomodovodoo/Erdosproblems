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

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev UpperTriangleSqValueTableFamily :=
  CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily

abbrev IndexedCrossBlockSqDistanceTableFamily :=
  CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTableFamily

/-- The exact remaining data for the current non-rigid finite-certificate
route to the arbitrary Pach--Toth target. -/
structure Obligations where
  periodSearch : PeriodSearchData
  sqValueTables :
    UpperTriangleSqValueTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace Obligations

/-- The role-hinged period-search family exposed by the summary package. -/
def toRoleHingedPeriodSearchFamily
    (O : Obligations) :
    RoleHingedPeriodSearchFamily :=
  O.periodSearch.toRoleHingedPeriodSearchFamily

@[simp]
theorem toRoleHingedPeriodSearchFamily_eq
    (O : Obligations) :
    O.toRoleHingedPeriodSearchFamily =
      O.periodSearch.toRoleHingedPeriodSearchFamily :=
  rfl

/-- The generated square-distance table family obtained from the stored
upper-triangle value tables. -/
def toSqDistanceTableFamily
    (O : Obligations) :
    IndexedCrossBlockSqDistanceTableFamily
      O.toRoleHingedPeriodSearchFamily :=
  O.sqValueTables.toSqDistanceTableFamily

/-- The cross-block lower-bound facade obtained from the stored finite
square-distance tables. -/
def toCrossBlockLowerBounds
    (O : Obligations) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      O.toRoleHingedPeriodSearchFamily :=
  O.sqValueTables.toCrossBlockLowerBounds

/-- The exact-multiple Pach--Toth target obtained from the summarized
non-rigid finite-certificate obligations. -/
theorem targetUpperConstructionFiveSixteen
    (O : Obligations) :
    PachToth.targetUpperConstructionFiveSixteen :=
  O.sqValueTables.targetUpperConstructionFiveSixteen

/-- The arbitrary-`n` Pach--Toth target obtained from the summarized
non-rigid finite-certificate obligations. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (O : Obligations) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  O.sqValueTables.targetUpperConstructionFiveSixteenArbitrary

end Obligations

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
