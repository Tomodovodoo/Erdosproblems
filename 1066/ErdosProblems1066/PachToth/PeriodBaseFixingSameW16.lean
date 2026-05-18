import ErdosProblems1066.PachToth.PeriodRowsAllPositiveProofW15
import ErdosProblems1066.PachToth.PeriodEquationConcreteW14
import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch

set_option autoImplicit false

/-!
# W16 same-orientation base fixing

This file isolates the same-orientation branch of the W15 all-positive
period-row gate.  The branch gives rows as soon as the selected transition
fixes the checked base block.  For the present strong role-hinge transition
package, however, the transition package itself is inconsistent: its
same-block preservation field ranges over arbitrary source placements.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodBaseFixingSameW16

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingeTransitions :=
  PeriodRowsAllPositiveProofW15.RoleHingeTransitions

abbrev PeriodRows :=
  PeriodRowsAllPositiveProofW15.PeriodRows

abbrev ConcretePeriodEquationFields :=
  PeriodEquationConcreteW14.ConcretePeriodEquationFields

abbrev SameFixesExactBase (T : RoleHingeTransitions) : Prop :=
  PeriodRowsAllPositiveProofW15.SameFixesExactBase T

abbrev BaseFixingAlternative (T : RoleHingeTransitions) : Prop :=
  PeriodRowsAllPositiveProofW15.BaseFixingAlternative T

/-- The checked base used by the same-fixing branch. -/
def exactBase : LocalVertex -> R2 :=
  BaseTransitionRealization.exactBase

@[simp]
theorem exactBase_eq :
    exactBase = BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem periodRows_eq_concreteFields :
    PeriodRows = ConcretePeriodEquationFields :=
  rfl

/-- The word-certificate spelling and the period-example spelling package the
same finite orientation word. -/
theorem periodWord_finiteOrientationWordOfWord_eq
    {k : Nat} (hk : 0 < k) (W : OrientationWord.Word k) :
    PeriodWordCertificates.finiteOrientationWordOfWord hk W =
      PeriodCertificateExamples.finiteOrientationWordOfWord hk W := by
  rfl

/-- The same-orientation base-fixing branch gives the concrete all-positive
row fields. -/
def sameRows
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    PeriodRows :=
  PeriodRowsAllPositiveProofW15.sameRows T hfix

@[simp]
theorem sameRows_transitions
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    (sameRows T hfix).transitions = T :=
  rfl

@[simp]
theorem sameRows_word
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T)
    (k : Nat) (hk : 0 < k) :
    (sameRows T hfix).word k hk =
      PeriodCertificateExamples.allPositiveSameWord k hk :=
  rfl

/-- The same disjunct alone closes the all-positive row package. -/
theorem exists_rows_of_sameFixesExactBase
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    exists P : PeriodRows, P.transitions = T :=
  Exists.intro (sameRows T hfix) rfl

/-- The same disjunct is the left branch of the W15 base-fixing alternative. -/
theorem baseFixingAlternative_of_sameFixesExactBase
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    BaseFixingAlternative T :=
  Or.inl hfix

/-- The W15 equivalence also closes from the same disjunct. -/
theorem rows_exist_iff_left_to_right_same
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    (exists P : PeriodRows, P.transitions = T) := by
  exact
    (PeriodRowsAllPositiveProofW15.rows_exist_iff_baseFixingAlternative T).2
      (baseFixingAlternative_of_sameFixesExactBase T hfix)

/-- Extract the same branch as the search-facing role-hinge fact package. -/
def sameTransitionFacts
    (T : RoleHingeTransitions) :
    RoleHingeTransitionSearch.RoleHingeTransitionFacts where
  placeNext := T.same.placeNext
  roleAngle := T.same.roleAngle
  realizes_role := T.same.realizes_role
  preserves_same_block_distances := T.same.preserves_same_block_distances

@[simp]
theorem sameTransitionFacts_placeNext
    (T : RoleHingeTransitions) :
    (sameTransitionFacts T).placeNext = T.same.placeNext :=
  rfl

/-- The strong role-hinge package has no viable same branch. -/
theorem false_of_roleHingeTransitions_same
    (T : RoleHingeTransitions) :
    False :=
  RoleHingeTransitionSearch.false_of_roleHingeTransitionFacts
    (sameTransitionFacts T)

/-- There is no viable strong same/opposite role-hinge package. -/
theorem not_nonempty_roleHingeTransitions :
    Not (Nonempty RoleHingeTransitions) := by
  intro h
  cases h with
  | intro T =>
      exact false_of_roleHingeTransitions_same T

/-- Hence no viable package can witness the same exact-base fixing branch. -/
theorem not_exists_sameFixesExactBase :
    Not (exists T : RoleHingeTransitions, SameFixesExactBase T) := by
  intro h
  cases h with
  | intro T _hfix =>
      exact false_of_roleHingeTransitions_same T

/-- Pointwise obstruction for the same branch under the present strong
transition interface. -/
theorem not_sameFixesExactBase
    (T : RoleHingeTransitions) :
    Not (SameFixesExactBase T) := by
  intro _hfix
  exact false_of_roleHingeTransitions_same T

end

end PeriodBaseFixingSameW16
end PachToth
end ErdosProblems1066
