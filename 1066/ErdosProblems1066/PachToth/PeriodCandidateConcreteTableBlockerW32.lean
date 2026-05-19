import ErdosProblems1066.PachToth.PeriodBaseFixingSameW16
import ErdosProblems1066.PachToth.PeriodCandidateTargetRoute

set_option autoImplicit false

/-!
# W32 blocker for the role-hinge concrete table route

The live Pach--Toth route should use the flexible W11 source directly.  The
older concrete lower-table package stores the strong role-hinge transition
package, and the strong package is already refuted by the checked same-branch
base-fixing obstruction.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodCandidateConcreteTableBlockerW32

noncomputable section

open PeriodCandidateTargetRoute.PeriodCandidatePartialLowerTableData

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily

abbrev PeriodCandidatePartialLowerTableData : Type :=
  PeriodCandidateTargetRoute.PeriodCandidatePartialLowerTableData

abbrev TargetConcreteSourceWithTransition : Type :=
  ConcreteNonConnectorLowerTableFamilyWithTransition

abbrev ConcreteNonConnectorLowerTableFamilyWithTransition : Type :=
  TargetConcreteSourceWithTransition

theorem false_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteNonConnectorLowerTableFamily) :
    False :=
  PeriodBaseFixingSameW16.false_of_roleHingeTransitions_same
    C.periodSearch.transitions

theorem not_nonempty_concreteNonConnectorLowerTableFamily :
    Not (Nonempty ConcreteNonConnectorLowerTableFamily) := by
  intro H
  cases H with
  | intro C =>
      exact false_of_concreteNonConnectorLowerTableFamily C

theorem not_nonempty_concreteNonConnectorLowerTableFamilyWithTransition :
    Not (Nonempty ConcreteNonConnectorLowerTableFamilyWithTransition) := by
  intro H
  cases H with
  | intro C =>
      exact
        not_nonempty_concreteNonConnectorLowerTableFamily
          (Nonempty.intro C.1)

theorem not_nonempty_periodCandidatePartialLowerTableData :
    Not (Nonempty PeriodCandidatePartialLowerTableData) := by
  intro H
  have hsource :
      Nonempty ConcreteNonConnectorLowerTableFamilyWithTransition :=
    nonempty_iff_concreteNonConnectorLowerTableFamilyWithTransition.1 H
  exact
    not_nonempty_concreteNonConnectorLowerTableFamilyWithTransition
      hsource

end

end PeriodCandidateConcreteTableBlockerW32
end PachToth
end ErdosProblems1066
