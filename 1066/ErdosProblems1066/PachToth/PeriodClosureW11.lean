import ErdosProblems1066.PachToth.PeriodEquationSearchW11
import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11

set_option autoImplicit false

/-!
# W11 period closure package

This file is a W11 facade for closing checked period/equation families once
their separation or lower-bound ledgers have been supplied.  It introduces no
period words, numeric inequalities, or certificate inhabitants.  Those remain
fields of the packages below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodClosureW11

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev Candidate := PeriodEquationSearchW11.Candidate
abbrev CheckedWordEquationPackage :=
  PeriodEquationSearchW11.CheckedWordEquationPackage
abbrev CheckedWordEquationFamily :=
  PeriodEquationSearchW11.CheckedWordEquationFamily
abbrev CandidateWordEquations :=
  PeriodEquationSearchW11.CandidateWordEquations
abbrev GeneratedFamilyRemainingFields :=
  PeriodEquationSearchW11.GeneratedFamilyRemainingFields
abbrev ExactCandidatePeriodFields :=
  PeriodEquationSearchW11.ExactCandidatePeriodFields
abbrev SmallWordObstructionLedger :=
  PeriodEquationSearchW11.SmallWordObstructionLedger
abbrev FamilyEquationObstruction :=
  PeriodEquationSearchW11.FamilyEquationObstruction
abbrev RoleHingeTransitions :=
  PeriodEquationSearchW11.RoleHingeTransitions
abbrev CrossBlockPeriodSearchFamily :=
  CrossBlockInequalityLedgerW11.RoleHingedPeriodSearchFamily
abbrev CrossBlockInequalityLedger :=
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger
abbrev W11NonRigidRouteFields :=
  FlexibleTransitionSearchW11.NonRigidRouteFields
abbrev W11NonRigidCandidateRemainingFields :=
  FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields

/-! ## Uniform target rows -/

theorem eventual_of_arbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

theorem arbitrary_of_exact
    (H : PachToth.targetUpperConstructionFiveSixteen) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachTothFinalDataAssembly.exactRemainderBridge_present H

theorem eventual_of_exact
    (H : PachToth.targetUpperConstructionFiveSixteen) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  eventual_of_arbitrary (arbitrary_of_exact H)

structure TargetProjectionRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

def rowOfExactAndArbitrary
    {alpha : Type}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    TargetProjectionRow alpha where
  exactTarget := exactTarget
  eventualTarget := fun A => eventual_of_arbitrary (arbitraryTarget A)
  arbitraryTarget := arbitraryTarget

def rowOfExact
    {alpha : Type}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen) :
    TargetProjectionRow alpha :=
  rowOfExactAndArbitrary exactTarget (fun A => arbitrary_of_exact (exactTarget A))

/-! ## Checked periods plus supplied separation -/

def separatedCheckedFamilyRow
    (T : Candidate) :
    TargetProjectionRow (GeneratedFamilyRemainingFields T) :=
  rowOfExact
    PeriodEquationSearchW11.GeneratedFamilyRemainingFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_of_separatedCheckedFamily
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (separatedCheckedFamilyRow T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_separatedCheckedFamily
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (separatedCheckedFamilyRow T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_separatedCheckedFamily
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (separatedCheckedFamilyRow T).arbitraryTarget D

/-! ## Checked periods plus W11 cross-block inequality ledgers -/

structure CrossBlockLedgerClosureFields (T : Candidate) where
  period : CheckedWordEquationFamily T
  transitions : RoleHingeTransitions
  transition_eq :
    transitions.toFigure2TransitionObligations =
      T.toFigure2TransitionObligations
  ledger :
    CrossBlockInequalityLedger
      ((NonRigidPeriodCandidateW10.concretePeriodSearchDataOfAlgebraicFamily
        transitions transition_eq period.toAlgebraicFamily)
          |>.toRoleHingedPeriodSearchFamily)

namespace CrossBlockLedgerClosureFields

def periodSearch
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    ConcretePeriodSearchFamily.PeriodSearchData :=
  NonRigidPeriodCandidateW10.concretePeriodSearchDataOfAlgebraicFamily
    D.transitions D.transition_eq D.period.toAlgebraicFamily

def roleHingedPeriodSearchFamily
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    CrossBlockPeriodSearchFamily :=
  D.periodSearch.toRoleHingedPeriodSearchFamily

theorem separated
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      T.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (D.period.orientation k hk) := by
  have hsep := D.ledger.separated k hk
  have hsep' :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        D.transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (D.period.orientation k hk) := by
    simpa [CrossBlockInequalityLedgerW11.GeneratedGlobalSeparationAt,
      periodSearch, roleHingedPeriodSearchFamily,
      NonRigidPeriodCandidateW10.concretePeriodSearchDataOfAlgebraicFamily,
      ConcretePeriodSearchFamily.PeriodSearchData.orientation] using hsep
  simpa [D.transition_eq] using hsep'

def toSeparatedCheckedFamily
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    GeneratedFamilyRemainingFields T where
  period := D.period
  separated := D.separated

theorem targetUpperConstructionFiveSixteen
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toSeparatedCheckedFamily.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  arbitrary_of_exact D.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenEventually
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  eventual_of_arbitrary D.targetUpperConstructionFiveSixteenArbitrary

end CrossBlockLedgerClosureFields

def crossBlockLedgerClosureFieldsRow
    (T : Candidate) :
    TargetProjectionRow (CrossBlockLedgerClosureFields T) where
  exactTarget :=
    CrossBlockLedgerClosureFields.targetUpperConstructionFiveSixteen
  eventualTarget :=
    CrossBlockLedgerClosureFields.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :=
    CrossBlockLedgerClosureFields.targetUpperConstructionFiveSixteenArbitrary

/-! ## Checked periods plus explicit lower-bound ledgers -/

structure ExplicitLowerBoundClosureFields (T : Candidate) where
  period : CheckedWordEquationFamily T
  transitions : RoleHingeTransitions
  transition_eq :
    transitions.toFigure2TransitionObligations =
      T.toFigure2TransitionObligations
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j -> 1 <= lower k hk i u j v
  lower_bound :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          lower k hk i u j v <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint
                T.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (period.orientation k hk)
                i u)
              (GeneratedClosedChain.generatedPoint
                T.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (period.orientation k hk)
                j v)

namespace ExplicitLowerBoundClosureFields

def equationsForTransitions
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationConcreteSearch.ExactPeriodEquations
      D.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (D.period.word k hk) := by
  simpa [D.transition_eq] using D.period.equations k hk

theorem lower_bound_for_transitions
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex)
    (hij : Ne i j) :
    D.lower k hk i u j v <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint
          D.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          ((D.period.word k hk).toFin)
          i u)
        (GeneratedClosedChain.generatedPoint
          D.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          ((D.period.word k hk).toFin)
          j v) := by
  simpa [PeriodEquationSearchW11.CheckedWordEquationFamily.orientation,
    D.transition_eq] using D.lower_bound k hk i u j v hij

def toConcreteCrossBlockFamily
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    ConcretePeriodSearchFamily.ConcreteCrossBlockFamily :=
  ConcretePeriodSearchFamily.ConcreteCrossBlockFamily.ofWordEquationsAndLowerBounds
    D.transitions
    D.period.word
    D.equationsForTransitions
    D.lower
    D.lower_ge_one
    D.lower_bound_for_transitions

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  D.toConcreteCrossBlockFamily.targetUpperConstructionFiveSixteenAt_exactBlock
    k hk

theorem targetUpperConstructionFiveSixteen
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toConcreteCrossBlockFamily.targetUpperConstructionFiveSixteen_viaGeneratedPeriod

theorem targetUpperConstructionFiveSixteenArbitrary
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  arbitrary_of_exact D.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenEventually
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  eventual_of_arbitrary D.targetUpperConstructionFiveSixteenArbitrary

end ExplicitLowerBoundClosureFields

def explicitLowerBoundClosureFieldsRow
    (T : Candidate) :
    TargetProjectionRow (ExplicitLowerBoundClosureFields T) where
  exactTarget :=
    ExplicitLowerBoundClosureFields.targetUpperConstructionFiveSixteen
  eventualTarget :=
    ExplicitLowerBoundClosureFields.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :=
    ExplicitLowerBoundClosureFields.targetUpperConstructionFiveSixteenArbitrary

/-! ## Existing exact-route and flexible-route rows -/

def exactCandidatePeriodFieldsRow
    (T : Candidate) :
    TargetProjectionRow (ExactCandidatePeriodFields T) :=
  rowOfExactAndArbitrary
    PeriodEquationSearchW11.ExactCandidatePeriodFields.targetUpperConstructionFiveSixteen
    PeriodEquationSearchW11.ExactCandidatePeriodFields.targetUpperConstructionFiveSixteenArbitrary

def w11NonRigidCandidateRemainingFieldsRow
    (T : FlexibleTransitionSearchW11.SameOppositeCandidate) :
    TargetProjectionRow (W11NonRigidCandidateRemainingFields T) :=
  rowOfExactAndArbitrary
    (fun R => R.targetUpperConstructionFiveSixteen)
    (fun R => R.targetUpperConstructionFiveSixteenArbitrary)

def w11NonRigidRouteFieldsRow :
    TargetProjectionRow W11NonRigidRouteFields :=
  rowOfExactAndArbitrary
    (fun R => R.targetUpperConstructionFiveSixteen)
    (fun R => R.targetUpperConstructionFiveSixteenArbitrary)

/-! ## Consolidated package -/

structure MissingDataLedger where
  checkedWordPackages : Candidate -> Type
  checkedFamilyPackages : Candidate -> Type
  separatedFamilyFields : Candidate -> Type
  crossBlockLedgerFields : Candidate -> Type
  explicitLowerBoundFields : Candidate -> Type
  exactCandidateFields : Candidate -> Type
  smallWordObstructions : Candidate -> Prop
  familyObstructions :
    forall _T : Candidate,
      (forall (k : Nat), 0 < k -> OrientationWord.Word k) -> Type
  nonRigidRoutes : Type

def missingDataLedger : MissingDataLedger where
  checkedWordPackages := CheckedWordEquationPackage
  checkedFamilyPackages := CheckedWordEquationFamily
  separatedFamilyFields := GeneratedFamilyRemainingFields
  crossBlockLedgerFields := CrossBlockLedgerClosureFields
  explicitLowerBoundFields := ExplicitLowerBoundClosureFields
  exactCandidateFields := ExactCandidatePeriodFields
  smallWordObstructions := SmallWordObstructionLedger
  familyObstructions := FamilyEquationObstruction
  nonRigidRoutes := W11NonRigidRouteFields

structure Matrix where
  periodEquationMatrix : PeriodEquationSearchW11.Matrix
  missingData : MissingDataLedger
  separatedFamilies :
    forall T : Candidate,
      TargetProjectionRow (GeneratedFamilyRemainingFields T)
  crossBlockLedgerClosures :
    forall T : Candidate,
      TargetProjectionRow (CrossBlockLedgerClosureFields T)
  explicitLowerBoundClosures :
    forall T : Candidate,
      TargetProjectionRow (ExplicitLowerBoundClosureFields T)
  exactCandidatePeriods :
    forall T : Candidate,
      TargetProjectionRow (ExactCandidatePeriodFields T)
  nonRigidCandidateRemaining :
    forall T : FlexibleTransitionSearchW11.SameOppositeCandidate,
      TargetProjectionRow (W11NonRigidCandidateRemainingFields T)
  nonRigidRoutes :
    TargetProjectionRow W11NonRigidRouteFields

def matrix : Matrix where
  periodEquationMatrix := PeriodEquationSearchW11.matrix
  missingData := missingDataLedger
  separatedFamilies := separatedCheckedFamilyRow
  crossBlockLedgerClosures := crossBlockLedgerClosureFieldsRow
  explicitLowerBoundClosures := explicitLowerBoundClosureFieldsRow
  exactCandidatePeriods := exactCandidatePeriodFieldsRow
  nonRigidCandidateRemaining := w11NonRigidCandidateRemainingFieldsRow
  nonRigidRoutes := w11NonRigidRouteFieldsRow

/-! ## Public projections -/

theorem targetUpperConstructionFiveSixteen_of_crossBlockLedgerClosureFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockLedgerClosures T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockLedgerClosureFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLedgerClosures T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLedgerClosureFields
    {T : Candidate}
    (D : CrossBlockLedgerClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLedgerClosures T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_explicitLowerBoundClosureFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.explicitLowerBoundClosures T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_explicitLowerBoundClosureFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.explicitLowerBoundClosures T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundClosureFields
    {T : Candidate}
    (D : ExplicitLowerBoundClosureFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.explicitLowerBoundClosures T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.exactCandidatePeriods T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.exactCandidatePeriods T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.exactCandidatePeriods T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_w11NonRigidRouteFields
    (D : W11NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.nonRigidRoutes.exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_w11NonRigidRouteFields
    (D : W11NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.nonRigidRoutes.eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_w11NonRigidRouteFields
    (D : W11NonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.nonRigidRoutes.arbitraryTarget D

end

end PeriodClosureW11
end PachToth
end ErdosProblems1066
