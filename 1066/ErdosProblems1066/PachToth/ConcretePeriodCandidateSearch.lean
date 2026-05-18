import ErdosProblems1066.PachToth.PeriodEquationConcreteSearch
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.RoleHingeFiniteFamilyBridge
import ErdosProblems1066.PachToth.CrossBlockLowerBoundsInterface

set_option autoImplicit false

/-!
# Concrete period-candidate search facade

This module is a thin search-facing layer over the existing period-equation
and role-hinge finite-family wrappers.  A candidate keeps its orientation word
and the remaining algebraic period equations as explicit `Fin 16` fields.  A
family of such candidates, together with the separate cross-block lower-bound
tables, projects to the exact and arbitrary Pach--Toth target facades.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcretePeriodCandidateSearch

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev TransitionFacts :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord
abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

def transitionObligationsOfFacts
    (T : TransitionFacts) : TransitionObligations :=
  T.toRoleHingeTransitions.toFigure2TransitionObligations

/-- Exact `Fin 16` algebraic period equations for a role-hinged word over the
checked exact base block. -/
abbrev ExactCandidateEquations
    (T : TransitionFacts)
    {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) : Prop :=
  PeriodEquationConcreteSearch.ExactPeriodEquations
    (transitionObligationsOfFacts T) hk
    BaseTransitionRealization.exactBase W

/-- A fixed-length role-hinged period candidate.

The only period-search proof data stored here is the finite `Fin 16` family of
algebraic vertex period equations. -/
structure FixedPeriodCandidate
    (T : TransitionFacts) (k : Nat) (hk : 0 < k) where
  word : OrientationWord.Word k
  equations : ExactCandidateEquations T hk word

namespace FixedPeriodCandidate

/-- The raw finite orientation function used by generated-chain APIs. -/
def orientation
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    Fin k -> OrientationData.BlockOrientation :=
  C.word.toFin

@[simp]
theorem orientation_apply
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) (i : Fin k) :
    C.orientation i = C.word i :=
  rfl

/-- The finite word used by `PeriodWordCertificates`. -/
def finiteWord
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) : FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord hk C.word

@[simp]
theorem finiteWord_length
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    C.finiteWord.length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) (i : Fin k) :
    C.finiteWord.letter i = C.word i :=
  rfl

/-- Repackage a fixed candidate through `PeriodEquationConcreteSearch`. -/
def toPeriodEquationCandidate
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    PeriodEquationConcreteSearch.PeriodEquationCandidate
      (transitionObligationsOfFacts T)
      BaseTransitionRealization.exactBase where
  length := k
  positive_length := hk
  word := C.word
  equations := C.equations

/-- Repackage the explicit equations as the `PeriodWordCertificates`
indexed algebraic certificate. -/
def indexedAlgebraicCertificate
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      (transitionObligationsOfFacts T)
      BaseTransitionRealization.exactBase C.finiteWord :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    (transitionObligationsOfFacts T) hk
    BaseTransitionRealization.exactBase C.word C.equations

/-- The same indexed certificate in the spelling used by the role-hinge
finite-family bridge. -/
def indexedAlgebraicCertificateForBridge
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      (transitionObligationsOfFacts T)
      BaseTransitionRealization.exactBase
      (PeriodCertificateExamples.finiteOrientationWordOfWord hk C.word) where
  equation := by
    intro i
    simpa [PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord]
      using C.equations i

/-- The generated closure equation obtained from the explicit `Fin 16`
algebraic fields. -/
def closure
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    PeriodInterface.GeneratedClosureEquation
      (transitionObligationsOfFacts T) hk
      BaseTransitionRealization.exactBase C.orientation :=
  PeriodWordCertificates.generatedClosureEquationOfWord
    (transitionObligationsOfFacts T) hk
    BaseTransitionRealization.exactBase C.word C.equations

/-- The generated final-block period equation obtained from the explicit
`Fin 16` algebraic fields. -/
def periodEquation
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    PeriodInterface.GeneratedPeriodEquation
      (transitionObligationsOfFacts T) hk
      BaseTransitionRealization.exactBase C.orientation :=
  PeriodWordCertificates.generatedPeriodEquationOfWord
    (transitionObligationsOfFacts T) hk
    BaseTransitionRealization.exactBase C.word C.equations

/-- The downstream generated-period hypothesis obtained from the same
candidate equations. -/
def generatedPeriod
    {T : TransitionFacts} {k : Nat} {hk : 0 < k}
    (C : FixedPeriodCandidate T k hk) :
    GeneratedSeparationInterface.GeneratedPeriod
      (transitionObligationsOfFacts T) hk
      BaseTransitionRealization.exactBase C.orientation :=
  PeriodWordCertificates.generatedPeriodOfWord
    (transitionObligationsOfFacts T) hk
    BaseTransitionRealization.exactBase C.word C.equations

end FixedPeriodCandidate

/-- A length-carrying candidate record, convenient for storing one explicit
period candidate before choosing a family index. -/
structure PeriodCandidate
    (T : TransitionFacts) where
  length : Nat
  positive_length : 0 < length
  word : OrientationWord.Word length
  equations : ExactCandidateEquations T positive_length word

namespace PeriodCandidate

/-- Forget the length-carrying wrapper to the fixed-length candidate. -/
def toFixed
    {T : TransitionFacts}
    (C : PeriodCandidate T) :
    FixedPeriodCandidate T C.length C.positive_length where
  word := C.word
  equations := C.equations

def orientation
    {T : TransitionFacts}
    (C : PeriodCandidate T) :
    Fin C.length -> OrientationData.BlockOrientation :=
  C.word.toFin

def finiteWord
    {T : TransitionFacts}
    (C : PeriodCandidate T) : FiniteOrientationWord :=
  C.toFixed.finiteWord

def toPeriodEquationCandidate
    {T : TransitionFacts}
    (C : PeriodCandidate T) :
    PeriodEquationConcreteSearch.PeriodEquationCandidate
      (transitionObligationsOfFacts T)
      BaseTransitionRealization.exactBase :=
  C.toFixed.toPeriodEquationCandidate

def indexedAlgebraicCertificate
    {T : TransitionFacts}
    (C : PeriodCandidate T) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      (transitionObligationsOfFacts T)
      BaseTransitionRealization.exactBase C.finiteWord :=
  C.toFixed.indexedAlgebraicCertificate

def closure
    {T : TransitionFacts}
    (C : PeriodCandidate T) :
    PeriodInterface.GeneratedClosureEquation
      (transitionObligationsOfFacts T) C.positive_length
      BaseTransitionRealization.exactBase C.orientation :=
  C.toFixed.closure

def periodEquation
    {T : TransitionFacts}
    (C : PeriodCandidate T) :
    PeriodInterface.GeneratedPeriodEquation
      (transitionObligationsOfFacts T) C.positive_length
      BaseTransitionRealization.exactBase C.orientation :=
  C.toFixed.periodEquation

end PeriodCandidate

namespace SmallWords

open PeriodEquationConcreteSearch.SmallWords

def sameOneCandidate
    (T : TransitionFacts)
    (equations :
      SameOneEquations (transitionObligationsOfFacts T)
        BaseTransitionRealization.exactBase) :
    PeriodCandidate T where
  length := 1
  positive_length := PeriodEquationConcreteSearch.onePositive
  word := sameOneWord
  equations := equations

def oppositeOneCandidate
    (T : TransitionFacts)
    (equations :
      OppositeOneEquations (transitionObligationsOfFacts T)
        BaseTransitionRealization.exactBase) :
    PeriodCandidate T where
  length := 1
  positive_length := PeriodEquationConcreteSearch.onePositive
  word := oppositeOneWord
  equations := equations

def sameOppositeTwoCandidate
    (T : TransitionFacts)
    (equations :
      SameOppositeTwoEquations (transitionObligationsOfFacts T)
        BaseTransitionRealization.exactBase) :
    PeriodCandidate T where
  length := 2
  positive_length := PeriodEquationConcreteSearch.twoPositive
  word := sameOppositeTwoWord
  equations := equations

def twoWordCandidate
    (T : TransitionFacts)
    (a b : OrientationData.BlockOrientation)
    (equations :
      TwoWordEquations (transitionObligationsOfFacts T)
        BaseTransitionRealization.exactBase a b) :
    PeriodCandidate T where
  length := 2
  positive_length := PeriodEquationConcreteSearch.twoPositive
  word := twoWord a b
  equations := equations

end SmallWords

/-- A role-hinged period-candidate family, one explicit candidate for every
positive block count.  Each member exposes exactly the finite `Fin 16`
period-equation fields. -/
structure PeriodCandidateFamily where
  transitions : TransitionFacts
  candidate :
    forall (k : Nat) (hk : 0 < k),
      FixedPeriodCandidate transitions k hk

namespace PeriodCandidateFamily

def word
    (F : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) : OrientationWord.Word k :=
  (F.candidate k hk).word

def orientation
    (F : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    (F : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

def period
    (F : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      (transitionObligationsOfFacts F.transitions)
      BaseTransitionRealization.exactBase
      (PeriodCertificateExamples.finiteOrientationWordOfWord hk
        (F.word k hk)) :=
  (F.candidate k hk).indexedAlgebraicCertificateForBridge

def closure
    (F : PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      (transitionObligationsOfFacts F.transitions) hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.candidate k hk).closure

/-- Project period candidates to the finite period-search family used by the
cross-block lower-bound interface. -/
def toRoleHingedPeriodSearchFamily
    (F : PeriodCandidateFamily) :
    CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily where
  transitions := F.transitions.toRoleHingeTransitions
  orientation := F.orientation
  period := by
    intro k hk
    refine { equation := ?_ }
    intro i
    simpa [ExactFamilyClosure.finiteOrientationWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord, orientation,
      word]
      using (F.candidate k hk).equations i

end PeriodCandidateFamily

/-- Period candidates plus the remaining cross-block lower-bound family.

The period equations remain in `period.candidate`; the lower-bound table and
its two finite metric predicates are the separate remaining separation data. -/
structure PeriodCandidateSearchFamily where
  period : PeriodCandidateFamily
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hk)
  lower_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        (transitionObligationsOfFacts period.transitions)
        hk
        BaseTransitionRealization.exactBase
        (period.orientation k hk)
        (lower k hk)

namespace PeriodCandidateSearchFamily

def transitions
    (F : PeriodCandidateSearchFamily) : TransitionFacts :=
  F.period.transitions

def word
    (F : PeriodCandidateSearchFamily)
    (k : Nat) (hk : 0 < k) : OrientationWord.Word k :=
  F.period.word k hk

def orientation
    (F : PeriodCandidateSearchFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  F.period.orientation k hk

/-- Projection to the role-hinge finite-family bridge requested by the
role-hinged exact target route. -/
def toRoleHingeTransitionFactsFiniteSearchFamily
    (F : PeriodCandidateSearchFamily) :
    RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily
      where
  transitions := F.transitions
  word := F.word
  period := F.period.period
  lower := F.lower
  lower_ge_one := F.lower_ge_one
  lower_bound := F.lower_bound

def toRoleHingedPeriodSearchFamily
    (F : PeriodCandidateSearchFamily) :
    CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily :=
  F.period.toRoleHingedPeriodSearchFamily

/-- Projection to the cross-block lower-bound facade, used for the arbitrary
`n` wrapper. -/
def toCrossBlockLowerBounds
    (F : PeriodCandidateSearchFamily) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds
      F.toRoleHingedPeriodSearchFamily where
  lower := F.lower
  lower_ge_one := by
    intro k hk i u j v hij
    exact F.lower_ge_one k hk i u j v hij
  lower_bound := by
    intro k hk i u j v hij
    exact F.lower_bound k hk i u j v hij

/-- Generated separation for one family member, projected from the explicit
cross-block lower-bound fields. -/
def separated
    (F : PeriodCandidateSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      (transitionObligationsOfFacts F.transitions) hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  F.toRoleHingeTransitionFactsFiniteSearchFamily.separated k hk

/-- Generated closure for one family member, projected from its explicit
period-candidate equations. -/
def closure
    (F : PeriodCandidateSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      (transitionObligationsOfFacts F.transitions) hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  F.toRoleHingeTransitionFactsFiniteSearchFamily.closure k hk

/-- Exact-block target at a chosen positive block count. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (F : PeriodCandidateSearchFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  F.toRoleHingeTransitionFactsFiniteSearchFamily
    |>.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact-multiple Pach--Toth target through
`RoleHingeFiniteFamilyBridge`. -/
theorem targetUpperConstructionFiveSixteen
    (F : PeriodCandidateSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toRoleHingeTransitionFactsFiniteSearchFamily
    |>.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target through the cross-block lower-bound facade
and the checked small-case/remainder closure already imported downstream. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : PeriodCandidateSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end PeriodCandidateSearchFamily

end

end ConcretePeriodCandidateSearch
end PachToth
end ErdosProblems1066
