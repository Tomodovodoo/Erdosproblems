import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.OrientationWord
import ErdosProblems1066.PachToth.PeriodInterface

set_option autoImplicit false

/-!
# Concrete finite period-equation search ledger

This module records the small finite orientation words currently worth trying
first in the period-equation search.  It does not assert that any search has
succeeded.  Each candidate keeps the exact `Fin 16` family of algebraic
period equations as an explicit field, then projects those equations through
`PeriodWordCertificates` to the existing generated period interface.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodEquationConcreteSearch

open FiniteGraph

noncomputable section

abbrev Orientation := OrientationWord.Orientation
abbrev R2 := Prod Real Real
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord

def onePositive : 0 < 1 :=
  Nat.zero_lt_succ 0

def twoPositive : 0 < 2 :=
  Nat.zero_lt_succ 1

/-- The exact algebraic period equations left for a finite word. -/
abbrev ExactPeriodEquations
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k) : Prop :=
  PeriodWordCertificates.AlgebraicEquationsForWord O hk base W

/-- A finite period-equation candidate: word data plus all exact local-vertex
period equations. -/
structure PeriodEquationCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2) where
  length : Nat
  positive_length : 0 < length
  word : OrientationWord.Word length
  equations : ExactPeriodEquations O positive_length base word

namespace PeriodEquationCandidate

/-- The finite orientation word consumed by the period-search interface. -/
def finiteWord
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord
    C.positive_length C.word

@[simp]
theorem finiteWord_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    C.finiteWord.length = C.length :=
  rfl

@[simp]
theorem finiteWord_letter
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) (i : Fin C.length) :
    C.finiteWord.letter i = C.word i :=
  rfl

/-- Repackage the explicit equations as the indexed algebraic certificate. -/
def indexedAlgebraicCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O base C.finiteWord :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    O C.positive_length base C.word C.equations

/-- Repackage the candidate as a full period-search certificate. -/
def toPeriodSearchCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  PeriodWordCertificates.periodSearchCertificateOfWord
    O C.positive_length base C.word C.equations

/-- The exact algebraic equations imply algebraic generated closure. -/
def generatedClosureEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    PeriodInterface.GeneratedClosureEquation
      O C.positive_length base C.word.toFin :=
  PeriodWordCertificates.generatedClosureEquationOfWord
    O C.positive_length base C.word C.equations

/-- The exact algebraic equations imply the generated final-block period
equation. -/
def generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    PeriodInterface.GeneratedPeriodEquation
      O C.positive_length base C.word.toFin :=
  PeriodWordCertificates.generatedPeriodEquationOfWord
    O C.positive_length base C.word C.equations

end PeriodEquationCandidate

/-- If the exact equations for a word are inconsistent, that word has no
candidate certificate in this ledger. -/
def ContradictoryEquations
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k) : Prop :=
  ExactPeriodEquations O hk base W -> False

theorem noExactPeriodEquations_of_contradictory
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (hbad : ContradictoryEquations O hk base W) :
    Not (ExactPeriodEquations O hk base W) := by
  intro heq
  exact hbad heq

namespace SmallWords

def oneWord (a : Orientation) : OrientationWord.Word 1 :=
  OrientationWord.Word.ofFin fun _ => a

def twoWord (a b : Orientation) : OrientationWord.Word 2 :=
  OrientationWord.Word.ofFin fun i =>
    if i = (0 : Fin 2) then a else b

def constantWord {k : Nat} (a : Orientation) : OrientationWord.Word k :=
  OrientationWord.Word.ofFin fun _ => a

def alternatingWord {k : Nat} : OrientationWord.Word k :=
  OrientationWord.Word.ofFin fun i =>
    if i.val % 2 = 0 then
      OrientationData.BlockOrientation.same
    else
      OrientationData.BlockOrientation.opposite

def sameOneWord : OrientationWord.Word 1 :=
  oneWord OrientationData.BlockOrientation.same

def oppositeOneWord : OrientationWord.Word 1 :=
  oneWord OrientationData.BlockOrientation.opposite

def sameSameTwoWord : OrientationWord.Word 2 :=
  twoWord OrientationData.BlockOrientation.same
    OrientationData.BlockOrientation.same

def sameOppositeTwoWord : OrientationWord.Word 2 :=
  twoWord OrientationData.BlockOrientation.same
    OrientationData.BlockOrientation.opposite

def oppositeSameTwoWord : OrientationWord.Word 2 :=
  twoWord OrientationData.BlockOrientation.opposite
    OrientationData.BlockOrientation.same

def oppositeOppositeTwoWord : OrientationWord.Word 2 :=
  twoWord OrientationData.BlockOrientation.opposite
    OrientationData.BlockOrientation.opposite

@[simp]
theorem oneWord_letter (a : Orientation) (i : Fin 1) :
    (oneWord a) i = a :=
  rfl

@[simp]
theorem twoWord_zero (a b : Orientation) :
    (twoWord a b) (0 : Fin 2) = a := by
  simp [twoWord]

@[simp]
theorem twoWord_one (a b : Orientation) :
    (twoWord a b) (1 : Fin 2) = b := by
  simp [twoWord]

@[simp]
theorem sameOneWord_letter (i : Fin 1) :
    sameOneWord i = OrientationData.BlockOrientation.same :=
  rfl

@[simp]
theorem oppositeOneWord_letter (i : Fin 1) :
    oppositeOneWord i = OrientationData.BlockOrientation.opposite :=
  rfl

@[simp]
theorem sameSameTwoWord_zero :
    sameSameTwoWord (0 : Fin 2) =
      OrientationData.BlockOrientation.same := by
  simp [sameSameTwoWord]

@[simp]
theorem sameSameTwoWord_one :
    sameSameTwoWord (1 : Fin 2) =
      OrientationData.BlockOrientation.same := by
  simp [sameSameTwoWord]

@[simp]
theorem sameOppositeTwoWord_zero :
    sameOppositeTwoWord (0 : Fin 2) =
      OrientationData.BlockOrientation.same := by
  simp [sameOppositeTwoWord]

@[simp]
theorem sameOppositeTwoWord_one :
    sameOppositeTwoWord (1 : Fin 2) =
      OrientationData.BlockOrientation.opposite := by
  simp [sameOppositeTwoWord]

@[simp]
theorem oppositeSameTwoWord_zero :
    oppositeSameTwoWord (0 : Fin 2) =
      OrientationData.BlockOrientation.opposite := by
  simp [oppositeSameTwoWord]

@[simp]
theorem oppositeSameTwoWord_one :
    oppositeSameTwoWord (1 : Fin 2) =
      OrientationData.BlockOrientation.same := by
  simp [oppositeSameTwoWord]

@[simp]
theorem oppositeOppositeTwoWord_zero :
    oppositeOppositeTwoWord (0 : Fin 2) =
      OrientationData.BlockOrientation.opposite := by
  simp [oppositeOppositeTwoWord]

@[simp]
theorem oppositeOppositeTwoWord_one :
    oppositeOppositeTwoWord (1 : Fin 2) =
      OrientationData.BlockOrientation.opposite := by
  simp [oppositeOppositeTwoWord]

/-- Exact equations left for the one-letter same-orientation word. -/
abbrev SameOneEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  ExactPeriodEquations O onePositive base sameOneWord

/-- Exact equations left for the one-letter opposite-orientation word. -/
abbrev OppositeOneEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  ExactPeriodEquations O onePositive base oppositeOneWord

/-- Exact equations left for an arbitrary two-letter word. -/
abbrev TwoWordEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (a b : Orientation) : Prop :=
  ExactPeriodEquations O twoPositive base (twoWord a b)

/-- Exact equations left for the two-letter same/same word. -/
abbrev SameSameTwoEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  ExactPeriodEquations O twoPositive base sameSameTwoWord

/-- Exact equations left for the two-letter same/opposite word. -/
abbrev SameOppositeTwoEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  ExactPeriodEquations O twoPositive base sameOppositeTwoWord

/-- Exact equations left for the two-letter opposite/same word. -/
abbrev OppositeSameTwoEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  ExactPeriodEquations O twoPositive base oppositeSameTwoWord

/-- Exact equations left for the two-letter opposite/opposite word. -/
abbrev OppositeOppositeTwoEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  ExactPeriodEquations O twoPositive base oppositeOppositeTwoWord

def sameOneCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : SameOneEquations O base) :
    PeriodEquationCandidate O base where
  length := 1
  positive_length := onePositive
  word := sameOneWord
  equations := equations

def oppositeOneCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : OppositeOneEquations O base) :
    PeriodEquationCandidate O base where
  length := 1
  positive_length := onePositive
  word := oppositeOneWord
  equations := equations

def twoWordCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (a b : Orientation)
    (equations : TwoWordEquations O base a b) :
    PeriodEquationCandidate O base where
  length := 2
  positive_length := twoPositive
  word := twoWord a b
  equations := equations

def sameSameTwoCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : SameSameTwoEquations O base) :
    PeriodEquationCandidate O base where
  length := 2
  positive_length := twoPositive
  word := sameSameTwoWord
  equations := equations

def sameOppositeTwoCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : SameOppositeTwoEquations O base) :
    PeriodEquationCandidate O base where
  length := 2
  positive_length := twoPositive
  word := sameOppositeTwoWord
  equations := equations

def oppositeSameTwoCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : OppositeSameTwoEquations O base) :
    PeriodEquationCandidate O base where
  length := 2
  positive_length := twoPositive
  word := oppositeSameTwoWord
  equations := equations

def oppositeOppositeTwoCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : OppositeOppositeTwoEquations O base) :
    PeriodEquationCandidate O base where
  length := 2
  positive_length := twoPositive
  word := oppositeOppositeTwoWord
  equations := equations

theorem sameOneGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : SameOneEquations O base) :
    PeriodInterface.GeneratedPeriodEquation
      O onePositive base sameOneWord.toFin :=
  (sameOneCandidate O base equations).generatedPeriodEquation

theorem oppositeOneGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : OppositeOneEquations O base) :
    PeriodInterface.GeneratedPeriodEquation
      O onePositive base oppositeOneWord.toFin :=
  (oppositeOneCandidate O base equations).generatedPeriodEquation

theorem twoWordGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (a b : Orientation)
    (equations : TwoWordEquations O base a b) :
    PeriodInterface.GeneratedPeriodEquation
      O twoPositive base (twoWord a b).toFin :=
  (twoWordCandidate O base a b equations).generatedPeriodEquation

theorem sameOppositeTwoGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equations : SameOppositeTwoEquations O base) :
    PeriodInterface.GeneratedPeriodEquation
      O twoPositive base sameOppositeTwoWord.toFin :=
  (sameOppositeTwoCandidate O base equations).generatedPeriodEquation

theorem noSameOneCandidate_of_contradictory
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hbad : ContradictoryEquations O onePositive base sameOneWord) :
    Not (SameOneEquations O base) :=
  noExactPeriodEquations_of_contradictory
    O onePositive base sameOneWord hbad

theorem noTwoWordCandidate_of_contradictory
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (a b : Orientation)
    (hbad : ContradictoryEquations O twoPositive base (twoWord a b)) :
    Not (TwoWordEquations O base a b) :=
  noExactPeriodEquations_of_contradictory
    O twoPositive base (twoWord a b) hbad

end SmallWords

end

end PeriodEquationConcreteSearch
end PachToth
end ErdosProblems1066
