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

/-- The raw orientation function carried by the candidate. -/
def orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    Fin C.length -> Orientation :=
  C.word.toFin

@[simp]
theorem orientation_apply
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) (i : Fin C.length) :
    C.orientation i = C.word i :=
  rfl

/-- Project one indexed algebraic vertex equation out of the explicit
`Fin 16` equation family stored by the candidate. -/
theorem indexedEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) (i : Fin 16) :
    PeriodSearchInterface.AlgebraicVertexPeriodEquation
      O base C.finiteWord
      (BlockPartition.localVertexEquivFin16.symm i) :=
  C.equations i

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

@[simp]
theorem toPeriodSearchCertificate_word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    C.toPeriodSearchCertificate.word = C.finiteWord :=
  rfl

/-- Reindex the exact `Fin 16` equations to pointwise algebraic equations at
all local vertices. -/
def algebraicPeriodCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    PeriodSearchInterface.AlgebraicPeriodCertificate O base C.finiteWord :=
  C.indexedAlgebraicCertificate.toPointwise

/-- Project the algebraic period equation at an arbitrary local vertex. -/
theorem algebraicVertexEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) (v : LocalVertex) :
    PeriodSearchInterface.AlgebraicVertexPeriodEquation
      O base C.finiteWord v :=
  C.algebraicPeriodCertificate.equation v

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

/-- The exact algebraic equations imply the downstream generated-period
hypothesis used by separation interfaces. -/
def generatedPeriod
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationCandidate O base) :
    GeneratedSeparationInterface.GeneratedPeriod
      O C.positive_length base C.orientation :=
  PeriodWordCertificates.generatedPeriodOfWord
    O C.positive_length base C.word C.equations

end PeriodEquationCandidate

/-- A period-equation candidate at a fixed positive length.  This is the
length-indexed form useful when assembling a family indexed by `k`. -/
structure FixedPeriodEquationCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (k : Nat) (hk : 0 < k) where
  word : OrientationWord.Word k
  equations : ExactPeriodEquations O hk base word

namespace FixedPeriodEquationCandidate

/-- The raw orientation function carried by a fixed-length candidate. -/
def orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    Fin k -> Orientation :=
  C.word.toFin

@[simp]
theorem orientation_apply
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) (i : Fin k) :
    C.orientation i = C.word i :=
  rfl

/-- The finite orientation word consumed by the period-search interface. -/
def finiteWord
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord hk C.word

@[simp]
theorem finiteWord_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    C.finiteWord.length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) (i : Fin k) :
    C.finiteWord.letter i = C.word i :=
  rfl

/-- Project one indexed algebraic vertex equation from a fixed-length
candidate. -/
theorem indexedEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) (i : Fin 16) :
    PeriodSearchInterface.AlgebraicVertexPeriodEquation
      O base C.finiteWord
      (BlockPartition.localVertexEquivFin16.symm i) :=
  C.equations i

/-- Repackage the explicit equations as an indexed algebraic certificate. -/
def indexedAlgebraicCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O base C.finiteWord :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    O hk base C.word C.equations

/-- Forget the fixed-length wrapper to the existing length-carrying candidate
record. -/
def toPeriodEquationCandidate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    PeriodEquationCandidate O base where
  length := k
  positive_length := hk
  word := C.word
  equations := C.equations

@[simp]
theorem toPeriodEquationCandidate_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    C.toPeriodEquationCandidate.length = k :=
  rfl

@[simp]
theorem toPeriodEquationCandidate_word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    C.toPeriodEquationCandidate.word = C.word :=
  rfl

/-- Repackage a fixed-length candidate as a full period-search certificate. -/
def toPeriodSearchCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  C.toPeriodEquationCandidate.toPeriodSearchCertificate

@[simp]
theorem toPeriodSearchCertificate_word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    C.toPeriodSearchCertificate.word = C.finiteWord :=
  rfl

/-- Reindex the fixed candidate to pointwise algebraic equations. -/
def algebraicPeriodCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    PeriodSearchInterface.AlgebraicPeriodCertificate O base C.finiteWord :=
  C.indexedAlgebraicCertificate.toPointwise

/-- Project the algebraic period equation at an arbitrary local vertex. -/
theorem algebraicVertexEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) (v : LocalVertex) :
    PeriodSearchInterface.AlgebraicVertexPeriodEquation
      O base C.finiteWord v :=
  C.algebraicPeriodCertificate.equation v

/-- The generated closure equation obtained from the fixed candidate's exact
`Fin 16` equations. -/
def generatedClosureEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    PeriodInterface.GeneratedClosureEquation O hk base C.orientation :=
  PeriodWordCertificates.generatedClosureEquationOfWord
    O hk base C.word C.equations

/-- The generated final-block period equation obtained from the fixed
candidate's exact `Fin 16` equations. -/
def generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    PeriodInterface.GeneratedPeriodEquation O hk base C.orientation :=
  PeriodWordCertificates.generatedPeriodEquationOfWord
    O hk base C.word C.equations

/-- The downstream generated-period hypothesis obtained from the fixed
candidate's exact `Fin 16` equations. -/
def generatedPeriod
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C : FixedPeriodEquationCandidate O base k hk) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base C.orientation :=
  PeriodWordCertificates.generatedPeriodOfWord
    O hk base C.word C.equations

end FixedPeriodEquationCandidate

/-- A period-equation candidate family over all positive lengths.  Each
member is still just an explicit orientation word plus its exact `Fin 16`
algebraic period equations. -/
structure PeriodEquationCandidateFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2) where
  candidate :
    forall (k : Nat) (hk : 0 < k),
      FixedPeriodEquationCandidate O base k hk

namespace PeriodEquationCandidateFamily

/-- Assemble a candidate family directly from words and exact indexed
equations. -/
def ofWordEquations
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        ExactPeriodEquations O hk base (word k hk)) :
    PeriodEquationCandidateFamily O base where
  candidate := fun k hk =>
    { word := word k hk
      equations := equations k hk }

def word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    OrientationWord.Word k :=
  (F.candidate k hk).word

@[simp]
theorem ofWordEquations_word
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        ExactPeriodEquations O hk base (word k hk))
    (k : Nat) (hk : 0 < k) :
    (ofWordEquations word equations).word k hk = word k hk :=
  rfl

def orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

def equations
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    ExactPeriodEquations O hk base (F.word k hk) :=
  (F.candidate k hk).equations

def finiteWord
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    FiniteOrientationWord :=
  (F.candidate k hk).finiteWord

@[simp]
theorem finiteWord_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    (F.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hk).letter i = F.word k hk i :=
  rfl

def indexedAlgebraicCertificate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O base (F.finiteWord k hk) :=
  (F.candidate k hk).indexedAlgebraicCertificate

def toPeriodEquationCandidate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationCandidate O base :=
  (F.candidate k hk).toPeriodEquationCandidate

def generatedClosureEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      O hk base (F.orientation k hk) :=
  (F.candidate k hk).generatedClosureEquation

def generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      O hk base (F.orientation k hk) :=
  (F.candidate k hk).generatedPeriodEquation

def generatedPeriod
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      O hk base (F.orientation k hk) :=
  (F.candidate k hk).generatedPeriod

end PeriodEquationCandidateFamily

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

/-- The currently explicit small period-equation candidates. -/
inductive CandidateTag where
  | sameOne
  | oppositeOne
  | sameSameTwo
  | sameOppositeTwo
  | oppositeSameTwo
  | oppositeOppositeTwo
  deriving DecidableEq, Repr

namespace CandidateTag

/-- The finite list of currently explicit small candidate tags. -/
def all : List CandidateTag :=
  [sameOne, oppositeOne, sameSameTwo, sameOppositeTwo,
    oppositeSameTwo, oppositeOppositeTwo]

theorem mem_all (tag : CandidateTag) :
    tag ∈ all := by
  cases tag <;> simp [all]

/-- Length of the word represented by a small candidate tag. -/
def length : CandidateTag -> Nat
  | sameOne => 1
  | oppositeOne => 1
  | sameSameTwo => 2
  | sameOppositeTwo => 2
  | oppositeSameTwo => 2
  | oppositeOppositeTwo => 2

/-- Positivity witness for the word represented by a small candidate tag. -/
def positiveLength : (tag : CandidateTag) -> 0 < tag.length
  | sameOne => onePositive
  | oppositeOne => onePositive
  | sameSameTwo => twoPositive
  | sameOppositeTwo => twoPositive
  | oppositeSameTwo => twoPositive
  | oppositeOppositeTwo => twoPositive

/-- The orientation word represented by a small candidate tag. -/
def word : (tag : CandidateTag) -> OrientationWord.Word tag.length
  | sameOne => sameOneWord
  | oppositeOne => oppositeOneWord
  | sameSameTwo => sameSameTwoWord
  | sameOppositeTwo => sameOppositeTwoWord
  | oppositeSameTwo => oppositeSameTwoWord
  | oppositeOppositeTwo => oppositeOppositeTwoWord

/-- Exact equations needed by the small candidate represented by a tag. -/
abbrev Equations
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag) : Prop :=
  ExactPeriodEquations O tag.positiveLength base tag.word

/-- Build the fixed-length candidate represented by a tag from its exact
indexed period equations. -/
def fixedCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    FixedPeriodEquationCandidate O base tag.length tag.positiveLength where
  word := tag.word
  equations := equations

/-- Build the length-carrying candidate represented by a tag from its exact
indexed period equations. -/
def candidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    PeriodEquationCandidate O base where
  length := tag.length
  positive_length := tag.positiveLength
  word := tag.word
  equations := equations

@[simp]
theorem candidate_length
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    (candidate O base tag equations).length = tag.length :=
  rfl

@[simp]
theorem candidate_word
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    (candidate O base tag equations).word = tag.word :=
  rfl

/-- The indexed algebraic certificate projected from a tagged small
candidate. -/
def indexedAlgebraicCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O base (tag.fixedCandidate O base equations).finiteWord :=
  (tag.fixedCandidate O base equations).indexedAlgebraicCertificate

/-- Generated closure projected from a tagged small candidate. -/
def generatedClosureEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    PeriodInterface.GeneratedClosureEquation
      O tag.positiveLength base tag.word.toFin :=
  (tag.candidate O base equations).generatedClosureEquation

/-- Generated final-block period projected from a tagged small candidate. -/
def generatedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    PeriodInterface.GeneratedPeriodEquation
      O tag.positiveLength base tag.word.toFin :=
  (tag.candidate O base equations).generatedPeriodEquation

/-- Downstream generated-period hypothesis projected from a tagged small
candidate. -/
def generatedPeriod
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (tag : CandidateTag)
    (equations : Equations O base tag) :
    GeneratedSeparationInterface.GeneratedPeriod
      O tag.positiveLength base tag.word.toFin :=
  (tag.candidate O base equations).generatedPeriod

end CandidateTag

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
