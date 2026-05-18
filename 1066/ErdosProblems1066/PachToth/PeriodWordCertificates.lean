import ErdosProblems1066.PachToth.OrientationWord
import ErdosProblems1066.PachToth.PeriodSearchInterface

set_option autoImplicit false

/-!
# Period-word certificates

This module packages finite orientation words as `PeriodSearchInterface`
certificates.  The constructors keep the algebraic period equations as
explicit fields: a finite word supplies the indexing data, while a caller
supplies the exact `Fin 16` family of local-vertex equations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodWordCertificates

open FiniteGraph

noncomputable section

abbrev Orientation := OrientationWord.Orientation
abbrev R2 := Prod Real Real
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord

/-- Repackage an `OrientationWord.Word` as the finite word expected by the
period-search interface. -/
def finiteOrientationWordOfWord {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) : FiniteOrientationWord where
  length := k
  positive_length := hk
  letter := W.toFin

@[simp]
theorem finiteOrientationWordOfWord_length {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) :
    (finiteOrientationWordOfWord hk W).length = k :=
  rfl

@[simp]
theorem finiteOrientationWordOfWord_letter {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) (i : Fin k) :
    (finiteOrientationWordOfWord hk W).letter i = W i :=
  rfl

/-- Repackage `SearchData` as the finite word expected by the period-search
interface. -/
def finiteOrientationWordOfSearchData
    (D : OrientationWord.SearchData) : FiniteOrientationWord where
  length := D.k
  positive_length := D.hk
  letter := D.orientation

@[simp]
theorem finiteOrientationWordOfSearchData_length
    (D : OrientationWord.SearchData) :
    (finiteOrientationWordOfSearchData D).length = D.k :=
  rfl

@[simp]
theorem finiteOrientationWordOfSearchData_letter
    (D : OrientationWord.SearchData) (i : Fin D.k) :
    (finiteOrientationWordOfSearchData D).letter i = D.orientation i :=
  rfl

/-- Exact algebraic period-equation fields for an orientation word. -/
abbrev AlgebraicEquationsForWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k) : Prop :=
  forall i : Fin 16,
    PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
      (finiteOrientationWordOfWord hk W)
      (BlockPartition.localVertexEquivFin16.symm i)

/-- Exact algebraic period-equation fields for bundled search data. -/
abbrev AlgebraicEquationsForSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData) : Prop :=
  forall i : Fin 16,
    PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
      (finiteOrientationWordOfSearchData D)
      (BlockPartition.localVertexEquivFin16.symm i)

/-- Build the indexed algebraic certificate for an orientation word from exact
local-vertex equations. -/
def indexedAlgebraicCertificateOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate O base
      (finiteOrientationWordOfWord hk W) where
  equation := equation

/-- Build the indexed algebraic certificate for bundled search data from exact
local-vertex equations. -/
def indexedAlgebraicCertificateOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate O base
      (finiteOrientationWordOfSearchData D) where
  equation := equation

/-- A full period-search certificate built from an orientation word and exact
indexed algebraic equations. -/
def periodSearchCertificateOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := finiteOrientationWordOfWord hk W
  period := indexedAlgebraicCertificateOfWord O hk base W equation

/-- A full period-search certificate built from bundled search data and exact
indexed algebraic equations. -/
def periodSearchCertificateOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := finiteOrientationWordOfSearchData D
  period := indexedAlgebraicCertificateOfSearchData O base D equation

@[simp]
theorem periodSearchCertificateOfWord_word
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    (periodSearchCertificateOfWord O hk base W equation).word =
      finiteOrientationWordOfWord hk W :=
  rfl

@[simp]
theorem periodSearchCertificateOfSearchData_word
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    (periodSearchCertificateOfSearchData O base D equation).word =
      finiteOrientationWordOfSearchData D :=
  rfl

/-- The exact algebraic equations for a word imply the generated closure
equation for that word. -/
theorem generatedClosureEquationOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodInterface.GeneratedClosureEquation O hk base W.toFin :=
  (indexedAlgebraicCertificateOfWord O hk base W equation)
    |>.toGeneratedClosureEquation

/-- The exact algebraic equations for bundled search data imply the generated
closure equation for the stored orientation function. -/
theorem generatedClosureEquationOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodInterface.GeneratedClosureEquation O D.hk base D.orientation :=
  (indexedAlgebraicCertificateOfSearchData O base D equation)
    |>.toGeneratedClosureEquation

/-- The exact algebraic equations for a word imply the generated final-block
period equation for that word. -/
theorem generatedPeriodEquationOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    PeriodInterface.GeneratedPeriodEquation O hk base W.toFin :=
  (periodSearchCertificateOfWord O hk base W equation)
    |>.toGeneratedPeriodEquation

/-- The exact algebraic equations for bundled search data imply the generated
final-block period equation for the stored orientation function. -/
theorem generatedPeriodEquationOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    PeriodInterface.GeneratedPeriodEquation O D.hk base D.orientation :=
  (periodSearchCertificateOfSearchData O base D equation)
    |>.toGeneratedPeriodEquation

/-- The downstream generated-period hypothesis obtained from exact algebraic
equations for a word. -/
theorem generatedPeriodOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation : AlgebraicEquationsForWord O hk base W) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base W.toFin :=
  (periodSearchCertificateOfWord O hk base W equation)
    |>.toGeneratedPeriod

/-- The downstream generated-period hypothesis obtained from exact algebraic
equations for bundled search data. -/
theorem generatedPeriodOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation : AlgebraicEquationsForSearchData O base D) :
    GeneratedSeparationInterface.GeneratedPeriod O D.hk base D.orientation :=
  (periodSearchCertificateOfSearchData O base D equation)
    |>.toGeneratedPeriod

namespace Examples

def onePositive : 0 < 1 :=
  Nat.zero_lt_succ 0

def twoPositive : 0 < 2 :=
  Nat.zero_lt_succ 1

/-- The one-letter same-orientation word. -/
def sameOneWord : OrientationWord.Word 1 :=
  OrientationWord.Word.ofFin fun _ =>
    OrientationData.BlockOrientation.same

/-- Conditional certificate shape for the one-letter word. -/
def sameOnePeriodSearchCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation : AlgebraicEquationsForWord O onePositive base sameOneWord) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  periodSearchCertificateOfWord O onePositive base sameOneWord equation

/-- Conditional generated closure equation for the one-letter word. -/
theorem sameOneGeneratedClosureEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation : AlgebraicEquationsForWord O onePositive base sameOneWord) :
    PeriodInterface.GeneratedClosureEquation O onePositive base
      sameOneWord.toFin :=
  generatedClosureEquationOfWord O onePositive base sameOneWord equation

/-- Conditional generated final-block period equation for the one-letter
word. -/
theorem sameOneGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation : AlgebraicEquationsForWord O onePositive base sameOneWord) :
    PeriodInterface.GeneratedPeriodEquation O onePositive base
      sameOneWord.toFin :=
  generatedPeriodEquationOfWord O onePositive base sameOneWord equation

/-- The two-letter same/opposite word. -/
def sameOppositeTwoWord : OrientationWord.Word 2 :=
  OrientationWord.Word.ofFin fun i =>
    if i = (0 : Fin 2) then
      OrientationData.BlockOrientation.same
    else
      OrientationData.BlockOrientation.opposite

/-- Conditional certificate shape for the two-letter same/opposite word. -/
def sameOppositeTwoPeriodSearchCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      AlgebraicEquationsForWord O twoPositive base sameOppositeTwoWord) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  periodSearchCertificateOfWord O twoPositive base sameOppositeTwoWord equation

/-- Conditional generated closure equation for the two-letter same/opposite
word. -/
theorem sameOppositeTwoGeneratedClosureEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      AlgebraicEquationsForWord O twoPositive base sameOppositeTwoWord) :
    PeriodInterface.GeneratedClosureEquation O twoPositive base
      sameOppositeTwoWord.toFin :=
  generatedClosureEquationOfWord O twoPositive base sameOppositeTwoWord
    equation

/-- Conditional generated final-block period equation for the two-letter
same/opposite word. -/
theorem sameOppositeTwoGeneratedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      AlgebraicEquationsForWord O twoPositive base sameOppositeTwoWord) :
    PeriodInterface.GeneratedPeriodEquation O twoPositive base
      sameOppositeTwoWord.toFin :=
  generatedPeriodEquationOfWord O twoPositive base sameOppositeTwoWord
    equation

end Examples

end

end PeriodWordCertificates
end PachToth
end ErdosProblems1066
