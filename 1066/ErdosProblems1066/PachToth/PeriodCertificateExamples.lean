import ErdosProblems1066.PachToth.OrientationWord
import ErdosProblems1066.PachToth.PeriodSearchInterface

set_option autoImplicit false

/-!
# Period certificate examples

This module gives small, kernel-checked packaging examples for finite
orientation words.  The reusable constructors below do not treat an external
search as a proof: the exact algebraic equations are explicit Lean fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodCertificateExamples

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

/-- Build the period-search finite word directly from exact finite data. -/
def finiteOrientationWordOfFin {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> Orientation) : FiniteOrientationWord :=
  finiteOrientationWordOfWord hk (OrientationWord.Word.ofFin orientation)

@[simp]
theorem finiteOrientationWordOfFin_length {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> Orientation) :
    (finiteOrientationWordOfFin hk orientation).length = k :=
  rfl

@[simp]
theorem finiteOrientationWordOfFin_letter {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> Orientation) (i : Fin k) :
    (finiteOrientationWordOfFin hk orientation).letter i = orientation i :=
  rfl

/-- Repackage positive `OrientationWord.SearchData` as period-search input. -/
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

/-- An indexed algebraic period certificate from a finite orientation word and
exact vertex equations. -/
def indexedAlgebraicCertificateOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfWord hk W)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate O base
      (finiteOrientationWordOfWord hk W) where
  equation := equation

/-- An indexed generated-period certificate from a finite orientation word and
exact generated vertex equations. -/
def indexedGeneratedCertificateOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.GeneratedVertexPeriodEquation O base
          (finiteOrientationWordOfWord hk W)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.IndexedGeneratedPeriodCertificate O base
      (finiteOrientationWordOfWord hk W) where
  equation := equation

/-- A full finite period-search certificate from word data plus exact
algebraic equations. -/
def periodSearchCertificateOfWord
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfWord hk W)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := finiteOrientationWordOfWord hk W
  period := indexedAlgebraicCertificateOfWord O hk base W equation

/-- The same reusable constructor, starting from raw `Fin k` orientation data. -/
def periodSearchCertificateOfFin
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> Orientation)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfFin hk orientation)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := finiteOrientationWordOfFin hk orientation
  period := by
    exact
      indexedAlgebraicCertificateOfWord O hk base
        (OrientationWord.Word.ofFin orientation) equation

/-- A constructor for already bundled `OrientationWord.SearchData`. -/
def periodSearchCertificateOfSearchData
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (D : OrientationWord.SearchData)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfSearchData D)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := finiteOrientationWordOfSearchData D
  period := { equation := equation }

theorem periodSearchCertificateOfFin_closure
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> Orientation)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfFin hk orientation)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodInterface.GeneratedClosureEquation O hk base orientation :=
  (periodSearchCertificateOfFin O hk base orientation equation).period
    |>.toGeneratedClosureEquation

theorem periodSearchCertificateOfFin_period
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> Orientation)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfFin hk orientation)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodInterface.GeneratedPeriodEquation O hk base orientation :=
  (periodSearchCertificateOfFin O hk base orientation equation)
    |>.toGeneratedPeriodEquation

namespace Examples

def onePositive : 0 < 1 :=
  Nat.zero_lt_succ 0

def twoPositive : 0 < 2 :=
  Nat.zero_lt_succ 1

/-- The one-letter same-orientation word. -/
def sameOneWord : OrientationWord.Word 1 :=
  OrientationWord.Word.ofFin fun _ => OrientationData.BlockOrientation.same

/-- The one-letter same-orientation word as period-search input. -/
def sameOneFiniteWord : FiniteOrientationWord :=
  finiteOrientationWordOfWord onePositive sameOneWord

@[simp]
theorem sameOneFiniteWord_length :
    sameOneFiniteWord.length = 1 :=
  rfl

@[simp]
theorem sameOneFiniteWord_letter (i : Fin 1) :
    sameOneFiniteWord.letter i = OrientationData.BlockOrientation.same :=
  rfl

/-- The two-letter same/opposite word. -/
def sameOppositeTwoWord : OrientationWord.Word 2 :=
  OrientationWord.Word.ofFin fun i =>
    if i = (0 : Fin 2) then
      OrientationData.BlockOrientation.same
    else
      OrientationData.BlockOrientation.opposite

/-- The two-letter same/opposite word as period-search input. -/
def sameOppositeTwoFiniteWord : FiniteOrientationWord :=
  finiteOrientationWordOfWord twoPositive sameOppositeTwoWord

@[simp]
theorem sameOppositeTwoFiniteWord_length :
    sameOppositeTwoFiniteWord.length = 2 :=
  rfl

@[simp]
theorem sameOppositeTwoFiniteWord_zero :
    sameOppositeTwoFiniteWord.letter (0 : Fin 2) =
      OrientationData.BlockOrientation.same := by
  simp [sameOppositeTwoFiniteWord, sameOppositeTwoWord,
    finiteOrientationWordOfWord]

@[simp]
theorem sameOppositeTwoFiniteWord_one :
    sameOppositeTwoFiniteWord.letter (1 : Fin 2) =
      OrientationData.BlockOrientation.opposite := by
  simp [sameOppositeTwoFiniteWord, sameOppositeTwoWord,
    finiteOrientationWordOfWord]

/-- A small concrete certificate shape for the one-letter word.  The exact
period equations are supplied as fields, not inferred from a search. -/
def sameOnePeriodSearchCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          sameOneFiniteWord
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := sameOneFiniteWord
  period := { equation := equation }

/-- A small concrete certificate shape for the two-letter same/opposite word.
The equations remain exact Lean data supplied by the caller. -/
def sameOppositeTwoPeriodSearchCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          sameOppositeTwoFiniteWord
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := sameOppositeTwoFiniteWord
  period := { equation := equation }

end Examples

end

end PeriodCertificateExamples
end PachToth
end ErdosProblems1066
