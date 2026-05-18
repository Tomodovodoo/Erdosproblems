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

/-- A word certificate reduces to the downstream generated-period hypothesis
used by the separation interfaces. -/
theorem periodSearchCertificateOfWord_generatedPeriod
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfWord hk W)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base W.toFin :=
  (periodSearchCertificateOfWord O hk base W equation)
    |>.toGeneratedPeriod

/-- Raw `Fin k` orientation data with exact equations also reduces to the
downstream generated-period hypothesis. -/
theorem periodSearchCertificateOfFin_generatedPeriod
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> Orientation)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfFin hk orientation)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base orientation :=
  (periodSearchCertificateOfFin O hk base orientation equation)
    |>.toGeneratedPeriod

/-- A selected transition fixes the chosen base block pointwise.  This is the
exact narrowed condition under which fixed-letter period examples close
without any external search. -/
abbrev TransitionFixesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (orientation : Orientation) : Prop :=
  (O.transitionFor orientation).placeNext base = base

def onePositiveLength : 0 < 1 :=
  Nat.zero_lt_succ 0

def twoPositiveLength : 0 < 2 :=
  Nat.zero_lt_succ 1

/-- A two-letter orientation word with named first and second letters. -/
def twoLetterWord (first second : Orientation) : OrientationWord.Word 2 :=
  OrientationWord.Word.ofFin fun i =>
    if i = (0 : Fin 2) then first else second

@[simp]
theorem twoLetterWord_zero (first second : Orientation) :
    twoLetterWord first second (0 : Fin 2) = first := by
  simp [twoLetterWord]

@[simp]
theorem twoLetterWord_one (first second : Orientation) :
    twoLetterWord first second (1 : Fin 2) = second := by
  simp [twoLetterWord]

/-- The genuinely two-step closure condition for a two-letter word: the
second selected transition returns the block obtained after the first
selected transition to the original base block.  This is not the `k = 1`
base-fixing condition for either letter. -/
abbrev TwoStepTransitionClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (first second : Orientation) : Prop :=
  (O.transitionFor second).placeNext
    ((O.transitionFor first).placeNext base) = base

/-- The first generated block of a two-letter word is obtained by applying
the first selected transition to the base block. -/
theorem generatedBlock_twoLetterWord_one
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (first second : Orientation) :
    GeneratedClosedChain.generatedBlock O twoPositiveLength base
      (twoLetterWord first second).toFin 1 =
        (O.transitionFor first).placeNext base := by
  funext v
  simp [GeneratedClosedChain.generatedBlock,
    GeneratedClosedChain.orientationAt, twoLetterWord]

/-- A two-step composite closure equation gives the generated final-block
period equation for the corresponding two-letter word. -/
theorem generatedPeriodEquation_twoLetterWord_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (first second : Orientation)
    (hclose : TwoStepTransitionClosesBase O base first second) :
    PeriodInterface.GeneratedPeriodEquation O twoPositiveLength base
      (twoLetterWord first second).toFin := by
  funext v
  simpa [PeriodInterface.GeneratedPeriodEquation,
    GeneratedClosedChain.generatedBlock,
    GeneratedClosedChain.orientationAt, twoLetterWord,
    TwoStepTransitionClosesBase] using congrFun hclose v

/-- A two-step composite closure equation also gives the downstream
`GeneratedPeriod` hypothesis used by generated separation interfaces. -/
theorem generatedPeriod_twoLetterWord_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (first second : Orientation)
    (hclose : TwoStepTransitionClosesBase O base first second) :
    GeneratedSeparationInterface.GeneratedPeriod O twoPositiveLength base
      (twoLetterWord first second).toFin := by
  exact
    generatedPeriodEquation_twoLetterWord_of_twoStepClosesBase
      O base first second hclose

/-- The same/opposite two-letter word closes from a composite transition
equation, with no requirement that the same transition fixes the base block
by itself. -/
theorem generatedPeriodEquation_sameOppositeTwo_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.same
        OrientationData.BlockOrientation.opposite) :
    PeriodInterface.GeneratedPeriodEquation O twoPositiveLength base
      (twoLetterWord OrientationData.BlockOrientation.same
        OrientationData.BlockOrientation.opposite).toFin :=
  generatedPeriodEquation_twoLetterWord_of_twoStepClosesBase
    O base OrientationData.BlockOrientation.same
      OrientationData.BlockOrientation.opposite hclose

/-- The opposite/same two-letter word is the reversed concrete composite
closure fact. -/
theorem generatedPeriodEquation_oppositeSameTwo_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.opposite
        OrientationData.BlockOrientation.same) :
    PeriodInterface.GeneratedPeriodEquation O twoPositiveLength base
      (twoLetterWord OrientationData.BlockOrientation.opposite
        OrientationData.BlockOrientation.same).toFin :=
  generatedPeriodEquation_twoLetterWord_of_twoStepClosesBase
    O base OrientationData.BlockOrientation.opposite
      OrientationData.BlockOrientation.same hclose

/-- If each letter used by a finite word fixes the base block, every generated
prefix up to the word length is the base block. -/
theorem generatedBlock_eq_base_of_letters_fix_base
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> Orientation)
    (hfix : forall i : Fin k, TransitionFixesBase O base (orientation i))
    {n : Nat} (hn : n <= k) :
    GeneratedClosedChain.generatedBlock O hk base orientation n = base := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hn_lt : n < k := Nat.lt_of_succ_le hn
      have hprev :
          GeneratedClosedChain.generatedBlock O hk base orientation n =
            base :=
        ih (Nat.le_of_succ_le hn)
      funext v
      calc
        GeneratedClosedChain.generatedBlock O hk base orientation (n + 1) v =
            (O.transitionFor
              (GeneratedClosedChain.orientationAt hk orientation n)).placeNext
              (GeneratedClosedChain.generatedBlock O hk base orientation n) v := by
              rfl
        _ =
            (O.transitionFor (orientation ⟨n, hn_lt⟩)).placeNext base v := by
              rw [GeneratedClosedChain.orientationAt_of_lt hk orientation hn_lt,
                hprev]
        _ = base v := by
              exact congrFun (hfix ⟨n, hn_lt⟩) v

/-- Base-fixing letters give the generated final-block period equation. -/
theorem generatedPeriodEquation_of_letters_fix_base
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> Orientation)
    (hfix : forall i : Fin k, TransitionFixesBase O base (orientation i)) :
    PeriodInterface.GeneratedPeriodEquation O hk base orientation :=
  generatedBlock_eq_base_of_letters_fix_base O hk base orientation hfix
    (Nat.le_refl k)

/-- Reindex a generated final-block period equation as the exact algebraic
`Fin 16` period-equation family expected by finite search certificates. -/
theorem indexedAlgebraicEquations_of_generatedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (W : FiniteOrientationWord)
    (hperiod :
      PeriodInterface.GeneratedPeriodEquation O W.positive_length base
        W.letter) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base W
        (BlockPartition.localVertexEquivFin16.symm i) := by
  intro i
  exact
    congrFun
      (PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
        O W.positive_length base W.letter hperiod)
      (BlockPartition.localVertexEquivFin16.symm i)

/-- Reindex a two-step generated period equation as the exact algebraic
`Fin 16` equation family expected by finite-search certificates. -/
theorem algebraicEquationsForTwoLetterWord_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (first second : Orientation)
    (hclose : TwoStepTransitionClosesBase O base first second) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        (finiteOrientationWordOfWord twoPositiveLength
          (twoLetterWord first second))
        (BlockPartition.localVertexEquivFin16.symm i) :=
  indexedAlgebraicEquations_of_generatedPeriodEquation O base
    (finiteOrientationWordOfWord twoPositiveLength
      (twoLetterWord first second))
    (generatedPeriodEquation_twoLetterWord_of_twoStepClosesBase
      O base first second hclose)

/-- Base-fixing letters give the exact algebraic fields for an arbitrary
finite orientation word. -/
theorem algebraicEquationsForWord_of_letters_fix_base
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word k)
    (hfix : forall i : Fin k, TransitionFixesBase O base (W i)) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        (finiteOrientationWordOfWord hk W)
        (BlockPartition.localVertexEquivFin16.symm i) :=
  indexedAlgebraicEquations_of_generatedPeriodEquation O base
    (finiteOrientationWordOfWord hk W)
    (generatedPeriodEquation_of_letters_fix_base O hk base W.toFin hfix)

/-- A word whose letters are all the same orientation. -/
def constantWord (k : Nat) (orientation : Orientation) :
    OrientationWord.Word k :=
  OrientationWord.Word.ofFin fun _ => orientation

@[simp]
theorem constantWord_apply
    (k : Nat) (orientation : Orientation) (i : Fin k) :
    constantWord k orientation i = orientation :=
  rfl

/-- The all-same word at length `k`. -/
def sameWord (k : Nat) : OrientationWord.Word k :=
  constantWord k OrientationData.BlockOrientation.same

/-- The all-opposite word at length `k`. -/
def oppositeWord (k : Nat) : OrientationWord.Word k :=
  constantWord k OrientationData.BlockOrientation.opposite

@[simp]
theorem sameWord_apply (k : Nat) (i : Fin k) :
    sameWord k i = OrientationData.BlockOrientation.same :=
  rfl

@[simp]
theorem oppositeWord_apply (k : Nat) (i : Fin k) :
    oppositeWord k i = OrientationData.BlockOrientation.opposite :=
  rfl

/-- All-positive word family using the same-orientation letter at every
positive length.  Its equation theorem below is directly field-compatible
with all-positive period-search data. -/
def allPositiveSameWord (k : Nat) (_hk : 0 < k) :
    OrientationWord.Word k :=
  sameWord k

/-- All-positive word family using the opposite-orientation letter at every
positive length. -/
def allPositiveOppositeWord (k : Nat) (_hk : 0 < k) :
    OrientationWord.Word k :=
  oppositeWord k

/-- The all-same family supplies exact period equations at every positive
length once the same transition fixes the base block. -/
theorem allPositiveSameEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hfix : TransitionFixesBase O base OrientationData.BlockOrientation.same)
    (k : Nat) (hk : 0 < k) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        (finiteOrientationWordOfWord hk (allPositiveSameWord k hk))
        (BlockPartition.localVertexEquivFin16.symm i) :=
  algebraicEquationsForWord_of_letters_fix_base O hk base
    (allPositiveSameWord k hk) (by intro i; simpa using hfix)

/-- The all-opposite family supplies exact period equations at every positive
length once the opposite transition fixes the base block. -/
theorem allPositiveOppositeEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hfix :
      TransitionFixesBase O base OrientationData.BlockOrientation.opposite)
    (k : Nat) (hk : 0 < k) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        (finiteOrientationWordOfWord hk (allPositiveOppositeWord k hk))
        (BlockPartition.localVertexEquivFin16.symm i) :=
  algebraicEquationsForWord_of_letters_fix_base O hk base
    (allPositiveOppositeWord k hk) (by intro i; simpa using hfix)

/-- Thresholded/eventual same-word family.  The threshold proof is retained in
the argument list so this can be used directly in eventual certificate fields. -/
def eventualSameWord (_K0 : Nat)
    (k : Nat) (_hK : _K0 <= k) (_hk : 0 < k) :
    OrientationWord.Word k :=
  sameWord k

/-- Thresholded/eventual opposite-word family. -/
def eventualOppositeWord (_K0 : Nat)
    (k : Nat) (_hK : _K0 <= k) (_hk : 0 < k) :
    OrientationWord.Word k :=
  oppositeWord k

/-- Exact period equations for the thresholded all-same route under the same
base-fixing condition. -/
theorem eventualSameEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hfix : TransitionFixesBase O base OrientationData.BlockOrientation.same)
    (K0 k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        (finiteOrientationWordOfWord hk (eventualSameWord K0 k hK hk))
        (BlockPartition.localVertexEquivFin16.symm i) :=
  allPositiveSameEquations O base hfix k hk

/-- Exact period equations for the thresholded all-opposite route under the
opposite base-fixing condition. -/
theorem eventualOppositeEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hfix :
      TransitionFixesBase O base OrientationData.BlockOrientation.opposite)
    (K0 k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        (finiteOrientationWordOfWord hk (eventualOppositeWord K0 k hK hk))
        (BlockPartition.localVertexEquivFin16.symm i) :=
  allPositiveOppositeEquations O base hfix k hk

/-- Any one-letter exact algebraic period certificate forces the selected
transition to fix the base block.  This is the checked obstruction/narrowing
for all-positive searches: the `k = 1` member cannot avoid a base-fixing
transition. -/
theorem oneLetterEquations_force_transitionFixesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (W : OrientationWord.Word 1)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfWord onePositiveLength W)
          (BlockPartition.localVertexEquivFin16.symm i)) :
    TransitionFixesBase O base (W (0 : Fin 1)) := by
  funext v
  simpa [TransitionFixesBase,
    PeriodSearchInterface.AlgebraicVertexPeriodEquation,
    PeriodSearchInterface.FiniteOrientationWord.iteratedTransitionBlock,
    PeriodSearchInterface.FiniteOrientationWord.generatedPoint,
    GeneratedClosedChain.generatedPoint,
    GeneratedClosedChain.generatedBlock,
    finiteOrientationWordOfWord] using
      equation (BlockPartition.localVertexEquivFin16 v)

/-- Any all-positive period-equation family must have a base-fixing transition
at its length-one member. -/
theorem allPositiveEquations_force_lengthOneFixesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equation :
      forall (k : Nat) (hk : 0 < k) (i : Fin 16),
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfWord hk (word k hk))
          (BlockPartition.localVertexEquivFin16.symm i)) :
    TransitionFixesBase O base (word 1 onePositiveLength (0 : Fin 1)) :=
  oneLetterEquations_force_transitionFixesBase O base
    (word 1 onePositiveLength) (equation 1 onePositiveLength)

/-- Since the current orientation alphabet is exactly same/opposite, any
all-positive period-equation family forces either the same or the opposite
transition to fix the base block at the `k = 1` member. -/
theorem allPositiveEquations_force_same_or_opposite_fixesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equation :
      forall (k : Nat) (hk : 0 < k) (i : Fin 16),
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          (finiteOrientationWordOfWord hk (word k hk))
          (BlockPartition.localVertexEquivFin16.symm i)) :
    (word 1 onePositiveLength (0 : Fin 1) =
        OrientationData.BlockOrientation.same /\
      TransitionFixesBase O base OrientationData.BlockOrientation.same) \/
    (word 1 onePositiveLength (0 : Fin 1) =
        OrientationData.BlockOrientation.opposite /\
      TransitionFixesBase O base OrientationData.BlockOrientation.opposite) := by
  have hfix :=
    allPositiveEquations_force_lengthOneFixesBase O base word equation
  rcases Figure2Certificate.blockOrientation_eq_same_or_opposite
      (word 1 onePositiveLength (0 : Fin 1)) with hsame | hopposite
  · left
    exact ⟨hsame, by simpa [hsame] using hfix⟩
  · right
    exact ⟨hopposite, by simpa [hopposite] using hfix⟩

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

/-- The same/opposite example is the reusable two-letter word specialized to
the two concrete orientation labels. -/
@[simp]
theorem sameOppositeTwoWord_eq_twoLetterWord :
    sameOppositeTwoWord =
      twoLetterWord OrientationData.BlockOrientation.same
        OrientationData.BlockOrientation.opposite :=
  rfl

/-- The two-letter opposite/same word. -/
def oppositeSameTwoWord : OrientationWord.Word 2 :=
  twoLetterWord OrientationData.BlockOrientation.opposite
    OrientationData.BlockOrientation.same

/-- The two-letter opposite/same word as period-search input. -/
def oppositeSameTwoFiniteWord : FiniteOrientationWord :=
  finiteOrientationWordOfWord twoPositive oppositeSameTwoWord

@[simp]
theorem oppositeSameTwoFiniteWord_length :
    oppositeSameTwoFiniteWord.length = 2 :=
  rfl

@[simp]
theorem oppositeSameTwoFiniteWord_zero :
    oppositeSameTwoFiniteWord.letter (0 : Fin 2) =
      OrientationData.BlockOrientation.opposite := by
  simp [oppositeSameTwoFiniteWord, oppositeSameTwoWord,
    finiteOrientationWordOfWord]

@[simp]
theorem oppositeSameTwoFiniteWord_one :
    oppositeSameTwoFiniteWord.letter (1 : Fin 2) =
      OrientationData.BlockOrientation.same := by
  simp [oppositeSameTwoFiniteWord, oppositeSameTwoWord,
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

/-- A small concrete certificate shape for the two-letter opposite/same word. -/
def oppositeSameTwoPeriodSearchCertificate
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          oppositeSameTwoFiniteWord
          (BlockPartition.localVertexEquivFin16.symm i)) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := oppositeSameTwoFiniteWord
  period := { equation := equation }

/-- The two-letter same/opposite certificate projects to the downstream
generated-period declaration used by the generated separation interface. -/
theorem sameOppositeTwoGeneratedPeriod
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          sameOppositeTwoFiniteWord
          (BlockPartition.localVertexEquivFin16.symm i)) :
    GeneratedSeparationInterface.GeneratedPeriod O twoPositive base
      sameOppositeTwoWord.toFin := by
  simpa [sameOppositeTwoFiniteWord] using
    (sameOppositeTwoPeriodSearchCertificate O base equation)
      |>.toGeneratedPeriod

/-- The two-letter opposite/same certificate projects to the downstream
generated-period declaration used by the generated separation interface. -/
theorem oppositeSameTwoGeneratedPeriod
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (equation :
      forall i : Fin 16,
        PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
          oppositeSameTwoFiniteWord
          (BlockPartition.localVertexEquivFin16.symm i)) :
    GeneratedSeparationInterface.GeneratedPeriod O twoPositive base
      oppositeSameTwoWord.toFin := by
  simpa [oppositeSameTwoFiniteWord] using
    (oppositeSameTwoPeriodSearchCertificate O base equation)
      |>.toGeneratedPeriod

/-- A same/opposite composite closure equation supplies the exact finite-word
algebraic equations for the concrete two-letter example. -/
theorem sameOppositeTwoAlgebraicEquations_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.same
        OrientationData.BlockOrientation.opposite) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        sameOppositeTwoFiniteWord
        (BlockPartition.localVertexEquivFin16.symm i) := by
  intro i
  simpa [sameOppositeTwoFiniteWord, sameOppositeTwoWord] using
    algebraicEquationsForTwoLetterWord_of_twoStepClosesBase O base
      OrientationData.BlockOrientation.same
      OrientationData.BlockOrientation.opposite hclose i

/-- An opposite/same composite closure equation supplies the exact finite-word
algebraic equations for the reversed concrete two-letter example. -/
theorem oppositeSameTwoAlgebraicEquations_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.opposite
        OrientationData.BlockOrientation.same) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        oppositeSameTwoFiniteWord
        (BlockPartition.localVertexEquivFin16.symm i) := by
  intro i
  simpa [oppositeSameTwoFiniteWord, oppositeSameTwoWord] using
    algebraicEquationsForTwoLetterWord_of_twoStepClosesBase O base
      OrientationData.BlockOrientation.opposite
      OrientationData.BlockOrientation.same hclose i

/-- Package the same/opposite composite closure equation as a concrete
period-search certificate. -/
def sameOppositeTwoPeriodSearchCertificate_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.same
        OrientationData.BlockOrientation.opposite) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  sameOppositeTwoPeriodSearchCertificate O base
    (sameOppositeTwoAlgebraicEquations_of_twoStepClosesBase O base hclose)

/-- Package the opposite/same composite closure equation as a concrete
period-search certificate. -/
def oppositeSameTwoPeriodSearchCertificate_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.opposite
        OrientationData.BlockOrientation.same) :
    PeriodSearchInterface.PeriodSearchCertificate O base :=
  oppositeSameTwoPeriodSearchCertificate O base
    (oppositeSameTwoAlgebraicEquations_of_twoStepClosesBase O base hclose)

/-- The same/opposite composite closure route reduced through the existing
certificate-to-generated-period declaration. -/
theorem sameOppositeTwoGeneratedPeriod_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.same
        OrientationData.BlockOrientation.opposite) :
    GeneratedSeparationInterface.GeneratedPeriod O twoPositive base
      sameOppositeTwoWord.toFin :=
  sameOppositeTwoGeneratedPeriod O base
    (sameOppositeTwoAlgebraicEquations_of_twoStepClosesBase O base hclose)

/-- The opposite/same composite closure route reduced through the existing
certificate-to-generated-period declaration. -/
theorem oppositeSameTwoGeneratedPeriod_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose :
      TwoStepTransitionClosesBase O base
        OrientationData.BlockOrientation.opposite
        OrientationData.BlockOrientation.same) :
    GeneratedSeparationInterface.GeneratedPeriod O twoPositive base
      oppositeSameTwoWord.toFin :=
  oppositeSameTwoGeneratedPeriod O base
    (oppositeSameTwoAlgebraicEquations_of_twoStepClosesBase O base hclose)

end Examples

end

end PeriodCertificateExamples
end PachToth
end ErdosProblems1066
