import ErdosProblems1066.PachToth.BaseTransitionRealization
import ErdosProblems1066.PachToth.GeneratedPeriodClosure
import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.PeriodEquationConcreteSearch

set_option autoImplicit false

/-!
# Concrete period-word search candidate

This module records the first nontrivial orientation-word candidate from the
existing period examples: the two-letter same/opposite word.  The useful fact
below is not a facade over a hidden finite-search assumption.  It reduces the
generated final-block period equation to the actual two-step transition
closure equation, then packages that equation through the existing generated
period and finite-period-certificate interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcretePeriodWordSearch

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev Orientation := OrientationData.BlockOrientation
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord

abbrev same : Orientation :=
  OrientationData.BlockOrientation.same

abbrev opposite : Orientation :=
  OrientationData.BlockOrientation.opposite

/-- The concrete nonconstant length-two word selected from the existing
period examples. -/
def candidateWord : OrientationWord.Word 2 :=
  PeriodCertificateExamples.Examples.sameOppositeTwoWord

/-- The same candidate as period-search input. -/
def candidateFiniteWord : FiniteOrientationWord :=
  PeriodCertificateExamples.Examples.sameOppositeTwoFiniteWord

/-- The corresponding small-word search tag. -/
def candidateTag : PeriodEquationConcreteSearch.SmallWords.CandidateTag :=
  PeriodEquationConcreteSearch.SmallWords.CandidateTag.sameOppositeTwo

@[simp]
theorem candidateWord_zero :
    candidateWord (0 : Fin 2) = same := by
  simp [candidateWord, same]

@[simp]
theorem candidateWord_one :
    candidateWord (1 : Fin 2) = opposite := by
  simp [candidateWord, opposite]

/-- The selected word is genuinely nonconstant. -/
theorem candidateWord_nonconstant :
    Ne (candidateWord (0 : Fin 2)) (candidateWord (1 : Fin 2)) := by
  simp

@[simp]
theorem candidateWord_eq_twoLetterWord :
    candidateWord =
      PeriodCertificateExamples.twoLetterWord same opposite := by
  simp [candidateWord, same, opposite,
    PeriodCertificateExamples.Examples.sameOppositeTwoWord_eq_twoLetterWord]

@[simp]
theorem candidateFiniteWord_length :
    candidateFiniteWord.length = 2 := by
  simp [candidateFiniteWord]

@[simp]
theorem candidateFiniteWord_zero :
    candidateFiniteWord.letter (0 : Fin 2) = same := by
  simp [candidateFiniteWord, same]

@[simp]
theorem candidateFiniteWord_one :
    candidateFiniteWord.letter (1 : Fin 2) = opposite := by
  simp [candidateFiniteWord, opposite]

/-- The actual closure equation for the selected two-letter candidate. -/
abbrev CandidateClosureEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2) : Prop :=
  PeriodCertificateExamples.TwoStepTransitionClosesBase O base same opposite

/-- The same closure equation specialized to the checked exact Figure 2 base
block. -/
abbrev ExactBaseCandidateClosureEquation
    (O : TransitionObligations) : Prop :=
  CandidateClosureEquation O BaseTransitionRealization.exactBase

/-- After one letter, the generated block is the same-transition image of the
base block. -/
theorem candidateGeneratedBlock_one
    (O : TransitionObligations)
    (base : LocalVertex -> R2) :
    GeneratedClosedChain.generatedBlock O
      PeriodCertificateExamples.twoPositiveLength base
      candidateWord.toFin 1 =
        (O.transitionFor same).placeNext base := by
  simpa [candidateWord, same, opposite] using
    PeriodCertificateExamples.generatedBlock_twoLetterWord_one
      O base same opposite

/-- After the two letters, the generated final block is exactly the
opposite-after-same composite transition. -/
theorem candidateGeneratedBlock_two
    (O : TransitionObligations)
    (base : LocalVertex -> R2) :
    GeneratedClosedChain.generatedBlock O
      PeriodCertificateExamples.twoPositiveLength base
      candidateWord.toFin 2 =
        (O.transitionFor opposite).placeNext
          ((O.transitionFor same).placeNext base) := by
  funext v
  simp [candidateWord, same, opposite,
    PeriodCertificateExamples.Examples.sameOppositeTwoWord,
    GeneratedClosedChain.generatedBlock,
    GeneratedClosedChain.orientationAt]

/-- For the selected candidate, the generated period equation is exactly the
two-step composite closure equation. -/
theorem candidateClosureEquation_iff_generatedPeriodEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2) :
    CandidateClosureEquation O base <->
      PeriodInterface.GeneratedPeriodEquation O
        PeriodCertificateExamples.twoPositiveLength base
        candidateWord.toFin := by
  constructor
  · intro hclose
    simpa [CandidateClosureEquation, candidateWord, same, opposite] using
      PeriodCertificateExamples.generatedPeriodEquation_sameOppositeTwo_of_twoStepClosesBase
        O base hclose
  · intro hperiod
    exact (candidateGeneratedBlock_two O base).symm.trans hperiod

/-- The actual two-step closure equation also matches the algebraic generated
closure equation from cyclic index `0`. -/
theorem candidateClosureEquation_iff_generatedClosureEquation
    (O : TransitionObligations)
    (base : LocalVertex -> R2) :
    CandidateClosureEquation O base <->
      PeriodInterface.GeneratedClosureEquation O
        PeriodCertificateExamples.twoPositiveLength base
        candidateWord.toFin := by
  constructor
  · intro hclose
    exact
      GeneratedPeriodClosure.generatedClosureEquation_of_generatedPeriodEquation
        O PeriodCertificateExamples.twoPositiveLength base
        candidateWord.toFin
        ((candidateClosureEquation_iff_generatedPeriodEquation O base).mp
          hclose)
  · intro hclosure
    exact
      (candidateClosureEquation_iff_generatedPeriodEquation O base).mpr
        (PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
          O PeriodCertificateExamples.twoPositiveLength base
          candidateWord.toFin hclosure)

/-- The two-step closure equation supplies the generated final-block period
equation for the concrete candidate. -/
theorem candidateGeneratedPeriodEquation_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose : CandidateClosureEquation O base) :
    PeriodInterface.GeneratedPeriodEquation O
      PeriodCertificateExamples.twoPositiveLength base
      candidateWord.toFin :=
  (candidateClosureEquation_iff_generatedPeriodEquation O base).mp hclose

/-- The same equation, routed through the generated closure reduction. -/
theorem candidateGeneratedClosureEquation_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose : CandidateClosureEquation O base) :
    PeriodInterface.GeneratedClosureEquation O
      PeriodCertificateExamples.twoPositiveLength base
      candidateWord.toFin :=
  (candidateClosureEquation_iff_generatedClosureEquation O base).mp hclose

/-- The two-step closure equation gives the downstream generated-period
hypothesis used by separation and closed-placement reductions. -/
theorem candidateGeneratedPeriod_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose : CandidateClosureEquation O base) :
    GeneratedSeparationInterface.GeneratedPeriod O
      PeriodCertificateExamples.twoPositiveLength base
      candidateWord.toFin :=
  GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
    O PeriodCertificateExamples.twoPositiveLength base candidateWord.toFin
    (candidateGeneratedPeriodEquation_of_twoStepClosesBase O base hclose)

/-- Reindex the two-step closure equation as the exact `Fin 16` algebraic
equations expected by finite period certificates. -/
theorem candidateAlgebraicEquations_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose : CandidateClosureEquation O base) :
    forall i : Fin 16,
      PeriodSearchInterface.AlgebraicVertexPeriodEquation O base
        candidateFiniteWord
        (BlockPartition.localVertexEquivFin16.symm i) := by
  intro i
  simpa [CandidateClosureEquation, candidateFiniteWord, same, opposite] using
    PeriodCertificateExamples.Examples.sameOppositeTwoAlgebraicEquations_of_twoStepClosesBase
      O base hclose i

/-- Package the actual two-step closure equation as a finite period-search
certificate for the concrete candidate. -/
def candidatePeriodSearchCertificate_of_twoStepClosesBase
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (hclose : CandidateClosureEquation O base) :
    PeriodSearchInterface.PeriodSearchCertificate O base where
  word := candidateFiniteWord
  period :=
    { equation :=
        candidateAlgebraicEquations_of_twoStepClosesBase O base hclose }

/-- Exact-base spelling of the generated final-block period equation for the
candidate. -/
theorem exactBase_candidateGeneratedPeriodEquation_of_twoStepClosesBase
    (O : TransitionObligations)
    (hclose : ExactBaseCandidateClosureEquation O) :
    PeriodInterface.GeneratedPeriodEquation O
      PeriodCertificateExamples.twoPositiveLength
      BaseTransitionRealization.exactBase
      candidateWord.toFin :=
  candidateGeneratedPeriodEquation_of_twoStepClosesBase
    O BaseTransitionRealization.exactBase hclose

/-! ## Reusable closure-checked finite word surface -/

/-- A checked closure equation for an arbitrary finite orientation word.

The field is deliberately the generated final-block equation itself: this
module records exact finite-word checks that have already been discharged, and
then projects them into the downstream period interfaces. -/
abbrev WordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (word : OrientationWord.Word k) : Prop :=
  PeriodInterface.GeneratedPeriodEquation O hk base word.toFin

/-- Exact-base spelling of the closure equation for an arbitrary finite word. -/
abbrev ExactBaseWordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (word : OrientationWord.Word k) : Prop :=
  WordCandidateClosureEquation O hk BaseTransitionRealization.exactBase word

/-- Project a checked candidate closure equation to the generated final-block
period equation. -/
theorem generatedPeriodEquation_of_wordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (word : OrientationWord.Word k)
    (hclose : WordCandidateClosureEquation O hk base word) :
    PeriodInterface.GeneratedPeriodEquation O hk base word.toFin :=
  hclose

/-- Project a checked candidate closure equation to the algebraic generated
closure equation from cyclic index `0`. -/
theorem generatedClosureEquation_of_wordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (word : OrientationWord.Word k)
    (hclose : WordCandidateClosureEquation O hk base word) :
    PeriodInterface.GeneratedClosureEquation O hk base word.toFin :=
  GeneratedPeriodClosure.generatedClosureEquation_of_generatedPeriodEquation
    O hk base word.toFin hclose

/-- Project a checked candidate closure equation to the downstream generated
period hypothesis. -/
theorem generatedPeriod_of_wordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (word : OrientationWord.Word k)
    (hclose : WordCandidateClosureEquation O hk base word) :
    GeneratedSeparationInterface.GeneratedPeriod O hk base word.toFin :=
  GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
    O hk base word.toFin hclose

/-- Exact-base projection to the generated final-block period equation. -/
theorem exactBase_generatedPeriodEquation_of_wordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (word : OrientationWord.Word k)
    (hclose : ExactBaseWordCandidateClosureEquation O hk word) :
    PeriodInterface.GeneratedPeriodEquation
      O hk BaseTransitionRealization.exactBase word.toFin :=
  generatedPeriodEquation_of_wordCandidateClosureEquation
    O hk BaseTransitionRealization.exactBase word hclose

/-- Exact-base projection to the algebraic generated closure equation. -/
theorem exactBase_generatedClosureEquation_of_wordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (word : OrientationWord.Word k)
    (hclose : ExactBaseWordCandidateClosureEquation O hk word) :
    PeriodInterface.GeneratedClosureEquation
      O hk BaseTransitionRealization.exactBase word.toFin :=
  generatedClosureEquation_of_wordCandidateClosureEquation
    O hk BaseTransitionRealization.exactBase word hclose

/-- Exact-base projection to the downstream generated-period hypothesis. -/
theorem exactBase_generatedPeriod_of_wordCandidateClosureEquation
    (O : TransitionObligations)
    {k : Nat} (hk : 0 < k)
    (word : OrientationWord.Word k)
    (hclose : ExactBaseWordCandidateClosureEquation O hk word) :
    GeneratedSeparationInterface.GeneratedPeriod
      O hk BaseTransitionRealization.exactBase word.toFin :=
  generatedPeriod_of_wordCandidateClosureEquation
    O hk BaseTransitionRealization.exactBase word hclose

/-- A single finite word with its checked closure equation. -/
structure CheckedWordCandidate
    (O : TransitionObligations)
    (base : LocalVertex -> R2) where
  length : Nat
  positive_length : 0 < length
  word : OrientationWord.Word length
  closure : WordCandidateClosureEquation O positive_length base word

namespace CheckedWordCandidate

/-- The raw orientation function carried by a checked word candidate. -/
def orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) :
    Fin C.length -> Orientation :=
  C.word.toFin

@[simp]
theorem orientation_apply
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) (i : Fin C.length) :
    C.orientation i = C.word i :=
  rfl

/-- The finite orientation word associated to a checked candidate. -/
def finiteWord
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) :
    FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord
    C.positive_length C.word

@[simp]
theorem finiteWord_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) :
    C.finiteWord.length = C.length :=
  rfl

@[simp]
theorem finiteWord_letter
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) (i : Fin C.length) :
    C.finiteWord.letter i = C.orientation i :=
  rfl

/-- The stored closure equation projected in generated-period-equation form. -/
theorem generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) :
    PeriodInterface.GeneratedPeriodEquation
      O C.positive_length base C.orientation :=
  C.closure

/-- The stored closure equation projected to cyclic-index algebraic closure. -/
theorem generatedClosureEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) :
    PeriodInterface.GeneratedClosureEquation
      O C.positive_length base C.orientation :=
  generatedClosureEquation_of_wordCandidateClosureEquation
    O C.positive_length base C.word C.closure

/-- The stored closure equation projected to the downstream generated-period
hypothesis. -/
theorem generatedPeriod
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : CheckedWordCandidate O base) :
    GeneratedSeparationInterface.GeneratedPeriod
      O C.positive_length base C.orientation :=
  generatedPeriod_of_wordCandidateClosureEquation
    O C.positive_length base C.word C.closure

/-- Build a closure-checked word candidate from the existing algebraic
period-equation candidate surface. -/
def ofPeriodEquationCandidate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (C : PeriodEquationConcreteSearch.PeriodEquationCandidate O base) :
    CheckedWordCandidate O base where
  length := C.length
  positive_length := C.positive_length
  word := C.word
  closure := C.generatedPeriodEquation

/-- Build a closure-checked word candidate from a fixed-length algebraic
period-equation candidate. -/
def ofFixedPeriodEquationCandidate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    {k : Nat} {hk : 0 < k}
    (C :
      PeriodEquationConcreteSearch.FixedPeriodEquationCandidate
        O base k hk) :
    CheckedWordCandidate O base where
  length := k
  positive_length := hk
  word := C.word
  closure := C.generatedPeriodEquation

end CheckedWordCandidate

/-- Exact-base variant of a checked finite-word candidate. -/
abbrev ExactBaseCheckedWordCandidate
    (O : TransitionObligations) :=
  CheckedWordCandidate O BaseTransitionRealization.exactBase

namespace ExactBaseCheckedWordCandidate

/-- Exact-base generated final-block period equation from a checked word
candidate. -/
theorem generatedPeriodEquation
    {O : TransitionObligations}
    (C : ExactBaseCheckedWordCandidate O) :
    PeriodInterface.GeneratedPeriodEquation
      O C.positive_length BaseTransitionRealization.exactBase
      C.orientation :=
  CheckedWordCandidate.generatedPeriodEquation C

/-- Exact-base algebraic generated closure from a checked word candidate. -/
theorem generatedClosureEquation
    {O : TransitionObligations}
    (C : ExactBaseCheckedWordCandidate O) :
    PeriodInterface.GeneratedClosureEquation
      O C.positive_length BaseTransitionRealization.exactBase
      C.orientation :=
  CheckedWordCandidate.generatedClosureEquation C

/-- Exact-base downstream generated-period hypothesis from a checked word
candidate. -/
theorem generatedPeriod
    {O : TransitionObligations}
    (C : ExactBaseCheckedWordCandidate O) :
    GeneratedSeparationInterface.GeneratedPeriod
      O C.positive_length BaseTransitionRealization.exactBase
      C.orientation :=
  CheckedWordCandidate.generatedPeriod C

end ExactBaseCheckedWordCandidate

/-- A closure-checked finite word for every positive block count. -/
structure CheckedWordFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  closure :
    forall (k : Nat) (hk : 0 < k),
      WordCandidateClosureEquation O hk base (word k hk)

namespace CheckedWordFamily

/-- The raw orientation function carried by one family member. -/
def orientation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The finite orientation word associated to one family member. -/
def finiteWord
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord hk (F.word k hk)

@[simp]
theorem finiteWord_length
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    (F.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hk).letter i = F.orientation k hk i :=
  rfl

/-- The single checked candidate at one positive length. -/
def candidate
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    CheckedWordCandidate O base where
  length := k
  positive_length := hk
  word := F.word k hk
  closure := F.closure k hk

/-- Generated final-block period equation for one checked family member. -/
theorem generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      O hk base (F.orientation k hk) :=
  generatedPeriodEquation_of_wordCandidateClosureEquation
    O hk base (F.word k hk) (F.closure k hk)

/-- Algebraic generated closure equation for one checked family member. -/
theorem generatedClosureEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      O hk base (F.orientation k hk) :=
  generatedClosureEquation_of_wordCandidateClosureEquation
    O hk base (F.word k hk) (F.closure k hk)

/-- Downstream generated-period hypothesis for one checked family member. -/
theorem generatedPeriod
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      O hk base (F.orientation k hk) :=
  generatedPeriod_of_wordCandidateClosureEquation
    O hk base (F.word k hk) (F.closure k hk)

/-- Forget a checked word family to the generated-chain family interface. -/
def toGeneratedChainFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => O
  base := fun _ _ => base
  orientation := F.orientation

/-- Generated-period hypotheses for every positive member of the family. -/
theorem generatedPeriods
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CheckedWordFamily O base) :
    F.toGeneratedChainFamily.Periods :=
  fun k hk => F.generatedPeriod k hk

/-- Build a closure-checked family from the existing algebraic period-equation
candidate family. -/
def ofPeriodEquationCandidateFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base) :
    CheckedWordFamily O base where
  word := F.word
  closure := fun k hk => F.generatedPeriodEquation k hk

end CheckedWordFamily

/-- Exact-base variant of a closure-checked finite-word family. -/
abbrev ExactBaseCheckedWordFamily
    (O : TransitionObligations) :=
  CheckedWordFamily O BaseTransitionRealization.exactBase

namespace ExactBaseCheckedWordFamily

/-- Generated final-block period equation for one exact-base family member. -/
theorem generatedPeriodEquation
    {O : TransitionObligations}
    (F : ExactBaseCheckedWordFamily O)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      O hk BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  CheckedWordFamily.generatedPeriodEquation F k hk

/-- Algebraic generated closure equation for one exact-base family member. -/
theorem generatedClosureEquation
    {O : TransitionObligations}
    (F : ExactBaseCheckedWordFamily O)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      O hk BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  CheckedWordFamily.generatedClosureEquation F k hk

/-- Downstream generated-period hypothesis for one exact-base family member. -/
theorem generatedPeriod
    {O : TransitionObligations}
    (F : ExactBaseCheckedWordFamily O)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      O hk BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  CheckedWordFamily.generatedPeriod F k hk

/-- Build an exact-base closure-checked family from the exact-base algebraic
period-equation candidate family. -/
def ofPeriodEquationCandidateFamily
    {O : TransitionObligations}
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily
        O BaseTransitionRealization.exactBase) :
    ExactBaseCheckedWordFamily O :=
  CheckedWordFamily.ofPeriodEquationCandidateFamily F

end ExactBaseCheckedWordFamily

end

end ConcretePeriodWordSearch
end PachToth
end ErdosProblems1066
