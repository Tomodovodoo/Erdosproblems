import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.PeriodEquationSearchW11
import ErdosProblems1066.PachToth.FiniteCertificateInstantiationW13
import ErdosProblems1066.PachToth.EventualRoleHingeClosure

set_option autoImplicit false

/-!
# W14 concrete period-equation rows

This module is an instantiation ledger, not a new search oracle.  It isolates
the exact `Fin 16` algebraic period-equation rows that remain to be supplied
and checks the projections from those rows into the W11 search surface, the
W12/W13 finite-certificate fields, the concrete role-hinge candidate facade,
and the thresholded/eventual route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodEquationConcreteW14

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations

abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions

abbrev TransitionFacts :=
  ConcretePeriodCandidateSearch.TransitionFacts

abbrev Candidate :=
  PeriodEquationSearchW11.Candidate

abbrev SmallCandidateTag :=
  PeriodEquationConcreteSearch.SmallWords.CandidateTag

abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord

/-! ## All-positive role-hinge period rows -/

/-- One remaining all-positive algebraic period-equation row.

The row is indexed by the block length `k`, the positive-length witness, and
one of the sixteen local vertices. -/
abbrev AlgebraicEquationRow
    (T : RoleHingeTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (k : Nat) (hk : 0 < k) (i : Fin 16) : Prop :=
  PeriodSearchInterface.AlgebraicVertexPeriodEquation
    T.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    (PeriodCertificateExamples.finiteOrientationWordOfWord hk
      (word k hk))
    (BlockPartition.localVertexEquivFin16.symm i)

/-- Concrete all-positive period-equation fields, stripped down to exactly the
transition package, word family, and remaining `Fin 16` rows. -/
structure ConcretePeriodEquationFields where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      AlgebraicEquationRow transitions word k hk i

namespace ConcretePeriodEquationFields

def orientation
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (P.word k hk).toFin

@[simp]
theorem orientation_apply
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    P.orientation k hk i = P.word k hk i :=
  rfl

def finiteWord
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfWord hk (P.word k hk)

@[simp]
theorem finiteWord_length
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    (P.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (P.finiteWord k hk).letter i = P.orientation k hk i :=
  rfl

/-- The named row projection. -/
theorem row
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) (i : Fin 16) :
    AlgebraicEquationRow P.transitions P.word k hk i :=
  P.equation k hk i

/-- The same rows in the `PeriodEquationConcreteSearch` spelling. -/
def exactPeriodEquations
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationConcreteSearch.ExactPeriodEquations
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.word k hk) := by
  intro i
  simpa [AlgebraicEquationRow,
    PeriodCertificateExamples.finiteOrientationWordOfWord,
    PeriodWordCertificates.finiteOrientationWordOfWord]
    using P.equation k hk i

def indexedCertificate
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      P.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (P.finiteWord k hk) where
  equation := P.equation k hk

def closure
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  (P.indexedCertificate k hk).toGeneratedClosureEquation

def periodEquation
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  (P.indexedCertificate k hk).toGeneratedPeriodEquation

def generatedPeriod
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hk) :=
  (P.indexedCertificate k hk).toGeneratedPeriod

def fixedCandidate
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationConcreteSearch.FixedPeriodEquationCandidate
      P.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      k hk where
  word := P.word k hk
  equations := P.exactPeriodEquations k hk

@[simp]
theorem fixedCandidate_word
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    (P.fixedCandidate k hk).word = P.word k hk :=
  rfl

def toPeriodEquationCandidateFamily
    (P : ConcretePeriodEquationFields) :
    PeriodEquationConcreteSearch.PeriodEquationCandidateFamily
      P.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase where
  candidate := P.fixedCandidate

@[simp]
theorem toPeriodEquationCandidateFamily_word
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toPeriodEquationCandidateFamily.word k hk = P.word k hk :=
  rfl

def toPeriodSearchData
    (P : ConcretePeriodEquationFields) :
    ConcretePeriodSearchFamily.PeriodSearchData where
  transitions := P.transitions
  word := P.word
  equation := P.equation

@[simp]
theorem toPeriodSearchData_transitions
    (P : ConcretePeriodEquationFields) :
    P.toPeriodSearchData.transitions = P.transitions :=
  rfl

@[simp]
theorem toPeriodSearchData_word
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toPeriodSearchData.word k hk = P.word k hk :=
  rfl

@[simp]
theorem toPeriodSearchData_orientation
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toPeriodSearchData.orientation k hk = P.orientation k hk :=
  rfl

def toW12PeriodEquationFields
    (P : ConcretePeriodEquationFields) :
    FiniteCertificateInstantiationW13.W12.PeriodEquationFields where
  transitions := P.transitions
  word := P.word
  equation := P.equation

@[simp]
theorem toW12PeriodEquationFields_word
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toW12PeriodEquationFields.word k hk = P.word k hk :=
  rfl

@[simp]
theorem toW12PeriodEquationFields_orientation
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toW12PeriodEquationFields.orientation k hk =
      P.orientation k hk :=
  rfl

theorem toW12_closure
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toW12PeriodEquationFields.closure k hk = P.closure k hk :=
  rfl

theorem toW12_periodEquation
    (P : ConcretePeriodEquationFields)
    (k : Nat) (hk : 0 < k) :
    P.toW12PeriodEquationFields.periodEquation k hk =
      P.periodEquation k hk :=
  rfl

/-- All-positive period-equation rows force the length-one letter to fix the
exact base block.  This records the checked narrowing imposed by the remaining
rows themselves. -/
theorem lengthOne_forces_same_or_opposite_fixesExactBase
    (P : ConcretePeriodEquationFields) :
    (P.word 1 PeriodCertificateExamples.onePositiveLength (0 : Fin 1) =
        OrientationData.BlockOrientation.same /\
      PeriodCertificateExamples.TransitionFixesBase
        P.transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        OrientationData.BlockOrientation.same) \/
    (P.word 1 PeriodCertificateExamples.onePositiveLength (0 : Fin 1) =
        OrientationData.BlockOrientation.opposite /\
      PeriodCertificateExamples.TransitionFixesBase
        P.transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        OrientationData.BlockOrientation.opposite) :=
  PeriodCertificateExamples.allPositiveEquations_force_same_or_opposite_fixesBase
    P.transitions.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    P.word
    P.equation

end ConcretePeriodEquationFields

/-- Repackage existing concrete period-search data as the W14 row ledger. -/
def ofPeriodSearchData
    (P : ConcretePeriodSearchFamily.PeriodSearchData) :
    ConcretePeriodEquationFields where
  transitions := P.transitions
  word := P.word
  equation := P.equation

@[simp]
theorem ofPeriodSearchData_toPeriodSearchData
    (P : ConcretePeriodSearchFamily.PeriodSearchData) :
    (ofPeriodSearchData P).toPeriodSearchData = P := by
  cases P
  rfl

/-- Repackage W12/W13 period-equation fields as the W14 row ledger. -/
def ofW12PeriodEquationFields
    (P : FiniteCertificateInstantiationW13.W12.PeriodEquationFields) :
    ConcretePeriodEquationFields where
  transitions := P.transitions
  word := P.word
  equation := P.equation

@[simp]
theorem ofW12PeriodEquationFields_toW12
    (P : FiniteCertificateInstantiationW13.W12.PeriodEquationFields) :
    (ofW12PeriodEquationFields P).toW12PeriodEquationFields = P := by
  cases P
  rfl

/-- Repackage role-hinge candidate period data as concrete all-positive rows. -/
def ofPeriodCandidateFamily
    (P : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :
    ConcretePeriodEquationFields where
  transitions := P.transitions.toRoleHingeTransitions
  word := P.word
  equation := by
    intro k hk i
    simpa [AlgebraicEquationRow,
      ConcretePeriodCandidateSearch.transitionObligationsOfFacts]
      using (P.period k hk).equation i

/-- Conditional all-same all-positive fields, available exactly when the same
transition fixes the checked exact base block. -/
def allPositiveSameFields_of_transitionFixesExactBase
    (T : RoleHingeTransitions)
    (hfix :
      PeriodCertificateExamples.TransitionFixesBase
        T.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        OrientationData.BlockOrientation.same) :
    ConcretePeriodEquationFields where
  transitions := T
  word := PeriodCertificateExamples.allPositiveSameWord
  equation := by
    intro k hk i
    exact
      PeriodCertificateExamples.allPositiveSameEquations
        T.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase hfix k hk i

/-- Conditional all-opposite all-positive fields, available exactly when the
opposite transition fixes the checked exact base block. -/
def allPositiveOppositeFields_of_transitionFixesExactBase
    (T : RoleHingeTransitions)
    (hfix :
      PeriodCertificateExamples.TransitionFixesBase
        T.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        OrientationData.BlockOrientation.opposite) :
    ConcretePeriodEquationFields where
  transitions := T
  word := PeriodCertificateExamples.allPositiveOppositeWord
  equation := by
    intro k hk i
    exact
      PeriodCertificateExamples.allPositiveOppositeEquations
        T.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase hfix k hk i

/-! ## W11 candidate rows -/

/-- The exact W11 row shape for one non-rigid candidate, length, and local
vertex. -/
abbrev CandidateEquationRow
    (T : Candidate)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (k : Nat) (hk : 0 < k) (i : Fin 16) : Prop :=
  PeriodSearchInterface.AlgebraicVertexPeriodEquation
    T.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    (PeriodWordCertificates.finiteOrientationWordOfWord hk (word k hk))
    (BlockPartition.localVertexEquivFin16.symm i)

/-- W11 candidate period-equation rows, one word and sixteen rows at every
positive block count. -/
structure CandidatePeriodEquationRows (T : Candidate) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      CandidateEquationRow T word k hk i

namespace CandidatePeriodEquationRows

def equations
    {T : Candidate}
    (P : CandidatePeriodEquationRows T)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationSearchW11.CandidateWordEquations
      T hk (P.word k hk) :=
  P.equation k hk

def toCheckedWordEquationFamily
    {T : Candidate}
    (P : CandidatePeriodEquationRows T) :
    PeriodEquationSearchW11.CheckedWordEquationFamily T where
  word := P.word
  equations := P.equations

@[simp]
theorem toCheckedWordEquationFamily_word
    {T : Candidate}
    (P : CandidatePeriodEquationRows T)
    (k : Nat) (hk : 0 < k) :
    P.toCheckedWordEquationFamily.word k hk = P.word k hk :=
  rfl

def package
    {T : Candidate}
    (P : CandidatePeriodEquationRows T)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationSearchW11.CheckedWordEquationPackage T :=
  P.toCheckedWordEquationFamily.package k hk

def indexedCertificate
    {T : Candidate}
    (P : CandidatePeriodEquationRows T)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      ((P.package k hk).finiteWord) :=
  (P.package k hk).indexedAlgebraicCertificate

def generatedClosureEquation
    {T : Candidate}
    (P : CandidatePeriodEquationRows T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.word k hk).toFin :=
  (P.toCheckedWordEquationFamily).generatedClosureEquation k hk

def generatedPeriod
    {T : Candidate}
    (P : CandidatePeriodEquationRows T)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.word k hk).toFin :=
  (P.toCheckedWordEquationFamily).generatedPeriod k hk

def toGeneratedFamilyRemainingFields
    {T : Candidate}
    (P : CandidatePeriodEquationRows T)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (P.word k hk).toFin) :
    PeriodEquationSearchW11.GeneratedFamilyRemainingFields T where
  period := P.toCheckedWordEquationFamily
  separated := by
    intro k hk
    exact separated k hk

end CandidatePeriodEquationRows

/-! ## Small tagged rows -/

/-- One tagged small-word row for a role-hinge transition-fact package. -/
abbrev TaggedSmallEquationRow
    (T : TransitionFacts) (tag : SmallCandidateTag) (i : Fin 16) : Prop :=
  PeriodSearchInterface.AlgebraicVertexPeriodEquation
    (ConcretePeriodCandidateSearch.transitionObligationsOfFacts T)
    BaseTransitionRealization.exactBase
    (PeriodWordCertificates.finiteOrientationWordOfWord
      tag.positiveLength tag.word)
    (BlockPartition.localVertexEquivFin16.symm i)

/-- The finite currently-explicit small-word rows. -/
structure TaggedSmallEquationRows (T : TransitionFacts) where
  equation :
    forall tag : SmallCandidateTag,
      ConcretePeriodCandidateSearch.SmallWords.tagEquations T tag

namespace TaggedSmallEquationRows

theorem row
    {T : TransitionFacts}
    (P : TaggedSmallEquationRows T)
    (tag : SmallCandidateTag) (i : Fin 16) :
    TaggedSmallEquationRow T tag i :=
  P.equation tag i

def fixedCandidate
    {T : TransitionFacts}
    (P : TaggedSmallEquationRows T)
    (tag : SmallCandidateTag) :
    ConcretePeriodCandidateSearch.FixedPeriodCandidate
      T tag.length tag.positiveLength :=
  ConcretePeriodCandidateSearch.SmallWords.fixedCandidateOfTag
    T tag (P.equation tag)

def candidate
    {T : TransitionFacts}
    (P : TaggedSmallEquationRows T)
    (tag : SmallCandidateTag) :
    ConcretePeriodCandidateSearch.PeriodCandidate T :=
  ConcretePeriodCandidateSearch.SmallWords.candidateOfTag
    T tag (P.equation tag)

def indexedCertificate
    {T : TransitionFacts}
    (P : TaggedSmallEquationRows T)
    (tag : SmallCandidateTag) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      (ConcretePeriodCandidateSearch.transitionObligationsOfFacts T)
      BaseTransitionRealization.exactBase
      ((P.fixedCandidate tag).finiteWord) :=
  (P.fixedCandidate tag).indexedAlgebraicCertificate

def generatedPeriod
    {T : TransitionFacts}
    (P : TaggedSmallEquationRows T)
    (tag : SmallCandidateTag) :
    GeneratedSeparationInterface.GeneratedPeriod
      (ConcretePeriodCandidateSearch.transitionObligationsOfFacts T)
      tag.positiveLength
      BaseTransitionRealization.exactBase
      tag.word.toFin :=
  ConcretePeriodCandidateSearch.SmallWords.generatedPeriodOfTag
    T tag (P.equation tag)

end TaggedSmallEquationRows

/-! ## Thresholded/eventual period rows -/

/-- One thresholded/eventual period-equation row. -/
abbrev EventualEquationRow
    (T : RoleHingeTransitions)
    (K0 : Nat)
    (word :
      forall (k : Nat), K0 <= k -> 0 < k -> OrientationWord.Word k)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin 16) : Prop :=
  PeriodSearchInterface.AlgebraicVertexPeriodEquation
    T.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    (PeriodCertificateExamples.finiteOrientationWordOfWord hk
      (word k hK hk))
    (BlockPartition.localVertexEquivFin16.symm i)

/-- Thresholded/eventual period-equation fields without the separate global
separation rows. -/
structure EventualPeriodEquationFields (K0 : Nat) where
  transitions : RoleHingeTransitions
  word :
    forall (k : Nat), K0 <= k -> 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin 16),
      EventualEquationRow transitions K0 word k hK hk i

namespace EventualPeriodEquationFields

def orientation
    {K0 : Nat} (P : EventualPeriodEquationFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (P.word k hK hk).toFin

@[simp]
theorem orientation_apply
    {K0 : Nat} (P : EventualPeriodEquationFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin k) :
    P.orientation k hK hk i = P.word k hK hk i :=
  rfl

def indexedCertificate
    {K0 : Nat} (P : EventualPeriodEquationFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      P.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (PeriodCertificateExamples.finiteOrientationWordOfWord hk
        (P.word k hK hk)) where
  equation := P.equation k hK hk

def closure
    {K0 : Nat} (P : EventualPeriodEquationFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk) :=
  (P.indexedCertificate k hK hk).toGeneratedClosureEquation

def generatedPeriod
    {K0 : Nat} (P : EventualPeriodEquationFields K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      P.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (P.orientation k hK hk) :=
  (P.indexedCertificate k hK hk).toGeneratedPeriod

def toEventualFiniteCertificateObligations
    {K0 : Nat} (P : EventualPeriodEquationFields K0)
    (separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          P.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (P.orientation k hK hk)) :
    EventualRoleHingeClosure.EventualFiniteCertificateObligations K0 where
  transitions := P.transitions
  word := P.word
  equation := P.equation
  separated := separated

def ofAllPositive
    (K0 : Nat) (P : ConcretePeriodEquationFields) :
    EventualPeriodEquationFields K0 where
  transitions := P.transitions
  word := fun k _hK hk => P.word k hk
  equation := fun k _hK hk i => P.equation k hk i

@[simp]
theorem ofAllPositive_word
    (K0 : Nat) (P : ConcretePeriodEquationFields)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (ofAllPositive K0 P).word k hK hk = P.word k hk :=
  rfl

end EventualPeriodEquationFields

end

end PeriodEquationConcreteW14
end PachToth
end ErdosProblems1066
