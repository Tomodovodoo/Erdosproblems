import ErdosProblems1066.PachToth.PeriodFamilyCandidateSearchW9
import ErdosProblems1066.PachToth.ConcretePeriodWordSearch
import ErdosProblems1066.PachToth.PeriodCandidateTargetRoute
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.PeriodCertificateExamples

set_option autoImplicit false

/-!
# W10 non-rigid period-candidate adapters

This module is a thin W10 layer over the W9 period-family surfaces.  It records
checked adapters for the currently concrete two-step word and keeps the
metric/lower-table inputs explicit for the still-open family route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonRigidPeriodCandidateW10

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev Candidate := PeriodFamilyCandidateSearchW9.Candidate
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev Orientation := OrientationData.BlockOrientation
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord
abbrev AlgebraicFamily (T : Candidate) :=
  PeriodFamilyCandidateSearchW9.AlgebraicEquationFamilyData T
abbrev ClosureFamily (T : Candidate) :=
  PeriodFamilyCandidateSearchW9.ClosureEquationFamilyData T
abbrev SearchSurfacePeriodData (T : Candidate) :=
  RoleHingeCandidateSearchSurface.PeriodSearchData T
abbrev SearchSurfaceCrossBlockMetricData
    {T : Candidate} (P : SearchSurfacePeriodData T) :=
  RoleHingeCandidateSearchSurface.CrossBlockMetricData P
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions
abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

/-! ## Concrete length-two period word -/

abbrev twoStepLength : Nat := 2

def twoStepPositive : 0 < twoStepLength :=
  PeriodCertificateExamples.twoPositiveLength

abbrev twoStepWord : OrientationWord.Word twoStepLength :=
  ConcretePeriodWordSearch.candidateWord

abbrev twoStepFiniteWord : FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord
    twoStepPositive twoStepWord

abbrev TwoStepClosureEquation (T : Candidate) : Prop :=
  ConcretePeriodWordSearch.ExactBaseCandidateClosureEquation
    T.toFigure2TransitionObligations

abbrev ConcreteTargetTwoStepClosureEquation : Prop :=
  PeriodCandidateTargetRoute.TwoStepCandidateClosureEquation

@[simp]
theorem twoStepWord_zero :
    twoStepWord (0 : Fin twoStepLength) =
      OrientationData.BlockOrientation.same := by
  simp [twoStepWord]

@[simp]
theorem twoStepWord_one :
    twoStepWord (1 : Fin twoStepLength) =
      OrientationData.BlockOrientation.opposite := by
  simp [twoStepWord]

theorem twoStepWord_nontrivial :
    Ne (twoStepWord (0 : Fin twoStepLength))
      (twoStepWord (1 : Fin twoStepLength)) := by
  simp [twoStepWord]

@[simp]
theorem twoStepFiniteWord_length :
    twoStepFiniteWord.length = twoStepLength :=
  rfl

@[simp]
theorem twoStepFiniteWord_zero :
    twoStepFiniteWord.letter (0 : Fin twoStepLength) =
      OrientationData.BlockOrientation.same := by
  simp [twoStepFiniteWord]

@[simp]
theorem twoStepFiniteWord_one :
    twoStepFiniteWord.letter (1 : Fin twoStepLength) =
      OrientationData.BlockOrientation.opposite := by
  simp [twoStepFiniteWord]

/-- A checked two-step period word for one non-rigid role-hinge candidate. -/
structure TwoStepCheckedData (T : Candidate) where
  closure : TwoStepClosureEquation T

namespace TwoStepCheckedData

def word
    {T : Candidate}
    (_D : TwoStepCheckedData T) :
    OrientationWord.Word twoStepLength :=
  twoStepWord

@[simp]
theorem word_eq
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    D.word = twoStepWord :=
  rfl

def finiteWord
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord
    twoStepPositive D.word

@[simp]
theorem finiteWord_length
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    D.finiteWord.length = twoStepLength :=
  rfl

@[simp]
theorem finiteWord_letter
    {T : Candidate}
    (D : TwoStepCheckedData T) (i : Fin twoStepLength) :
    D.finiteWord.letter i = D.word i :=
  rfl

/-- The concrete two-step closure equation gives the indexed algebraic
period equations for the two-step word. -/
theorem algebraicEquations
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    PeriodWordCertificates.AlgebraicEquationsForWord
      T.toFigure2TransitionObligations
      twoStepPositive
      BaseTransitionRealization.exactBase
      D.word := by
  intro i
  simpa [word, twoStepWord, ConcretePeriodWordSearch.candidateFiniteWord,
    PeriodWordCertificates.finiteOrientationWordOfWord,
    PeriodCertificateExamples.finiteOrientationWordOfWord] using
      ConcretePeriodWordSearch.candidateAlgebraicEquations_of_twoStepClosesBase
        T.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase D.closure i

def indexedAlgebraicCertificate
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      D.finiteWord :=
  PeriodWordCertificates.indexedAlgebraicCertificateOfWord
    T.toFigure2TransitionObligations
    twoStepPositive
    BaseTransitionRealization.exactBase
    D.word
    D.algebraicEquations

def periodSearchCertificate
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    PeriodSearchInterface.PeriodSearchCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase :=
  PeriodWordCertificates.periodSearchCertificateOfWord
    T.toFigure2TransitionObligations
    twoStepPositive
    BaseTransitionRealization.exactBase
    D.word
    D.algebraicEquations

def fixedPeriodEquationCandidate
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    PeriodEquationConcreteSearch.FixedPeriodEquationCandidate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      twoStepLength
      twoStepPositive where
  word := D.word
  equations := D.algebraicEquations

theorem generatedPeriodEquation
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations
      twoStepPositive
      BaseTransitionRealization.exactBase
      D.word.toFin := by
  simpa [word, twoStepWord] using
    ConcretePeriodWordSearch.exactBase_candidateGeneratedPeriodEquation_of_twoStepClosesBase
      T.toFigure2TransitionObligations D.closure

theorem generatedClosureEquation
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations
      twoStepPositive
      BaseTransitionRealization.exactBase
      D.word.toFin := by
  simpa [word, twoStepWord] using
    ConcretePeriodWordSearch.candidateGeneratedClosureEquation_of_twoStepClosesBase
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase D.closure

theorem generatedPeriod
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations
      twoStepPositive
      BaseTransitionRealization.exactBase
      D.word.toFin := by
  simpa [word, twoStepWord] using
    ConcretePeriodWordSearch.candidateGeneratedPeriod_of_twoStepClosesBase
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase D.closure

def checkedWordCandidate
    {T : Candidate}
    (D : TwoStepCheckedData T) :
    ConcretePeriodWordSearch.ExactBaseCheckedWordCandidate
      T.toFigure2TransitionObligations where
  length := twoStepLength
  positive_length := twoStepPositive
  word := D.word
  closure := D.generatedPeriodEquation

def generatedClosureData
    {T : Candidate}
    (D : TwoStepCheckedData T)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        twoStepPositive
        BaseTransitionRealization.exactBase
        D.word.toFin) :
    FlexibleExactLocalTransition.GeneratedClosureData
      twoStepLength twoStepPositive where
  transitions := T.toFlexibleSameOpposite
  orientation := D.word.toFin
  closure := by
    simpa using D.generatedClosureEquation
  separated := by
    simpa using separated

/-- Conditional exact-block route for the checked two-step word.  The
separation data remains an explicit input. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {T : Candidate}
    (D : TwoStepCheckedData T)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        twoStepPositive
        BaseTransitionRealization.exactBase
        D.word.toFin) :
    targetUpperConstructionFiveSixteenAt (16 * twoStepLength) :=
  (D.generatedClosureData separated).targetUpperConstructionFiveSixteenAt_exactBlock

end TwoStepCheckedData

/-- The target-route spelling of the two-step closure gives the same indexed
equations used by the concrete exact-target route. -/
theorem concreteTargetTwoStep_algebraicEquations
    (hclose : ConcreteTargetTwoStepClosureEquation) :
    PeriodWordCertificates.AlgebraicEquationsForWord
      ExactTargetCandidateClosure.concreteObligations
      PeriodCertificateExamples.twoPositiveLength
      BaseTransitionRealization.exactBase
      PeriodCandidateTargetRoute.twoStepCandidateWord :=
  PeriodCandidateTargetRoute.twoStepCandidate_equations hclose

/-! ## W9 family adapters -/

def allPositivePeriodWordFamily
    {T : Candidate}
    (F : AlgebraicFamily T) :
    PeriodWordCertificates.AllPositivePeriodWordFamily
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase where
  word := F.word
  equation := F.equations

def checkedWordFamilyOfClosureFamily
    {T : Candidate}
    (F : ClosureFamily T) :
    ConcretePeriodWordSearch.ExactBaseCheckedWordFamily
      T.toFigure2TransitionObligations :=
  F.toCheckedWordFamily

def checkedWordFamilyOfAlgebraicFamily
    {T : Candidate}
    (F : AlgebraicFamily T) :
    ConcretePeriodWordSearch.ExactBaseCheckedWordFamily
      T.toFigure2TransitionObligations :=
  F.toClosureEquationFamilyData.toCheckedWordFamily

def concretePeriodSearchDataOfAlgebraicFamily
    {T : Candidate}
    (transitions : RoleHingeTransitions)
    (transition_eq :
      transitions.toFigure2TransitionObligations =
        T.toFigure2TransitionObligations)
    (F : AlgebraicFamily T) :
    ConcretePeriodSearchFamily.PeriodSearchData where
  transitions := transitions
  word := F.word
  equation := by
    intro k hk i
    simpa [transition_eq,
      PeriodCertificateExamples.finiteOrientationWordOfWord,
      PeriodWordCertificates.finiteOrientationWordOfWord] using
        F.equations k hk i

/-- Period equations plus generated separation for every positive length.
This is the exact remaining package needed to produce a flexible generated
closure family from the W9 algebraic family surface. -/
structure FlexibleFamilyFields (T : Candidate) where
  period : AlgebraicFamily T
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (period.orientation k hk)

namespace FlexibleFamilyFields

/-- Build the flexible family fields directly from the non-rigid search
surface period data and generated separation. -/
def ofSearchSurfacePeriodData
    {T : Candidate}
    (P : SearchSurfacePeriodData T)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (P.orientation k hk)) :
    FlexibleFamilyFields T where
  period :=
    { word := P.word
      equations := P.equation }
  separated := by
    intro k hk
    simpa [RoleHingeCandidateSearchSurface.PeriodSearchData.orientation,
      PeriodFamilyCandidateSearchW9.AlgebraicEquationFamilyData.orientation]
      using separated k hk

/-- Cross-block metric data on the non-rigid search surface supplies exactly
the generated-separation field needed by the flexible exact-local route. -/
def ofSearchSurfaceMetricData
    {T : Candidate}
    {P : SearchSurfacePeriodData T}
    (M : SearchSurfaceCrossBlockMetricData P) :
    FlexibleFamilyFields T :=
  ofSearchSurfacePeriodData P M.separated

def orientation
    {T : Candidate}
    (F : FlexibleFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  F.period.orientation k hk

def toGeneratedChainFamily
    {T : Candidate}
    (F : FlexibleFamilyFields T) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  F.period.toGeneratedChainFamily

theorem periods
    {T : Candidate}
    (F : FlexibleFamilyFields T) :
    F.toGeneratedChainFamily.Periods :=
  F.period.periods

def toFlexibleGeneratedClosureFamily
    {T : Candidate}
    (F : FlexibleFamilyFields T) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  F.period.toFlexibleGeneratedClosureFamily F.separated

def data
    {T : Candidate}
    (F : FlexibleFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    FlexibleExactLocalTransition.GeneratedClosureData k hk :=
  (F.toFlexibleGeneratedClosureFamily).data k hk

def closedPlacement
    {T : Candidate}
    (F : FlexibleFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  (F.data k hk).toClosedPlacement

/-- Conditional exact-multiple route from the explicit W9 period family plus
the remaining generated-separation data. -/
theorem targetUpperConstructionFiveSixteen
    {T : Candidate}
    (F : FlexibleFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toFlexibleGeneratedClosureFamily.targetUpperConstructionFiveSixteen

end FlexibleFamilyFields

/-! ## Exact-target route remaining fields -/

/-- Remaining fields needed to feed a W9 algebraic period family into the
existing exact-target route.  The transition equalities and lower tables are
explicit data, so this wrapper does not supply the missing search output by
itself. -/
structure ExactTargetRouteFields
    (T : Candidate)
    (F : AlgebraicFamily T) where
  transitions : RoleHingeTransitions
  transition_eq :
    transitions.toFigure2TransitionObligations =
      T.toFigure2TransitionObligations
  concrete_eq :
    transitions.toFigure2TransitionObligations =
      ExactTargetCandidateClosure.concreteObligations
  same_rest :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.samePlaceNext source u)
                (RoleHingeConcreteSearch.samePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4
  opposite_rest :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.oppositePlaceNext source u)
                (RoleHingeConcreteSearch.oppositePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4
  tables :
    ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily
      (concretePeriodSearchDataOfAlgebraicFamily
        transitions transition_eq F).toRoleHingedPeriodSearchFamily

namespace ExactTargetRouteFields

def periodSearch
    {T : Candidate}
    {F : AlgebraicFamily T}
    (D : ExactTargetRouteFields T F) :
    ConcretePeriodSearchFamily.PeriodSearchData :=
  concretePeriodSearchDataOfAlgebraicFamily
    D.transitions D.transition_eq F

def toPeriodCandidateLowerTableData
    {T : Candidate}
    {F : AlgebraicFamily T}
    (D : ExactTargetRouteFields T F) :
    PeriodCandidateTargetRoute.PeriodCandidateLowerTableData where
  periodSearch := D.periodSearch
  transition_eq := D.concrete_eq
  same_rest := D.same_rest
  opposite_rest := D.opposite_rest
  tables := by
    simpa [periodSearch] using D.tables

def toMinimalExactTargetCertificate
    {T : Candidate}
    {F : AlgebraicFamily T}
    (D : ExactTargetRouteFields T F) :
    ExactTargetCandidateClosure.MinimalExactTargetCertificate :=
  D.toPeriodCandidateLowerTableData.toMinimalExactTargetCertificate

/-- Conditional exact-target route from explicit W9 period data, concrete
transition equality, residual exact-local fields, and non-connector lower
tables. -/
theorem targetUpperConstructionFiveSixteen
    {T : Candidate}
    {F : AlgebraicFamily T}
    (D : ExactTargetRouteFields T F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toPeriodCandidateLowerTableData.targetUpperConstructionFiveSixteen

/-- Conditional arbitrary-vertex route from the same explicit package. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {T : Candidate}
    {F : AlgebraicFamily T}
    (D : ExactTargetRouteFields T F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  D.toPeriodCandidateLowerTableData.targetUpperConstructionFiveSixteenArbitrary

end ExactTargetRouteFields

end

end NonRigidPeriodCandidateW10
end PachToth
end ErdosProblems1066
