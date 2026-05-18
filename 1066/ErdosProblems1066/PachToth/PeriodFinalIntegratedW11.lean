import ErdosProblems1066.PachToth.PeriodTargetIntegratedW11
import ErdosProblems1066.PachToth.PeriodIntegratedW11
import ErdosProblems1066.PachToth.PeriodClosureW11
import ErdosProblems1066.PachToth.TransitionTargetIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNFinalIntegratedW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# Final W11 period aggregate

This module is a terminal ledger for the W11 period route.  It keeps the
finite word plus separation data, the all-positive separated family, the
explicit lower table fields, and the exact candidate fields as displayed
inputs.  The target conclusions below are therefore all projections from a
caller-supplied package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodFinalIntegratedW11

open FiniteGraph

noncomputable section

universe u

abbrev Candidate := PeriodTargetIntegratedW11.Candidate

abbrev CheckedWordEquationPackage :=
  PeriodTargetIntegratedW11.CheckedWordEquationPackage

abbrev CheckedWordEquationFamily :=
  PeriodTargetIntegratedW11.CheckedWordEquationFamily

abbrev BaseWordSeparationFields :=
  PeriodTargetIntegratedW11.CheckedWordSeparationFields

abbrev BaseSeparatedFamilyFields :=
  PeriodTargetIntegratedW11.GeneratedFamilyRemainingFields

abbrev BaseLowerBoundFields :=
  PeriodTargetIntegratedW11.ExplicitLowerBoundClosureFields

abbrev BaseExactCandidateFields :=
  PeriodTargetIntegratedW11.ExactCandidatePeriodFields

abbrev ArbitraryNTargetFacade :=
  PeriodTargetIntegratedW11.ArbitraryNTargetFacade

abbrev GeneratedGlobalSeparation
    (T : Candidate) {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> PeriodEquationSearchW11.Orientation) : Prop :=
  GeneratedSeparationInterface.GeneratedGlobalSeparation
    T.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    orientation

/-! ## Displayed final fields -/

/-- A checked period word with the separation witness needed for its block. -/
structure WordSeparationFields (T : Candidate)
    extends BaseWordSeparationFields T

namespace WordSeparationFields

def length
    {T : Candidate}
    (D : WordSeparationFields T) : Nat :=
  D.checkedWord.length

theorem positiveLength
    {T : Candidate}
    (D : WordSeparationFields T) :
    0 < D.length :=
  D.checkedWord.positive_length

def word
    {T : Candidate}
    (D : WordSeparationFields T) :
    OrientationWord.Word D.length :=
  D.checkedWord.word

def orientation
    {T : Candidate}
    (D : WordSeparationFields T) :
    Fin D.length -> PeriodEquationSearchW11.Orientation :=
  D.checkedWord.orientation

theorem separationWitness
    {T : Candidate}
    (D : WordSeparationFields T) :
    GeneratedGlobalSeparation
      T D.checkedWord.positive_length D.checkedWord.orientation :=
  D.toCheckedWordSeparationFields.separated

theorem exactBlockTarget
    {T : Candidate}
    (D : WordSeparationFields T) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * D.length) :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_checkedWordSeparation
    D.toCheckedWordSeparationFields

end WordSeparationFields

/-- A checked period family with separation at every positive block count. -/
structure SeparatedFamilyFields (T : Candidate)
    extends BaseSeparatedFamilyFields T

namespace SeparatedFamilyFields

def word
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    OrientationWord.Word k :=
  D.period.word k hk

def orientation
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    Fin k -> PeriodEquationSearchW11.Orientation :=
  D.period.orientation k hk

theorem separationWitness
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparation T hk (D.orientation k hk) :=
  D.toGeneratedFamilyRemainingFields.separated k hk

theorem exactBlockTarget
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_separatedFamilyFields
    D.toGeneratedFamilyRemainingFields k hk

theorem exactTarget
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_separatedFamilyFields
    D.toGeneratedFamilyRemainingFields

theorem fixedTarget
    {T : Candidate}
    (D : SeparatedFamilyFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_separatedFamilyFields
    D.toGeneratedFamilyRemainingFields n

theorem eventualTarget
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_separatedFamilyFields
    D.toGeneratedFamilyRemainingFields

theorem arbitraryTarget
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_separatedFamilyFields
    D.toGeneratedFamilyRemainingFields

def targetFacade
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    ArbitraryNTargetFacade :=
  PeriodTargetIntegratedW11.targetFacade_of_separatedFamilyFields
    D.toGeneratedFamilyRemainingFields

end SeparatedFamilyFields

/-- Explicit lower tables for a checked period family. -/
structure LowerBoundFields (T : Candidate)
    extends BaseLowerBoundFields T

namespace LowerBoundFields

theorem lowerGeOne
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hij : Ne i j) :
    1 <= D.lower k hk i u j v :=
  D.lower_ge_one k hk i u j v hij

theorem lowerBound
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hij : Ne i j) :
    D.lower k hk i u j v <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (D.period.orientation k hk)
          i u)
        (GeneratedClosedChain.generatedPoint
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (D.period.orientation k hk)
          j v) :=
  D.lower_bound k hk i u j v hij

theorem exactBlockTarget
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundFields
    D.toExplicitLowerBoundClosureFields k hk

theorem exactTarget
    {T : Candidate}
    (D : LowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_explicitLowerBoundFields
    D.toExplicitLowerBoundClosureFields

theorem fixedTarget
    {T : Candidate}
    (D : LowerBoundFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_explicitLowerBoundFields
    D.toExplicitLowerBoundClosureFields n

theorem eventualTarget
    {T : Candidate}
    (D : LowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_explicitLowerBoundFields
    D.toExplicitLowerBoundClosureFields

theorem arbitraryTarget
    {T : Candidate}
    (D : LowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
    D.toExplicitLowerBoundClosureFields

def targetFacade
    {T : Candidate}
    (D : LowerBoundFields T) :
    ArbitraryNTargetFacade :=
  PeriodTargetIntegratedW11.targetFacade_of_explicitLowerBoundFields
    D.toExplicitLowerBoundClosureFields

end LowerBoundFields

/-- Exact candidate period data for the final period route. -/
structure ExactCandidateFields (T : Candidate)
    extends BaseExactCandidateFields T

namespace ExactCandidateFields

theorem exactTarget
    {T : Candidate}
    (D : ExactCandidateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
    D.toExactCandidatePeriodFields

theorem fixedTarget
    {T : Candidate}
    (D : ExactCandidateFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_exactCandidatePeriodFields
    D.toExactCandidatePeriodFields n

theorem eventualTarget
    {T : Candidate}
    (D : ExactCandidateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_exactCandidatePeriodFields
    D.toExactCandidatePeriodFields

theorem arbitraryTarget
    {T : Candidate}
    (D : ExactCandidateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
    D.toExactCandidatePeriodFields

def targetFacade
    {T : Candidate}
    (D : ExactCandidateFields T) :
    ArbitraryNTargetFacade :=
  PeriodTargetIntegratedW11.targetFacade_of_exactCandidatePeriodFields
    D.toExactCandidatePeriodFields

end ExactCandidateFields

/-! ## Full displayed period aggregate -/

/-- The final period source package with all requested period data visible. -/
structure AggregateFields (T : Candidate) where
  wordSeparation : WordSeparationFields T
  separatedFamily : SeparatedFamilyFields T
  lowerBound : LowerBoundFields T
  exactCandidate : ExactCandidateFields T

namespace AggregateFields

theorem wordExactBlockTarget
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * A.wordSeparation.length) :=
  A.wordSeparation.exactBlockTarget

theorem exactTargetOfSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  A.separatedFamily.exactTarget

theorem eventualTargetOfSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  A.separatedFamily.eventualTarget

theorem arbitraryTargetOfSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  A.separatedFamily.arbitraryTarget

theorem exactTargetOfLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  A.lowerBound.exactTarget

theorem eventualTargetOfLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  A.lowerBound.eventualTarget

theorem arbitraryTargetOfLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  A.lowerBound.arbitraryTarget

theorem exactTargetOfExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  A.exactCandidate.exactTarget

theorem eventualTargetOfExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  A.exactCandidate.eventualTarget

theorem arbitraryTargetOfExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  A.exactCandidate.arbitraryTarget

end AggregateFields

/-! ## Route rows -/

/-- Fixed block route for one checked word plus separation witness. -/
structure WordSeparationRoute (T : Candidate) where
  length : WordSeparationFields T -> Nat
  positiveLength :
    forall D : WordSeparationFields T, 0 < length D
  word :
    forall D : WordSeparationFields T,
      OrientationWord.Word (length D)
  separated :
    forall D : WordSeparationFields T,
      GeneratedGlobalSeparation
        T D.checkedWord.positive_length D.checkedWord.orientation
  exactBlockTarget :
    forall D : WordSeparationFields T,
      PachToth.targetUpperConstructionFiveSixteenAt (16 * length D)

def wordSeparationRoute
    (T : Candidate) :
    WordSeparationRoute T where
  length := WordSeparationFields.length
  positiveLength := WordSeparationFields.positiveLength
  word := WordSeparationFields.word
  separated := WordSeparationFields.separationWitness
  exactBlockTarget := WordSeparationFields.exactBlockTarget

/-- Full target row for a displayed period package. -/
structure TargetRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

def separatedFamilyTargetRoute
    (T : Candidate) :
    TargetRoute (SeparatedFamilyFields T) where
  exactTarget := SeparatedFamilyFields.exactTarget
  fixedTarget := SeparatedFamilyFields.fixedTarget
  eventualTarget := SeparatedFamilyFields.eventualTarget
  arbitraryTarget := SeparatedFamilyFields.arbitraryTarget
  targetFacade := SeparatedFamilyFields.targetFacade

def lowerBoundTargetRoute
    (T : Candidate) :
    TargetRoute (LowerBoundFields T) where
  exactTarget := LowerBoundFields.exactTarget
  fixedTarget := LowerBoundFields.fixedTarget
  eventualTarget := LowerBoundFields.eventualTarget
  arbitraryTarget := LowerBoundFields.arbitraryTarget
  targetFacade := LowerBoundFields.targetFacade

def exactCandidateTargetRoute
    (T : Candidate) :
    TargetRoute (ExactCandidateFields T) where
  exactTarget := ExactCandidateFields.exactTarget
  fixedTarget := ExactCandidateFields.fixedTarget
  eventualTarget := ExactCandidateFields.eventualTarget
  arbitraryTarget := ExactCandidateFields.arbitraryTarget
  targetFacade := ExactCandidateFields.targetFacade

/-- Routes from the combined final package, split by the source of data. -/
structure AggregateTargetRoutes (T : Candidate) where
  separatedFamily : TargetRoute (AggregateFields T)
  lowerBound : TargetRoute (AggregateFields T)
  exactCandidate : TargetRoute (AggregateFields T)

def aggregateTargetRoutes
    (T : Candidate) :
    AggregateTargetRoutes T where
  separatedFamily :=
    { exactTarget := AggregateFields.exactTargetOfSeparatedFamily
      fixedTarget := fun A n => A.separatedFamily.fixedTarget n
      eventualTarget := AggregateFields.eventualTargetOfSeparatedFamily
      arbitraryTarget := AggregateFields.arbitraryTargetOfSeparatedFamily
      targetFacade := fun A => A.separatedFamily.targetFacade }
  lowerBound :=
    { exactTarget := AggregateFields.exactTargetOfLowerBound
      fixedTarget := fun A n => A.lowerBound.fixedTarget n
      eventualTarget := AggregateFields.eventualTargetOfLowerBound
      arbitraryTarget := AggregateFields.arbitraryTargetOfLowerBound
      targetFacade := fun A => A.lowerBound.targetFacade }
  exactCandidate :=
    { exactTarget := AggregateFields.exactTargetOfExactCandidate
      fixedTarget := fun A n => A.exactCandidate.fixedTarget n
      eventualTarget := AggregateFields.eventualTargetOfExactCandidate
      arbitraryTarget := AggregateFields.arbitraryTargetOfExactCandidate
      targetFacade := fun A => A.exactCandidate.targetFacade }

/-! ## Matrix -/

/-- Source package shapes consumed by this final period aggregate. -/
structure FieldLedger where
  wordSeparation : Candidate -> Type
  separatedFamily : Candidate -> Type
  lowerBound : Candidate -> Type
  exactCandidate : Candidate -> Type
  aggregate : Candidate -> Type

def fieldLedger : FieldLedger where
  wordSeparation := WordSeparationFields
  separatedFamily := SeparatedFamilyFields
  lowerBound := LowerBoundFields
  exactCandidate := ExactCandidateFields
  aggregate := AggregateFields

/-- Checked W11 matrices imported by the final period aggregate. -/
structure ImportedMatrices where
  periodTarget : PeriodTargetIntegratedW11.Matrix
  periodIntegrated : PeriodIntegratedW11.Matrix
  periodClosure : PeriodClosureW11.Matrix
  transitionTarget : TransitionTargetIntegratedW11.Matrix
  arbitraryNFinal : ArbitraryNFinalIntegratedW11.Matrix
  crossBlockFinal : CrossBlockFinalIntegratedW11.Matrix
  finalConsistency : PachTothW11FinalConsistency.Matrix

def importedMatrices : ImportedMatrices where
  periodTarget := PeriodTargetIntegratedW11.matrix
  periodIntegrated := PeriodIntegratedW11.matrix
  periodClosure := PeriodClosureW11.matrix
  transitionTarget := TransitionTargetIntegratedW11.matrix
  arbitraryNFinal := ArbitraryNFinalIntegratedW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  finalConsistency := PachTothW11FinalConsistency.matrix

/-- Final W11 period aggregate.

The matrix stores package ledgers and route projections only; every target
statement below consumes explicit period data.
-/
structure Matrix where
  fields : FieldLedger
  imported : ImportedMatrices
  wordSeparation :
    forall T : Candidate, WordSeparationRoute T
  separatedFamily :
    forall T : Candidate, TargetRoute (SeparatedFamilyFields T)
  lowerBound :
    forall T : Candidate, TargetRoute (LowerBoundFields T)
  exactCandidate :
    forall T : Candidate, TargetRoute (ExactCandidateFields T)
  aggregate :
    forall T : Candidate, AggregateTargetRoutes T

/-- The checked final W11 period aggregate. -/
def matrix : Matrix where
  fields := fieldLedger
  imported := importedMatrices
  wordSeparation := wordSeparationRoute
  separatedFamily := separatedFamilyTargetRoute
  lowerBound := lowerBoundTargetRoute
  exactCandidate := exactCandidateTargetRoute
  aggregate := aggregateTargetRoutes

/-! ## Public word and separation projections -/

theorem targetUpperConstructionFiveSixteenAt_of_wordSeparationFields
    {T : Candidate}
    (D : WordSeparationFields T) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * D.length) :=
  (matrix.wordSeparation T).exactBlockTarget D

theorem separated_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    GeneratedGlobalSeparation T hk (D.orientation k hk) :=
  D.separated k hk

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  D.exactBlockTarget k hk

theorem targetUpperConstructionFiveSixteen_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.separatedFamily T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.separatedFamily T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_separatedFamilyFields
    {T : Candidate}
    (D : SeparatedFamilyFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.separatedFamily T).arbitraryTarget D

/-! ## Public lower table projections -/

theorem lower_ge_one_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hij : Ne i j) :
    1 <= D.lower k hk i u j v :=
  D.lowerGeOne k hk i u j v hij

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  D.exactBlockTarget k hk

theorem targetUpperConstructionFiveSixteen_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.lowerBound T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.lowerBound T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_lowerBoundFields
    {T : Candidate}
    (D : LowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.lowerBound T).arbitraryTarget D

/-! ## Public exact candidate projections -/

theorem targetUpperConstructionFiveSixteen_of_exactCandidateFields
    {T : Candidate}
    (D : ExactCandidateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.exactCandidate T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_exactCandidateFields
    {T : Candidate}
    (D : ExactCandidateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.exactCandidate T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactCandidateFields
    {T : Candidate}
    (D : ExactCandidateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.exactCandidate T).arbitraryTarget D

/-! ## Public aggregate projections -/

theorem targetUpperConstructionFiveSixteenAt_of_aggregateWordSeparation
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * A.wordSeparation.length) :=
  A.wordExactBlockTarget

theorem targetUpperConstructionFiveSixteen_of_aggregateSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  ((matrix.aggregate T).separatedFamily).exactTarget A

theorem targetUpperConstructionFiveSixteenEventually_of_aggregateSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  ((matrix.aggregate T).separatedFamily).eventualTarget A

theorem targetUpperConstructionFiveSixteenArbitrary_of_aggregateSeparatedFamily
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ((matrix.aggregate T).separatedFamily).arbitraryTarget A

theorem targetUpperConstructionFiveSixteen_of_aggregateLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  ((matrix.aggregate T).lowerBound).exactTarget A

theorem targetUpperConstructionFiveSixteenEventually_of_aggregateLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  ((matrix.aggregate T).lowerBound).eventualTarget A

theorem targetUpperConstructionFiveSixteenArbitrary_of_aggregateLowerBound
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ((matrix.aggregate T).lowerBound).arbitraryTarget A

theorem targetUpperConstructionFiveSixteen_of_aggregateExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  ((matrix.aggregate T).exactCandidate).exactTarget A

theorem targetUpperConstructionFiveSixteenEventually_of_aggregateExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  ((matrix.aggregate T).exactCandidate).eventualTarget A

theorem targetUpperConstructionFiveSixteenArbitrary_of_aggregateExactCandidate
    {T : Candidate}
    (A : AggregateFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  ((matrix.aggregate T).exactCandidate).arbitraryTarget A

end

end PeriodFinalIntegratedW11
end PachToth
end ErdosProblems1066
