import ErdosProblems1066.PachToth.NonRigidPeriodCandidateW10
import ErdosProblems1066.PachToth.PeriodFamilyCandidateSearchW9
import ErdosProblems1066.PachToth.ConcretePeriodWordSearch
import ErdosProblems1066.PachToth.PeriodCandidateTargetRoute

set_option autoImplicit false

/-!
# W11 period-equation search surface

This module records the W11-facing search payloads for non-rigid closed
chains.  It does not manufacture a concrete period.  Instead it makes the
checked word/equation packages, their projections to generated-period
families, and the exact remaining candidate fields explicit.  It also records
ledger shapes for failed finite words, so a search run can narrow the missing
period equations without closing the target theorem.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodEquationSearchW11

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev Candidate := NonRigidPeriodCandidateW10.Candidate
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev Orientation := OrientationData.BlockOrientation
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord
abbrev AlgebraicFamily (T : Candidate) :=
  PeriodFamilyCandidateSearchW9.AlgebraicEquationFamilyData T
abbrev ClosureFamily (T : Candidate) :=
  PeriodFamilyCandidateSearchW9.ClosureEquationFamilyData T
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions
abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex
abbrev SmallCandidateTag :=
  PeriodEquationConcreteSearch.SmallWords.CandidateTag

/-! ## Checked finite words -/

/-- Exact-base algebraic period equations for one candidate and one word. -/
abbrev CandidateWordEquations
    (T : Candidate)
    {k : Nat} (hk : 0 < k)
    (word : OrientationWord.Word k) : Prop :=
  PeriodWordCertificates.AlgebraicEquationsForWord
    T.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    word

/-- One checked finite word together with the exact indexed period equations
for the candidate transition data. -/
structure CheckedWordEquationPackage (T : Candidate) where
  length : Nat
  positive_length : 0 < length
  word : OrientationWord.Word length
  equations : CandidateWordEquations T positive_length word

namespace CheckedWordEquationPackage

def orientation
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    Fin P.length -> Orientation :=
  P.word.toFin

@[simp]
theorem orientation_apply
    {T : Candidate}
    (P : CheckedWordEquationPackage T) (i : Fin P.length) :
    P.orientation i = P.word i :=
  rfl

def finiteWord
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord
    P.positive_length P.word

@[simp]
theorem finiteWord_length
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    P.finiteWord.length = P.length :=
  rfl

@[simp]
theorem finiteWord_letter
    {T : Candidate}
    (P : CheckedWordEquationPackage T) (i : Fin P.length) :
    P.finiteWord.letter i = P.orientation i :=
  rfl

def fixedPeriodEquationCandidate
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    PeriodEquationConcreteSearch.FixedPeriodEquationCandidate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      P.length
      P.positive_length where
  word := P.word
  equations := P.equations

def checkedWordCandidate
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    ConcretePeriodWordSearch.ExactBaseCheckedWordCandidate
      T.toFigure2TransitionObligations :=
  ConcretePeriodWordSearch.CheckedWordCandidate.ofFixedPeriodEquationCandidate
    P.fixedPeriodEquationCandidate

def indexedAlgebraicCertificate
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      P.finiteWord :=
  P.fixedPeriodEquationCandidate.indexedAlgebraicCertificate

def periodSearchCertificate
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    PeriodSearchInterface.PeriodSearchCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase :=
  P.fixedPeriodEquationCandidate.toPeriodSearchCertificate

theorem generatedClosureEquation
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations
      P.positive_length
      BaseTransitionRealization.exactBase
      P.orientation :=
  P.fixedPeriodEquationCandidate.generatedClosureEquation

theorem generatedPeriodEquation
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations
      P.positive_length
      BaseTransitionRealization.exactBase
      P.orientation :=
  P.fixedPeriodEquationCandidate.generatedPeriodEquation

theorem generatedPeriod
    {T : Candidate}
    (P : CheckedWordEquationPackage T) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations
      P.positive_length
      BaseTransitionRealization.exactBase
      P.orientation :=
  P.fixedPeriodEquationCandidate.generatedPeriod

def generatedClosureData
    {T : Candidate}
    (P : CheckedWordEquationPackage T)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        P.positive_length
        BaseTransitionRealization.exactBase
        P.orientation) :
    FlexibleExactLocalTransition.GeneratedClosureData
      P.length P.positive_length where
  transitions := T.toFlexibleSameOpposite
  orientation := P.orientation
  closure := by
    simpa using P.generatedClosureEquation
  separated := by
    simpa using separated

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {T : Candidate}
    (P : CheckedWordEquationPackage T)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        P.positive_length
        BaseTransitionRealization.exactBase
        P.orientation) :
    targetUpperConstructionFiveSixteenAt (16 * P.length) :=
  (P.generatedClosureData separated)
    |>.targetUpperConstructionFiveSixteenAt_exactBlock

end CheckedWordEquationPackage

/-! ## Checked all-positive families -/

/-- Search output for every positive period length, keeping the word and the
exact indexed equations visible. -/
structure CheckedWordEquationFamily (T : Candidate) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equations :
    forall (k : Nat) (hk : 0 < k),
      CandidateWordEquations T hk (word k hk)

namespace CheckedWordEquationFamily

def orientation
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

def package
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (k : Nat) (hk : 0 < k) :
    CheckedWordEquationPackage T where
  length := k
  positive_length := hk
  word := F.word k hk
  equations := F.equations k hk

def toAlgebraicFamily
    {T : Candidate}
    (F : CheckedWordEquationFamily T) :
    AlgebraicFamily T where
  word := F.word
  equations := F.equations

def toClosureFamily
    {T : Candidate}
    (F : CheckedWordEquationFamily T) :
    ClosureFamily T :=
  F.toAlgebraicFamily.toClosureEquationFamilyData

def toCheckedWordFamily
    {T : Candidate}
    (F : CheckedWordEquationFamily T) :
    ConcretePeriodWordSearch.ExactBaseCheckedWordFamily
      T.toFigure2TransitionObligations :=
  F.toClosureFamily.toCheckedWordFamily

def toPeriodEquationCandidateFamily
    {T : Candidate}
    (F : CheckedWordEquationFamily T) :
    PeriodEquationConcreteSearch.PeriodEquationCandidateFamily
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase :=
  PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.ofWordEquations
    F.word F.equations

def toGeneratedChainFamily
    {T : Candidate}
    (F : CheckedWordEquationFamily T) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  F.toAlgebraicFamily.toGeneratedChainFamily

theorem generatedClosureEquation
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  F.toAlgebraicFamily.generatedClosureEquation k hk

theorem generatedPeriodEquation
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  F.toAlgebraicFamily.generatedPeriodEquation k hk

theorem generatedPeriod
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  F.toAlgebraicFamily.generatedPeriod k hk

theorem periods
    {T : Candidate}
    (F : CheckedWordEquationFamily T) :
    F.toGeneratedChainFamily.Periods :=
  F.toAlgebraicFamily.periods

def toFlexibleFamilyFields
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (F.orientation k hk)) :
    NonRigidPeriodCandidateW10.FlexibleFamilyFields T where
  period := F.toAlgebraicFamily
  separated := by
    intro k hk
    simpa using separated k hk

def toFlexibleGeneratedClosureFamily
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (F.orientation k hk)) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  (F.toFlexibleFamilyFields separated).toFlexibleGeneratedClosureFamily

theorem targetUpperConstructionFiveSixteen
    {T : Candidate}
    (F : CheckedWordEquationFamily T)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (F.orientation k hk)) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (F.toFlexibleFamilyFields separated).targetUpperConstructionFiveSixteen

end CheckedWordEquationFamily

/-! ## Two-step checked package inherited from W10 -/

def twoStepPackage
    {T : Candidate}
    (D : NonRigidPeriodCandidateW10.TwoStepCheckedData T) :
    CheckedWordEquationPackage T where
  length := NonRigidPeriodCandidateW10.twoStepLength
  positive_length := NonRigidPeriodCandidateW10.twoStepPositive
  word := D.word
  equations := D.algebraicEquations

@[simp]
theorem twoStepPackage_word
    {T : Candidate}
    (D : NonRigidPeriodCandidateW10.TwoStepCheckedData T) :
    (twoStepPackage D).word = NonRigidPeriodCandidateW10.twoStepWord :=
  rfl

theorem twoStepPackage_generatedPeriodEquation
    {T : Candidate}
    (D : NonRigidPeriodCandidateW10.TwoStepCheckedData T) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations
      NonRigidPeriodCandidateW10.twoStepPositive
      BaseTransitionRealization.exactBase
      (twoStepPackage D).orientation :=
  (twoStepPackage D).generatedPeriodEquation

/-! ## Exact remaining fields for candidate period data -/

/-- The flexible generated-chain fields that remain after a candidate
all-positive equation family has been checked. -/
structure GeneratedFamilyRemainingFields (T : Candidate) where
  period : CheckedWordEquationFamily T
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (period.orientation k hk)

namespace GeneratedFamilyRemainingFields

def toFlexibleFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    NonRigidPeriodCandidateW10.FlexibleFamilyFields T :=
  D.period.toFlexibleFamilyFields D.separated

def toFlexibleGeneratedClosureFamily
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  D.toFlexibleFamilyFields.toFlexibleGeneratedClosureFamily

theorem targetUpperConstructionFiveSixteen
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toFlexibleFamilyFields.targetUpperConstructionFiveSixteen

end GeneratedFamilyRemainingFields

/-- Exact-target route fields for a checked candidate period family.  These
are the remaining concrete transition equality, residual exact-local rows,
and non-connector lower tables consumed by the exact target route. -/
structure ExactCandidatePeriodFields (T : Candidate) where
  period : CheckedWordEquationFamily T
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
      ((NonRigidPeriodCandidateW10.concretePeriodSearchDataOfAlgebraicFamily
        transitions transition_eq period.toAlgebraicFamily)
          |>.toRoleHingedPeriodSearchFamily)

namespace ExactCandidatePeriodFields

def toExactTargetRouteFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    NonRigidPeriodCandidateW10.ExactTargetRouteFields
      T D.period.toAlgebraicFamily where
  transitions := D.transitions
  transition_eq := D.transition_eq
  concrete_eq := D.concrete_eq
  same_rest := D.same_rest
  opposite_rest := D.opposite_rest
  tables := D.tables

def periodSearch
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    ConcretePeriodSearchFamily.PeriodSearchData :=
  D.toExactTargetRouteFields.periodSearch

def toPeriodCandidateLowerTableData
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PeriodCandidateTargetRoute.PeriodCandidateLowerTableData :=
  D.toExactTargetRouteFields.toPeriodCandidateLowerTableData

def toMinimalExactTargetCertificate
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    ExactTargetCandidateClosure.MinimalExactTargetCertificate :=
  D.toExactTargetRouteFields.toMinimalExactTargetCertificate

theorem targetUpperConstructionFiveSixteen
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toExactTargetRouteFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  D.toExactTargetRouteFields.targetUpperConstructionFiveSixteenArbitrary

end ExactCandidatePeriodFields

/-! ## Obstruction ledgers for failed finite words -/

/-- A checked refutation of the exact equations for one candidate word. -/
structure WordEquationObstruction
    (T : Candidate)
    {k : Nat} (hk : 0 < k)
    (word : OrientationWord.Word k) where
  refutes : Not (CandidateWordEquations T hk word)

namespace WordEquationObstruction

theorem noPackageForWord
    {T : Candidate}
    {k : Nat} {hk : 0 < k}
    {word : OrientationWord.Word k}
    (B : WordEquationObstruction T hk word) :
  Not
      (exists C :
        PeriodEquationConcreteSearch.FixedPeriodEquationCandidate
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase
          k hk,
        C.word = word) := by
  intro h
  cases h with
  | intro C hword =>
    cases hword
    exact B.refutes C.equations

theorem noCheckedPackageWithWord
    {T : Candidate}
    {k : Nat} {hk : 0 < k}
    {word : OrientationWord.Word k}
    (B : WordEquationObstruction T hk word) :
    Not
      (exists P : CheckedWordEquationPackage T,
        P.length = k /\
        HEq P.positive_length hk /\
        HEq P.word word) := by
  intro h
  cases h with
  | intro P hrest =>
    cases hrest with
    | intro hlen hrest2 =>
      cases hrest2 with
      | intro hpos hword =>
        cases hlen
        cases hpos
        cases hword
        exact B.refutes P.equations

end WordEquationObstruction

/-- A finite small-word ledger: every tagged small word has a checked
refutation of its exact equation package. -/
structure SmallWordObstructionLedger (T : Candidate) where
  refutes :
    forall tag : SmallCandidateTag,
      Not
        (PeriodEquationConcreteSearch.SmallWords.CandidateTag.Equations
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase
          tag)

namespace SmallWordObstructionLedger

def obstruction
    {T : Candidate}
    (L : SmallWordObstructionLedger T)
    (tag : SmallCandidateTag) :
    WordEquationObstruction T tag.positiveLength tag.word where
  refutes := L.refutes tag

theorem noTaggedFixedCandidate
    {T : Candidate}
    (L : SmallWordObstructionLedger T)
    (tag : SmallCandidateTag) :
    Not
      (exists C :
        PeriodEquationConcreteSearch.FixedPeriodEquationCandidate
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase
          tag.length tag.positiveLength,
        C.word = tag.word) := by
  intro h
  cases h with
  | intro C hword =>
    have heq :
        PeriodEquationConcreteSearch.SmallWords.CandidateTag.Equations
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase
          tag := by
      simpa [hword] using C.equations
    exact L.refutes tag heq

theorem noTaggedCheckedPackage
    {T : Candidate}
    (L : SmallWordObstructionLedger T)
    (tag : SmallCandidateTag) :
    Not
      (exists P : CheckedWordEquationPackage T,
        P.length = tag.length /\
        HEq P.positive_length tag.positiveLength /\
        HEq P.word tag.word) :=
  (L.obstruction tag).noCheckedPackageWithWord

end SmallWordObstructionLedger

/-- A search ledger for a chosen all-positive word family.  It records the
first positive length where the exact equations fail, which blocks that
family from becoming a checked period family. -/
structure FamilyEquationObstruction
    (T : Candidate)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k) where
  length : Nat
  positive_length : 0 < length
  refutes :
    Not (CandidateWordEquations T positive_length
      (word length positive_length))

namespace FamilyEquationObstruction

theorem noCheckedFamily
    {T : Candidate}
    {word : forall (k : Nat), 0 < k -> OrientationWord.Word k}
    (B : FamilyEquationObstruction T word) :
    Not
      (exists F : CheckedWordEquationFamily T,
        forall (k : Nat) (hk : 0 < k), F.word k hk = word k hk) := by
  intro h
  cases h with
  | intro F hword =>
    have heq :
        CandidateWordEquations T B.positive_length
          (word B.length B.positive_length) := by
      simpa [hword B.length B.positive_length] using
        F.equations B.length B.positive_length
    exact B.refutes heq

end FamilyEquationObstruction

/-! ## W11 matrix -/

structure TargetProjectionRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

structure ExactBlockProjectionRow (alpha : Type) where
  exactBlock :
    alpha -> forall (k : Nat), 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k)
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen

def generatedFamilyRemainingFieldsRow
    (T : Candidate) :
    TargetProjectionRow (GeneratedFamilyRemainingFields T) where
  exactTarget := GeneratedFamilyRemainingFields.targetUpperConstructionFiveSixteen
  arbitraryTarget := fun D =>
    ArbitraryNClosureCandidate.arbitrary_of_exactTarget
      D.targetUpperConstructionFiveSixteen

def exactCandidatePeriodFieldsRow
    (T : Candidate) :
    TargetProjectionRow (ExactCandidatePeriodFields T) where
  exactTarget := ExactCandidatePeriodFields.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    ExactCandidatePeriodFields.targetUpperConstructionFiveSixteenArbitrary

structure SearchLedger where
  checkedWordPackages : Candidate -> Type
  checkedFamilyPackages : Candidate -> Type
  generatedFamilyFields : Candidate -> Type
  exactCandidateFields : Candidate -> Type
  smallWordObstructions : Candidate -> Prop
  familyObstructions :
    forall _T : Candidate,
      (forall (k : Nat), 0 < k -> OrientationWord.Word k) -> Type

def searchLedger : SearchLedger where
  checkedWordPackages := CheckedWordEquationPackage
  checkedFamilyPackages := CheckedWordEquationFamily
  generatedFamilyFields := GeneratedFamilyRemainingFields
  exactCandidateFields := ExactCandidatePeriodFields
  smallWordObstructions := SmallWordObstructionLedger
  familyObstructions := FamilyEquationObstruction

structure Matrix where
  ledger : SearchLedger
  generatedFamilyRows :
    forall T : Candidate,
      TargetProjectionRow (GeneratedFamilyRemainingFields T)
  exactCandidateRows :
    forall T : Candidate,
      TargetProjectionRow (ExactCandidatePeriodFields T)

def matrix : Matrix where
  ledger := searchLedger
  generatedFamilyRows := generatedFamilyRemainingFieldsRow
  exactCandidateRows := exactCandidatePeriodFieldsRow

theorem targetUpperConstructionFiveSixteen_of_generatedFamilyFields
    {T : Candidate}
    (D : GeneratedFamilyRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.generatedFamilyRows T).exactTarget D

theorem targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.exactCandidateRows T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
    {T : Candidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.exactCandidateRows T).arbitraryTarget D

end

end PeriodEquationSearchW11
end PachToth
end ErdosProblems1066
