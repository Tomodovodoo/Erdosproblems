import ErdosProblems1066.PachToth.PeriodClosureSourceW21
import ErdosProblems1066.PachToth.PeriodEquationConcreteW14
import ErdosProblems1066.PachToth.PeriodRowsAllPositiveProofW15
import ErdosProblems1066.PachToth.ConcretePeriodWordSearch
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.PeriodBaseFixingSameW16
import ErdosProblems1066.PachToth.PeriodBaseFixingOppositeW16
import ErdosProblems1066.PachToth.PeriodBaseFixingCertificateW16
import ErdosProblems1066.PachToth.PeriodCandidateCompatibilityW18

set_option autoImplicit false

/-!
# W22 period-equation source fields

This file works directly with
`PeriodClosureSourceW21.PeriodEquationSourceFields`.  The main point is that,
over the checked exact base and a fixed role-hinge transition package, those
W21 fields are exactly the W14 concrete all-positive period rows.  Therefore
the W15 same/opposite base-fixing alternative is not merely sufficient: it is
equivalent to inhabiting the W21 source-field type.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodEquationSourceFieldsW22

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev TransitionObligations :=
  PeriodClosureSourceW21.TransitionObligations

abbrev SourceFields :=
  PeriodClosureSourceW21.PeriodEquationSourceFields

abbrev ClosureSource :=
  PeriodClosureSourceW21.ClosureSource

abbrev CandidateFamily :=
  PeriodEquationConcreteSearch.PeriodEquationCandidateFamily

abbrev AllPositivePeriodWordFamily :=
  PeriodWordCertificates.AllPositivePeriodWordFamily

abbrev CheckedWordFamily :=
  ConcretePeriodWordSearch.CheckedWordFamily

abbrev RoleHingeTransitions :=
  PeriodRowsAllPositiveProofW15.RoleHingeTransitions

abbrev PeriodRows :=
  PeriodEquationConcreteW14.ConcretePeriodEquationFields

abbrev BaseFixingAlternative :=
  PeriodRowsAllPositiveProofW15.BaseFixingAlternative

abbrev SameFixesExactBase :=
  PeriodRowsAllPositiveProofW15.SameFixesExactBase

abbrev OppositeFixesExactBase :=
  PeriodRowsAllPositiveProofW15.OppositeFixesExactBase

abbrev MissingBaseFixingRows :=
  PeriodRowsAllPositiveProofW15.MissingAllPositiveBaseFixingRows

def exactBase : LocalVertex -> R2 :=
  BaseTransitionRealization.exactBase

@[simp]
theorem exactBase_eq :
    exactBase = BaseTransitionRealization.exactBase :=
  rfl

abbrev ExactBaseSourceFields (O : TransitionObligations) :=
  SourceFields O exactBase

abbrev RoleHingeSourceFields (T : RoleHingeTransitions) :=
  SourceFields T.toFigure2TransitionObligations exactBase

/-! ## Equivalences with the existing word and candidate surfaces -/

def toAllPositivePeriodWordFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : SourceFields O base) :
    AllPositivePeriodWordFamily O base where
  word := S.word
  equation := S.equations

def ofAllPositivePeriodWordFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base) :
    SourceFields O base where
  word := F.word
  equations := F.equation

@[simp]
theorem ofAllPositivePeriodWordFamily_toAllPositivePeriodWordFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : SourceFields O base) :
    ofAllPositivePeriodWordFamily (toAllPositivePeriodWordFamily S) = S := by
  cases S
  rfl

@[simp]
theorem toAllPositivePeriodWordFamily_ofAllPositivePeriodWordFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : AllPositivePeriodWordFamily O base) :
    toAllPositivePeriodWordFamily (ofAllPositivePeriodWordFamily F) = F := by
  cases F
  rfl

def sourceFieldsEquivAllPositivePeriodWordFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2) :
    Equiv (SourceFields O base) (AllPositivePeriodWordFamily O base) where
  toFun := toAllPositivePeriodWordFamily
  invFun := ofAllPositivePeriodWordFamily
  left_inv := ofAllPositivePeriodWordFamily_toAllPositivePeriodWordFamily
  right_inv := toAllPositivePeriodWordFamily_ofAllPositivePeriodWordFamily

def ofCandidateFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CandidateFamily O base) :
    SourceFields O base where
  word := F.word
  equations := F.equations

@[simp]
theorem ofCandidateFamily_toCandidateFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : SourceFields O base) :
    ofCandidateFamily S.toCandidateFamily = S := by
  cases S
  rfl

@[simp]
theorem toCandidateFamily_ofCandidateFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (F : CandidateFamily O base) :
    (ofCandidateFamily F).toCandidateFamily = F := by
  cases F
  rfl

def sourceFieldsEquivCandidateFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2) :
    Equiv (SourceFields O base) (CandidateFamily O base) where
  toFun := fun S => S.toCandidateFamily
  invFun := ofCandidateFamily
  left_inv := ofCandidateFamily_toCandidateFamily
  right_inv := toCandidateFamily_ofCandidateFamily

def toCheckedWordFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : SourceFields O base) :
    CheckedWordFamily O base where
  word := S.word
  closure := by
    intro k hk
    exact
      PeriodWordCertificates.generatedPeriodEquationOfWord
        O hk base (S.word k hk) (S.equations k hk)

theorem toCheckedWordFamily_generatedPeriodEquation
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : SourceFields O base)
    (k : Nat) (hk : 0 < k) :
    (toCheckedWordFamily S).generatedPeriodEquation k hk =
      PeriodWordCertificates.generatedPeriodEquationOfWord
        O hk base (S.word k hk) (S.equations k hk) :=
  rfl

/-! ## Exact-base W14 row equivalence -/

def sourceFieldsOfPeriodRows
    (P : PeriodRows) :
    SourceFields
      P.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase where
  word := P.word
  equations := P.exactPeriodEquations

@[simp]
theorem sourceFieldsOfPeriodRows_word
    (P : PeriodRows)
    (k : Nat) (hk : 0 < k) :
    (sourceFieldsOfPeriodRows P).word k hk = P.word k hk :=
  rfl

def periodRowsOfSourceFields
    (T : RoleHingeTransitions)
    (S : RoleHingeSourceFields T) :
    PeriodRows where
  transitions := T
  word := S.word
  equation := by
    intro k hk i
    simpa [PeriodEquationConcreteW14.AlgebraicEquationRow,
      exactBase, PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord]
      using S.equations k hk i

@[simp]
theorem periodRowsOfSourceFields_transitions
    (T : RoleHingeTransitions)
    (S : RoleHingeSourceFields T) :
    (periodRowsOfSourceFields T S).transitions = T :=
  rfl

@[simp]
theorem periodRowsOfSourceFields_word
    (T : RoleHingeTransitions)
    (S : RoleHingeSourceFields T)
    (k : Nat) (hk : 0 < k) :
    (periodRowsOfSourceFields T S).word k hk = S.word k hk :=
  rfl

theorem nonempty_sourceFields_iff_exists_periodRows
    (T : RoleHingeTransitions) :
    Nonempty (RoleHingeSourceFields T) <->
      exists P : PeriodRows, P.transitions = T := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Exists.intro (periodRowsOfSourceFields T S) rfl
  case mpr =>
    intro h
    cases h with
    | intro P hP =>
        cases hP
        exact Nonempty.intro (sourceFieldsOfPeriodRows P)

theorem sourceFields_iff_baseFixingAlternative
    (T : RoleHingeTransitions) :
    Nonempty (RoleHingeSourceFields T) <->
      BaseFixingAlternative T := by
  exact
    (nonempty_sourceFields_iff_exists_periodRows T).trans
      (PeriodRowsAllPositiveProofW15.rows_exist_iff_baseFixingAlternative T)

/-! ## Explicit same/opposite constructors -/

def sameSourceFields
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    RoleHingeSourceFields T where
  word := PeriodCertificateExamples.allPositiveSameWord
  equations := by
    intro k hk i
    simpa [exactBase, PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord]
      using
        PeriodCertificateExamples.allPositiveSameEquations
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase hfix k hk i

def oppositeSourceFields
    (T : RoleHingeTransitions)
    (hfix : OppositeFixesExactBase T) :
    RoleHingeSourceFields T where
  word := PeriodCertificateExamples.allPositiveOppositeWord
  equations := by
    intro k hk i
    simpa [exactBase, PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord]
      using
        PeriodCertificateExamples.allPositiveOppositeEquations
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase hfix k hk i

@[simp]
theorem sameSourceFields_word
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T)
    (k : Nat) (hk : 0 < k) :
    (sameSourceFields T hfix).word k hk =
      PeriodCertificateExamples.allPositiveSameWord k hk :=
  rfl

@[simp]
theorem oppositeSourceFields_word
    (T : RoleHingeTransitions)
    (hfix : OppositeFixesExactBase T)
    (k : Nat) (hk : 0 < k) :
    (oppositeSourceFields T hfix).word k hk =
      PeriodCertificateExamples.allPositiveOppositeWord k hk :=
  rfl

theorem sourceFields_of_baseFixingAlternative
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    Nonempty (RoleHingeSourceFields T) := by
  cases H with
  | inl hsame =>
    exact Nonempty.intro (sameSourceFields T hsame)
  | inr hopposite =>
    exact Nonempty.intro (oppositeSourceFields T hopposite)

theorem baseFixingAlternative_of_sourceFields
    (T : RoleHingeTransitions)
    (S : RoleHingeSourceFields T) :
    BaseFixingAlternative T :=
  (sourceFields_iff_baseFixingAlternative T).1 (Nonempty.intro S)

/-! ## No-go forms for the reduced source-field target -/

theorem not_sourceFields_of_missingBaseFixingRows
    {T : RoleHingeTransitions}
    (M : MissingBaseFixingRows T) :
    RoleHingeSourceFields T -> False := by
  intro S
  exact M.no_baseFixingAlternative
    (baseFixingAlternative_of_sourceFields T S)

theorem not_sourceFields_iff_missingBaseFixingRows
    (T : RoleHingeTransitions) :
    (RoleHingeSourceFields T -> False) <-> MissingBaseFixingRows T := by
  constructor
  case mp =>
    intro h
    constructor
    case same =>
      intro hsame
      exact h (sameSourceFields T hsame)
    case opposite =>
      intro hopposite
      exact h (oppositeSourceFields T hopposite)
  case mpr =>
    exact not_sourceFields_of_missingBaseFixingRows

theorem not_nonempty_sourceFields_iff_missingBaseFixingRows
    (T : RoleHingeTransitions) :
    Not (Nonempty (RoleHingeSourceFields T)) <->
      MissingBaseFixingRows T := by
  constructor
  case mp =>
    intro h
    exact (not_sourceFields_iff_missingBaseFixingRows T).1
      (fun S => h (Nonempty.intro S))
  case mpr =>
    intro M h
    cases h with
    | intro S =>
        exact not_sourceFields_of_missingBaseFixingRows M S

theorem no_sourceFields_of_not_baseFixingAlternative
    {T : RoleHingeTransitions}
    (hno : Not (BaseFixingAlternative T)) :
    RoleHingeSourceFields T -> False := by
  intro S
  exact hno (baseFixingAlternative_of_sourceFields T S)

theorem false_of_roleHingeSourceFields
    (T : RoleHingeTransitions)
    (_S : RoleHingeSourceFields T) :
    False :=
  PeriodBaseFixingSameW16.false_of_roleHingeTransitions_same T

theorem not_roleHingeSourceFields
    (T : RoleHingeTransitions) :
    RoleHingeSourceFields T -> False :=
  false_of_roleHingeSourceFields T

theorem not_exists_roleHingeSourceFields :
    Not (exists T : RoleHingeTransitions, Nonempty (RoleHingeSourceFields T)) := by
  intro h
  cases h with
  | intro T hS =>
      cases hS with
      | intro S =>
          exact false_of_roleHingeSourceFields T S

end

end PeriodEquationSourceFieldsW22
end PachToth
end ErdosProblems1066
