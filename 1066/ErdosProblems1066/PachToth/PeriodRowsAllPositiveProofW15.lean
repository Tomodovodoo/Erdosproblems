import ErdosProblems1066.PachToth.PeriodEquationConcreteW14
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.PeriodWordCertificates
import ErdosProblems1066.PachToth.PeriodEquationSearchW11

set_option autoImplicit false

/-!
# W15 all-positive period-row proof surface

This file owns the all-positive period-equation row step.  The existing W14
ledger can already inhabit the uniform all-same and all-opposite row families
once the corresponding transition fixes the exact base block.  Conversely,
the length-one member of any all-positive row family forces exactly one of
those base-fixing alternatives.  Thus the checked missing row family is not an
extra period theorem: it is precisely the unresolved same/opposite base-fixing
alternative for the chosen transition package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodRowsAllPositiveProofW15

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingeTransitions :=
  PeriodEquationConcreteW14.RoleHingeTransitions

abbrev PeriodRows :=
  PeriodEquationConcreteW14.ConcretePeriodEquationFields

abbrev Orientation :=
  OrientationData.BlockOrientation

abbrev TransitionFixesExactBase
    (T : RoleHingeTransitions) (orientation : Orientation) : Prop :=
  PeriodCertificateExamples.TransitionFixesBase
    T.toFigure2TransitionObligations
    BaseTransitionRealization.exactBase
    orientation

abbrev SameFixesExactBase (T : RoleHingeTransitions) : Prop :=
  TransitionFixesExactBase T OrientationData.BlockOrientation.same

abbrev OppositeFixesExactBase (T : RoleHingeTransitions) : Prop :=
  TransitionFixesExactBase T OrientationData.BlockOrientation.opposite

abbrev BaseFixingAlternative (T : RoleHingeTransitions) : Prop :=
  SameFixesExactBase T \/ OppositeFixesExactBase T

/-! ## Inhabited row families when the base-fixing row is supplied -/

/-- The all-same all-positive rows, conditional on the same transition fixing
the exact base block. -/
def sameRows
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    PeriodRows :=
  PeriodEquationConcreteW14.allPositiveSameFields_of_transitionFixesExactBase
    T hfix

/-- The all-opposite all-positive rows, conditional on the opposite transition
fixing the exact base block. -/
def oppositeRows
    (T : RoleHingeTransitions)
    (hfix : OppositeFixesExactBase T) :
    PeriodRows :=
  PeriodEquationConcreteW14.allPositiveOppositeFields_of_transitionFixesExactBase
    T hfix

@[simp]
theorem sameRows_transitions
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T) :
    (sameRows T hfix).transitions = T :=
  rfl

@[simp]
theorem oppositeRows_transitions
    (T : RoleHingeTransitions)
    (hfix : OppositeFixesExactBase T) :
    (oppositeRows T hfix).transitions = T :=
  rfl

@[simp]
theorem sameRows_word
    (T : RoleHingeTransitions)
    (hfix : SameFixesExactBase T)
    (k : Nat) (hk : 0 < k) :
    (sameRows T hfix).word k hk =
      PeriodCertificateExamples.allPositiveSameWord k hk :=
  rfl

@[simp]
theorem oppositeRows_word
    (T : RoleHingeTransitions)
    (hfix : OppositeFixesExactBase T)
    (k : Nat) (hk : 0 < k) :
    (oppositeRows T hfix).word k hk =
      PeriodCertificateExamples.allPositiveOppositeWord k hk :=
  rfl

/-- A supplied base-fixing alternative is enough to inhabit the all-positive
period-row ledger over the chosen transition package. -/
theorem exists_rows_of_baseFixingAlternative
    (T : RoleHingeTransitions)
    (H : BaseFixingAlternative T) :
    exists P : PeriodRows, P.transitions = T := by
  rcases H with hsame | hopposite
  · exact ⟨sameRows T hsame, rfl⟩
  · exact ⟨oppositeRows T hopposite, rfl⟩

/-! ## Necessity of the same/opposite base-fixing row -/

/-- Any all-positive row package forces the same/opposite base-fixing
alternative at its length-one member. -/
theorem baseFixingAlternative_of_rows
    (P : PeriodRows) :
    BaseFixingAlternative P.transitions := by
  rcases P.lengthOne_forces_same_or_opposite_fixesExactBase with hsame | hopposite
  · exact Or.inl (by simpa [SameFixesExactBase, TransitionFixesExactBase] using hsame.2)
  · exact Or.inr (by
      simpa [OppositeFixesExactBase, TransitionFixesExactBase] using hopposite.2)

/-- The all-positive period-row package over a fixed transition package is
equivalent to the same/opposite exact-base fixing alternative. -/
theorem rows_exist_iff_baseFixingAlternative
    (T : RoleHingeTransitions) :
    (exists P : PeriodRows, P.transitions = T) <->
      BaseFixingAlternative T := by
  constructor
  · intro h
    rcases h with ⟨P, hT⟩
    cases hT
    exact baseFixingAlternative_of_rows P
  · exact exists_rows_of_baseFixingAlternative T

/-! ## Checked missing-row family -/

/-- The precise checked obstruction to all-positive period rows for a
transition package: neither uniform orientation fixes the exact base block. -/
structure MissingAllPositiveBaseFixingRows
    (T : RoleHingeTransitions) : Prop where
  same : Not (SameFixesExactBase T)
  opposite : Not (OppositeFixesExactBase T)

namespace MissingAllPositiveBaseFixingRows

theorem no_baseFixingAlternative
    {T : RoleHingeTransitions}
    (M : MissingAllPositiveBaseFixingRows T) :
    Not (BaseFixingAlternative T) := by
  intro H
  rcases H with hsame | hopposite
  · exact M.same hsame
  · exact M.opposite hopposite

/-- If both base-fixing alternatives are checked absent, then no
all-positive period-equation row package exists over that transition package. -/
theorem no_periodRows
    {T : RoleHingeTransitions}
    (M : MissingAllPositiveBaseFixingRows T) :
    Not (exists P : PeriodRows, P.transitions = T) := by
  intro h
  exact M.no_baseFixingAlternative
    ((rows_exist_iff_baseFixingAlternative T).1 h)

end MissingAllPositiveBaseFixingRows

/-- Expanded spelling of the exact missing row family.  A future concrete
search can close the W15 all-positive rows by proving either disjunct; a
failed search should instead supply both negated base-fixing rows above. -/
theorem precise_missing_family
    (T : RoleHingeTransitions) :
    (Not (exists P : PeriodRows, P.transitions = T)) <->
      MissingAllPositiveBaseFixingRows T := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hsame
      exact h ⟨sameRows T hsame, rfl⟩
    · intro hopposite
      exact h ⟨oppositeRows T hopposite, rfl⟩
  · intro M
    exact M.no_periodRows

end

end PeriodRowsAllPositiveProofW15
end PachToth
end ErdosProblems1066
