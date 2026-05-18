import ErdosProblems1066.PachToth.ConcretePeriodWordSearch
import ErdosProblems1066.PachToth.RoleHingeCandidateSearchSurface

set_option autoImplicit false

/-!
# W9 candidate period-family data for flexible role-hinge branches

This module is a search-facing bridge between the closure-checked finite-word
surface in `ConcretePeriodWordSearch` and the flexible role-hinge candidate
surface in `RoleHingeCandidateSearchSurface`.

It deliberately stops at generated period/closure data.  Producing the
Pach--Toth target still requires the separate lower-table/global-separation
data consumed by the metric interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodFamilyCandidateSearchW9

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev Candidate :=
  RoleHingeCandidateSearchSurface.SameOppositeCandidate
abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations
abbrev Orientation :=
  OrientationData.BlockOrientation
abbrev FiniteOrientationWord :=
  PeriodSearchInterface.FiniteOrientationWord

/-! ## Generated-period equation families -/

/-- Explicit generated final-block period equations for one flexible
role-hinge candidate and one finite word. -/
abbrev ExplicitGeneratedPeriodEquation
    (T : Candidate)
    {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) : Prop :=
  ConcretePeriodWordSearch.ExactBaseWordCandidateClosureEquation
    T.toFigure2TransitionObligations hk W

/-- A reusable period-family candidate whose stored equations are already the
generated final-block period equations.

This is the lightest reusable payload for downstream generated-chain routes:
one word for each positive length and the exact period equation for that word.
-/
structure ClosureEquationFamilyData (T : Candidate) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  periodEquation :
    forall (k : Nat) (hk : 0 < k),
      ExplicitGeneratedPeriodEquation T hk (word k hk)

namespace ClosureEquationFamilyData

/-- Raw generated-chain orientation for one family member. -/
def orientation
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The finite word associated to one family member. -/
def finiteWord
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    FiniteOrientationWord :=
  PeriodWordCertificates.finiteOrientationWordOfWord hk (F.word k hk)

@[simp]
theorem finiteWord_length
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    (F.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hk).letter i = F.orientation k hk i :=
  rfl

/-- Repackage explicit generated-period equations through the checked-word
surface. -/
def toCheckedWordFamily
    {T : Candidate}
    (F : ClosureEquationFamilyData T) :
    ConcretePeriodWordSearch.ExactBaseCheckedWordFamily
      T.toFigure2TransitionObligations where
  word := F.word
  closure := F.periodEquation

/-- Generated final-block period equation for one family member, projected
from the explicit equations. -/
theorem generatedPeriodEquation
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.toCheckedWordFamily).generatedPeriodEquation k hk

/-- Algebraic generated closure equation for one family member, projected
from the same explicit period equations. -/
theorem generatedClosureEquation
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.toCheckedWordFamily).generatedClosureEquation k hk

/-- Downstream generated-period hypothesis for one family member. -/
theorem generatedPeriod
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.toCheckedWordFamily).generatedPeriod k hk

/-- Generated-chain family associated to the closure-equation payload. -/
def toGeneratedChainFamily
    {T : Candidate}
    (F : ClosureEquationFamilyData T) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => T.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

@[simp]
theorem toGeneratedChainFamily_O
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.O k hk =
      T.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem toGeneratedChainFamily_base
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toGeneratedChainFamily_orientation
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    F.toGeneratedChainFamily.orientation k hk =
      F.orientation k hk :=
  rfl

/-- Period hypotheses for the generated-chain family, projected from the
explicit equations. -/
theorem periods
    {T : Candidate}
    (F : ClosureEquationFamilyData T) :
    F.toGeneratedChainFamily.Periods :=
  fun k hk => F.generatedPeriod k hk

/-- Build the flexible generated-closure family once the separate global
separation data has been supplied.  This is intentionally not a target
theorem: lower-table/metric data remains an explicit input. -/
def toFlexibleGeneratedClosureFamily
    {T : Candidate}
    (F : ClosureEquationFamilyData T)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (F.orientation k hk)) :
    FlexibleExactLocalTransition.GeneratedClosureFamily where
  transitions := T.toFlexibleSameOpposite
  orientation := F.orientation
  closure := by
    intro k hk
    simpa using F.generatedClosureEquation k hk
  separated := by
    intro k hk
    simpa using separated k hk

end ClosureEquationFamilyData

/-! ## Algebraic finite-equation families -/

/-- Exact `Fin 16` algebraic equations for one word over a flexible
role-hinge candidate. -/
abbrev ExplicitAlgebraicPeriodEquations
    (T : Candidate)
    {k : Nat} (hk : 0 < k)
    (W : OrientationWord.Word k) : Prop :=
  RoleHingeCandidateSearchSurface.ExactPeriodEquations T hk W

/-- Search-output period-family data with explicit indexed algebraic
equations for every positive period length. -/
structure AlgebraicEquationFamilyData (T : Candidate) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equations :
    forall (k : Nat) (hk : 0 < k),
      ExplicitAlgebraicPeriodEquations T hk (word k hk)

namespace AlgebraicEquationFamilyData

/-- Raw generated-chain orientation for one family member. -/
def orientation
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The role-hinge candidate-search period data obtained from the explicit
algebraic equations. -/
def toSearchSurfacePeriodData
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T) :
    RoleHingeCandidateSearchSurface.PeriodSearchData T where
  word := F.word
  equation := F.equations

@[simp]
theorem toSearchSurfacePeriodData_orientation
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    F.toSearchSurfacePeriodData.orientation k hk =
      F.orientation k hk :=
  rfl

/-- Forget the algebraic equations to the generated-period equation payload. -/
def toClosureEquationFamilyData
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T) :
    ClosureEquationFamilyData T where
  word := F.word
  periodEquation := fun k hk =>
    (F.toSearchSurfacePeriodData).periodEquation k hk

/-- Generated final-block period equation for one family member, projected
from the explicit indexed algebraic equations. -/
theorem generatedPeriodEquation
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.toSearchSurfacePeriodData).periodEquation k hk

/-- Algebraic generated closure equation for one family member, projected
from the explicit indexed algebraic equations. -/
theorem generatedClosureEquation
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.toSearchSurfacePeriodData).closure k hk

/-- Downstream generated-period hypothesis for one family member. -/
theorem generatedPeriod
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.toSearchSurfacePeriodData).generatedPeriod k hk

/-- The generated-chain family attached to the algebraic-equation payload. -/
def toGeneratedChainFamily
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  (F.toClosureEquationFamilyData).toGeneratedChainFamily

/-- Period hypotheses for the generated-chain family, projected from the
explicit indexed algebraic equations. -/
theorem periods
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T) :
    F.toGeneratedChainFamily.Periods :=
  (F.toClosureEquationFamilyData).periods

/-- Build the flexible generated-closure family once the separate global
separation data has been supplied. -/
def toFlexibleGeneratedClosureFamily
    {T : Candidate}
    (F : AlgebraicEquationFamilyData T)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (F.orientation k hk)) :
    FlexibleExactLocalTransition.GeneratedClosureFamily :=
  (F.toClosureEquationFamilyData).toFlexibleGeneratedClosureFamily separated

end AlgebraicEquationFamilyData

end

end PeriodFamilyCandidateSearchW9
end PachToth
end ErdosProblems1066
