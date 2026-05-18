import ErdosProblems1066.PachToth.CrossBlockLowerBoundsInterface
import ErdosProblems1066.PachToth.PeriodEquationConcreteSearch
import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.OrientationWord

set_option autoImplicit false

/-!
# Concrete role-hinged period-search families

This module gives a concrete, reusable input shape for the role-hinged
period-search route.  The data is intentionally explicit: an orientation word
for each positive block count and the indexed algebraic period equations for
that word.  It then projects that data to the existing
`CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily`.

The remaining cross-block inequalities are kept as separate fields in the
`ConcreteCrossBlockFamily` wrapper below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcretePeriodSearchFamily

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions
abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily
abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F

/-- Concrete finite-word data for the role-hinged period-search family.

For every positive `k`, the fields supply a finite orientation word and the
exact indexed algebraic period equations for the corresponding generated
chain. -/
structure PeriodSearchData where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      PeriodSearchInterface.AlgebraicVertexPeriodEquation
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))
        (BlockPartition.localVertexEquivFin16.symm i)

namespace PeriodSearchData

/-- The raw generated-chain orientation function stored in a concrete family. -/
def orientation
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The finite period-search word attached to a concrete family member. -/
def finiteWord
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfWord hk (F.word k hk)

@[simp]
theorem finiteWord_length
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (F.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hk).letter i = F.orientation k hk i :=
  rfl

/-- Repackage the stored indexed equations in the candidate-family spelling
from `PeriodEquationConcreteSearch`. -/
def exactPeriodEquations
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationConcreteSearch.ExactPeriodEquations
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.word k hk) := by
  intro i
  simpa [PeriodWordCertificates.finiteOrientationWordOfWord,
    PeriodCertificateExamples.finiteOrientationWordOfWord]
    using F.equation k hk i

/-- The fixed-length period-equation candidate supplied by a concrete family
member. -/
def fixedCandidate
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodEquationConcreteSearch.FixedPeriodEquationCandidate
      F.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      k hk where
  word := F.word k hk
  equations := F.exactPeriodEquations k hk

@[simp]
theorem fixedCandidate_word
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (F.fixedCandidate k hk).word = F.word k hk :=
  rfl

/-- Project the concrete family to the reusable candidate-family machinery. -/
def toPeriodEquationCandidateFamily
    (F : PeriodSearchData) :
    PeriodEquationConcreteSearch.PeriodEquationCandidateFamily
      F.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase where
  candidate := F.fixedCandidate

@[simp]
theorem toPeriodEquationCandidateFamily_word
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    F.toPeriodEquationCandidateFamily.word k hk = F.word k hk :=
  rfl

/-- Build concrete period-search data from the candidate-family machinery. -/
def ofCandidateFamily
    (transitions : RoleHingeTransitions)
    (candidates :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase) :
    PeriodSearchData where
  transitions := transitions
  word := candidates.word
  equation := by
    intro k hk i
    simpa [PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.word,
      PeriodWordCertificates.finiteOrientationWordOfWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord]
      using candidates.equations k hk i

/-- Build concrete period-search data directly from finite words and the
exact `Fin 16` equation family, routed through `PeriodEquationConcreteSearch`. -/
def ofWordEquations
    (transitions : RoleHingeTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        PeriodEquationConcreteSearch.ExactPeriodEquations
          transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (word k hk)) :
    PeriodSearchData :=
  ofCandidateFamily transitions
    (PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.ofWordEquations
      word equations)

/-- Repackage the explicit indexed equations as the certificate expected by
`RoleHingedPeriodSearchFamily`. -/
def indexedCertificate
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      F.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (ExactFamilyClosure.finiteOrientationWord k hk
        (F.orientation k hk)) where
  equation := by
    intro i
    simpa [ExactFamilyClosure.finiteOrientationWord, finiteWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord,
      orientation]
      using F.equation k hk i

/-- The generated closure equation obtained from the concrete period
certificate for one positive block count. -/
def closure
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (F.fixedCandidate k hk).generatedClosureEquation

/-- The generated final-block period equation obtained from the concrete
algebraic certificate. -/
def periodEquation
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (F.fixedCandidate k hk).generatedPeriodEquation

/-- The downstream generated-period hypothesis obtained from the concrete
candidate equations. -/
def generatedPeriod
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (F.fixedCandidate k hk).generatedPeriod

/-- Project concrete word-and-equation data to the current role-hinged
period-search interface. -/
def toRoleHingedPeriodSearchFamily
    (F : PeriodSearchData) :
    RoleHingedPeriodSearchFamily where
  transitions := F.transitions
  orientation := F.orientation
  period := F.indexedCertificate

@[simp]
theorem toRoleHingedPeriodSearchFamily_transitions
    (F : PeriodSearchData) :
    F.toRoleHingedPeriodSearchFamily.transitions = F.transitions :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_orientation
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    F.toRoleHingedPeriodSearchFamily.orientation k hk =
      F.orientation k hk :=
  rfl

/-- A concrete period-search family gives the role-hinged generated-closure
family once generated separation is supplied. -/
def toRoleHingedGeneratedClosureFamily
    (F : PeriodSearchData)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          F.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (F.orientation k hk)) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily where
  transitions := F.transitions
  orientation := F.orientation
  closure := F.closure
  separated := separated

end PeriodSearchData

/-- Concrete period-search data plus the remaining cross-block lower-bound
table and inequalities. -/
structure ConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j -> 1 <= lower k hk i u j v
  lower_bound :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          lower k hk i u j v <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint
                periodSearch.transitions.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (periodSearch.orientation k hk)
                i u)
              (GeneratedClosedChain.generatedPoint
                periodSearch.transitions.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (periodSearch.orientation k hk)
                j v)

namespace ConcreteCrossBlockFamily

/-- Build the concrete cross-block family directly from finite words, exact
candidate equations, and pointwise cross-block lower-bound inequalities. -/
def ofWordEquationsAndLowerBounds
    (transitions : RoleHingeTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        PeriodEquationConcreteSearch.ExactPeriodEquations
          transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (word k hk))
    (lower :
      forall (k : Nat), 0 < k ->
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (lower_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j -> 1 <= lower k hk i u j v)
    (lower_bound :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j ->
            lower k hk i u j v <=
              _root_.eucDist
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  i u)
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  j v)) :
    ConcreteCrossBlockFamily where
  periodSearch :=
    PeriodSearchData.ofWordEquations transitions word equations
  lower := lower
  lower_ge_one := lower_ge_one
  lower_bound := by
    intro k hk i u j v hij
    simpa [PeriodSearchData.ofWordEquations,
      PeriodSearchData.ofCandidateFamily, PeriodSearchData.orientation,
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.ofWordEquations,
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.word]
      using lower_bound k hk i u j v hij

/-- Forget concrete words to the period-search family expected by the
cross-block lower-bound interface. -/
def toRoleHingedPeriodSearchFamily
    (F : ConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  F.periodSearch.toRoleHingedPeriodSearchFamily

/-- Project the explicit concrete lower-bound fields to the existing
cross-block lower-bound interface. -/
def toCrossBlockLowerBounds
    (F : ConcreteCrossBlockFamily) :
    CrossBlockLowerBounds F.toRoleHingedPeriodSearchFamily where
  lower := F.lower
  lower_ge_one := F.lower_ge_one
  lower_bound := by
    intro k hk i u j v hij
    exact F.lower_bound k hk i u j v hij

/-- Generated global separation obtained from the explicit cross-block
lower-bound fields and the checked exact-base same-block facts. -/
def separated
    (F : ConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk) :=
  F.toCrossBlockLowerBounds.separated k hk

/-- The generated-period hypothesis obtained from the candidate-family
period equations. -/
def generatedPeriod
    (F : ConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      F.periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk) :=
  F.periodSearch.generatedPeriod k hk

/-- Reduced metric hypotheses obtained from the concrete cross-block
inequalities and the checked exact-base role-hinge metric facts. -/
def reducedMetricHypotheses
    (F : ConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk) :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    F.periodSearch.transitions hk (F.periodSearch.orientation k hk)
    (F.separated k hk)

/-- Forget the concrete family to the generated-chain interface consumed by
the generated-period target route. -/
def toGeneratedChainFamily
    (F : ConcreteCrossBlockFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => F.periodSearch.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.periodSearch.orientation

/-- Period hypotheses for the generated-chain route, obtained from the
candidate-family period equations. -/
def generatedPeriods
    (F : ConcreteCrossBlockFamily) :
    F.toGeneratedChainFamily.Periods :=
  fun k hk => F.generatedPeriod k hk

/-- Reduced generated metric hypotheses for the generated-chain route. -/
def toReducedMetricHypotheses
    (F : ConcreteCrossBlockFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      F.toGeneratedChainFamily where
  metric := F.reducedMetricHypotheses

/-- The role-hinged generated-closure family obtained from the concrete
period-search and cross-block data. -/
def toRoleHingedGeneratedClosureFamily
    (F : ConcreteCrossBlockFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  F.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

/-- Exact-block target at a chosen positive period length, routed through the
generated-period theorem consumed downstream. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (F : ConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteenAt_exactBlock_reduced
      F.periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk)
      (F.generatedPeriod k hk)
      (F.reducedMetricHypotheses k hk)

/-- Exact-multiple Pach-Toth target, routed through generated periods and the
reduced generated-chain metric interface. -/
theorem targetUpperConstructionFiveSixteen_viaGeneratedPeriod
    (F : ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteen_of_family_reduced
      F.toGeneratedChainFamily F.generatedPeriods F.toReducedMetricHypotheses

/-- Exact-multiple Pach-Toth target from concrete period-search data and
explicit cross-block lower-bound inequalities. -/
theorem targetUpperConstructionFiveSixteen
    (F : ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach-Toth target routed through the generated-period exact
target and the checked small cases already imported by `ExactFamilyClosure`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_viaGeneratedPeriod
    (F : ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      F.targetUpperConstructionFiveSixteen_viaGeneratedPeriod

/-- Arbitrary-`n` Pach-Toth target from concrete period-search data,
explicit cross-block lower-bound inequalities, and the checked small cases
already imported by `ExactFamilyClosure`. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

/-- Exact-block target directly from finite word equations and pointwise
cross-block lower-bound inequalities. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_ofWordEquationsAndLowerBounds
    (transitions : RoleHingeTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        PeriodEquationConcreteSearch.ExactPeriodEquations
          transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (word k hk))
    (lower :
      forall (k : Nat), 0 < k ->
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (lower_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j -> 1 <= lower k hk i u j v)
    (lower_bound :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j ->
            lower k hk i u j v <=
              _root_.eucDist
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  i u)
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  j v))
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  (ofWordEquationsAndLowerBounds
    transitions word equations lower lower_ge_one lower_bound)
      |>.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact-multiple Pach-Toth target directly from finite word equations and
pointwise cross-block lower-bound inequalities, routed through generated
periods. -/
theorem targetUpperConstructionFiveSixteen_viaGeneratedPeriod_ofWordEquationsAndLowerBounds
    (transitions : RoleHingeTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        PeriodEquationConcreteSearch.ExactPeriodEquations
          transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (word k hk))
    (lower :
      forall (k : Nat), 0 < k ->
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (lower_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j -> 1 <= lower k hk i u j v)
    (lower_bound :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j ->
            lower k hk i u j v <=
              _root_.eucDist
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  i u)
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  j v)) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (ofWordEquationsAndLowerBounds
    transitions word equations lower lower_ge_one lower_bound)
      |>.targetUpperConstructionFiveSixteen_viaGeneratedPeriod

/-- Arbitrary-`n` Pach-Toth target directly from finite word equations and
pointwise cross-block lower-bound inequalities, routed through generated
periods and the checked small cases. -/
theorem targetUpperConstructionFiveSixteenArbitrary_viaGeneratedPeriod_ofWordEquationsAndLowerBounds
    (transitions : RoleHingeTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        PeriodEquationConcreteSearch.ExactPeriodEquations
          transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (word k hk))
    (lower :
      forall (k : Nat), 0 < k ->
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (lower_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j -> 1 <= lower k hk i u j v)
    (lower_bound :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
          Ne i j ->
            lower k hk i u j v <=
              _root_.eucDist
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  i u)
                (GeneratedClosedChain.generatedPoint
                  transitions.toFigure2TransitionObligations
                  hk
                  BaseTransitionRealization.exactBase
                  ((word k hk).toFin)
                  j v)) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (ofWordEquationsAndLowerBounds
    transitions word equations lower lower_ge_one lower_bound)
      |>.targetUpperConstructionFiveSixteenArbitrary_viaGeneratedPeriod

end ConcreteCrossBlockFamily

end

end ConcretePeriodSearchFamily
end PachToth
end ErdosProblems1066
