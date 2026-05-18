import ErdosProblems1066.PachToth.ConnectorEquationClosure
import ErdosProblems1066.PachToth.ExactFamilyClosure
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart

set_option autoImplicit false

/-!
# Final conditional Pach--Toth facade

This module assembles the currently strongest honest conditional Pach--Toth
route from:

* finite period-search certificates,
* same/opposite transition maps whose connector unit edges are closed by the
  explicit connector equations, and
* quantitative cross-block lower bounds.

It does not assert that those certificates or lower-bound tables exist, and it
does not add public `KnownBounds` wrappers.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FinalConditional

open FiniteGraph
open GeneratedPeriodClosure

noncomputable section

abbrev R2 := Prod Real Real

/-- Equation-carried same/opposite transitions preserve same-block distances
after forgetting to the generated-chain Figure 2 transition interface. -/
theorem equationTransitions_preserveSameBlockDistances
    (T : ConnectorEquationClosure.SameOppositeEquationTransition) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      T.toFigure2TransitionObligations := by
  intro orientation source u v
  cases orientation
  · exact T.same.preserves_same_block_distances source u v
  · exact T.opposite.preserves_same_block_distances source u v

/-- One closed generated chain certified by period-search equations, equation
transitions, and cross-block lower bounds.  The target block count is the
period-search word length. -/
structure EquationPeriodSearchCrossBlockCertificate where
  transitions : ConnectorEquationClosure.SameOppositeEquationTransition
  search :
    PeriodSearchInterface.PeriodSearchCertificate
      transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
  lower :
    Fin search.word.length -> LocalVertex ->
      Fin search.word.length -> LocalVertex -> Real
  lower_ge_one :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne lower
  lower_bound :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      transitions.toFigure2TransitionObligations
      search.word.positive_length
      BaseTransitionRealization.exactBase
      search.word.letter
      lower

namespace EquationPeriodSearchCrossBlockCertificate

/-- The period-search certificate projected to the generated period equation. -/
def periodEquation
    (C : EquationPeriodSearchCrossBlockCertificate) :
    PeriodInterface.GeneratedPeriodEquation
      C.transitions.toFigure2TransitionObligations
      C.search.word.positive_length
      BaseTransitionRealization.exactBase
      C.search.word.letter :=
  C.search.toGeneratedPeriodEquation

/-- Cross-block lower bounds and the checked one-block geometry supply global
generated separation for the certified word. -/
def separated
    (C : EquationPeriodSearchCrossBlockCertificate) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.transitions.toFigure2TransitionObligations
      C.search.word.positive_length
      BaseTransitionRealization.exactBase
      C.search.word.letter :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    C.transitions.toFigure2TransitionObligations
    C.search.word.positive_length
    BaseTransitionRealization.exactBase
    C.search.word.letter
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (equationTransitions_preserveSameBlockDistances C.transitions)
    C.lower
    C.lower_ge_one
    C.lower_bound

/-- The reduced metric package obtained from the final conditional inputs. -/
def reducedMetricHypotheses
    (C : EquationPeriodSearchCrossBlockCertificate) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      C.transitions.toFigure2TransitionObligations
      C.search.word.positive_length
      BaseTransitionRealization.exactBase
      C.search.word.letter where
  separated := C.separated
  base_same_block_isometry :=
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    equationTransitions_preserveSameBlockDistances C.transitions

/-- A single period-search/equation-transition/cross-block certificate gives
the exact `16 * k` target for its certified period length. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : EquationPeriodSearchCrossBlockCertificate) :
    targetUpperConstructionFiveSixteenAt (16 * C.search.word.length) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      C.transitions.toFigure2TransitionObligations
      C.search.word.positive_length
      BaseTransitionRealization.exactBase
      C.search.word.letter
      C.periodEquation
      C.reducedMetricHypotheses

end EquationPeriodSearchCrossBlockCertificate

/-- A family of period-search certificates and cross-block lower-bound tables
for every positive exact block count, using one equation-transition package. -/
structure EquationPeriodSearchCrossBlockFamily where
  transitions : ConnectorEquationClosure.SameOppositeEquationTransition
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (ExactFamilyClosure.finiteOrientationWord k hk (orientation k hk))
  lower :
    forall (k : Nat) (_hk : 0 < k),
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hk)
  lower_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (orientation k hk)
        (lower k hk)

namespace EquationPeriodSearchCrossBlockFamily

/-- The indexed finite period-search certificate projected to a generated
period equation for one exact block count. -/
def periodEquation
    (F : EquationPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) := by
  simpa [ExactFamilyClosure.finiteOrientationWord] using
    (F.period k hk).toGeneratedPeriodEquation

/-- The same period-search certificate projected to the algebraic closure
equation used by closed-placement closure. -/
def closure
    (F : EquationPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) := by
  simpa [ExactFamilyClosure.finiteOrientationWord] using
    (F.period k hk).toGeneratedClosureEquation

/-- Cross-block lower bounds projected to generated global separation for one
exact block count. -/
def separated
    (F : EquationPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (equationTransitions_preserveSameBlockDistances F.transitions)
    (F.lower k hk)
    (F.lower_ge_one k hk)
    (F.lower_bound k hk)

/-- The reduced generated metric package obtained for one exact block count. -/
def reducedMetricHypotheses
    (F : EquationPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) where
  separated := F.separated k hk
  base_same_block_isometry :=
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    equationTransitions_preserveSameBlockDistances F.transitions

/-- One member of a final conditional family gives the exact `16 * k` target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (F : EquationPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk)
      (F.periodEquation k hk)
      (F.reducedMetricHypotheses k hk)

/-- A final conditional family gives the exact-multiple Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (F : EquationPeriodSearchCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      (fun _k _hk => F.transitions.toFigure2TransitionObligations)
      (fun _k _hk => BaseTransitionRealization.exactBase)
      F.orientation
      F.periodEquation
      F.separated
      (fun _k _hk =>
        GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry)
      (fun _k _hk =>
        equationTransitions_preserveSameBlockDistances F.transitions)

/-- A final conditional family also gives the arbitrary-`n` Pach--Toth target,
using the checked small cases below sixteen. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : EquationPeriodSearchCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      F.targetUpperConstructionFiveSixteen

end EquationPeriodSearchCrossBlockFamily

/-- Exact-multiple target from period-search certificates, equation transitions,
and cross-block lower bounds for every positive block count. -/
theorem exactTarget_of_periodSearch_equationTransitions_crossBlock
    (F : EquationPeriodSearchCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target from period-search certificates, equation
transitions, cross-block lower bounds for every positive block count, and the
checked small cases below sixteen. -/
theorem arbitraryTarget_of_periodSearch_equationTransitions_crossBlock
    (F : EquationPeriodSearchCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.targetUpperConstructionFiveSixteenArbitrary

end

end FinalConditional
end PachToth
end ErdosProblems1066
