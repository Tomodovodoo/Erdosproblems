import ErdosProblems1066.PachToth.FinalConditional
import ErdosProblems1066.Swanepoel.FinalConditional

set_option autoImplicit false

/-!
# Conditional spine audit aliases

This standalone audit module gives short, stable names to the exact remaining
construction hypotheses used by the current final conditional endpoints.
-/

namespace ErdosProblems1066
namespace Audit
namespace ConditionalSpine

noncomputable section

/-- Remaining exact Swanepoel construction hypothesis: the checked `m = 8`
separated construction eliminator for minimal failures. -/
abbrev SwanepoelM8SeparatedConstructionHypothesis : Prop :=
  Swanepoel.FinalConditional.MinimalFailureM8SeparatedConstructionEliminator

/-- Remaining exact Pach--Toth single-block-count construction hypothesis:
period search, equation transitions, and cross-block lower bounds for one
certified period. -/
abbrev PachTothSingleExactBlockHypothesis : Type :=
  PachToth.FinalConditional.EquationPeriodSearchCrossBlockCertificate

/-- Remaining exact Pach--Toth family construction hypothesis: period search,
equation transitions, and cross-block lower bounds for every positive exact
block count. -/
abbrev PachTothExactFamilyHypothesis : Type :=
  PachToth.FinalConditional.EquationPeriodSearchCrossBlockFamily

/-- Audit alias for the conditional Swanepoel endpoint. -/
theorem swanepoel_targetLowerBoundEightThirtyOne
    (h : SwanepoelM8SeparatedConstructionHypothesis) :
    Swanepoel.targetLowerBoundEightThirtyOne :=
  Swanepoel.FinalConditional.targetLowerBoundEightThirtyOne h

/-- Audit alias for the conditional Pach--Toth exact-block endpoint from a
single exact-block certificate. -/
theorem pachToth_targetUpperConstructionFiveSixteenAt_exactBlock
    (C : PachTothSingleExactBlockHypothesis) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * C.search.word.length) :=
  C.targetUpperConstructionFiveSixteenAt_exactBlock

/-- Audit alias for the conditional Pach--Toth exact-multiple endpoint. -/
theorem pachToth_targetUpperConstructionFiveSixteen
    (F : PachTothExactFamilyHypothesis) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PachToth.FinalConditional.exactTarget_of_periodSearch_equationTransitions_crossBlock F

/-- Audit alias for the conditional Pach--Toth arbitrary-`n` endpoint. -/
theorem pachToth_targetUpperConstructionFiveSixteenArbitrary
    (F : PachTothExactFamilyHypothesis) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.FinalConditional.arbitraryTarget_of_periodSearch_equationTransitions_crossBlock F

end

end ConditionalSpine
end Audit
end ErdosProblems1066
