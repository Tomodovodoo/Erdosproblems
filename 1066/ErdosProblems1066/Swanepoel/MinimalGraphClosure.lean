import ErdosProblems1066.Swanepoel.MinimalGraphFacts
import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.TargetReduction

set_option autoImplicit false

/-!
# Minimal cleared-failure target closure

This file contains only wrapper theorems.  It composes the generic
minimal-cleared-failure eliminators from `MinimalGraphFacts` with the public
pipeline target wrapper from `TargetReduction`, and records the current
M8 separated-construction remainder as an explicit data field.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalGraphClosure

open CounterexamplePipeline
open MinimalGraphFacts

noncomputable section

/-! ## Generic eliminator closure -/

/-- Pipeline-cleared form of a minimal cleared-failure eliminator. -/
theorem pipelineCleared_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  MinimalGraphFacts.hasCleared_of_minimalClearedFailureEliminator hElim

/-- Pipeline-cleared form of a clearing eliminator for minimal cleared
failures. -/
theorem pipelineCleared_of_minimalClearedFailureClearingEliminator
    (hElim : MinimalClearedFailureClearingEliminator) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  MinimalGraphFacts.hasCleared_of_minimalClearedFailureClearingEliminator
    hElim

/-- Target wrapper from a minimal cleared-failure eliminator. -/
theorem targetLowerBoundEightThirtyOne_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_pipelineCleared
    (pipelineCleared_of_minimalClearedFailureEliminator hElim)

/-- Target wrapper from a clearing eliminator for minimal cleared failures. -/
theorem targetLowerBoundEightThirtyOne_of_minimalClearedFailureClearingEliminator
    (hElim : MinimalClearedFailureClearingEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_pipelineCleared
    (pipelineCleared_of_minimalClearedFailureClearingEliminator hElim)

/-- Target wrapper from a theorem ruling out minimal cleared failures. -/
theorem targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (hNoMin :
      forall {n : Nat} (C : _root_.UDConfig n),
        Not (IsMinimalClearedFailure C)) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_pipelineCleared
    (MinimalGraphFacts.hasCleared_of_no_minimalClearedFailure hNoMin)

/-! ## Single-field concrete input packages -/

/-- The exact generic remainder for the contradiction-valued route: a uniform
minimal cleared-failure eliminator. -/
structure MinimalClearedFailureEliminatorData where
  eliminator : MinimalClearedFailureEliminator

namespace MinimalClearedFailureEliminatorData

/-- The data package rules out minimal cleared failures. -/
theorem no_minimalClearedFailure
    (H : MinimalClearedFailureEliminatorData) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure H.eliminator

/-- The data package supplies the pipeline-cleared predicate. -/
theorem pipelineCleared
    (H : MinimalClearedFailureEliminatorData) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  pipelineCleared_of_minimalClearedFailureEliminator H.eliminator

/-- The data package proves the public target through the pipeline wrapper. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalClearedFailureEliminatorData) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_minimalClearedFailureEliminator
    H.eliminator

end MinimalClearedFailureEliminatorData

/-- The exact generic remainder for the clearing route: a uniform proof that
each proposed minimal cleared failure actually has the cleared independent set.
-/
structure MinimalClearedFailureClearingData where
  clearingEliminator : MinimalClearedFailureClearingEliminator

namespace MinimalClearedFailureClearingData

/-- A clearing-data package can be viewed as contradiction-valued data. -/
def toEliminatorData
    (H : MinimalClearedFailureClearingData) :
    MinimalClearedFailureEliminatorData where
  eliminator :=
    MinimalGraphFacts.minimalClearedFailureEliminator_of_clearingEliminator
      H.clearingEliminator

/-- The clearing-data package supplies the pipeline-cleared predicate. -/
theorem pipelineCleared
    (H : MinimalClearedFailureClearingData) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  pipelineCleared_of_minimalClearedFailureClearingEliminator
    H.clearingEliminator

/-- The clearing-data package proves the public target through the pipeline
wrapper. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalClearedFailureClearingData) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_minimalClearedFailureClearingEliminator
    H.clearingEliminator

end MinimalClearedFailureClearingData

/-! ## Current M8 concrete remainder -/

/-- The current concrete M8 remainder: for every minimal cleared failure,
provide the separated construction fields consumed by the checked M8 pipeline.
-/
structure M8SeparatedConstructionData where
  constructionFields :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8PipelineClosure.M8SeparatedConstructionFields C hmin

namespace M8SeparatedConstructionData

/-- Forget the concrete fields to the nonempty eliminator expected by
`M8PipelineClosure`. -/
def toSeparatedConstructionEliminator
    (H : M8SeparatedConstructionData) :
    M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.constructionFields C hmin)

/-- The concrete M8 data package is a contradiction-valued minimal-failure
eliminator. -/
theorem toMinimalClearedFailureEliminator
    (H : M8SeparatedConstructionData) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  exact
    M8PipelineClosure.M8SeparatedConstructionFields.contradiction
      (H.constructionFields C hmin)

/-- The concrete M8 data package rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (H : M8SeparatedConstructionData) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    H.toMinimalClearedFailureEliminator

/-- The concrete M8 data package supplies the pipeline-cleared predicate. -/
theorem pipelineCleared
    (H : M8SeparatedConstructionData) :
    forall (n : Nat) (C : _root_.UDConfig n),
      HasClearedEightThirtyOneIndependentSet C :=
  pipelineCleared_of_minimalClearedFailureEliminator
    H.toMinimalClearedFailureEliminator

/-- The concrete M8 data package proves the public target through the pipeline
wrapper. -/
theorem targetLowerBoundEightThirtyOne
    (H : M8SeparatedConstructionData) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_pipelineCleared
    H.pipelineCleared

end M8SeparatedConstructionData

/-! ## Theorem forms for the M8 pipeline gate -/

/-- The existing nonempty separated-construction eliminator is an ordinary
minimal cleared-failure eliminator. -/
theorem minimalClearedFailureEliminator_of_m8SeparatedConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  exact
    M8PipelineClosure.contradiction_of_separatedConstructionEliminator
      hbuild hmin

/-- Target wrapper from the existing M8 separated-construction eliminator. -/
theorem targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_minimalClearedFailureEliminator
    (minimalClearedFailureEliminator_of_m8SeparatedConstructionEliminator
      hbuild)

/-- Target wrapper from concrete separated-construction data, theorem form. -/
theorem targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionData
    (H : M8SeparatedConstructionData) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

end

end MinimalGraphClosure
end Swanepoel
end ErdosProblems1066
