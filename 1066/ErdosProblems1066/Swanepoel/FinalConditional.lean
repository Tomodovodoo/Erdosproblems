import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.MinimalFailureClosure

set_option autoImplicit false

/-!
# Final conditional Swanepoel closure

This module records the strongest currently checked conditional route to
Swanepoel's `8 / 31` target: if every minimal cleared failure supplies the
explicit separated `m = 8` construction fields, then the target proposition
follows.

The result remains conditional, so it is intentionally not exposed through
`KnownBounds`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FinalConditional

open MinimalGraphFacts

noncomputable section

/-- The explicit minimal-failure `m = 8` separated construction eliminator
currently needed to close the Swanepoel target. -/
abbrev MinimalFailureM8SeparatedConstructionEliminator : Prop :=
  M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator

/-- The separated construction eliminator rules out all minimal cleared
failures. -/
theorem no_minimalClearedFailure_of_m8SeparatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_separatedConstructionEliminator
    hbuild

/-- Honest conditional Swanepoel theorem from the current explicit M8 separated
minimal-failure eliminator. -/
theorem targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionEliminator
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8SeparatedConstructionEliminator hbuild)

/-- Short conditional wrapper for the target proposition inside this final
conditional namespace. -/
theorem targetLowerBoundEightThirtyOne
    (hbuild : MinimalFailureM8SeparatedConstructionEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_m8SeparatedConstructionEliminator hbuild

end

end FinalConditional
end Swanepoel
end ErdosProblems1066
