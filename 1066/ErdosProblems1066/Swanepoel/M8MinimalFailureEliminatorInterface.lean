import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.MinimalFailureClosure

set_option autoImplicit false

/-!
# Minimal M8 eliminator interface

This file is the small closure layer after `M8PipelineClosure`.  It does not
prove any new geometry.  Its single package field asks callers to supply the
explicit separated M8 construction fields for every minimal cleared failure.
The checked `M8PipelineClosure` contradiction then eliminates minimal failures,
and `MinimalFailureClosure` converts that elimination into the public target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8MinimalFailureEliminatorInterface

open MinimalFailureClosure
open MinimalGraphFacts

noncomputable section

/-- The minimal explicit package needed after `M8PipelineClosure`.

For every minimal cleared failure, the package returns the actual separated
construction data: honest local predicates, turn bounds, window geometry, and
late triples, as grouped by `M8PipelineClosure.M8SeparatedConstructionFields`.
-/
structure M8MinimalFailureEliminator where
  constructionFields :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8PipelineClosure.M8SeparatedConstructionFields C hmin

namespace M8MinimalFailureEliminator

/-- Forget the explicit package to the eliminator expected by
`M8PipelineClosure`. -/
def toSeparatedConstructionEliminator
    (H : M8MinimalFailureEliminator) :
    M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  exact Nonempty.intro (H.constructionFields C hmin)

/-- The explicit M8 package rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : M8MinimalFailureEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  exact
    M8PipelineClosure.no_minimalClearedFailure_of_separatedConstructionEliminator
      H.toSeparatedConstructionEliminator

/-- The explicit M8 package proves the public Swanepoel `8 / 31` target via
`MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure`.
-/
theorem targetLowerBoundEightThirtyOne
    (H : M8MinimalFailureEliminator) :
    targetLowerBoundEightThirtyOne := by
  exact
    MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
      H.no_minimalClearedFailure

end M8MinimalFailureEliminator

/-- Top-level theorem form of `M8MinimalFailureEliminator.targetLowerBoundEightThirtyOne`. -/
theorem targetLowerBoundEightThirtyOne_of_m8MinimalFailureEliminator
    (H : M8MinimalFailureEliminator) :
    targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

end

end M8MinimalFailureEliminatorInterface
end Swanepoel
end ErdosProblems1066
