import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.M8TurnWindowNoEarlyFinal
import ErdosProblems1066.Swanepoel.MinimalFailureClosure

set_option autoImplicit false

/-!
# Minimal M8 eliminator interface

This file is the small closure layer after `M8PipelineClosure`.  It does not
prove any new geometry.  It exposes the checked minimal-failure contradiction
interfaces currently available: separated M8 construction fields, clean
`M8ConstructionInterface` data, direct E22/E23 plus no-early fields, and the
turn/window/no-early package.  `MinimalFailureClosure` converts any resulting
minimal-failure elimination into the public target.
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

/-! ## Theorem forms for the current stronger pipeline gates -/

/-- Clean `M8ConstructionInterface` data for every minimal failure rules out
all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_constructionInterfaceEliminator
    hbuild

/-- Clean `M8ConstructionInterface` data for every minimal failure proves the
public Swanepoel `8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_m8ConstructionInterfaceEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator hbuild)

/-- Direct E22/E23 plus no-early fields for every minimal failure rule out all
minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8E22E23NoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_E22E23NoEarlyConstructionEliminator
    hbuild

/-- Direct E22/E23 plus no-early fields for every minimal failure prove the
public Swanepoel `8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_m8E22E23NoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8E22E23NoEarlyConstructionEliminator hbuild)

/-- Window geometry plus no-early fields for every minimal failure rule out
all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_windowNoEarlyConstructionEliminator
    hbuild

/-- Window geometry plus no-early fields for every minimal failure prove the
public Swanepoel `8 / 31` target. -/
theorem targetLowerBoundEightThirtyOne_of_m8WindowNoEarlyConstructionEliminator
    (hbuild :
      M8PipelineClosure.MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator hbuild)

/-! ## Uniform turn/window/no-early package -/

/-- Exact current upstream theorem shape for the turn/window/no-early route:
every minimal cleared failure supplies the package from
`M8TurnWindowNoEarlyFinal`, whose fields are local labels, nonconcave-arc turn
data, concrete no-early triples, and Figure 8/Figure 9 containment.
-/
def MinimalFailureM8TurnWindowNoEarlyEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Nonempty
        (M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin)

/-- The turn/window/no-early eliminator supplies clean
`M8ConstructionInterface` data for every minimal cleared failure. -/
theorem constructionInterfaceEliminator_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator := by
  intro n C hmin
  cases hbuild C hmin with
  | intro P =>
      exact Nonempty.intro P.toM8ConstructionData

/-- The turn/window/no-early eliminator rules out every minimal cleared
failure. -/
theorem no_minimalClearedFailure_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator
    (constructionInterfaceEliminator_of_turnWindowNoEarlyEliminator hbuild)

/-- The turn/window/no-early eliminator proves the public Swanepoel `8 / 31`
target. -/
theorem targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_turnWindowNoEarlyEliminator hbuild)

end

end M8MinimalFailureEliminatorInterface
end Swanepoel
end ErdosProblems1066
