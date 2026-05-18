import ErdosProblems1066.Swanepoel.M8PipelineClosure
import ErdosProblems1066.Swanepoel.M8MinimalFailureEliminatorInterface
import ErdosProblems1066.Swanepoel.MinimalFailureClosure

set_option autoImplicit false

/-!
# Final conditional Swanepoel closure

This module records the public conditional routes currently checked for
Swanepoel's `8 / 31` target.  The wrappers below keep the theorem conditional:
callers must still supply the remaining minimal-failure input family, or one of
the current closure-module eliminators.

The result remains conditional, so it is intentionally not exposed through
`KnownBounds`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FinalConditional

open MinimalGraphFacts

universe u

noncomputable section

/-- The explicit minimal-failure `m = 8` separated construction eliminator
currently needed to close the Swanepoel target. -/
abbrev MinimalFailureM8SeparatedConstructionEliminator : Prop :=
  M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator

/-- Clean construction-interface data for every minimal cleared failure. -/
abbrev MinimalFailureM8ConstructionInterfaceEliminator : Prop :=
  M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator

/-- Direct E22/E23 plus no-early fields for every minimal cleared failure. -/
abbrev MinimalFailureM8E22E23NoEarlyConstructionEliminator : Prop :=
  M8PipelineClosure.MinimalFailureM8E22E23NoEarlyConstructionEliminator

/-- Window geometry plus no-early fields for every minimal cleared failure. -/
abbrev MinimalFailureM8WindowNoEarlyConstructionEliminator : Prop :=
  M8PipelineClosure.MinimalFailureM8WindowNoEarlyConstructionEliminator

/-- Turn/window/no-early packages for every minimal cleared failure. -/
abbrev MinimalFailureM8TurnWindowNoEarlyEliminator : Prop :=
  M8MinimalFailureEliminatorInterface.MinimalFailureM8TurnWindowNoEarlyEliminator

/-! ## Generic refined input family wrapper -/

/-- A dependency-light public shape for a pointwise remaining input family.

Downstream refined matrices can instantiate `Facts` with their exact row type,
for example the row supplied by
`MinimalFailurePaperFactMatrix.TargetLowerBoundEightThirtyOneInputs`, without
forcing this final public module to import the downstream matrix and create an
import cycle.
-/
abbrev MinimalFailureRefinedInputFamily
    (Facts :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> Type u) :
    Type u :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Facts C hmin

/-- A checked consumer for a pointwise remaining input family. -/
abbrev MinimalFailureRefinedInputConsumer
    (Facts :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> Type u) :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      Facts C hmin -> False

/-- A supplied refined input family plus its checked consumer rules out all
minimal cleared failures. -/
theorem no_minimalClearedFailure_of_refinedInputFamily
    (Facts :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> Type u)
    (hfacts : MinimalFailureRefinedInputFamily Facts)
    (hconsume : MinimalFailureRefinedInputConsumer Facts) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalFailureClosure.no_minimalClearedFailure_of_pointwiseFacts
    Facts hfacts hconsume

/-- Public conditional Swanepoel theorem from a refined remaining input family
and its checked contradiction consumer. -/
theorem targetLowerBoundEightThirtyOne_of_refinedInputFamily
    (Facts :
      forall {n : Nat} (C : _root_.UDConfig n),
        IsMinimalClearedFailure C -> Type u)
    (hfacts : MinimalFailureRefinedInputFamily Facts)
    (hconsume : MinimalFailureRefinedInputConsumer Facts) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_pointwiseFacts
    Facts hfacts hconsume

/-! ## Current closure-module wrappers -/

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

/-- Clean construction-interface data rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator
    (hbuild : MinimalFailureM8ConstructionInterfaceEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_constructionInterfaceEliminator
    hbuild

/-- Public conditional Swanepoel theorem from clean construction-interface
data. -/
theorem targetLowerBoundEightThirtyOne_of_m8ConstructionInterfaceEliminator
    (hbuild : MinimalFailureM8ConstructionInterfaceEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8ConstructionInterfaceEliminator hbuild)

/-- Direct E22/E23 plus no-early fields rule out all minimal cleared
failures. -/
theorem no_minimalClearedFailure_of_m8E22E23NoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_E22E23NoEarlyConstructionEliminator
    hbuild

/-- Public conditional Swanepoel theorem from direct E22/E23 plus no-early
fields. -/
theorem targetLowerBoundEightThirtyOne_of_m8E22E23NoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8E22E23NoEarlyConstructionEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8E22E23NoEarlyConstructionEliminator hbuild)

/-- Window geometry plus no-early fields rule out all minimal cleared
failures. -/
theorem no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8PipelineClosure.no_minimalClearedFailure_of_windowNoEarlyConstructionEliminator
    hbuild

/-- Public conditional Swanepoel theorem from window geometry plus no-early
fields. -/
theorem targetLowerBoundEightThirtyOne_of_m8WindowNoEarlyConstructionEliminator
    (hbuild : MinimalFailureM8WindowNoEarlyConstructionEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_m8WindowNoEarlyConstructionEliminator hbuild)

/-- Turn/window/no-early packages rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M8MinimalFailureEliminatorInterface.no_minimalClearedFailure_of_turnWindowNoEarlyEliminator
    hbuild

/-- Public conditional Swanepoel theorem from turn/window/no-early packages. -/
theorem targetLowerBoundEightThirtyOne_of_turnWindowNoEarlyEliminator
    (hbuild : MinimalFailureM8TurnWindowNoEarlyEliminator) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    (no_minimalClearedFailure_of_turnWindowNoEarlyEliminator hbuild)

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
