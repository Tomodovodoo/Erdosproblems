import ErdosProblems1066.Swanepoel.RefinedPaperFactsAssemblyW13
import ErdosProblems1066.Swanepoel.BoundaryBudgetRefinedFactsW13
import ErdosProblems1066.Swanepoel.FiguresToRefinedM8W13
import ErdosProblems1066.Swanepoel.KnownBoundsSpineW13

set_option autoImplicit false

/-!
# W14 family wrappers for refined Swanepoel facts

This module keeps the W14 surface family-shaped: a caller supplies one
pointwise record for each minimal cleared failure, and the wrappers below route
that supplier to the checked W13 target theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace RefinedFactsFamilyW14

open M8MinimalFailureEliminatorInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- Pointwise refined paper facts in the W13 target-input shape. -/
abbrev PointwiseRefinedPaperFacts
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts C hmin

/-- Pointwise explicit W13 records from the refined paper-facts assembly. -/
abbrev PointwiseExplicitW13Records
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  RefinedPaperFactsAssemblyW13.ExplicitW12RefinedPaperFactRecords.{u} C hmin

/-- Pointwise W13 boundary-budget records with the refined M8 fields. -/
abbrev PointwiseBoundaryBudgetW13Records
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryBudgetRefinedFactsW13.BoundaryBudgetRefinedFactInputs.{u} C hmin

/-- Pointwise W13 late/local-window records from the figure route. -/
abbrev PointwiseLateLocalWindowW13Records
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  FiguresToRefinedM8W13.M8LateLocalWindowContainmentFields C hmin

/-- Package pointwise refined paper facts as the W13 refined facts family. -/
def refinedPaperFactsFamily_of_pointwise
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseRefinedPaperFacts C hmin) :
    KnownBoundsSpineW13.RefinedPaperFactsFamily.{u} where
  facts := fun C hmin => records C hmin

/-- Package pointwise explicit W13 records as the W13 refined facts family. -/
def refinedPaperFactsFamily_of_explicitW13Records
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseExplicitW13Records.{u} C hmin) :
    KnownBoundsSpineW13.RefinedPaperFactsFamily.{u} where
  facts := fun C hmin =>
    (records C hmin).toMinimalFailureM8RefinedPaperFacts

/-- Package pointwise boundary-budget W13 records as the W13 refined facts
family. -/
def refinedPaperFactsFamily_of_boundaryBudgetW13Records
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseBoundaryBudgetW13Records.{u} C hmin) :
    KnownBoundsSpineW13.RefinedPaperFactsFamily.{u} where
  facts := fun C hmin =>
    (records C hmin).toMinimalFailureM8RefinedPaperFacts

/-- Package pointwise late/local-window W13 records as the construction
interface eliminator. -/
def constructionInterfaceEliminator_of_lateLocalWindowW13Records
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseLateLocalWindowW13Records C hmin) :
    M8PipelineClosure.MinimalFailureM8ConstructionInterfaceEliminator :=
  (FiguresToRefinedM8W13.M8LateLocalWindowContainmentFieldsFamily.mk
    records).toConstructionInterfaceEliminator

/-- The refined paper-facts pointwise supplier proves the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_pointwiseRefinedPaperFacts
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseRefinedPaperFacts C hmin) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  KnownBoundsSpineW13.targetLowerBoundEightThirtyOne_of_refinedPaperFactsFamily
    (refinedPaperFactsFamily_of_pointwise records)

/-- The explicit W13 pointwise records prove the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_explicitW13Records
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseExplicitW13Records.{u} C hmin) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  KnownBoundsSpineW13.targetLowerBoundEightThirtyOne_of_refinedPaperFactsFamily
    (refinedPaperFactsFamily_of_explicitW13Records records)

/-- The boundary-budget W13 pointwise records prove the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_boundaryBudgetW13Records
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseBoundaryBudgetW13Records.{u} C hmin) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  KnownBoundsSpineW13.targetLowerBoundEightThirtyOne_of_refinedPaperFactsFamily
    (refinedPaperFactsFamily_of_boundaryBudgetW13Records records)

/-- The late/local-window W13 pointwise records prove the Swanepoel target. -/
theorem targetLowerBoundEightThirtyOne_of_lateLocalWindowW13Records
    (records :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : IsMinimalClearedFailure C),
          PointwiseLateLocalWindowW13Records C hmin) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_m8ConstructionInterfaceEliminator
    (constructionInterfaceEliminator_of_lateLocalWindowW13Records records)

end

end RefinedFactsFamilyW14
end Swanepoel
end ErdosProblems1066
