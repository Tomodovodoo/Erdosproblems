import ErdosProblems1066.Swanepoel.MinimalFailureClosureW13
import ErdosProblems1066.Swanepoel.RefinedPaperFactsAssemblyW13
import ErdosProblems1066.Swanepoel.BoundaryBudgetRefinedFactsW13
import ErdosProblems1066.Swanepoel.NoCutVertexExtractionW13

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace RemainingInputFamilyBuilderW14

open MinimalGraphFacts

universe u

noncomputable section

def remainingInputFamily_of_no_minimalClearedFailure
    (H :
      forall {n : Nat} (C : _root_.UDConfig n),
        Not (IsMinimalClearedFailure C)) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} where
  inputs := by
    intro n C hmin
    exact False.elim (H C hmin)

theorem no_minimalClearedFailure_iff_nonempty_remainingInputFamily :
    (forall {n : Nat} (C : _root_.UDConfig n),
        Not (IsMinimalClearedFailure C)) <->
      Nonempty MinimalFailureClosureW13.RemainingInputFamily.{u} := by
  constructor
  case mp =>
    intro H
    exact Nonempty.intro
      (remainingInputFamily_of_no_minimalClearedFailure H)
  case mpr =>
    intro H
    cases H with
    | intro R => exact R.no_minimalClearedFailure

def remainingInputFamily_of_explicitW12RefinedPaperFactRecordsFamily
    (H :
      RefinedPaperFactsAssemblyW13.ExplicitW12RefinedPaperFactRecordsFamily.{u}) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} :=
  remainingInputFamily_of_no_minimalClearedFailure
    H.no_minimalClearedFailure

def remainingInputFamily_of_minimalFailureM8RefinedPaperFactsFamily
    (H :
      M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily.{u}) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} :=
  remainingInputFamily_of_no_minimalClearedFailure
    H.no_minimalClearedFailure

def remainingInputFamily_of_concreteObligationFamily
    (H :
      MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligationFamily.{u}) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} :=
  remainingInputFamily_of_no_minimalClearedFailure
    (MinimalFailureClosureW13.no_minimalClearedFailure_of_concreteObligationFamily
      H)

theorem no_minimalClearedFailure_of_explicitW12RefinedPaperFactRecordsFamily
    (H :
      RefinedPaperFactsAssemblyW13.ExplicitW12RefinedPaperFactRecordsFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (remainingInputFamily_of_explicitW12RefinedPaperFactRecordsFamily
    H).no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_explicitW12RefinedPaperFactRecordsFamily
    (H :
      RefinedPaperFactsAssemblyW13.ExplicitW12RefinedPaperFactRecordsFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  (remainingInputFamily_of_explicitW12RefinedPaperFactRecordsFamily
    H).targetLowerBoundEightThirtyOne

theorem no_minimalClearedFailure_of_minimalFailureM8RefinedPaperFactsFamily
    (H :
      M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (remainingInputFamily_of_minimalFailureM8RefinedPaperFactsFamily
    H).no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_minimalFailureM8RefinedPaperFactsFamily
    (H :
      M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  (remainingInputFamily_of_minimalFailureM8RefinedPaperFactsFamily
    H).targetLowerBoundEightThirtyOne

theorem no_minimalClearedFailure_of_concreteObligationFamily
    (H :
      MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligationFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  (remainingInputFamily_of_concreteObligationFamily H).no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_concreteObligationFamily
    (H :
      MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligationFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  (remainingInputFamily_of_concreteObligationFamily
    H).targetLowerBoundEightThirtyOne

end

end RemainingInputFamilyBuilderW14
end Swanepoel
end ErdosProblems1066
