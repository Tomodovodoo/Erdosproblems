import ErdosProblems1066.Swanepoel.LongArcToM8AssemblyW13
import ErdosProblems1066.Swanepoel.M8PaperFactsAssemblyRefined

set_option autoImplicit false

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryBudgetRefinedFactsW13

open BoundarySpineFiniteCertificate
open CutVertexFinal
open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open Lemma8ExistenceConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalFailureComponentPackage
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  MinimalFailureComponentPackage.CanonicalGraph C

structure BoundaryBudgetRefinedFactInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  positiveCard : 0 < n
  remainingNoCutSlack : RemainingNoCutSlackFact C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C)
  turnFields :
    LongArcToM8AssemblyW13.BoundaryBudgetM8TurnFields arcBoundaryBudget
  spineCertificate :
    M8FinitePQSpineCertificate arcBoundaryBudget.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        arcBoundaryBudget.planarBoundary.core
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin
        (spineCertificate.toM8BoundarySpine
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)
        lemma8Existence.toLemma8Combinatorics).toM8LocalLabels.predicates.data
  figure8EuclideanFacts :
    HonestFigure8ExplicitEuclideanFacts
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        arcBoundaryBudget.planarBoundary.core
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin
        (spineCertificate.toM8BoundarySpine
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)
        lemma8Existence.toLemma8Combinatorics).toM8LocalLabels.predicates
      arcBoundaryBudget.toM8TurnBounds.turn
  figure9EuclideanFacts :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        arcBoundaryBudget.planarBoundary.core
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin
        (spineCertificate.toM8BoundarySpine
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)
        lemma8Existence.toLemma8Combinatorics).toM8LocalLabels.predicates
      arcBoundaryBudget.toM8TurnBounds.turn

namespace BoundaryBudgetRefinedFactInputs

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def toMinimalFailureM8RefinedPaperFacts
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts C hmin where
  positiveCard := P.positiveCard
  remainingNoCutSlack := P.remainingNoCutSlack
  arcBoundaryBudget := P.arcBoundaryBudget
  spineCertificate := P.spineCertificate
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  figure8EuclideanFacts := P.figure8EuclideanFacts
  figure9EuclideanFacts := P.figure9EuclideanFacts

def turnBounds
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    M8TurnBounds :=
  P.turnFields.turnBounds

def localLabels
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    M8LocalLabels C :=
  P.toMinimalFailureM8RefinedPaperFacts.localLabels

def lateTriples
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    M8LateTriples P.localLabels :=
  P.toMinimalFailureM8RefinedPaperFacts.lateTriples

theorem turnBounds_eq_boundaryBudget
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    P.turnBounds = P.arcBoundaryBudget.toM8TurnBounds :=
  P.turnFields.turnBounds_eq

theorem totalTurn_eq_rawTurn
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    Lemma10Inequalities.totalTurn P.turnBounds.turn =
      Lemma10Inequalities.totalTurn P.arcBoundaryBudget.rawTurn := by
  simpa [turnBounds] using P.turnFields.totalTurn_eq_rawTurn

theorem totalTurn_le_boundaryBudget
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    Lemma10Inequalities.totalTurn P.turnBounds.turn <=
      P.arcBoundaryBudget.boundaryAngleBudget.geometricAngleBudget := by
  simpa [turnBounds] using P.turnFields.totalTurn_le_boundaryBudget

theorem thirteenTurnSum_lt_pi_div_three
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    m8ThirteenTurnSum P.turnBounds.turn < Real.pi / 3 := by
  simpa [turnBounds] using P.turnFields.thirteenTurnSum_lt_pi_div_three

def windowGeometry
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    M8WindowGeometry P.localLabels P.turnBounds := by
  rw [turnBounds_eq_boundaryBudget P]
  exact P.toMinimalFailureM8RefinedPaperFacts.windowGeometry

def toM8ConstructionData
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    M8ConstructionData C hmin where
  localLabels := P.localLabels
  turnBounds := P.turnBounds
  lateTriples := P.lateTriples
  windowGeometry := P.windowGeometry

def toBoundaryBudgetM8ConstructionPreconditions
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    LongArcToM8AssemblyW13.BoundaryBudgetM8ConstructionPreconditions
      C hmin P.arcBoundaryBudget where
  localLabels := P.localLabels
  lateTriples := by
    change M8LateTriples P.localLabels
    exact P.lateTriples
  windowGeometry := by
    change M8WindowGeometry P.localLabels P.arcBoundaryBudget.toM8TurnBounds
    rw [<- P.turnBounds_eq_boundaryBudget]
    exact P.windowGeometry

theorem conditionalContradiction
    (P : BoundaryBudgetRefinedFactInputs C hmin) :
    False :=
  M8PipelineClosure.contradiction_of_constructionInterfaceData
    P.toM8ConstructionData

end BoundaryBudgetRefinedFactInputs

end BoundaryBudgetRefinedFactsW13
end Swanepoel
end ErdosProblems1066

end
