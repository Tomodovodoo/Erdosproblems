import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.Figure8EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.Figure9EuclideanFactsConcrete
import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureClosure
import ErdosProblems1066.Swanepoel.MinimalFailureFactsFamilyConcrete
import ErdosProblems1066.Swanepoel.M8TurnPackageW12
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary

set_option autoImplicit false

/-!
# Refined assembly of the remaining `m = 8` paper facts

This module is only an assembly layer. It keeps the remaining paper inputs in
the most refined packages currently available, then routes them directly to the
checked `M8ConstructionData` closure.

The checked reductions used here are:

* finite `p/q` boundary-spine certificates to `M8BoundarySpine`;
* the current Lemma 8 missing-existence package to
  `M8Lemma8Combinatorics`;
* boundary-attached nonconcave long-arc budget data to
  `NonconcaveArcTurnData`;
* Lemma 9 five-start late facts to concrete no-early-triple exclusions;
* Figure 8/Figure 9 Euclidean fact packages to construction window geometry.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8PaperFactsAssemblyRefined

open BoundarySpineFiniteCertificate
open CutVertexFinal
open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open Lemma8ExistenceConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LateTriplesFromNoEarly
open M8LabelsFromBoundaryInterface
open M8TurnBoundsFromArc
open M8TurnPackageW12
open Lemma10WindowGeometry
open MinimalFailureComponentPackage
open MinimalFailureFactsFamilyConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line graph attached to a configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  MinimalFailureComponentPackage.CanonicalGraph C

/-! ## One fixed minimal failure -/

/--
The refined remaining paper facts for one minimal cleared failure.

Compared with `MinimalFailureM8RemainingPaperFacts`, this package names the
smaller current inputs where reducers are available:
`positiveCard`/`remainingNoCutSlack` for the cut-vertex facade, boundary data
with a selected nonconcave long-arc budget, a finite boundary-spine
certificate, the Lemma 8 missing-existence package, Lemma 9 five-start late
facts, and the Figure 8/Figure 9 Euclidean fact packages.
-/
structure MinimalFailureM8RefinedPaperFacts
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  positiveCard : 0 < n
  remainingNoCutSlack : RemainingNoCutSlackFact C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C)
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

namespace MinimalFailureM8RefinedPaperFacts

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Cut-vertex facts assembled from the named positive-cardinality and
cut-slack paper inputs. -/
def cutVertex
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard := P.positiveCard
  remainingSlack := P.remainingNoCutSlack

/-- The planar-boundary package selected together with the nonconcave long
arc budget. -/
def planarBoundary
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.arcBoundaryBudget.planarBoundary

/-- Boundary spine produced by the finite `p/q` certificate. -/
def spine
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        P.planarBoundary.core P.cutVertex.preconnectedNoCut hmin) :=
  P.spineCertificate.toM8BoundarySpine
    P.cutVertex.preconnectedNoCut hmin

/-- Lemma 8 combinatorics produced by the current missing-existence reducer. -/
def lemma8
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8Lemma8Combinatorics P.spine :=
  P.lemma8Existence.toLemma8Combinatorics

/-- Boundary labels determined by the refined boundary and Lemma 8 packages. -/
def boundaryLabels
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8BoundaryLabelPackage C :=
  M8BoundaryLabelPackage.ofMinimalClearedFailure
    P.planarBoundary.core P.cutVertex.preconnectedNoCut hmin
    P.spine P.lemma8

/-- Local labels determined by the refined boundary package. -/
def localLabels
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8LocalLabels C :=
  P.boundaryLabels.toM8LocalLabels

/-- Nonconcave-arc turn data produced by the boundary-attached long-arc budget
selection. -/
def arc
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    NonconcaveArcTurnData :=
  P.arcBoundaryBudget.toNonconcaveArcTurnData

/-- M8 construction-level turn bounds produced by the boundary-attached
long-arc budget selection. -/
def turnBounds
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8TurnBounds :=
  P.arcBoundaryBudget.toM8TurnBounds

/-- W12 downstream-facing turn package for the selected nonconcave long arc. -/
def turnPackage
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    BoundaryLongArcM8TurnPackage P.arcBoundaryBudget :=
  BoundaryLongArcM8TurnPackage.ofBoundaryBudgetData P.arcBoundaryBudget

/-- The selected M8 total turn is the explicit thirteen-term sum. -/
theorem turnBounds_totalTurn_eq_thirteen
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    Lemma10Inequalities.totalTurn P.turnBounds.turn =
      NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
        P.turnBounds.turn :=
  P.turnPackage.totalTurn_eq_thirteen

/-- The selected M8 thirteen-term turn sum is below `pi / 3`. -/
theorem turnBounds_thirteenTurnSum_lt_pi_div_three
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      P.turnBounds.turn < Real.pi / 3 :=
  P.turnPackage.thirteenTurnSum_lt_pi_div_three

/-- Any separated Lemma 10 window over the selected M8 turns is below
`pi / 3`. -/
theorem separatedTurn_lt_pi_div_three
    (P : MinimalFailureM8RefinedPaperFacts C hmin) {i j : Nat}
    (hi : 1 <= i) (hj : j <= 10) :
    Lemma10Inequalities.separatedTurn P.turnBounds.turn i j <
      Real.pi / 3 :=
  P.turnPackage.separatedTurn_lt_pi_div_three hi hj

/-- Any adjacent Lemma 10 window over the selected M8 turns is below
`pi / 3`. -/
theorem adjacentTurn_lt_pi_div_three
    (P : MinimalFailureM8RefinedPaperFacts C hmin) {i : Nat}
    (hi : 1 <= i) (hi_next : i + 1 <= 10) :
    Lemma10Inequalities.adjacentTurn P.turnBounds.turn i <
      Real.pi / 3 :=
  P.turnPackage.adjacentTurn_lt_pi_div_three hi hi_next

/-- Concrete no-early-triple exclusions produced from the Lemma 9 five-start
late facts. -/
def noEarlyTripleEquality
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8ConcreteNoEarlyTripleEquality P.localLabels.predicates.data :=
  P.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality

/-- Convert the five concrete no-early exclusions to the construction-level
no-early package. -/
def noEarlyTriples
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8ConstructionNoEarlyTriples P.localLabels where
  noEarlyTripleEquality := P.noEarlyTripleEquality.toNoEarlyTripleEquality

/-- Label-level late triples obtained from the concrete no-early exclusions. -/
def lateTriples
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8LateTriples P.localLabels :=
  P.noEarlyTriples.toM8LateTriples

/-- Figure 8 explicit Euclidean facts supply the honest separated-window
geometry expected by the construction interface. -/
def figure8WindowGeometry_of_explicitEuclideanFacts
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (H :
      HonestFigure8ExplicitEuclideanFacts
        localLabels.predicates turnBounds.turn) :
    HonestFigure8SeparatedWindowGeometry
      localLabels.predicates turnBounds.turn := by
  intro i j hi hsep hj hbad_i hbad_j
  rcases H.distance_data hi hsep hj hbad_i hbad_j with
    ⟨p, qi, qj, s, r, D⟩
  exact ⟨p, qi, qj, s, r, D,
    H.central_angle_le_separatedTurn hi hsep hj hbad_i hbad_j D⟩

/-- Figure 9 selected Euclidean facts supply the honest adjacent-left window
geometry expected by the construction interface. -/
def figure9WindowGeometry_of_euclideanFactWitnesses
    {localLabels : M8LocalLabels C} {turnBounds : M8TurnBounds}
    (H :
      HonestFigure9AdjacentLeftEuclideanFactWitnesses
        localLabels.predicates turnBounds.turn) :
    HonestFigure9AdjacentLeftWindowGeometry
      localLabels.predicates turnBounds.turn :=
  honestLeftWindowGeometry_of_euclideanFactWitnesses H

/-- Figure 8/Figure 9 window geometry assembled from the refined Euclidean
fact packages. -/
def windowGeometry
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8WindowGeometry P.localLabels P.turnBounds where
  figure8 :=
    figure8WindowGeometry_of_explicitEuclideanFacts
      (localLabels := P.localLabels) (turnBounds := P.turnBounds)
      P.figure8EuclideanFacts
  figure9_left :=
    figure9WindowGeometry_of_euclideanFactWitnesses
      (localLabels := P.localLabels) (turnBounds := P.turnBounds)
      P.figure9EuclideanFacts

/-- Assemble the refined package directly into the clean M8 construction
interface. -/
def toM8ConstructionData
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8ConstructionData C hmin where
  localLabels := P.localLabels
  turnBounds := P.turnBounds
  lateTriples := P.lateTriples
  windowGeometry := P.windowGeometry

/-- A fixed minimal failure equipped with the refined remaining paper facts is
contradictory by the checked M8 construction closure. -/
theorem contradiction
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    False :=
  P.toM8ConstructionData.toBrokenLatticeMinimalFailure.contradiction

end MinimalFailureM8RefinedPaperFacts

/-! ## Uniform refined family -/

/-- Uniform refined remaining paper facts for every minimal cleared failure. -/
structure MinimalFailureM8RefinedPaperFactsFamily where
  facts :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureM8RefinedPaperFacts C hmin

namespace MinimalFailureM8RefinedPaperFactsFamily

/-- Assemble the refined family into the broken-lattice construction-data
eliminator. -/
def toM8ConstructionEliminator
    (H : MinimalFailureM8RefinedPaperFactsFamily) :
    BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator :=
  fun C hmin =>
    Nonempty.intro
      (H.facts C hmin).toM8ConstructionData.toBrokenLatticeMinimalFailure

/-- The refined family rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureM8RefinedPaperFactsFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  BrokenLatticeMinimalFailure.no_minimalClearedFailure_of_m8ConstructionEliminator
    H.toM8ConstructionEliminator

/-- Target wrapper from the refined remaining-facts family. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureM8RefinedPaperFactsFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
    H.no_minimalClearedFailure

end MinimalFailureM8RefinedPaperFactsFamily

end

end M8PaperFactsAssemblyRefined
end Swanepoel
end ErdosProblems1066
