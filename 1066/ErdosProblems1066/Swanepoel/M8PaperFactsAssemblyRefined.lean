import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureFactsFamilyConcrete
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.NonconcaveArcAngleFacts

set_option autoImplicit false

/-!
# Refined assembly of the remaining `m = 8` paper facts

This module is only an assembly layer.  It keeps the remaining paper inputs in
the most refined packages currently available, then repackages them into
`MinimalFailureFactsFamilyConcrete.MinimalFailureM8RemainingPaperFactsFamily`.

The checked reductions used here are:

* finite `p/q` boundary-spine certificates to `M8BoundarySpine`;
* the current Lemma 8 missing-existence package to
  `M8Lemma8Combinatorics`;
* nonconcave-arc geometric angle facts to `NonconcaveArcTurnData`;
* Lemma 9 five-start late facts to concrete no-early-triple exclusions;
* combined Figure 8/Figure 9 containment bridges to `M8WindowContainment`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8PaperFactsAssemblyRefined

open AngleContainmentInterface
open BoundarySpineFiniteCertificate
open CutVertexFinal
open Lemma8ExistenceConcrete
open Lemma10Bridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalFailureComponentPackage
open MinimalFailureFactsFamilyConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NonconcaveArcAngleFacts

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
`positiveCard`/`remainingNoCutSlack` for the cut-vertex facade, a finite
boundary-spine certificate, the Lemma 8 missing-existence package, geometric
nonconcave-arc angle facts, Lemma 9 five-start late facts, and the two
containment bridges.
-/
structure MinimalFailureM8RefinedPaperFacts
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  positiveCard : 0 < n
  remainingNoCutSlack : RemainingNoCutSlackFact C
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)
  spineCertificate : M8FinitePQSpineCertificate planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)
  arcAngleFacts : NonconcaveArcGeometricAngleFacts
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        planarBoundary.core
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin
        (spineCertificate.toM8BoundarySpine
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)
        lemma8Existence.toLemma8Combinatorics).toM8LocalLabels.predicates.data
  angleContainment :
    AngleContainmentBridges
      (M8BrokenLatticeGood
        (M8BoundaryLabelPackage.ofMinimalClearedFailure
          planarBoundary.core
          ({ positiveCard := positiveCard
             remainingSlack := remainingNoCutSlack } :
            MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin
          (spineCertificate.toM8BoundarySpine
            ({ positiveCard := positiveCard
               remainingSlack := remainingNoCutSlack } :
              MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)
          lemma8Existence.toLemma8Combinatorics).toM8LocalLabels.predicates.data)
      arcAngleFacts.toNonconcaveArcTurnData.toM8TurnBounds.turn

namespace MinimalFailureM8RefinedPaperFacts

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Cut-vertex facts assembled from the named positive-cardinality and
cut-slack paper inputs. -/
def cutVertex
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard := P.positiveCard
  remainingSlack := P.remainingNoCutSlack

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

/-- Nonconcave-arc turn data produced by the geometric angle reducer. -/
def arc
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    NonconcaveArcTurnData :=
  P.arcAngleFacts.toNonconcaveArcTurnData

/-- Concrete no-early-triple exclusions produced from the Lemma 9 five-start
late facts. -/
def noEarlyTripleEquality
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8ConcreteNoEarlyTripleEquality P.localLabels.predicates.data :=
  P.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality

/-- Figure 8/Figure 9 containment packaged for the concrete remaining-facts
family. -/
def windowContainment
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    M8WindowContainment P.localLabels P.arc.toM8TurnBounds :=
  M8WindowContainment.ofAngleContainmentBridges P.angleContainment

/-- Forget the refined package to the current concrete remaining-facts
family. -/
def toRemainingPaperFacts
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    MinimalFailureM8RemainingPaperFacts C hmin where
  cutVertex := P.cutVertex
  planarBoundary := P.planarBoundary
  spine := P.spine
  lemma8 := P.lemma8
  arc := P.arc
  noEarlyTripleEquality := P.noEarlyTripleEquality
  windowContainment := P.windowContainment

/-- A fixed minimal failure equipped with the refined remaining paper facts is
contradictory by the checked concrete family closure. -/
theorem contradiction
    (P : MinimalFailureM8RefinedPaperFacts C hmin) :
    False :=
  P.toRemainingPaperFacts.contradiction

end MinimalFailureM8RefinedPaperFacts

/-! ## Uniform refined family -/

/-- Uniform refined remaining paper facts for every minimal cleared failure. -/
structure MinimalFailureM8RefinedPaperFactsFamily where
  facts :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureM8RefinedPaperFacts C hmin

namespace MinimalFailureM8RefinedPaperFactsFamily

/-- Assemble the refined family into the concrete remaining-facts family. -/
def toRemainingPaperFactsFamily
    (H : MinimalFailureM8RefinedPaperFactsFamily) :
    MinimalFailureM8RemainingPaperFactsFamily where
  facts := fun C hmin =>
    (H.facts C hmin).toRemainingPaperFacts

/-- The refined family rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureM8RefinedPaperFactsFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toRemainingPaperFactsFamily.no_minimalClearedFailure

/-- Target wrapper from the refined remaining-facts family. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureM8RefinedPaperFactsFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toRemainingPaperFactsFamily.targetLowerBoundEightThirtyOne

end MinimalFailureM8RefinedPaperFactsFamily

end

end M8PaperFactsAssemblyRefined
end Swanepoel
end ErdosProblems1066
