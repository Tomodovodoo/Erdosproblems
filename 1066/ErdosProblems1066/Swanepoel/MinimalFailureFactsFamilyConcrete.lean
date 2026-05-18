import ErdosProblems1066.Swanepoel.MinimalFailureComponentPackage
import ErdosProblems1066.Swanepoel.NoEarlyTripleConcrete

set_option autoImplicit false

/-!
# Concrete family wrapper for minimal-failure paper facts

This module records the smallest current paper-fact interface needed to
instantiate `MinimalFailureComponentPackage.MinimalFailureM8PaperFactsFamily`.
The only conversion performed here is the checked finite reduction from the
five concrete no-early triple exclusions to the construction-level
no-early-triples package.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureFactsFamilyConcrete

open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8LateTriplesFromNoEarly
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalFailureComponentPackage
open MinimalGraphFacts
open NoEarlyTripleConcrete

universe u

noncomputable section

variable {n : Nat}

/-- The remaining explicit paper facts for one minimal cleared failure, using
the concrete five-exclusion no-early interface. -/
structure MinimalFailureM8RemainingPaperFacts
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  cutVertex : MinimalFailureCutVertexFacts C hmin
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)
  spine :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        planarBoundary.core cutVertex.preconnectedNoCut hmin)
  lemma8 : M8Lemma8Combinatorics spine
  arc : NonconcaveArcTurnData
  noEarlyTripleEquality :
    M8ConcreteNoEarlyTripleEquality
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        planarBoundary.core cutVertex.preconnectedNoCut hmin spine
        lemma8).toM8LocalLabels.predicates.data
  windowContainment :
    M8WindowContainment
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        planarBoundary.core cutVertex.preconnectedNoCut hmin spine
        lemma8).toM8LocalLabels
      arc.toM8TurnBounds

namespace MinimalFailureM8RemainingPaperFacts

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Boundary-derived labels from the remaining paper facts. -/
def boundaryLabels
    (P : MinimalFailureM8RemainingPaperFacts C hmin) :
    M8BoundaryLabelPackage C :=
  M8BoundaryLabelPackage.ofMinimalClearedFailure
    P.planarBoundary.core P.cutVertex.preconnectedNoCut hmin
    P.spine P.lemma8

/-- Local labels from the boundary-derived label package. -/
def localLabels
    (P : MinimalFailureM8RemainingPaperFacts C hmin) :
    M8LocalLabels C :=
  P.boundaryLabels.toM8LocalLabels

/-- Convert the five concrete no-early exclusions to the construction-level
no-early package. -/
def noEarlyTriples
    (P : MinimalFailureM8RemainingPaperFacts C hmin) :
    M8ConstructionNoEarlyTriples P.localLabels where
  noEarlyTripleEquality := P.noEarlyTripleEquality.toNoEarlyTripleEquality

/-- Assemble the remaining facts into the component-package paper facts. -/
def toMinimalFailureM8PaperFacts
    (P : MinimalFailureM8RemainingPaperFacts C hmin) :
    MinimalFailureM8PaperFacts C hmin where
  cutVertex := P.cutVertex
  planarBoundary := P.planarBoundary
  spine := P.spine
  lemma8 := P.lemma8
  arc := P.arc
  noEarlyTriples := P.noEarlyTriples
  windowContainment := P.windowContainment

/-- A fixed minimal failure with the remaining paper facts is contradictory. -/
theorem contradiction
    (P : MinimalFailureM8RemainingPaperFacts C hmin) :
    False :=
  P.toMinimalFailureM8PaperFacts.contradiction

end MinimalFailureM8RemainingPaperFacts

/-! ## Uniform family -/

/-- Uniform remaining explicit paper facts for every minimal cleared failure. -/
structure MinimalFailureM8RemainingPaperFactsFamily where
  facts :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureM8RemainingPaperFacts C hmin

namespace MinimalFailureM8RemainingPaperFactsFamily

/-- Assemble the concrete remaining-facts family into
`MinimalFailureComponentPackage.MinimalFailureM8PaperFactsFamily`. -/
def toMinimalFailureM8PaperFactsFamily
    (H : MinimalFailureM8RemainingPaperFactsFamily) :
    MinimalFailureM8PaperFactsFamily where
  facts := fun C hmin =>
    (H.facts C hmin).toMinimalFailureM8PaperFacts

/-- The concrete remaining-facts family rules out every minimal cleared
failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureM8RemainingPaperFactsFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toMinimalFailureM8PaperFactsFamily.no_minimalClearedFailure

/-- Target wrapper from the concrete remaining-facts family. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureM8RemainingPaperFactsFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toMinimalFailureM8PaperFactsFamily.targetLowerBoundEightThirtyOne

end MinimalFailureM8RemainingPaperFactsFamily

end

end MinimalFailureFactsFamilyConcrete
end Swanepoel
end ErdosProblems1066
