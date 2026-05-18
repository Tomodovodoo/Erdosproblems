import ErdosProblems1066.Swanepoel.CutVertexFinal
import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete
import ErdosProblems1066.Swanepoel.M8TurnBoundsConcrete
import ErdosProblems1066.Swanepoel.M8LateTriplesConcrete
import ErdosProblems1066.Swanepoel.M8WindowGeometryConcrete
import ErdosProblems1066.Swanepoel.M8SeparatedConstructionConcrete

set_option autoImplicit false

/-!
# Explicit minimal-failure component package

This file is a standalone conditional package for one fixed minimal cleared
failure.  It combines the checked cut-vertex, planar-boundary, boundary-label,
turn-bound, late-triples, and window-geometry facades into the component
package consumed by `M8SeparatedConstructionConcrete`.

The paper-specific content is deliberately still data: the all-cut slack,
planar-boundary package, boundary spine, Lemma 8 combinatorics, nonconcave arc,
no-early triples, and containment witnesses are fields.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureComponentPackage

open CutVertexFinal
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8LateTriplesFromNoEarly
open M8SeparatedConstructionConcrete
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a
configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C

/-! ## Cut-vertex data routed to the boundary-label context -/

/-- The cut-vertex facts used by the minimal-failure package.

The only paper input here is `remainingSlack`; the connectedness, no-cut, and
degree conclusions are checked projections from `CutVertexFinal`.
-/
structure MinimalFailureCutVertexFacts {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) : Prop where
  positiveCard : 0 < n
  remainingSlack : RemainingNoCutSlackFact C

namespace MinimalFailureCutVertexFacts

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Connectedness and degree range from the checked final cut-vertex facade. -/
def connectedDegreeRange
    (K : MinimalFailureCutVertexFacts C hmin) :
    ConnectedDegreeRangeCertificate C :=
  connectedDegreeRangeCertificate_of_minimalFailure
    (C := C) K.positiveCard hmin

/-- Connectedness, no supplied cut vertex, and degree range from the checked
final cut-vertex facade. -/
def connectedNoCutDegreeRange
    (K : MinimalFailureCutVertexFacts C hmin) :
    ConnectedNoCutDegreeRangeCertificate C :=
  connectedNoCutDegreeRangeCertificate_of_minimalFailure_remainingSlack
    (C := C) K.positiveCard hmin K.remainingSlack

/-- The preconnected/no-cut certificate expected by the boundary-label
interface. -/
def preconnectedNoCut
    (K : MinimalFailureCutVertexFacts C hmin) :
    CutVertexClosure.PreconnectedNoCutVertexCertificate C where
  preconnected := (K.connectedNoCutDegreeRange.connected).preconnected
  noCutVertex := K.connectedNoCutDegreeRange.noCutVertex

end MinimalFailureCutVertexFacts

/-! ## Explicit paper facts for one minimal failure -/

/--
The explicit remaining paper data for a fixed minimal cleared failure.

Fields before `spine` set up the checked structural context.  The remaining
fields are precisely the still-supplied `m = 8` construction facts: the
boundary spine, Lemma 8 labels, nonconcave arc turn data, no-early triples, and
Figure 8/Figure 9 containment witnesses.
-/
structure MinimalFailureM8PaperFacts
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  cutVertex : MinimalFailureCutVertexFacts C hmin
  planarBoundary : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)
  spine :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        planarBoundary.core cutVertex.preconnectedNoCut hmin)
  lemma8 : M8Lemma8Combinatorics spine
  arc : NonconcaveArcTurnData
  noEarlyTriples :
    M8ConstructionNoEarlyTriples
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        planarBoundary.core cutVertex.preconnectedNoCut hmin spine
        lemma8).toM8LocalLabels
  windowContainment :
    M8WindowContainment
      (M8BoundaryLabelPackage.ofMinimalClearedFailure
        planarBoundary.core cutVertex.preconnectedNoCut hmin spine
        lemma8).toM8LocalLabels
      arc.toM8TurnBounds

namespace MinimalFailureM8PaperFacts

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The checked cut-vertex/degree certificate projected from the explicit
cut-vertex fields. -/
def connectedNoCutDegreeRange
    (P : MinimalFailureM8PaperFacts C hmin) :
    ConnectedNoCutDegreeRangeCertificate C :=
  P.cutVertex.connectedNoCutDegreeRange

/-- The concrete planar face-counting data projected from the supplied
planar-boundary package. -/
def concreteFaceCountingData
    (P : MinimalFailureM8PaperFacts C hmin) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      P.planarBoundary :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    P.planarBoundary

/-- The proposition-valued counting conclusions projected from the supplied
planar-boundary package. -/
theorem faceCountingTheorems
    (P : MinimalFailureM8PaperFacts C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      P.planarBoundary :=
  PlanarBoundaryFinal.PlanarBoundaryData.faceCountingTheorems_of_concreteData
    P.planarBoundary

/-- Boundary-derived labels assembled from the explicit outer boundary, no-cut
certificate, boundary spine, and Lemma 8 combinatorics. -/
def boundaryLabels
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8BoundaryLabelPackage C :=
  M8BoundaryLabelPackage.ofMinimalClearedFailure
    P.planarBoundary.core P.cutVertex.preconnectedNoCut hmin
    P.spine P.lemma8

/-- The local labels consumed by the `m = 8` construction interface. -/
def localLabels
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8LocalLabels C :=
  P.boundaryLabels.toM8LocalLabels

/-- The normalized construction-level turn bounds obtained from the explicit
nonconcave arc. -/
def turnBounds
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8TurnBounds :=
  M8TurnBoundsConcrete.m8TurnBounds P.arc

/-- The label-level late-triples field obtained from explicit no-early triple
exclusions. -/
theorem lateTriples
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8LateTriples P.localLabels :=
  P.noEarlyTriples.toM8LateTriples

/-- The window geometry obtained from explicit Figure 8/Figure 9 containment
witnesses. -/
def windowGeometry
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8WindowGeometry P.localLabels P.turnBounds :=
  P.windowContainment.toM8WindowGeometry

/-- The clean construction-interface package assembled from the explicit
paper facts. -/
def toM8ConstructionData
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8ConstructionData C hmin :=
  P.boundaryLabels.toM8ConstructionData
    P.turnBounds P.lateTriples P.windowGeometry

/-- The abstract component package consumed by
`M8SeparatedConstructionConcrete`. -/
def toM8SeparatedConstructionComponentPackage
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8SeparatedConstructionComponentPackage C hmin where
  labels := P.boundaryLabels.toLabelsFromBoundaryData
  arc := P.arc
  noEarlyTriples := P.noEarlyTriples
  windowContainment := P.windowContainment

/-- The separated-field package obtained by the existing concrete aggregator.
-/
def toM8SeparatedConstructionFields
    (P : MinimalFailureM8PaperFacts C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  P.toM8SeparatedConstructionComponentPackage.toM8SeparatedConstructionFields

/-- A fixed minimal cleared failure equipped with all explicit paper facts is
contradictory through the checked `m = 8` separated-construction closure. -/
theorem contradiction
    (P : MinimalFailureM8PaperFacts C hmin) :
    False :=
  P.toM8SeparatedConstructionComponentPackage.contradiction

end MinimalFailureM8PaperFacts

/-! ## Uniform conditional package -/

/-- Uniform explicit paper data for every minimal cleared failure. -/
structure MinimalFailureM8PaperFactsFamily where
  facts :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureM8PaperFacts C hmin

namespace MinimalFailureM8PaperFactsFamily

/-- Assemble the uniform explicit data into the component-family package from
`M8SeparatedConstructionConcrete`. -/
def toSeparatedConstructionComponents
    (H : MinimalFailureM8PaperFactsFamily) :
    M8SeparatedConstructionComponents where
  componentPackage := fun C hmin =>
    (H.facts C hmin).toM8SeparatedConstructionComponentPackage

/-- The uniform explicit paper-data package rules out every minimal cleared
failure. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureM8PaperFactsFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toSeparatedConstructionComponents.no_minimalClearedFailure

/-- Final conditional Swanepoel target from the uniform explicit paper-data
package. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureM8PaperFactsFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toSeparatedConstructionComponents.targetLowerBoundEightThirtyOne

end MinimalFailureM8PaperFactsFamily

end

end MinimalFailureComponentPackage
end Swanepoel
end ErdosProblems1066
