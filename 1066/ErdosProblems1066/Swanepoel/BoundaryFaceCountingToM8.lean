import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.M8BoundaryLabelsConcrete

set_option autoImplicit false

/-!
# Planar face counting to the M8 boundary-label route

This file connects the checked planar-boundary face-counting facade to the
current `m = 8` boundary-label construction route.

The bridge is intentionally conditional.  The planar-boundary data supplies
the selected outer core and the checked E12/E13 count conclusions.  The M8
label route still asks for the no-cut certificate, the boundary spine, and the
paper Lemma 8 extra-neighbor package as explicit fields.  The later turn,
late-triples, and window-geometry fields are likewise kept as later inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryFaceCountingToM8

open CutVertexClosure
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- The canonical unit-distance graph attached to a configuration. -/
abbrev CanonicalUDGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  FaceReduction.CanonicalStraightLineUnitDistanceGraph.ofUDConfig C

/-! ## From planar-boundary data to the structural M8 context -/

/-- The face-counting data extracted from a planar-boundary package on the
canonical graph of `C`. -/
def concreteFaceCountingDataOfPlanarBoundary
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C)) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData D :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData D

/-- The structural M8 boundary/cut/degree context obtained by using the
planar-boundary core as the outer boundary. -/
def boundaryCutDegreeContextOfPlanarBoundary
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    M8BoundaryCutDegreeContext C :=
  M8BoundaryCutDegreeContext.of_minimalClearedFailure
    D.core connectedNoCut hmin

@[simp]
theorem boundaryCutDegreeContext_outerBoundary
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    (boundaryCutDegreeContextOfPlanarBoundary
      D connectedNoCut hmin).outerBoundary = D.core :=
  rfl

@[simp]
theorem boundaryCutDegreeContext_faceBoundary
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    (boundaryCutDegreeContextOfPlanarBoundary
      D connectedNoCut hmin).outerBoundary.faceBoundary =
        D.faceBoundary :=
  rfl

@[simp]
theorem boundaryCutDegreeContext_outerFace
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    (boundaryCutDegreeContextOfPlanarBoundary
      D connectedNoCut hmin).outerBoundary.outerFace =
        D.outerFace :=
  rfl

/-- Checked face-counting consequences attached to the structural M8 context.

The data is proposition-valued where possible and records the exact canonical
count package fields that agree with the selected planar-boundary core. -/
structure PlanarBoundaryFaceCountingFields
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (context : M8BoundaryCutDegreeContext C) where
  concrete :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData D
  context_outerBoundary_eq : context.outerBoundary = D.core
  boundary_package_faceBoundary_eq :
    concrete.boundaryCountHypotheses.faceBoundary =
      context.outerBoundary.faceBoundary
  boundary_package_counts_eq :
    concrete.boundaryCountHypotheses.counts =
      concrete.boundaryCounts
  boundaryAngleCount :
    concrete.boundaryCounts.d5 + 2 * concrete.boundaryCounts.d6 +
        concrete.boundaryCounts.b + concrete.boundaryCounts.B + 6 <=
      concrete.boundaryCounts.d3
  boundaryNegativeCount :
    concrete.boundaryCounts.negativeCount +
        concrete.boundaryCounts.B + 6 <=
      concrete.boundaryCounts.d3
  subpolygonLowDegreeWithHighDegreeSlack :
    forall S : concrete.Subpolygon,
      (concrete.subpolygonCounts S).D5 +
          2 * (concrete.subpolygonCounts S).D6 + 6 <=
        2 * (concrete.subpolygonCounts S).D2 +
          (concrete.subpolygonCounts S).D3
  subpolygonLowDegree :
    forall S : concrete.Subpolygon,
      6 <= 2 * (concrete.subpolygonCounts S).D2 +
        (concrete.subpolygonCounts S).D3

/-- Build the checked face-counting fields for the M8 structural context. -/
def planarBoundaryFaceCountingFields
    {C : _root_.UDConfig n}
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) :
    PlanarBoundaryFaceCountingFields D
      (boundaryCutDegreeContextOfPlanarBoundary D connectedNoCut hmin) where
  concrete := concreteFaceCountingDataOfPlanarBoundary D
  context_outerBoundary_eq := rfl
  boundary_package_faceBoundary_eq := rfl
  boundary_package_counts_eq :=
    (concreteFaceCountingDataOfPlanarBoundary D).boundary_counts_eq
  boundaryAngleCount :=
    (concreteFaceCountingDataOfPlanarBoundary D).boundaryAngleCount
  boundaryNegativeCount :=
    (concreteFaceCountingDataOfPlanarBoundary D).boundaryNegativeCount
  subpolygonLowDegreeWithHighDegreeSlack :=
    (concreteFaceCountingDataOfPlanarBoundary D).subpolygonLowDegreeWithHighDegreeSlack
  subpolygonLowDegree :=
    (concreteFaceCountingDataOfPlanarBoundary D).subpolygonLowDegree

/-! ## Planar-boundary data plus the still-explicit label inputs -/

/-- Planar-boundary face-counting data connected to the M8 boundary-label
route, with the actual label facts still explicit.

The `planarBoundary` field supplies the outer core and checked count data.
The `connectedNoCut` and `hmin` inputs fill the structural degree context.
The `spine` and `lemma8` fields are exactly the remaining boundary-label
facts required by `M8BoundaryLabelsConcrete`. -/
structure M8BoundaryRouteData
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C)
  connectedNoCut : PreconnectedNoCutVertexCertificate C
  spine :
    M8BoundarySpine
      (boundaryCutDegreeContextOfPlanarBoundary
        planarBoundary connectedNoCut hmin)
  lemma8 : M8Lemma8Combinatorics spine

namespace M8BoundaryRouteData

variable {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The structural context filled by the planar-boundary core. -/
def context (D : M8BoundaryRouteData.{u} C hmin) :
    M8BoundaryCutDegreeContext C :=
  boundaryCutDegreeContextOfPlanarBoundary
    D.planarBoundary D.connectedNoCut hmin

/-- The checked face-counting fields attached to this route. -/
def faceCounting
    (D : M8BoundaryRouteData.{u} C hmin) :
    PlanarBoundaryFaceCountingFields D.planarBoundary D.context :=
  planarBoundaryFaceCountingFields
    D.planarBoundary D.connectedNoCut hmin

/-- Forget the bridge wrapper to the concrete M8 boundary-label package. -/
def toBoundaryLabelPackage
    (D : M8BoundaryRouteData.{u} C hmin) :
    M8BoundaryLabelPackage C where
  context := D.context
  spine := D.spine
  lemma8 := D.lemma8

@[simp]
theorem context_outerBoundary
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary = D.planarBoundary.core :=
  rfl

@[simp]
theorem context_faceBoundary
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary.faceBoundary =
      D.planarBoundary.faceBoundary :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_context
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.context = D.context :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_spine
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.spine = D.spine :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_lemma8
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.lemma8 = D.lemma8 :=
  rfl

/-- The outer face-boundary package used by face counting is the same package
used by the M8 boundary-label context. -/
theorem boundaryCountHypotheses_faceBoundary_eq_context
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCountHypotheses.faceBoundary =
      D.toBoundaryLabelPackage.context.outerBoundary.faceBoundary :=
  D.faceCounting.boundary_package_faceBoundary_eq

/-- The outer boundary counts used by the canonical count package are exactly
the concrete counts extracted from the planar-boundary data. -/
theorem boundaryCountHypotheses_counts_eq_concrete
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCountHypotheses.counts =
      D.faceCounting.concrete.boundaryCounts :=
  D.faceCounting.boundary_package_counts_eq

/-- The E12 count conclusion available on the M8 boundary route. -/
theorem boundaryAngleCount
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCounts.d5 +
        2 * D.faceCounting.concrete.boundaryCounts.d6 +
        D.faceCounting.concrete.boundaryCounts.b +
        D.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.faceCounting.concrete.boundaryCounts.d3 :=
  D.faceCounting.boundaryAngleCount

/-- The negative-element E12 count conclusion available on the M8 boundary
route. -/
theorem boundaryNegativeCount
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCounts.negativeCount +
        D.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.faceCounting.concrete.boundaryCounts.d3 :=
  D.faceCounting.boundaryNegativeCount

/-- The E13 high-degree-slack conclusion for each supplied subpolygon. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (D : M8BoundaryRouteData.{u} C hmin)
    (S : D.faceCounting.concrete.Subpolygon) :
    (D.faceCounting.concrete.subpolygonCounts S).D5 +
        2 * (D.faceCounting.concrete.subpolygonCounts S).D6 + 6 <=
      2 * (D.faceCounting.concrete.subpolygonCounts S).D2 +
        (D.faceCounting.concrete.subpolygonCounts S).D3 :=
  D.faceCounting.subpolygonLowDegreeWithHighDegreeSlack S

/-- The Lemma 4 low-degree count conclusion for each supplied subpolygon. -/
theorem subpolygonLowDegree
    (D : M8BoundaryRouteData.{u} C hmin)
    (S : D.faceCounting.concrete.Subpolygon) :
    6 <= 2 * (D.faceCounting.concrete.subpolygonCounts S).D2 +
      (D.faceCounting.concrete.subpolygonCounts S).D3 :=
  D.faceCounting.subpolygonLowDegree S

/-- The local-label field produced by the explicit boundary spine and Lemma 8
package. -/
def toM8LocalLabels
    (D : M8BoundaryRouteData.{u} C hmin) :
    M8LocalLabels C :=
  D.toBoundaryLabelPackage.toM8LocalLabels

@[simp]
theorem toM8LocalLabels_labels
    (D : M8BoundaryRouteData.{u} C hmin) :
    D.toM8LocalLabels.labels =
      D.toBoundaryLabelPackage.labels :=
  rfl

/-- Assemble the clean M8 construction-interface package once the later
turn, late-triples, and window-geometry fields are supplied. -/
def toM8ConstructionData
    (D : M8BoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin :=
  D.toBoundaryLabelPackage.toM8ConstructionData
    turnBounds lateTriples windowGeometry

@[simp]
theorem toM8ConstructionData_localLabels
    (D : M8BoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels =
        D.toM8LocalLabels :=
  rfl

@[simp]
theorem toM8ConstructionData_turnBounds
    (D : M8BoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData
      turnBounds lateTriples windowGeometry).turnBounds =
        turnBounds :=
  rfl

/-- Once the remaining M8 fields are supplied, the route reaches the existing
minimal-failure contradiction package. -/
def toBrokenLatticeMinimalFailure
    (D : M8BoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  (D.toM8ConstructionData
    turnBounds lateTriples windowGeometry).toBrokenLatticeMinimalFailure

/-- Final conditional endpoint for one fixed route: all label, turn,
late-triples, and window-geometry fields imply a contradiction for the indexed
minimal cleared failure. -/
theorem contradiction
    (D : M8BoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    False :=
  (D.toBrokenLatticeMinimalFailure
    turnBounds lateTriples windowGeometry).contradiction

end M8BoundaryRouteData

end

end BoundaryFaceCountingToM8
end Swanepoel
end ErdosProblems1066
