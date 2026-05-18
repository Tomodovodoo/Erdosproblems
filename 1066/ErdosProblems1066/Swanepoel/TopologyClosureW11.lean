import ErdosProblems1066.Swanepoel.TopologyInstantiationW11
import ErdosProblems1066.Swanepoel.SubpolygonFamilyW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ClosureMatrix
import ErdosProblems1066.Swanepoel.TopologyFrontierW10

set_option autoImplicit false

/-!
# W11 topology closure facade

This file is a checked closure layer for the W11 topology work.

It deliberately keeps the concrete topology extraction payload visible.  A
`CheckedTopologyPackage` is the topology-side witness; an
`ExplicitBoundarySubpolygonPackage` additionally carries the explicit
outer-face/angle/subpolygon data used by the boundary and subpolygon
frontiers.  The final section records how the available Swanepoel W11 target
matrix projects downstream targets from its explicit input matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyClosureW11

open FaceReduction
open BoundaryCounting
open OuterBoundaryInterface
open SubpolygonInstantiation

universe u

noncomputable section

variable {n : Nat}

/-! ## Shared names -/

/-- The canonical graph used by the W10 and W11 topology layers. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  TopologyInstantiationW11.canonicalGraph C

/-- The compact W11 checked topology package. -/
abbrev CheckedTopologyPackage (C : _root_.UDConfig n) :=
  TopologyInstantiationW11.CheckedTopologyPackage C

/-- The W10 exact explicit topology field target. -/
abbrev W10ExactFieldTarget (C : _root_.UDConfig n) : Prop :=
  TopologyFrontierW10.ExactOuterBoundaryTopologyFieldTarget C

/-- The W10 noncrossing-to-exact topology frontier. -/
abbrev W10NoncrossingToExactFrontier (C : _root_.UDConfig n) : Prop :=
  TopologyFrontierW10.NoncrossingToExactOuterBoundaryFrontier C

/-- The public Swanepoel target. -/
abbrev Target : Prop :=
  SwanepoelW11ClosureMatrix.Target

/-! ## Topology frontier package -/

/--
One checked topology row for a concrete configuration.

The row is only a wrapper around the explicit W11 package, but it records all
checked projections used by W10 topology frontiers and later boundary modules.
-/
structure TopologyFrontierPackage (C : _root_.UDConfig n) where
  topology : CheckedTopologyPackage C

namespace TopologyFrontierPackage

variable {C : _root_.UDConfig n}

/-- The checked outer-boundary core selected by the row. -/
def core (T : TopologyFrontierPackage C) :
    OuterBoundaryCore.{0} (CanonicalGraph C) :=
  T.topology.toCore

/-- The W10 exact explicit topology fields selected by the row. -/
def exactFields (T : TopologyFrontierPackage C) :
    TopologyFrontierW10.ExactOuterBoundaryTopologyFields C :=
  T.topology.toExactFields

/-- Selected outer-face fields for the noncrossing extraction layer. -/
def selectedOuterFaceFields (T : TopologyFrontierPackage C) :
    TopologyExtractionFromNoncrossing.SelectedOuterFaceFields C :=
  T.topology.toSelectedOuterFaceFields

/-- Enclosure data over the selected outer face. -/
def enclosureFields
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFromNoncrossing.EnclosureFields
      T.selectedOuterFaceFields :=
  T.topology.toEnclosureFields

/-- Split exact topology fields for the noncrossing extraction layer. -/
def splitExactTopologyFields (T : TopologyFrontierPackage C) :
    TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  T.topology.toSplitExactTopologyFields

/-- Concrete missing topology facts for the Jordan-boundary layer. -/
def missingTopologyFacts (T : TopologyFrontierPackage C) :
    JordanBoundaryConcrete.MissingTopologyFacts.{0} C :=
  T.topology.toMissingTopologyFacts

/-- Concrete topology facts used by the Swanepoel W8/W9 boundary stack. -/
def topologyFacts (T : TopologyFrontierPackage C) :
    JordanTopologyFactsConcrete.TopologyFacts.{0} C :=
  T.exactFields.toTopologyFacts

/-- Extraction facade data consumed by the Jordan-boundary layer. -/
def extractionData (T : TopologyFrontierPackage C) :
    JordanBoundaryExtraction.Data.{0} (CanonicalGraph C) :=
  T.topology.toExtractionData

/-- Component shape used by W10 minimal-failure direct rows. -/
def toTopologyComponentFields (T : TopologyFrontierPackage C) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C where
  topology := T.topologyFacts

/-- The package supplies the W11 topology target for this configuration. -/
theorem checkedTopologyPackageTarget (T : TopologyFrontierPackage C) :
    TopologyInstantiationW11.CheckedTopologyPackageTarget C :=
  Nonempty.intro T.topology

/-- The package supplies the W10 exact-field topology target. -/
theorem exactFieldTarget (T : TopologyFrontierPackage C) :
    W10ExactFieldTarget C :=
  T.topology.toExactFieldTarget

/-- The package supplies the W10 noncrossing-to-exact frontier. -/
theorem noncrossingToExactFrontier (T : TopologyFrontierPackage C) :
    W10NoncrossingToExactFrontier C :=
  T.topology.toNoncrossingToExactOuterBoundaryFrontier

/-- The package supplies the older concrete noncrossing topology frontier. -/
theorem concreteNoncrossingTopologyFrontier
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C :=
  T.topology.toConcreteNoncrossingTopologyFrontier

/-- The package discharges the remaining core-topology proposition. -/
theorem remainingCoreTopologyRequirements
    (T : TopologyFrontierPackage C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  T.topology.toRemainingCoreTopologyRequirements

/-- The package discharges the remaining Jordan topology theorem. -/
theorem remainingTopologyTheorem
    (T : TopologyFrontierPackage C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem C :=
  T.topology.toRemainingTopologyTheorem

@[simp]
theorem exactFields_toCore (T : TopologyFrontierPackage C) :
    T.exactFields.toCore = T.core := by
  cases T with
  | mk topology =>
      exact topology.toExactFields_toCore

@[simp]
theorem missingTopologyFacts_faceBoundary
    (T : TopologyFrontierPackage C) :
    T.missingTopologyFacts.faceBoundary = T.core.faceBoundary := by
  cases T with
  | mk topology =>
      exact topology.toMissingTopologyFacts_faceBoundary

@[simp]
theorem extractionData_outerEnclosure
    (T : TopologyFrontierPackage C) :
    T.extractionData.outerEnclosure = T.core.outerEnclosure := by
  cases T with
  | mk topology =>
      exact topology.toExtractionData_outerEnclosure

end TopologyFrontierPackage

/-! ## Boundary and subpolygon closure package -/

/--
Topology plus the explicit boundary/subpolygon data needed downstream.

The `faceData_core_eq` field is the visible agreement obligation between the
checked topology package and the explicit outer-face data used to instantiate
subpolygons.  Nothing in this file manufactures that concrete extraction data.
-/
structure ExplicitBoundarySubpolygonPackage
    (C : _root_.UDConfig n) where
  topology : CheckedTopologyPackage C
  faceData :
    ExplicitOuterBoundaryFaceData.{0} (CanonicalGraph C)
  faceData_core_eq : faceData.core = topology.toCore
  subpolygons :
    SubpolygonFamilyW11.SubpolygonFamilyPackage faceData

namespace ExplicitBoundarySubpolygonPackage

variable {C : _root_.UDConfig n}

/-- The topology row associated with the boundary/subpolygon package. -/
def topologyFrontier
    (B : ExplicitBoundarySubpolygonPackage C) :
    TopologyFrontierPackage C where
  topology := B.topology

/-- The explicit outer-boundary angle bounds carried by the face data. -/
def outerAngleBounds
    (B : ExplicitBoundarySubpolygonPackage C) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{0} :=
  B.faceData.outerAngleBounds

/-- The explicit outer-boundary core used by the boundary/subpolygon package. -/
def explicitCore
    (B : ExplicitBoundarySubpolygonPackage C) :
    OuterBoundaryCore (CanonicalGraph C) :=
  B.faceData.core

/-- The concrete topology facts produced from the checked topology row. -/
def topologyFacts
    (B : ExplicitBoundarySubpolygonPackage C) :
    JordanTopologyFactsConcrete.TopologyFacts.{0} C :=
  B.topologyFrontier.topologyFacts

/-- The planar boundary assembled from the explicit face and subpolygon data. -/
def planarBoundary
    (B : ExplicitBoundarySubpolygonPackage C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{0} (CanonicalGraph C) :=
  B.subpolygons.toPlanarBoundaryData

/-- Concrete face-counting data exposed by the assembled planar boundary. -/
def concreteFaceCountingData
    (B : ExplicitBoundarySubpolygonPackage C) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      B.planarBoundary :=
  B.subpolygons.concreteFaceCountingData

/-- Face-count bridge data exposed by the assembled planar boundary. -/
def faceCountingBridgeData
    (B : ExplicitBoundarySubpolygonPackage C) :
    PlanarBoundaryClosure.FaceCountingBridgeData.{0} (CanonicalGraph C) :=
  B.subpolygons.toFaceCountingBridgeData

/-- Outer-boundary angle data over the explicit core. -/
def outerBoundaryAngleData
    (B : ExplicitBoundarySubpolygonPackage C) :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{0}
      (CanonicalGraph C) where
  core := B.explicitCore
  angleBounds := B.outerAngleBounds

/-- The subpolygon index type selected by the explicit package. -/
abbrev Subpolygon (B : ExplicitBoundarySubpolygonPackage C) :
    Type :=
  B.subpolygons.Subpolygon

/-- The computed counts for one selected subpolygon. -/
def subpolygonCounts
    (B : ExplicitBoundarySubpolygonPackage C)
    (S : B.Subpolygon) :
    SubpolygonDegreeCounts :=
  B.subpolygons.subpolygonCounts S

/-- The boundary angle inequality from the explicit outer-boundary angle data. -/
theorem boundaryAngleCountInequality
    (B : ExplicitBoundarySubpolygonPackage C) :
    B.outerAngleBounds.counts.d5 +
        2 * B.outerAngleBounds.counts.d6 +
        B.outerAngleBounds.counts.b +
        B.outerAngleBounds.counts.B + 6 <=
      B.outerAngleBounds.counts.d3 :=
  B.outerAngleBounds.boundaryAngleCountInequality

/-- Negative-element boundary inequality from the same angle data. -/
theorem boundaryNegativeCountInequality
    (B : ExplicitBoundarySubpolygonPackage C) :
    B.outerAngleBounds.counts.negativeCount +
        B.outerAngleBounds.counts.B + 6 <=
      B.outerAngleBounds.counts.d3 :=
  B.outerAngleBounds.boundaryNegativeCountInequality

/-- The outer-boundary angle inequality routed through the explicit core. -/
theorem boundaryAngleCountInequality_viaExplicitCore
    (B : ExplicitBoundarySubpolygonPackage C) :
    B.outerAngleBounds.counts.d5 +
        2 * B.outerAngleBounds.counts.d6 +
        B.outerAngleBounds.counts.b +
        B.outerAngleBounds.counts.B + 6 <=
      B.outerAngleBounds.counts.d3 :=
  B.outerBoundaryAngleData.boundaryAngleCountInequality

/-- Every explicit subpolygon has the checked E13 angle lower bound. -/
theorem subpolygonAngleLowerBound
    (B : ExplicitBoundarySubpolygonPackage C)
    (S : B.Subpolygon) :
    (B.subpolygonCounts S).AngleLowerBound :=
  B.subpolygons.subpolygonAngleLowerBound S

/-- Every explicit subpolygon satisfies the high-degree-slack low-degree row. -/
theorem lowDegreeWithHighDegreeSlack
    (B : ExplicitBoundarySubpolygonPackage C)
    (S : B.Subpolygon) :
    (B.subpolygonCounts S).D5 + 2 * (B.subpolygonCounts S).D6 + 6 <=
      2 * (B.subpolygonCounts S).D2 + (B.subpolygonCounts S).D3 :=
  B.subpolygons.lowDegreeWithHighDegreeSlack S

/-- Every explicit subpolygon satisfies Swanepoel Lemma 4's low-degree row. -/
theorem lowDegree
    (B : ExplicitBoundarySubpolygonPackage C)
    (S : B.Subpolygon) :
    6 <= 2 * (B.subpolygonCounts S).D2 +
      (B.subpolygonCounts S).D3 :=
  B.subpolygons.lowDegree S

/-- The assembled planar-boundary package supplies the face-count theorems. -/
theorem faceCountingTheorems
    (B : ExplicitBoundarySubpolygonPackage C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      B.planarBoundary :=
  B.subpolygons.faceCountingTheorems

/-- The assembled face-counting bridge supplies the same theorem summary. -/
theorem bridgeCountingTheorems
    (B : ExplicitBoundarySubpolygonPackage C) :
    PlanarBoundaryClosure.FaceCountingBridgeData.CountingTheorems
      B.faceCountingBridgeData :=
  B.subpolygons.bridgeCountingTheorems

theorem planarBoundary_core
    (B : ExplicitBoundarySubpolygonPackage C) :
    B.planarBoundary.core = B.explicitCore :=
  rfl

theorem planarBoundary_core_eq_topology_core
    (B : ExplicitBoundarySubpolygonPackage C) :
    B.planarBoundary.core = B.topology.toCore := by
  change B.faceData.core = B.topology.toCore
  exact B.faceData_core_eq

theorem planarBoundary_outerBoundaryCounts
    (B : ExplicitBoundarySubpolygonPackage C) :
    B.planarBoundary.outerBoundaryCounts = B.outerAngleBounds.counts :=
  rfl

theorem concreteFaceCountingData_subpolygonCounts
    (B : ExplicitBoundarySubpolygonPackage C)
    (S : B.Subpolygon) :
    B.concreteFaceCountingData.subpolygonCounts S =
      B.subpolygonCounts S :=
  rfl

end ExplicitBoundarySubpolygonPackage

/-! ## Target matrix ledger -/

/--
The checked target-facing rows available downstream of the topology closure.

The ledger contains projections only.  It does not turn topology data alone
into the final `8 / 31` target; the corresponding input matrices remain
explicit parameters.
-/
structure TargetMatrixLedger : Type (u + 1) where
  matrix : SwanepoelW11ClosureMatrix.Matrix.{u}
  w8 :
    SwanepoelW11ClosureMatrix.W8Matrix.{u} -> Target
  w9Direct :
    SwanepoelW11ClosureMatrix.W9DirectMatrix.{u} -> Target
  w9K23 :
    SwanepoelW11ClosureMatrix.W9K23Matrix.{u} -> Target
  w10TargetFacade :
    SwanepoelW11ClosureMatrix.W10TargetFacadeMatrix -> Target
  w10DirectComponents :
    SwanepoelW11ClosureMatrix.W10DirectComponentMatrix.{u} -> Target
  w10K23Components :
    SwanepoelW11ClosureMatrix.W10K23ComponentMatrix.{u} -> Target
  w10MinimalFailureDirect :
    SwanepoelW11ClosureMatrix.W10MinimalFailureDirectMatrix.{u} -> Target
  w10DirectGeometry :
    SwanepoelW11ClosureMatrix.W10DirectGeometryMatrix.{u} -> Target
  w10K23Geometry :
    SwanepoelW11ClosureMatrix.W10K23GeometryMatrix.{u} -> Target
  w10CommonNeighborGeometry :
    SwanepoelW11ClosureMatrix.W10CommonNeighborGeometryMatrix.{u} -> Target

/-- The downstream W11 target ledger assembled from checked matrix rows. -/
def targetMatrixLedger : TargetMatrixLedger.{u} where
  matrix := SwanepoelW11ClosureMatrix.matrix
  w8 := SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w8Matrix
  w9Direct :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w9DirectMatrix
  w9K23 :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w9K23Matrix
  w10TargetFacade :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10TargetFacadeMatrix
  w10DirectComponents :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10DirectComponentMatrix
  w10K23Components :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10K23ComponentMatrix
  w10MinimalFailureDirect :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10MinimalFailureDirectMatrix
  w10DirectGeometry :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10DirectGeometryMatrix
  w10K23Geometry :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10K23GeometryMatrix
  w10CommonNeighborGeometry :=
    SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10CommonNeighborGeometryMatrix

/-! ## Consolidated closure matrix -/

/-- A compact ledger of the checked closure projections in this file. -/
structure Matrix : Type (u + 1) where
  topologyExact :
    forall {n : Nat} {C : _root_.UDConfig n},
      TopologyFrontierPackage C -> W10ExactFieldTarget C
  topologyFrontier :
    forall {n : Nat} {C : _root_.UDConfig n},
      TopologyFrontierPackage C -> W10NoncrossingToExactFrontier C
  boundaryCounting :
    forall {n : Nat} {C : _root_.UDConfig n}
      (B : ExplicitBoundarySubpolygonPackage C),
        PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
          B.planarBoundary
  targetLedger : TargetMatrixLedger.{u}

/-- The checked W11 topology closure matrix. -/
def matrix : Matrix.{u} where
  topologyExact := fun T => T.exactFieldTarget
  topologyFrontier := fun T => T.noncrossingToExactFrontier
  boundaryCounting := fun B => B.faceCountingTheorems
  targetLedger := targetMatrixLedger

/-! ## Public projections -/

/-- Public W10 exact-field projection from a checked topology package. -/
theorem w10ExactFieldTarget_of_checkedTopologyPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    W10ExactFieldTarget C :=
  (TopologyFrontierPackage.mk T).exactFieldTarget

/-- Public W10 frontier projection from a checked topology package. -/
theorem w10NoncrossingToExactFrontier_of_checkedTopologyPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    W10NoncrossingToExactFrontier C :=
  (TopologyFrontierPackage.mk T).noncrossingToExactFrontier

/-- Public remaining-core projection from a checked topology package. -/
theorem remainingCoreTopologyRequirements_of_checkedTopologyPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  (TopologyFrontierPackage.mk T).remainingCoreTopologyRequirements

/-- Public face-count theorem projection from explicit boundary/subpolygon data. -/
theorem faceCountingTheorems_of_explicitBoundarySubpolygonPackage
    {C : _root_.UDConfig n}
    (B : ExplicitBoundarySubpolygonPackage C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      B.planarBoundary :=
  B.faceCountingTheorems

/-- Public target projection from the downstream W10 direct-geometry matrix. -/
theorem targetLowerBoundEightThirtyOne_of_w10DirectGeometryMatrix
    (M : SwanepoelW11ClosureMatrix.W10DirectGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10DirectGeometryMatrix M

/-- Public target projection from the downstream W10 common-neighbor matrix. -/
theorem targetLowerBoundEightThirtyOne_of_w10CommonNeighborGeometryMatrix
    (M : SwanepoelW11ClosureMatrix.W10CommonNeighborGeometryMatrix.{u}) :
    Target :=
  SwanepoelW11ClosureMatrix.targetLowerBoundEightThirtyOne_of_w10CommonNeighborGeometryMatrix M

end

end TopologyClosureW11
end Swanepoel
end ErdosProblems1066
