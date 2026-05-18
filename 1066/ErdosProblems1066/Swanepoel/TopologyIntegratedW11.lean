import ErdosProblems1066.Swanepoel.TopologyClosureW11
import ErdosProblems1066.Swanepoel.SubpolygonIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 integrated topology matrix

This module is a source-facing integration layer for the checked W11
topology, boundary-angle, subpolygon, and target-route packages.

The topology extraction payload is displayed as named fields.  Boundary and
subpolygon sources are routed into the existing W11 closure ledgers, and the
target-facing rows stay conditional on explicit geometry matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyIntegratedW11

open FaceReduction
open MinimalGraphFacts
open OuterBoundaryInterface
open SubpolygonInstantiation

universe u v

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  TopologyClosureW11.CanonicalGraph C

abbrev CheckedTopologyPackage (C : _root_.UDConfig n) :=
  TopologyInstantiationW11.CheckedTopologyPackage C

abbrev TopologyFrontierPackage (C : _root_.UDConfig n) :=
  TopologyClosureW11.TopologyFrontierPackage C

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  BoundaryAngleClosureW11.BoundaryAngleClosureInput.{u} C

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

/-! ## Explicit topology extraction fields -/

/-- The concrete topology fields extracted from a checked topology package. -/
structure TopologyExtractionFields
    (C : _root_.UDConfig n) : Type 1 where
  frontier : TopologyFrontierPackage C
  core : OuterBoundaryCore.{0} (CanonicalGraph C)
  exactFields : TopologyFrontierW10.ExactOuterBoundaryTopologyFields C
  selectedOuterFaceFields :
    TopologyExtractionFromNoncrossing.SelectedOuterFaceFields C
  enclosureFields :
    TopologyExtractionFromNoncrossing.EnclosureFields
      selectedOuterFaceFields
  splitExactTopologyFields :
    TopologyExtractionFromNoncrossing.SplitExactTopologyFields C
  missingTopologyFacts :
    JordanBoundaryConcrete.MissingTopologyFacts.{0} C
  topologyFacts :
    JordanTopologyFactsConcrete.TopologyFacts.{0} C
  extractionData :
    JordanBoundaryExtraction.Data.{0} (CanonicalGraph C)
  topologyComponentFields :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C

namespace TopologyExtractionFields

variable {C : _root_.UDConfig n}

/-- Extract all displayed topology fields from a topology frontier row. -/
def ofFrontier
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFields C where
  frontier := T
  core := T.core
  exactFields := T.exactFields
  selectedOuterFaceFields := T.selectedOuterFaceFields
  enclosureFields := T.enclosureFields
  splitExactTopologyFields := T.splitExactTopologyFields
  missingTopologyFacts := T.missingTopologyFacts
  topologyFacts := T.topologyFacts
  extractionData := T.extractionData
  topologyComponentFields := T.toTopologyComponentFields

/-- Extract all displayed topology fields from a compact checked package. -/
def ofChecked
    (T : CheckedTopologyPackage C) :
    TopologyExtractionFields C :=
  ofFrontier ({ topology := T } : TopologyFrontierPackage C)

/-- The compact checked topology package underlying the extracted fields. -/
def checkedTopology
    (T : TopologyExtractionFields C) :
    CheckedTopologyPackage C :=
  T.frontier.topology

/-- The extracted exact fields inhabit the W10 exact topology target. -/
theorem exactFieldTarget
    (T : TopologyExtractionFields C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  Nonempty.intro T.exactFields

/-- The extracted exact fields give the W10 noncrossing-to-exact frontier. -/
theorem noncrossingToExactFrontier
    (T : TopologyExtractionFields C) :
    TopologyClosureW11.W10NoncrossingToExactFrontier C :=
  (TopologyFrontierW10.noncrossingToExactFrontier_iff_exactFieldTarget
      C).2 T.exactFieldTarget

/-- The extracted exact fields give the older noncrossing topology frontier. -/
theorem concreteNoncrossingTopologyFrontier
    (T : TopologyExtractionFields C) :
    TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier
      C :=
  TopologyFrontierW10.concreteNoncrossingTopologyFrontier_of_exactFields
    T.exactFields

/-- The extracted exact fields discharge the remaining core-topology row. -/
theorem remainingCoreTopologyRequirements
    (T : TopologyExtractionFields C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  TopologyFrontierW10.remainingCoreTopologyRequirements_of_exactFields
    T.exactFields

/-- The extracted Jordan-topology fields inhabit the remaining topology row. -/
theorem remainingTopologyTheorem
    (T : TopologyExtractionFields C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem
      C :=
  Nonempty.intro T.missingTopologyFacts

@[simp]
theorem ofFrontier_core
    (T : TopologyFrontierPackage C) :
    (ofFrontier T).core = T.core :=
  rfl

@[simp]
theorem ofFrontier_exactFields
    (T : TopologyFrontierPackage C) :
    (ofFrontier T).exactFields = T.exactFields :=
  rfl

@[simp]
theorem ofChecked_core
    (T : CheckedTopologyPackage C) :
    (ofChecked T).core = T.toCore :=
  rfl

@[simp]
theorem ofChecked_extractionData
    (T : CheckedTopologyPackage C) :
    (ofChecked T).extractionData = T.toExtractionData :=
  rfl

end TopologyExtractionFields

/-! ## Boundary and subpolygon packages -/

/-- Boundary-angle input with its checked topology and subpolygon projections. -/
structure BoundarySubpolygonPackage
    (C : _root_.UDConfig n) : Type (u + 1) where
  boundary : BoundaryInput.{u} C

namespace BoundarySubpolygonPackage

variable {C : _root_.UDConfig n}

/-- Explicit selected face, enclosure, and boundary-angle data. -/
def explicitFaceData
    (B : BoundarySubpolygonPackage.{u} C) :
    ExplicitOuterBoundaryFaceData.{u} (CanonicalGraph C) :=
  B.boundary.explicitFaceData

/-- The concrete subpolygon family over the selected boundary data. -/
def subpolygons
    (B : BoundarySubpolygonPackage.{u} C) :
    SubpolygonFamilyW11.SubpolygonFamilyPackage.{u}
      B.explicitFaceData :=
  B.boundary.subpolygons

/-- The subpolygon index type selected by the package. -/
abbrev Subpolygon
    (B : BoundarySubpolygonPackage.{u} C) :
    Type u :=
  B.subpolygons.Subpolygon

/-- Concrete subpolygon data consumed by the boundary/turn route. -/
def subpolygonData
    (B : BoundarySubpolygonPackage.{u} C)
    (S : B.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C) :=
  B.boundary.subpolygonData S

/-- The W9 topology/angle/subpolygon row selected by the boundary package. -/
def topologyAngleSubpolygonRow
    (B : BoundarySubpolygonPackage.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  B.boundary.toTopologyAngleSubpolygonRow

/-- The W10 topology/angle/long-arc geometry fields from the same package. -/
def geometryTopologyAngleLongArcFields
    (B : BoundarySubpolygonPackage.{u} C) :
    GeometryRemainingFieldsW10.TopologyAngleLongArcFields.{u} C :=
  B.boundary.toGeometryTopologyAngleLongArcFields

/-- W10 topology component fields selected by the same package. -/
def w10TopologyComponentFields
    (B : BoundarySubpolygonPackage.{u} C) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C :=
  B.boundary.toW10TopologyComponentFields

/-- W10 partition/angle component fields selected by the same package. -/
def w10PartitionAngleComponentFields
    (B : BoundarySubpolygonPackage.{u} C) :
    MinimalFailureDirectMatrixW10.PartitionAngleComponentFields.{u}
      C B.w10TopologyComponentFields :=
  B.boundary.toW10PartitionAngleComponentFields

/-- The checked face-counting theorems for the selected subpolygon family. -/
theorem faceCountingTheorems
    (B : BoundarySubpolygonPackage.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      B.subpolygons.toPlanarBoundaryData :=
  B.subpolygons.faceCountingTheorems

/-- The checked boundary-angle count inequality for the selected package. -/
theorem boundaryAngleCountInequality
    (B : BoundarySubpolygonPackage.{u} C) :
    B.boundary.classification.counts.d5 +
        2 * B.boundary.classification.counts.d6 +
        B.boundary.classification.counts.b +
        B.boundary.classification.counts.B + 6 <=
      B.boundary.classification.counts.d3 :=
  B.boundary.boundaryAngleCountInequality

/-- The checked negative-element boundary count inequality. -/
theorem boundaryNegativeCountInequality
    (B : BoundarySubpolygonPackage.{u} C) :
    B.boundary.classification.counts.negativeCount +
        B.boundary.classification.counts.B + 6 <=
      B.boundary.classification.counts.d3 :=
  B.boundary.boundaryNegativeCountInequality

/-- The checked low-degree row for every selected subpolygon. -/
theorem subpolygonLowDegree
    (B : BoundarySubpolygonPackage.{u} C)
    (S : B.Subpolygon) :
    6 <= 2 * (B.subpolygonData S).counts.D2 +
      (B.subpolygonData S).counts.D3 :=
  B.boundary.subpolygonLowDegree S

/-- The compact checked topology package selected by a universe-zero row. -/
def checkedTopology
    (B : BoundarySubpolygonPackage.{0} C) :
    CheckedTopologyPackage C :=
  TopologyInstantiationW11.ofTopologyFacts B.boundary.topology

/-- The full displayed topology extraction payload for a universe-zero row. -/
def topologyExtraction
    (B : BoundarySubpolygonPackage.{0} C) :
    TopologyExtractionFields C :=
  TopologyExtractionFields.ofChecked B.checkedTopology

/-- Repackage a universe-zero boundary row into the topology closure package. -/
def toTopologyClosurePackage
    (B : BoundarySubpolygonPackage.{0} C) :
    TopologyClosureW11.ExplicitBoundarySubpolygonPackage C where
  topology := TopologyInstantiationW11.ofTopologyFacts B.boundary.topology
  faceData := B.boundary.explicitFaceData
  faceData_core_eq := by
    rfl
  subpolygons := B.boundary.subpolygons

@[simp]
theorem toTopologyClosurePackage_topology
    (B : BoundarySubpolygonPackage.{0} C) :
    B.toTopologyClosurePackage.topology = B.checkedTopology :=
  rfl

@[simp]
theorem toTopologyClosurePackage_faceData
    (B : BoundarySubpolygonPackage.{0} C) :
    B.toTopologyClosurePackage.faceData = B.boundary.explicitFaceData :=
  rfl

/-- The topology closure face-count route for a universe-zero package. -/
theorem topologyClosureFaceCountingTheorems
    (B : BoundarySubpolygonPackage.{0} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      B.toTopologyClosurePackage.planarBoundary :=
  B.toTopologyClosurePackage.faceCountingTheorems

end BoundarySubpolygonPackage

/-- Build the integrated boundary/subpolygon package from boundary input. -/
def boundarySubpolygonPackageOfInput
    {C : _root_.UDConfig n}
    (B : BoundaryInput.{u} C) :
    BoundarySubpolygonPackage.{u} C where
  boundary := B

/-! ## Target facade routes from boundary-sourced geometry matrices -/

/-- Target routes supplied by the checked subpolygon integration module. -/
structure BoundaryGeometryTargetRoutes : Type (u + 3) where
  directToBoundaryClosure :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u} ->
      BoundaryAngleClosureW11.BoundaryDirectGeometryMatrix.{u}
  k23ToBoundaryClosure :
    SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u} ->
      BoundaryAngleClosureW11.BoundaryK23GeometryMatrix.{u}
  commonNeighborToBoundaryClosure :
    SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u} ->
      BoundaryAngleClosureW11.BoundaryCommonNeighborGeometryMatrix.{u}
  directNoMinimal :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u} ->
      MinimalFailureExclusion
  k23NoMinimal :
    SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u} ->
      MinimalFailureExclusion
  commonNeighborNoMinimal :
    SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u} ->
      MinimalFailureExclusion
  directPipeline :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u} ->
      PipelineCleared
  k23Pipeline :
    SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u} ->
      PipelineCleared
  commonNeighborPipeline :
    SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u} ->
      PipelineCleared
  directTarget :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u} ->
      Target
  k23Target :
    SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u} ->
      Target
  commonNeighborTarget :
    SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u} ->
      Target

/-- Boundary-sourced geometry target routes from the integrated subpolygon row. -/
def boundaryGeometryTargetRoutes :
    BoundaryGeometryTargetRoutes.{u} where
  directToBoundaryClosure :=
    SubpolygonIntegratedW11.matrix.directToBoundaryClosure
  k23ToBoundaryClosure :=
    SubpolygonIntegratedW11.matrix.k23ToBoundaryClosure
  commonNeighborToBoundaryClosure :=
    SubpolygonIntegratedW11.matrix.commonNeighborToBoundaryClosure
  directNoMinimal := SubpolygonIntegratedW11.matrix.directNoMinimal
  k23NoMinimal := SubpolygonIntegratedW11.matrix.k23NoMinimal
  commonNeighborNoMinimal :=
    SubpolygonIntegratedW11.matrix.commonNeighborNoMinimal
  directPipeline := SubpolygonIntegratedW11.matrix.directPipeline
  k23Pipeline := SubpolygonIntegratedW11.matrix.k23Pipeline
  commonNeighborPipeline :=
    SubpolygonIntegratedW11.matrix.commonNeighborPipeline
  directTarget := SubpolygonIntegratedW11.matrix.directTarget
  k23Target := SubpolygonIntegratedW11.matrix.k23Target
  commonNeighborTarget := SubpolygonIntegratedW11.matrix.commonNeighborTarget

/-- Imported W11 ledgers consumed by this topology integration layer. -/
structure ImportedLedgers : Type (u + 3) where
  topologyClosure : TopologyClosureW11.Matrix.{u}
  subpolygonIntegrated : SubpolygonIntegratedW11.Matrix.{u}
  targetIntegrated : TargetIntegratedMatrixW11.Matrix.{u}

/-- The imported W11 ledgers available to this layer. -/
def importedLedgers : ImportedLedgers.{u} where
  topologyClosure := TopologyClosureW11.matrix
  subpolygonIntegrated := SubpolygonIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix

/-! ## Integrated matrix -/

/-- Integrated W11 topology matrix.

The matrix records checked projections and target facades.  Every target route
still takes an explicit boundary-sourced geometry matrix as input.
-/
structure Matrix : Type (u + 3) where
  topologyExtraction :
    forall {n : Nat} {C : _root_.UDConfig n},
      TopologyFrontierPackage C -> TopologyExtractionFields C
  checkedTopologyExtraction :
    forall {n : Nat} {C : _root_.UDConfig n},
      CheckedTopologyPackage C -> TopologyExtractionFields C
  boundarySubpolygon :
    forall {n : Nat} {C : _root_.UDConfig n},
      BoundaryInput.{u} C -> BoundarySubpolygonPackage.{u} C
  imported : ImportedLedgers.{u}
  boundaryGeometryTargets : BoundaryGeometryTargetRoutes.{u}

/-- The checked integrated topology matrix assembled from present W11 modules. -/
def matrix : Matrix.{u} where
  topologyExtraction := fun T =>
    TopologyExtractionFields.ofFrontier T
  checkedTopologyExtraction := fun T =>
    TopologyExtractionFields.ofChecked T
  boundarySubpolygon := fun B =>
    boundarySubpolygonPackageOfInput B
  imported := importedLedgers
  boundaryGeometryTargets := boundaryGeometryTargetRoutes

/-! ## Public projections -/

/-- Public extraction of all displayed topology fields from a checked package. -/
def topologyExtractionFieldsOfCheckedPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    TopologyExtractionFields C :=
  TopologyExtractionFields.ofChecked T

/-- Public extraction of all displayed topology fields from a frontier row. -/
def topologyExtractionFieldsOfFrontier
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFields C :=
  TopologyExtractionFields.ofFrontier T

/-- Public exact-topology projection from displayed extraction fields. -/
theorem exactFieldTargetOfTopologyExtraction
    {C : _root_.UDConfig n}
    (T : TopologyExtractionFields C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  T.exactFieldTarget

/-- Public remaining-core projection from displayed extraction fields. -/
theorem remainingCoreTopologyRequirementsOfTopologyExtraction
    {C : _root_.UDConfig n}
    (T : TopologyExtractionFields C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  T.remainingCoreTopologyRequirements

/-- Public boundary/subpolygon package from a checked boundary input. -/
def boundarySubpolygonPackageOfBoundaryInput
    {C : _root_.UDConfig n}
    (B : BoundaryInput.{u} C) :
    BoundarySubpolygonPackage.{u} C :=
  boundarySubpolygonPackageOfInput B

/-- Public W9 topology/angle/subpolygon route from the integrated package. -/
def topologyAngleSubpolygonRowOfBoundarySubpolygonPackage
    {C : _root_.UDConfig n}
    (B : BoundarySubpolygonPackage.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  B.topologyAngleSubpolygonRow

/-- Public face-counting projection from the integrated package. -/
theorem faceCountingTheoremsOfBoundarySubpolygonPackage
    {C : _root_.UDConfig n}
    (B : BoundarySubpolygonPackage.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      B.subpolygons.toPlanarBoundaryData :=
  B.faceCountingTheorems

/-- Public target facade from direct boundary-sourced geometry rows. -/
theorem targetFacadeOfDirectBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}) :
    Target :=
  boundaryGeometryTargetRoutes.directTarget M

/-- Public target facade from K23 boundary-sourced geometry rows. -/
theorem targetFacadeOfK23BoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u}) :
    Target :=
  boundaryGeometryTargetRoutes.k23Target M

/-- Public target facade from common-neighbor boundary-sourced geometry rows. -/
theorem targetFacadeOfCommonNeighborBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u}) :
    Target :=
  boundaryGeometryTargetRoutes.commonNeighborTarget M

/-- Direct boundary-sourced geometry rows rule out minimal cleared failures. -/
theorem noMinimalFailureOfDirectBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  boundaryGeometryTargetRoutes.directNoMinimal M

/-- K23 boundary-sourced geometry rows rule out minimal cleared failures. -/
theorem noMinimalFailureOfK23BoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  boundaryGeometryTargetRoutes.k23NoMinimal M

/-- Common-neighbor boundary-sourced geometry rows rule out minimal failures. -/
theorem noMinimalFailureOfCommonNeighborBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  boundaryGeometryTargetRoutes.commonNeighborNoMinimal M

/-- Direct boundary-sourced geometry rows clear the target pipeline facade. -/
theorem pipelineClearedOfDirectBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}) :
    PipelineCleared :=
  boundaryGeometryTargetRoutes.directPipeline M

/-- K23 boundary-sourced geometry rows clear the target pipeline facade. -/
theorem pipelineClearedOfK23BoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u}) :
    PipelineCleared :=
  boundaryGeometryTargetRoutes.k23Pipeline M

/-- Common-neighbor rows clear the target pipeline facade. -/
theorem pipelineClearedOfCommonNeighborBoundaryGeometryMatrix
    (M : SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u}) :
    PipelineCleared :=
  boundaryGeometryTargetRoutes.commonNeighborPipeline M

end

end TopologyIntegratedW11
end Swanepoel
end ErdosProblems1066
