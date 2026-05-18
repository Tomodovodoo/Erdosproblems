import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleClosureW11
import ErdosProblems1066.Swanepoel.SubpolygonIntegratedW11
import ErdosProblems1066.Swanepoel.TopologyIntegratedW11
import ErdosProblems1066.Swanepoel.TargetLedgerConsistencyW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ConsistencyMatrix

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 boundary-angle aggregate

This file gathers the checked W11 boundary-angle, topology, subpolygon, target
ledger, and consistency matrices behind one explicit aggregate row shape.  The
row keeps the boundary topology, boundary classification, subpolygon family,
long-arc fields, boundary labels, window containment, and each selectable
no-early route visible as supplied fields.

All target projections below are conditional on a caller-supplied uniform
family of final rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleFinalIntegratedW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  BoundaryAngleClosureW11.BoundaryAngleClosureInput.{u} C

/-! ## Explicit boundary-angle source fields -/

/-- Boundary-angle source data with the topology, classification, subpolygon,
and long-arc pieces displayed before labels and window/no-early rows are
added. -/
structure BoundaryAngleSourceFields
    (C : _root_.UDConfig n) : Type (u + 1) where
  topology : JordanTopologyFactsConcrete.TopologyFacts C
  classification :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toCore
  angleWitness :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
      classification
  subpolygons :
    SubpolygonFamilyW11.SubpolygonFamilyPackage
      (BoundaryAngleClosureW11.explicitFaceDataOfTopologyAngle
        topology classification angleWitness)
  longArcFields :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      classification angleWitness.geometricAngleSum
      angleWitness.forced_le_geometricAngleSum
      angleWitness.geometric_le_polygon
      subpolygons.Subpolygon
      (fun S => subpolygons.toPlanarBoundaryData.subpolygonData S)

namespace BoundaryAngleSourceFields

variable {C : _root_.UDConfig n}

/-- Repackage the displayed source fields as the boundary-angle closure input. -/
def toBoundaryInput
    (S : BoundaryAngleSourceFields.{u} C) :
    BoundaryInput.{u} C where
  topology := S.topology
  classification := S.classification
  angleWitness := S.angleWitness
  subpolygons := S.subpolygons
  longArcFields := S.longArcFields

/-- The topology-integrated boundary/subpolygon package selected by the
source fields. -/
def toTopologyBoundarySubpolygonPackage
    (S : BoundaryAngleSourceFields.{u} C) :
    TopologyIntegratedW11.BoundarySubpolygonPackage.{u} C where
  boundary := S.toBoundaryInput

/-- The concrete boundary classification remains a visible source field. -/
def toClassification
    (S : BoundaryAngleSourceFields.{u} C) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      S.topology.toCore :=
  S.classification

/-- The concrete subpolygon family remains a visible source field. -/
def toSubpolygonFamily
    (S : BoundaryAngleSourceFields.{u} C) :
    SubpolygonFamilyW11.SubpolygonFamilyPackage
      (BoundaryAngleClosureW11.explicitFaceDataOfTopologyAngle
        S.topology S.classification S.angleWitness) :=
  S.subpolygons

/-- The long-arc field selected by the final source package. -/
def toLongArcFields
    (S : BoundaryAngleSourceFields.{u} C) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      S.classification S.angleWitness.geometricAngleSum
      S.angleWitness.forced_le_geometricAngleSum
      S.angleWitness.geometric_le_polygon
      S.subpolygons.Subpolygon
      (fun T => S.subpolygons.toPlanarBoundaryData.subpolygonData T) :=
  S.longArcFields

/-- The checked W9 topology/angle/subpolygon row from the same source fields. -/
def toTopologyAngleSubpolygonRow
    (S : BoundaryAngleSourceFields.{u} C) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  S.toBoundaryInput.toTopologyAngleSubpolygonRow

/-- The checked W10 topology/angle/long-arc geometry fields. -/
def toGeometryTopologyAngleLongArcFields
    (S : BoundaryAngleSourceFields.{u} C) :
    GeometryRemainingFieldsW10.TopologyAngleLongArcFields.{u} C :=
  S.toBoundaryInput.toGeometryTopologyAngleLongArcFields

/-- The checked outer-boundary E12 inequality for the visible classification. -/
theorem boundaryAngleCountInequality
    (S : BoundaryAngleSourceFields.{u} C) :
    S.classification.counts.d5 + 2 * S.classification.counts.d6 +
        S.classification.counts.b + S.classification.counts.B + 6 <=
      S.classification.counts.d3 :=
  S.toBoundaryInput.boundaryAngleCountInequality

/-- The checked negative-count E12 form for the visible classification. -/
theorem boundaryNegativeCountInequality
    (S : BoundaryAngleSourceFields.{u} C) :
    S.classification.counts.negativeCount +
        S.classification.counts.B + 6 <=
      S.classification.counts.d3 :=
  S.toBoundaryInput.boundaryNegativeCountInequality

/-- The checked E13 low-degree inequality for every visible subpolygon. -/
theorem subpolygonLowDegree
    (S : BoundaryAngleSourceFields.{u} C)
    (T : S.subpolygons.Subpolygon) :
    6 <= 2 * (S.toBoundaryInput.subpolygonData T).counts.D2 +
      (S.toBoundaryInput.subpolygonData T).counts.D3 :=
  S.toBoundaryInput.subpolygonLowDegree T

/-- The selected long-arc turn bound from the source package. -/
theorem totalTurn_lt_pi_div_three
    (S : BoundaryAngleSourceFields.{u} C) :
    Lemma10Inequalities.totalTurn
        S.toBoundaryInput.boundaryAngleTurnPackage.m8TurnBounds.turn <
      Real.pi / 3 :=
  S.toBoundaryInput.m8TurnBounds_totalTurn_lt_pi_div_three

@[simp]
theorem toBoundaryInput_topology
    (S : BoundaryAngleSourceFields.{u} C) :
    S.toBoundaryInput.topology = S.topology :=
  rfl

@[simp]
theorem toBoundaryInput_classification
    (S : BoundaryAngleSourceFields.{u} C) :
    S.toBoundaryInput.classification = S.classification :=
  rfl

@[simp]
theorem toBoundaryInput_subpolygons
    (S : BoundaryAngleSourceFields.{u} C) :
    S.toBoundaryInput.subpolygons = S.subpolygons :=
  rfl

@[simp]
theorem toBoundaryInput_longArcFields
    (S : BoundaryAngleSourceFields.{u} C) :
    S.toBoundaryInput.longArcFields = S.longArcFields :=
  rfl

end BoundaryAngleSourceFields

/-! ## Labelled final rows -/

/-- Boundary-angle source fields plus the matching explicit W11 label row. -/
structure LabelledBoundaryAngleSource
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  source : BoundaryAngleSourceFields.{u} C
  labels :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.{u}
      C hmin source.toBoundaryInput.toW10TopologyComponentFields
        source.toBoundaryInput.toW10PartitionAngleComponentFields

namespace LabelledBoundaryAngleSource

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View the displayed source and labels as the integrated boundary-angle
label prefix. -/
def toBoundaryAngleLabelPrefix
    (L : LabelledBoundaryAngleSource.{u} C hmin) :
    BoundaryAngleIntegratedW11.BoundaryAngleLabelPrefix.{u} C hmin where
  boundary := L.source.toBoundaryInput
  labels := L.labels

/-- View the displayed source and labels as the W10 label-base prefix. -/
def toLabelBasePrefix
    (L : LabelledBoundaryAngleSource.{u} C hmin) :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix.{u}
      C hmin :=
  L.toBoundaryAngleLabelPrefix.toLabelBasePrefix

/-- The geometry source fields determined by the displayed source and labels. -/
def toGeometrySourceFields
    (L : LabelledBoundaryAngleSource.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  L.toBoundaryAngleLabelPrefix.toGeometrySourceFields

/-- The checked base row reached from the displayed labels. -/
def toW9BaseRow
    (L : LabelledBoundaryAngleSource.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin :=
  L.toBoundaryAngleLabelPrefix.toW9BaseRow

/-- The checked topology/angle/subpolygon row selected before labels. -/
def toTopologyAngleSubpolygonRow
    (L : LabelledBoundaryAngleSource.{u} C hmin) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  L.source.toTopologyAngleSubpolygonRow

@[simp]
theorem toBoundaryAngleLabelPrefix_boundary
    (L : LabelledBoundaryAngleSource.{u} C hmin) :
    L.toBoundaryAngleLabelPrefix.boundary = L.source.toBoundaryInput :=
  rfl

@[simp]
theorem toBoundaryAngleLabelPrefix_labels
    (L : LabelledBoundaryAngleSource.{u} C hmin) :
    L.toBoundaryAngleLabelPrefix.labels = L.labels :=
  rfl

end LabelledBoundaryAngleSource

/-! ## Final pointwise aggregate row -/

/-- One final boundary-angle aggregate row for a fixed minimal cleared
failure.

The row keeps labels, window containment, direct no-start/no-early fields, K23
no-early fields, and common-neighbor no-early fields as separate supplied
fields over the same labelled boundary-angle source. -/
structure BoundaryAngleFinalRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  labelled : LabelledBoundaryAngleSource.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      labelled.toGeometrySourceFields
  directNoEarly :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      labelled.toGeometrySourceFields
  k23NoEarly :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      labelled.toGeometrySourceFields
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      labelled.toGeometrySourceFields

namespace BoundaryAngleFinalRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The visible boundary-angle source fields. -/
def source
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryAngleSourceFields.{u} C :=
  R.labelled.source

/-- The visible boundary classification field. -/
def classification
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      R.source.topology.toCore :=
  R.source.classification

/-- The visible subpolygon family field. -/
def subpolygons
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    SubpolygonFamilyW11.SubpolygonFamilyPackage
      (BoundaryAngleClosureW11.explicitFaceDataOfTopologyAngle
        R.source.topology R.source.classification R.source.angleWitness) :=
  R.source.subpolygons

/-- The visible long-arc field. -/
def longArcFields
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      R.source.classification R.source.angleWitness.geometricAngleSum
      R.source.angleWitness.forced_le_geometricAngleSum
      R.source.angleWitness.geometric_le_polygon
      R.source.subpolygons.Subpolygon
      (fun T => R.source.subpolygons.toPlanarBoundaryData.subpolygonData T) :=
  R.source.longArcFields

/-- The visible label field. -/
def labels
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.{u}
      C hmin R.source.toBoundaryInput.toW10TopologyComponentFields
        R.source.toBoundaryInput.toW10PartitionAngleComponentFields :=
  R.labelled.labels

/-- The geometry source selected by the final row. -/
def geometrySource
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.labelled.toGeometrySourceFields

/-- Repackage as the integrated boundary-angle label prefix. -/
def toBoundaryAngleLabelPrefix
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryAngleIntegratedW11.BoundaryAngleLabelPrefix.{u} C hmin :=
  R.labelled.toBoundaryAngleLabelPrefix

/-- Repackage as the integrated direct boundary-angle geometry row. -/
def toBoundaryAngleDirectGeometryRow
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryAngleIntegratedW11.DirectGeometryRow.{u} C hmin where
  boundaryPrefix := R.toBoundaryAngleLabelPrefix
  window := R.window
  noStartNoEarly := R.directNoEarly

/-- Repackage as the integrated K23 boundary-angle geometry row. -/
def toBoundaryAngleK23GeometryRow
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryAngleIntegratedW11.K23GeometryRow.{u} C hmin where
  boundaryPrefix := R.toBoundaryAngleLabelPrefix
  window := R.window
  k23NoEarly := R.k23NoEarly

/-- Repackage as the integrated common-neighbor boundary-angle geometry row. -/
def toBoundaryAngleCommonNeighborGeometryRow
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BoundaryAngleIntegratedW11.CommonNeighborGeometryRow.{u} C hmin where
  boundaryPrefix := R.toBoundaryAngleLabelPrefix
  window := R.window
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- View final direct fields as a source-facing broken-lattice package. -/
def toDirectFieldPackage
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin where
  source := R.geometrySource
  containment := R.window
  noStartNoEarly := R.directNoEarly

/-- View final K23 fields as a source-facing broken-lattice package. -/
def toK23FieldPackage
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin where
  source := R.geometrySource
  containment := R.window
  k23NoEarly := R.k23NoEarly

/-- View final common-neighbor fields as a source-facing broken-lattice
package. -/
def toCommonNeighborFieldPackage
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin where
  source := R.geometrySource
  containment := R.window
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- A fixed final row closes through its direct geometry route. -/
theorem contradiction_via_direct
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    False :=
  R.toBoundaryAngleDirectGeometryRow.contradiction

/-- A fixed final row closes through its K23 geometry route. -/
theorem contradiction_via_k23
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    False :=
  R.toBoundaryAngleK23GeometryRow.contradiction

/-- A fixed final row closes through its common-neighbor geometry route. -/
theorem contradiction_via_commonNeighbor
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    False :=
  R.toBoundaryAngleCommonNeighborGeometryRow.contradiction

@[simp]
theorem source_topology
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    R.source.topology = R.labelled.source.topology :=
  rfl

@[simp]
theorem geometrySource_eq
    (R : BoundaryAngleFinalRow.{u} C hmin) :
    R.geometrySource = R.labelled.toGeometrySourceFields :=
  rfl

end BoundaryAngleFinalRow

/-! ## Uniform final row families -/

/-- Uniform final boundary-angle rows for every minimal cleared failure. -/
structure BoundaryAngleFinalMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryAngleFinalRow.{u} C hmin

namespace BoundaryAngleFinalMatrix

/-- Forget final rows to integrated direct boundary-angle rows. -/
def toBoundaryAngleDirectGeometryMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBoundaryAngleDirectGeometryRow

/-- Forget final rows to integrated K23 boundary-angle rows. -/
def toBoundaryAngleK23GeometryMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    BoundaryAngleIntegratedW11.K23GeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBoundaryAngleK23GeometryRow

/-- Forget final rows to integrated common-neighbor boundary-angle rows. -/
def toBoundaryAngleCommonNeighborGeometryMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBoundaryAngleCommonNeighborGeometryRow

/-- Forget final rows to direct broken-lattice field matrices. -/
def toDirectFieldMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toDirectFieldPackage

/-- Forget final rows to K23 broken-lattice field matrices. -/
def toK23FieldMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toK23FieldPackage

/-- Forget final rows to common-neighbor broken-lattice field matrices. -/
def toCommonNeighborFieldMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborFieldPackage

/-- Minimal-failure eliminator through the direct final row route. -/
theorem minimalClearedFailureEliminator_via_direct
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_directFieldMatrix
    M.toDirectFieldMatrix

/-- Minimal-failure eliminator through the K23 final row route. -/
theorem minimalClearedFailureEliminator_via_k23
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_k23FieldMatrix
    M.toK23FieldMatrix

/-- Minimal-failure eliminator through the common-neighbor final row route. -/
theorem minimalClearedFailureEliminator_via_commonNeighbor
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
    M.toCommonNeighborFieldMatrix

/-- Minimal-failure exclusion through the direct final row route. -/
theorem no_minimalClearedFailure_via_direct
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_directFieldMatrix
    M.toDirectFieldMatrix

/-- Minimal-failure exclusion through the K23 final row route. -/
theorem no_minimalClearedFailure_via_k23
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_k23FieldMatrix
    M.toK23FieldMatrix

/-- Minimal-failure exclusion through the common-neighbor final row route. -/
theorem no_minimalClearedFailure_via_commonNeighbor
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
    M.toCommonNeighborFieldMatrix

/-- Cleared-pipeline projection through the direct final row route. -/
theorem pipelineCleared_via_direct
    (M : BoundaryAngleFinalMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_directFieldMatrix
    M.toDirectFieldMatrix

/-- Cleared-pipeline projection through the K23 final row route. -/
theorem pipelineCleared_via_k23
    (M : BoundaryAngleFinalMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_k23FieldMatrix
    M.toK23FieldMatrix

/-- Cleared-pipeline projection through the common-neighbor final row route. -/
theorem pipelineCleared_via_commonNeighbor
    (M : BoundaryAngleFinalMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_commonNeighborFieldMatrix
    M.toCommonNeighborFieldMatrix

/-- Conditional Swanepoel target projection through direct final fields. -/
theorem target_via_direct
    (M : BoundaryAngleFinalMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix
    M.toDirectFieldMatrix

/-- Conditional Swanepoel target projection through K23 final fields. -/
theorem target_via_k23
    (M : BoundaryAngleFinalMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix
    M.toK23FieldMatrix

/-- Conditional Swanepoel target projection through common-neighbor final
fields. -/
theorem target_via_commonNeighbor
    (M : BoundaryAngleFinalMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix
    M.toCommonNeighborFieldMatrix

/-- Non-target boundary-angle projection through direct fields. -/
theorem no_minimalClearedFailure_via_boundaryAngleDirect
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_directGeometryMatrix
    M.toBoundaryAngleDirectGeometryMatrix

/-- Non-target boundary-angle projection through K23 fields. -/
theorem no_minimalClearedFailure_via_boundaryAngleK23
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_k23GeometryMatrix
    M.toBoundaryAngleK23GeometryMatrix

/-- Non-target boundary-angle projection through common-neighbor fields. -/
theorem no_minimalClearedFailure_via_boundaryAngleCommonNeighbor
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleIntegratedW11.no_minimalClearedFailure_of_commonNeighborGeometryMatrix
    M.toBoundaryAngleCommonNeighborGeometryMatrix

end BoundaryAngleFinalMatrix

/-! ## Conditional route rows -/

/-- Direct final rows as a target-integrated route. -/
def directFinalRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryAngleFinalMatrix.{u}) where
  eliminator :=
    BoundaryAngleFinalMatrix.minimalClearedFailureEliminator_via_direct
  noMinimal := BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_direct
  pipeline := BoundaryAngleFinalMatrix.pipelineCleared_via_direct
  target := BoundaryAngleFinalMatrix.target_via_direct

/-- K23 final rows as a target-integrated route. -/
def k23FinalRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryAngleFinalMatrix.{u}) where
  eliminator :=
    BoundaryAngleFinalMatrix.minimalClearedFailureEliminator_via_k23
  noMinimal := BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_k23
  pipeline := BoundaryAngleFinalMatrix.pipelineCleared_via_k23
  target := BoundaryAngleFinalMatrix.target_via_k23

/-- Common-neighbor final rows as a target-integrated route. -/
def commonNeighborFinalRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryAngleFinalMatrix.{u}) where
  eliminator :=
    BoundaryAngleFinalMatrix.minimalClearedFailureEliminator_via_commonNeighbor
  noMinimal :=
    BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_commonNeighbor
  pipeline := BoundaryAngleFinalMatrix.pipelineCleared_via_commonNeighbor
  target := BoundaryAngleFinalMatrix.target_via_commonNeighbor

/-- Conditional route bundle from the final boundary-angle matrix. -/
structure ConditionalSwanepoelTargetRoutes : Type (u + 1) where
  direct :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryAngleFinalMatrix.{u})
  k23 :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryAngleFinalMatrix.{u})
  commonNeighbor :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (BoundaryAngleFinalMatrix.{u})

/-- Checked conditional Swanepoel target routes for final boundary-angle rows. -/
def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} where
  direct := directFinalRoute
  k23 := k23FinalRoute
  commonNeighbor := commonNeighborFinalRoute

/-! ## Aggregate ledger -/

/-- Imported ledgers used by the final boundary-angle aggregate. -/
structure ImportedLedgers : Type (u + 3) where
  boundaryAngleIntegrated : BoundaryAngleIntegratedW11.Matrix.{u}
  subpolygonIntegrated : SubpolygonIntegratedW11.Matrix.{u}
  topologyIntegrated : TopologyIntegratedW11.Matrix.{u}
  targetLedger : TargetLedgerConsistencyW11.Matrix.{u}
  swanepoelConsistencyDirectTarget :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} -> Target

/-- The checked imported ledgers available to this final aggregate. -/
def importedLedgers : ImportedLedgers.{u} where
  boundaryAngleIntegrated := BoundaryAngleIntegratedW11.matrix
  subpolygonIntegrated := SubpolygonIntegratedW11.matrix
  topologyIntegrated := TopologyIntegratedW11.matrix
  targetLedger := TargetLedgerConsistencyW11.matrix
  swanepoelConsistencyDirectTarget :=
    SwanepoelW11ConsistencyMatrix.target_of_brokenLatticeDirectFieldMatrix

/-- Final W11 boundary-angle aggregate ledger.

The ledger records checked adapters and route rows only; it does not construct
a uniform final boundary-angle matrix. -/
structure Matrix : Type (u + 3) where
  imported : ImportedLedgers.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}
  directToBoundaryAngle :
    BoundaryAngleFinalMatrix.{u} ->
      BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u}
  k23ToBoundaryAngle :
    BoundaryAngleFinalMatrix.{u} ->
      BoundaryAngleIntegratedW11.K23GeometryMatrix.{u}
  commonNeighborToBoundaryAngle :
    BoundaryAngleFinalMatrix.{u} ->
      BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u}
  directToBrokenLattice :
    BoundaryAngleFinalMatrix.{u} ->
      BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}
  k23ToBrokenLattice :
    BoundaryAngleFinalMatrix.{u} ->
      BrokenLatticeIntegratedW11.K23FieldMatrix.{u}
  commonNeighborToBrokenLattice :
    BoundaryAngleFinalMatrix.{u} ->
      BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}

/-- The checked final W11 boundary-angle aggregate ledger. -/
def matrix : Matrix.{u} where
  imported := importedLedgers
  routes := conditionalSwanepoelTargetRoutes
  directToBoundaryAngle :=
    BoundaryAngleFinalMatrix.toBoundaryAngleDirectGeometryMatrix
  k23ToBoundaryAngle :=
    BoundaryAngleFinalMatrix.toBoundaryAngleK23GeometryMatrix
  commonNeighborToBoundaryAngle :=
    BoundaryAngleFinalMatrix.toBoundaryAngleCommonNeighborGeometryMatrix
  directToBrokenLattice := BoundaryAngleFinalMatrix.toDirectFieldMatrix
  k23ToBrokenLattice := BoundaryAngleFinalMatrix.toK23FieldMatrix
  commonNeighborToBrokenLattice :=
    BoundaryAngleFinalMatrix.toCommonNeighborFieldMatrix

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_finalMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureEliminator :=
  BoundaryAngleFinalMatrix.minimalClearedFailureEliminator_via_direct M

theorem no_minimalClearedFailure_of_finalMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_direct M

theorem pipelineCleared_of_finalMatrix
    (M : BoundaryAngleFinalMatrix.{u}) :
    PipelineCleared :=
  BoundaryAngleFinalMatrix.pipelineCleared_via_direct M

theorem target_of_finalMatrix_via_direct
    (M : BoundaryAngleFinalMatrix.{u}) :
    Target :=
  BoundaryAngleFinalMatrix.target_via_direct M

theorem target_of_finalMatrix_via_k23
    (M : BoundaryAngleFinalMatrix.{u}) :
    Target :=
  BoundaryAngleFinalMatrix.target_via_k23 M

theorem target_of_finalMatrix_via_commonNeighbor
    (M : BoundaryAngleFinalMatrix.{u}) :
    Target :=
  BoundaryAngleFinalMatrix.target_via_commonNeighbor M

theorem no_minimalClearedFailure_of_finalMatrix_via_boundaryAngleDirect
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_boundaryAngleDirect M

theorem no_minimalClearedFailure_of_finalMatrix_via_boundaryAngleK23
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_boundaryAngleK23 M

theorem no_minimalClearedFailure_of_finalMatrix_via_boundaryAngleCommonNeighbor
    (M : BoundaryAngleFinalMatrix.{u}) :
    MinimalFailureExclusion :=
  BoundaryAngleFinalMatrix.no_minimalClearedFailure_via_boundaryAngleCommonNeighbor
    M

end

end BoundaryAngleFinalIntegratedW11
end Swanepoel
end ErdosProblems1066
