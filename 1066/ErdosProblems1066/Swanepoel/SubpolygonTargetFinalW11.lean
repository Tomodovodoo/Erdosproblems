import ErdosProblems1066.Swanepoel.SubpolygonFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SubpolygonTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleFinalIntegratedW11
import ErdosProblems1066.Swanepoel.TopologyFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 subpolygon/topology target consistency

This file is a target-facing consistency layer for the final W11 subpolygon
and topology ledgers.  The pointwise row keeps the topology/cycle/label prefix,
window containment, and all three no-early alternatives visible.  The public
target projections below all require an explicit uniform row family.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonTargetFinalW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev TopologyCycleLabelFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  SubpolygonFinalIntegratedW11.TopologyCycleLabelFields.{u} C hmin

abbrev FinalSubpolygonFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  SubpolygonFinalIntegratedW11.FinalSubpolygonFields.{u} C hmin

abbrev FinalSubpolygonMatrix :=
  SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}

/-! ## Explicit pointwise rows -/

/-- Explicit final subpolygon fields, with the topology/cycle/label prefix and
the three no-early alternatives displayed as fields over the same source. -/
structure Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  topologyCycleLabels : TopologyCycleLabelFields.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      (SubpolygonFinalIntegratedW11.TopologyCycleLabelFields.source
        topologyCycleLabels)
  noStartNoEarly :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      (SubpolygonFinalIntegratedW11.TopologyCycleLabelFields.source
        topologyCycleLabels)
  k23NoEarly :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      (SubpolygonFinalIntegratedW11.TopologyCycleLabelFields.source
        topologyCycleLabels)
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      (SubpolygonFinalIntegratedW11.TopologyCycleLabelFields.source
        topologyCycleLabels)

namespace Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage the displayed row as the final integrated subpolygon row. -/
def toFinalSubpolygonFields
    (R : Row.{u} C hmin) :
    FinalSubpolygonFields.{u} C hmin where
  topologyCycleLabels := R.topologyCycleLabels
  window := R.window
  noStartNoEarly := R.noStartNoEarly
  k23NoEarly := R.k23NoEarly
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- The target-facing subpolygon label prefix selected by the row. -/
def labelPrefix
    (R : Row.{u} C hmin) :
    SubpolygonTargetIntegratedW11.SubpolygonLabelPrefix.{u} C hmin :=
  R.toFinalSubpolygonFields.labelPrefix

/-- The geometry source induced by the visible topology/cycle/label prefix. -/
def source
    (R : Row.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.toFinalSubpolygonFields.source

/-- The visible topology component. -/
def topology
    (R : Row.{u} C hmin) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C :=
  R.topologyCycleLabels.topology

/-- The visible cycle/count/angle component. -/
def partitionAngle
    (R : Row.{u} C hmin) :
    MinimalFailureDirectMatrixW10.PartitionAngleComponentFields.{u}
      C R.topology :=
  R.topologyCycleLabels.partitionAngle

/-- The displayed subpolygon index type. -/
def Subpolygon (R : Row.{u} C hmin) : Type u :=
  R.toFinalSubpolygonFields.Subpolygon

/-- The displayed cycle/count/angle datum for one selected subpolygon. -/
def cycleData
    (R : Row.{u} C hmin) (S : R.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  R.toFinalSubpolygonFields.cycleData S

/-- Low-degree conclusion retained for each visible subpolygon cycle. -/
theorem cycle_lowDegree
    (R : Row.{u} C hmin) (S : R.Subpolygon) :
    6 <= 2 * (R.cycleData S).counts.D2 +
      (R.cycleData S).counts.D3 :=
  R.toFinalSubpolygonFields.cycle_lowDegree S

/-- Boundary-angle count conclusion retained with the visible labels. -/
theorem boundaryAngleCount
    (R : Row.{u} C hmin) :
    R.topologyCycleLabels.route.classification.counts.d5 +
          2 * R.topologyCycleLabels.route.classification.counts.d6 +
        R.topologyCycleLabels.route.classification.counts.b +
          R.topologyCycleLabels.route.classification.counts.B + 6 <=
      R.topologyCycleLabels.route.classification.counts.d3 :=
  R.topologyCycleLabels.boundaryAngleCount

/-- Repackage the row as the direct target-facing subpolygon row. -/
def toDirectRow
    (R : Row.{u} C hmin) :
    SubpolygonTargetIntegratedW11.DirectRow.{u} C hmin :=
  R.toFinalSubpolygonFields.toDirectRow

/-- Repackage the row as the K23 target-facing subpolygon row. -/
def toK23Row
    (R : Row.{u} C hmin) :
    SubpolygonTargetIntegratedW11.K23Row.{u} C hmin :=
  R.toFinalSubpolygonFields.toK23Row

/-- Repackage the row as the common-neighbor target-facing subpolygon row. -/
def toCommonNeighborRow
    (R : Row.{u} C hmin) :
    SubpolygonTargetIntegratedW11.CommonNeighborRow.{u} C hmin :=
  R.toFinalSubpolygonFields.toCommonNeighborRow

/-- Project the direct fields to a checked W11 no-start row. -/
def toNoStartRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toFinalSubpolygonFields.toNoStartRow

/-- Project the direct fields to a checked W11 no-early row. -/
def toDirectNoEarlyRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toFinalSubpolygonFields.toDirectNoEarlyRow

/-- Project the K23 fields to a checked W11 no-early row. -/
def toK23NoEarlyRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toFinalSubpolygonFields.toK23NoEarlyRow

/-- Project the common-neighbor fields to a checked W11 no-early row. -/
def toCommonNeighborNoEarlyRow
    (R : Row.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toFinalSubpolygonFields.toCommonNeighborNoEarlyRow

/-- A fixed row closes through the direct subpolygon route. -/
theorem contradiction_via_direct
    (R : Row.{u} C hmin) :
    False :=
  R.toFinalSubpolygonFields.contradiction_via_direct

/-- A fixed row closes through the K23 subpolygon route. -/
theorem contradiction_via_k23
    (R : Row.{u} C hmin) :
    False :=
  R.toFinalSubpolygonFields.contradiction_via_k23

/-- A fixed row closes through the common-neighbor subpolygon route. -/
theorem contradiction_via_commonNeighbor
    (R : Row.{u} C hmin) :
    False :=
  R.toFinalSubpolygonFields.contradiction_via_commonNeighbor

@[simp]
theorem toFinalSubpolygonFields_topologyCycleLabels
    (R : Row.{u} C hmin) :
    R.toFinalSubpolygonFields.topologyCycleLabels =
      R.topologyCycleLabels := by
  rfl

@[simp]
theorem toFinalSubpolygonFields_window
    (R : Row.{u} C hmin) :
    R.toFinalSubpolygonFields.window = R.window := by
  rfl

@[simp]
theorem toFinalSubpolygonFields_noStartNoEarly
    (R : Row.{u} C hmin) :
    R.toFinalSubpolygonFields.noStartNoEarly = R.noStartNoEarly := by
  rfl

end Row

/-! ## Uniform explicit row families -/

/-- Uniform final subpolygon target rows for every minimal cleared failure. -/
structure FinalMatrixInput : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Row.{u} C hmin

namespace FinalMatrixInput

/-- Forget final target rows to the final integrated subpolygon matrix. -/
def toFinalSubpolygonMatrix
    (M : FinalMatrixInput.{u}) :
    FinalSubpolygonMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toFinalSubpolygonFields

/-- Forget final target rows to direct target-facing subpolygon rows. -/
def toDirectMatrix
    (M : FinalMatrixInput.{u}) :
    SubpolygonTargetIntegratedW11.DirectMatrix.{u} :=
  M.toFinalSubpolygonMatrix.toDirectMatrix

/-- Forget final target rows to K23 target-facing subpolygon rows. -/
def toK23Matrix
    (M : FinalMatrixInput.{u}) :
    SubpolygonTargetIntegratedW11.K23Matrix.{u} :=
  M.toFinalSubpolygonMatrix.toK23Matrix

/-- Forget final target rows to common-neighbor target-facing subpolygon rows. -/
def toCommonNeighborMatrix
    (M : FinalMatrixInput.{u}) :
    SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u} :=
  M.toFinalSubpolygonMatrix.toCommonNeighborMatrix

/-- Project final target rows to checked W11 no-start rows. -/
def toNoStartMatrix
    (M : FinalMatrixInput.{u}) :
    WindowNoEarlyRowsW11.NoStartMatrix.{u} :=
  M.toFinalSubpolygonMatrix.toW11NoStartMatrix

/-- Project final target rows to checked W11 no-early rows through direct
fields. -/
def toDirectNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toFinalSubpolygonMatrix.toDirectW11NoEarlyMatrix

/-- Project final target rows to checked W11 no-early rows through K23
fields. -/
def toK23NoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toFinalSubpolygonMatrix.toK23W11NoEarlyMatrix

/-- Project final target rows to checked W11 no-early rows through
common-neighbor fields. -/
def toCommonNeighborNoEarlyMatrix
    (M : FinalMatrixInput.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toFinalSubpolygonMatrix.toCommonNeighborW11NoEarlyMatrix

/-- Final target rows give a pointwise eliminator through direct fields. -/
theorem minimalClearedFailureEliminator_via_direct
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.minimalClearedFailureEliminator_via_direct
    M.toFinalSubpolygonMatrix

/-- Final target rows rule out every minimal cleared failure through direct
fields. -/
theorem no_minimalClearedFailure_via_direct
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.no_minimalClearedFailure_via_direct
    M.toFinalSubpolygonMatrix

/-- Final target rows clear the pipeline through direct fields. -/
theorem pipelineCleared_via_direct
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.pipelineCleared_via_direct
    M.toFinalSubpolygonMatrix

/-- Conditional target projection through direct subpolygon fields. -/
theorem target_via_subpolygon_direct
    (M : FinalMatrixInput.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_direct
    M.toFinalSubpolygonMatrix

/-- Conditional target projection through K23 subpolygon fields. -/
theorem target_via_subpolygon_k23
    (M : FinalMatrixInput.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_k23
    M.toFinalSubpolygonMatrix

/-- Conditional target projection through common-neighbor subpolygon fields. -/
theorem target_via_subpolygon_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
    M.toFinalSubpolygonMatrix

/-- Conditional topology-layer target projection through direct subpolygon
fields. -/
theorem target_via_topology_direct
    (M : FinalMatrixInput.{u}) :
    Target :=
  TopologyFinalIntegratedW11.swanepoelTarget_of_subpolygonDirectMatrix
    M.toDirectMatrix

/-- Conditional topology-layer target projection through K23 subpolygon
fields. -/
theorem target_via_topology_k23
    (M : FinalMatrixInput.{u}) :
    Target :=
  TopologyFinalIntegratedW11.swanepoelTarget_of_subpolygonK23Matrix
    M.toK23Matrix

/-- Conditional topology-layer target projection through common-neighbor
subpolygon fields. -/
theorem target_via_topology_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  TopologyFinalIntegratedW11.swanepoelTarget_of_subpolygonCommonNeighborMatrix
    M.toCommonNeighborMatrix

end FinalMatrixInput

/-! ## Conditional route rows -/

/-- Direct final rows as a target-closure projection. -/
def directTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_direct
  pipeline := FinalMatrixInput.pipelineCleared_via_direct
  target := FinalMatrixInput.target_via_subpolygon_direct

/-- Direct final rows as a topology-layer target projection. -/
def directTopologyTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := FinalMatrixInput.no_minimalClearedFailure_via_direct
  pipeline := FinalMatrixInput.pipelineCleared_via_direct
  target := FinalMatrixInput.target_via_topology_direct

/-- K23 final rows as a topology-layer target projection. -/
def k23TopologyTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := fun M =>
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.no_minimalClearedFailure_via_k23
      M.toFinalSubpolygonMatrix
  pipeline := fun M =>
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.pipelineCleared_via_k23
      M.toFinalSubpolygonMatrix
  target := FinalMatrixInput.target_via_topology_k23

/-- Common-neighbor final rows as a topology-layer target projection. -/
def commonNeighborTopologyTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalMatrixInput.{u}) where
  noMinimal := fun M =>
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.no_minimalClearedFailure_via_commonNeighbor
      M.toFinalSubpolygonMatrix
  pipeline := fun M =>
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.pipelineCleared_via_commonNeighbor
      M.toFinalSubpolygonMatrix
  target := FinalMatrixInput.target_via_topology_commonNeighbor

/-! ## Checked final ledgers -/

/-- Checked ledgers imported into the final subpolygon/topology consistency
layer. -/
structure ImportedLedgers : Type (u + 5) where
  subpolygonTarget :
    SubpolygonTargetIntegratedW11.Matrix.{u}
  subpolygonFinal :
    SubpolygonFinalIntegratedW11.Matrix.{u}
  boundaryAngleFinal :
    BoundaryAngleFinalIntegratedW11.Matrix.{u}
  topologyFinal :
    TopologyFinalIntegratedW11.Matrix.{u}

/-- The checked imported ledgers. -/
def importedLedgers : ImportedLedgers.{u} where
  subpolygonTarget := SubpolygonTargetIntegratedW11.matrix
  subpolygonFinal := SubpolygonFinalIntegratedW11.matrix
  boundaryAngleFinal := BoundaryAngleFinalIntegratedW11.matrix
  topologyFinal := TopologyFinalIntegratedW11.matrix

/-- Final subpolygon/topology target consistency matrix.

The matrix records checked ledgers and route rows only; it does not construct
the uniform final row family required by the target projections. -/
structure Matrix : Type (u + 5) where
  imported : ImportedLedgers.{u}
  directSubpolygon :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u})
  directTopology :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u})
  k23Topology :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u})
  commonNeighborTopology :
    TargetClosureMatrixW11.TargetProjectionRow (FinalMatrixInput.{u})

/-- The checked final subpolygon/topology target consistency matrix. -/
def matrix : Matrix.{u} where
  imported := importedLedgers
  directSubpolygon := directTargetClosureRow
  directTopology := directTopologyTargetClosureRow
  k23Topology := k23TopologyTargetClosureRow
  commonNeighborTopology := commonNeighborTopologyTargetClosureRow

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_subpolygonTarget :
    matrix.{u}.imported.subpolygonTarget =
      SubpolygonTargetIntegratedW11.matrix := by
  rfl

theorem checked_subpolygonFinal :
    matrix.{u}.imported.subpolygonFinal =
      SubpolygonFinalIntegratedW11.matrix := by
  rfl

theorem checked_topologyFinal :
    matrix.{u}.imported.topologyFinal =
      TopologyFinalIntegratedW11.matrix := by
  rfl

/-- The final consistency ledger uses the same minimal-failure exclusion
proposition as this target layer. -/
theorem finalConsistency_minimalFailureExclusion
    (h : SwanepoelW11FinalConsistency.MinimalFailureExclusion) :
    MinimalFailureExclusion :=
  h

/-- The final consistency ledger uses the same cleared-pipeline proposition as
this target layer. -/
theorem finalConsistency_pipelineCleared
    (h : SwanepoelW11FinalConsistency.PipelineCleared) :
    PipelineCleared :=
  h

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    MinimalFailureEliminator :=
  FinalMatrixInput.minimalClearedFailureEliminator_via_direct M

theorem no_minimalClearedFailure_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    MinimalFailureExclusion :=
  FinalMatrixInput.no_minimalClearedFailure_via_direct M

theorem pipelineCleared_of_finalMatrix
    (M : FinalMatrixInput.{u}) :
    PipelineCleared :=
  FinalMatrixInput.pipelineCleared_via_direct M

theorem target_of_finalMatrix_via_subpolygon_direct
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_subpolygon_direct M

theorem target_of_finalMatrix_via_topology_direct
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_topology_direct M

theorem target_of_finalMatrix_via_topology_k23
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_topology_k23 M

theorem target_of_finalMatrix_via_topology_commonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  FinalMatrixInput.target_via_topology_commonNeighbor M

end

end SubpolygonTargetFinalW11
end Swanepoel
end ErdosProblems1066
