import ErdosProblems1066.Swanepoel.SubpolygonTargetIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ConsistencyMatrix

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 subpolygon aggregate

This file gathers the checked W11 subpolygon route behind one explicit final
row.  The row keeps the topology/cycle route, boundary labels, local window
containment, and all three no-early alternatives visible.  Every target
projection below remains conditional on a caller-supplied uniform final row
family.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonFinalIntegratedW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  SubpolygonTargetIntegratedW11.Target

abbrev MinimalFailureExclusion : Prop :=
  SubpolygonTargetIntegratedW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  SubpolygonTargetIntegratedW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev SubpolygonRoute (C : _root_.UDConfig n) :=
  SubpolygonTargetIntegratedW11.SubpolygonRoute.{u} C

/-! ## Explicit topology/cycle/label prefix -/

/-- The explicit topology/cycle route and matching boundary labels selected
for one fixed minimal cleared failure. -/
structure TopologyCycleLabelFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  route : SubpolygonRoute.{u} C
  labels :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.{u}
      C hmin route.toW10TopologyComponentFields
        route.toW10PartitionAngleComponentFields

namespace TopologyCycleLabelFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage the explicit fields in the target-facing subpolygon prefix
spelling. -/
def toSubpolygonLabelPrefix
    (P : TopologyCycleLabelFields.{u} C hmin) :
    SubpolygonTargetIntegratedW11.SubpolygonLabelPrefix.{u} C hmin where
  route := P.route
  labels := P.labels

/-- The topology component carried by the final subpolygon prefix. -/
def topology
    (P : TopologyCycleLabelFields.{u} C hmin) :
    MinimalFailureDirectMatrixW10.TopologyComponentFields C :=
  P.route.toW10TopologyComponentFields

/-- The cycle/count/angle partition component carried by the same prefix. -/
def partitionAngle
    (P : TopologyCycleLabelFields.{u} C hmin) :
    MinimalFailureDirectMatrixW10.PartitionAngleComponentFields.{u}
      C P.topology :=
  P.route.toW10PartitionAngleComponentFields

/-- The W9 topology/angle/subpolygon row selected by the route. -/
def toTopologyAngleSubpolygonRow
    (P : TopologyCycleLabelFields.{u} C hmin) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  P.route.toTopologyAngleSubpolygonRow

/-- The boundary-label base row induced by the explicit labels. -/
def toW9BaseRow
    (P : TopologyCycleLabelFields.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin :=
  P.toSubpolygonLabelPrefix.toW9BaseRow

/-- The source geometry determined by the topology/cycle/label fields. -/
def source
    (P : TopologyCycleLabelFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  P.toSubpolygonLabelPrefix.toGeometrySourceFields

/-- The displayed subpolygon index type. -/
def Subpolygon (P : TopologyCycleLabelFields.{u} C hmin) : Type u :=
  P.route.Subpolygon

/-- The displayed cycle/count/angle datum for one selected subpolygon. -/
def cycleData
    (P : TopologyCycleLabelFields.{u} C hmin) (S : P.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  P.route.cycleData S

/-- The retained E13 low-degree conclusion for each selected cycle. -/
theorem cycle_lowDegree
    (P : TopologyCycleLabelFields.{u} C hmin) (S : P.Subpolygon) :
    6 <= 2 * (P.cycleData S).counts.D2 +
      (P.cycleData S).counts.D3 :=
  P.route.cycle_lowDegree S

/-- The retained E12 boundary-angle count supplied by the route. -/
theorem boundaryAngleCount
    (P : TopologyCycleLabelFields.{u} C hmin) :
    P.route.classification.counts.d5 +
          2 * P.route.classification.counts.d6 +
        P.route.classification.counts.b +
          P.route.classification.counts.B + 6 <=
      P.route.classification.counts.d3 :=
  P.toSubpolygonLabelPrefix.boundaryAngleCount

end TopologyCycleLabelFields

/-! ## Explicit final rows -/

/-- One final subpolygon row for a fixed minimal cleared failure.

The row displays the topology/cycle/label prefix, local containment, and all
three no-early alternatives over the same source geometry. -/
structure FinalSubpolygonFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) where
  topologyCycleLabels : TopologyCycleLabelFields.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      (TopologyCycleLabelFields.source topologyCycleLabels)
  noStartNoEarly :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      (TopologyCycleLabelFields.source topologyCycleLabels)
  k23NoEarly :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      (TopologyCycleLabelFields.source topologyCycleLabels)
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      (TopologyCycleLabelFields.source topologyCycleLabels)

namespace FinalSubpolygonFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The target-facing subpolygon label prefix selected by a final row. -/
def labelPrefix
    (R : FinalSubpolygonFields.{u} C hmin) :
    SubpolygonTargetIntegratedW11.SubpolygonLabelPrefix.{u} C hmin :=
  R.topologyCycleLabels.toSubpolygonLabelPrefix

/-- The source geometry selected by the topology/cycle/label fields. -/
def source
    (R : FinalSubpolygonFields.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  R.topologyCycleLabels.source

/-- The displayed subpolygon index type. -/
def Subpolygon (R : FinalSubpolygonFields.{u} C hmin) : Type u :=
  R.topologyCycleLabels.Subpolygon

/-- The displayed cycle/count/angle datum for one selected subpolygon. -/
def cycleData
    (R : FinalSubpolygonFields.{u} C hmin) (S : R.Subpolygon) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) :=
  R.topologyCycleLabels.cycleData S

/-- Low-degree conclusion retained with the displayed cycle data. -/
theorem cycle_lowDegree
    (R : FinalSubpolygonFields.{u} C hmin) (S : R.Subpolygon) :
    6 <= 2 * (R.cycleData S).counts.D2 +
      (R.cycleData S).counts.D3 :=
  R.topologyCycleLabels.cycle_lowDegree S

/-- Repackage the final row as the target-facing direct subpolygon row. -/
def toDirectRow
    (R : FinalSubpolygonFields.{u} C hmin) :
    SubpolygonTargetIntegratedW11.DirectRow.{u} C hmin where
  labelPrefix := R.labelPrefix
  window := R.window
  noStartNoEarly := R.noStartNoEarly

/-- Repackage the final row as the target-facing K23 subpolygon row. -/
def toK23Row
    (R : FinalSubpolygonFields.{u} C hmin) :
    SubpolygonTargetIntegratedW11.K23Row.{u} C hmin where
  labelPrefix := R.labelPrefix
  window := R.window
  k23NoEarly := R.k23NoEarly

/-- Repackage the final row as the target-facing common-neighbor subpolygon
row. -/
def toCommonNeighborRow
    (R : FinalSubpolygonFields.{u} C hmin) :
    SubpolygonTargetIntegratedW11.CommonNeighborRow.{u} C hmin where
  labelPrefix := R.labelPrefix
  window := R.window
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage the final row as an integrated direct geometry row. -/
def toGeometryIntegratedDirectFields
    (R : FinalSubpolygonFields.{u} C hmin) :
    GeometryIntegratedW11.DirectGeometryFields.{u} C hmin where
  source := R.source
  containment := R.window
  noStartNoEarly := R.noStartNoEarly

/-- Repackage the final row as an integrated K23 geometry row. -/
def toGeometryIntegratedK23Fields
    (R : FinalSubpolygonFields.{u} C hmin) :
    GeometryIntegratedW11.K23GeometryFields.{u} C hmin where
  source := R.source
  containment := R.window
  k23NoEarly := R.k23NoEarly

/-- Repackage the final row as an integrated common-neighbor geometry row. -/
def toGeometryIntegratedCommonNeighborFields
    (R : FinalSubpolygonFields.{u} C hmin) :
    GeometryIntegratedW11.CommonNeighborGeometryFields.{u} C hmin where
  source := R.source
  containment := R.window
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- The checked W11 no-start row selected by the direct fields. -/
def toNoStartRow
    (R : FinalSubpolygonFields.{u} C hmin) :
    WindowNoEarlyRowsW11.NoStartRow.{u} C hmin :=
  R.toDirectRow.toNoStartRow

/-- The checked W11 no-early row selected by the direct fields. -/
def toDirectNoEarlyRow
    (R : FinalSubpolygonFields.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toDirectRow.toNoEarlyRow

/-- The checked W11 no-early row selected by the K23 fields. -/
def toK23NoEarlyRow
    (R : FinalSubpolygonFields.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toK23Row.toNoEarlyRow

/-- The checked W11 no-early row selected by the common-neighbor fields. -/
def toCommonNeighborNoEarlyRow
    (R : FinalSubpolygonFields.{u} C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin :=
  R.toCommonNeighborRow.toNoEarlyRow

/-- A fixed final row closes through the direct subpolygon route. -/
theorem contradiction_via_direct
    (R : FinalSubpolygonFields.{u} C hmin) :
    False :=
  R.toDirectRow.contradiction

/-- A fixed final row closes through the K23 subpolygon route. -/
theorem contradiction_via_k23
    (R : FinalSubpolygonFields.{u} C hmin) :
    False :=
  R.toK23Row.contradiction

/-- A fixed final row closes through the common-neighbor subpolygon route. -/
theorem contradiction_via_commonNeighbor
    (R : FinalSubpolygonFields.{u} C hmin) :
    False :=
  R.toCommonNeighborRow.contradiction

end FinalSubpolygonFields

/-! ## Uniform final row families -/

/-- Uniform final subpolygon rows for every minimal cleared failure. -/
structure FinalSubpolygonMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        FinalSubpolygonFields.{u} C hmin

namespace FinalSubpolygonMatrix

/-- Forget final rows to the target-facing direct matrix. -/
def toDirectMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    SubpolygonTargetIntegratedW11.DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectRow

/-- Forget final rows to the target-facing K23 matrix. -/
def toK23Matrix
    (M : FinalSubpolygonMatrix.{u}) :
    SubpolygonTargetIntegratedW11.K23Matrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23Row

/-- Forget final rows to the target-facing common-neighbor matrix. -/
def toCommonNeighborMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborRow

/-- View final rows as integrated direct geometry rows. -/
def toGeometryIntegratedDirectMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.DirectGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toGeometryIntegratedDirectFields

/-- View final rows as integrated K23 geometry rows. -/
def toGeometryIntegratedK23Matrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.K23GeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toGeometryIntegratedK23Fields

/-- View final rows as integrated common-neighbor geometry rows. -/
def toGeometryIntegratedCommonNeighborMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toGeometryIntegratedCommonNeighborFields

/-- Project final rows to checked W11 no-start rows. -/
def toW11NoStartMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    WindowNoEarlyRowsW11.NoStartMatrix.{u} :=
  M.toDirectMatrix.toNoStartMatrix

/-- Project final rows to checked W11 no-early rows through direct fields. -/
def toDirectW11NoEarlyMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toDirectMatrix.toNoEarlyMatrix

/-- Project final rows to checked W11 no-early rows through K23 fields. -/
def toK23W11NoEarlyMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toK23Matrix.toNoEarlyMatrix

/-- Project final rows to checked W11 no-early rows through
common-neighbor fields. -/
def toCommonNeighborW11NoEarlyMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} :=
  M.toCommonNeighborMatrix.toNoEarlyMatrix

/-- View final direct rows as a W11 geometry closure matrix. -/
def toDirectGeometryClosureMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedDirectMatrix.toGeometryClosureMatrix

/-- View final K23 rows as a W11 geometry closure matrix. -/
def toK23GeometryClosureMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedK23Matrix.toGeometryClosureMatrix

/-- View final common-neighbor rows as a W11 geometry closure matrix. -/
def toCommonNeighborGeometryClosureMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedCommonNeighborMatrix.toGeometryClosureMatrix

/-- Narrow closure inputs selected by the direct final rows. -/
def toDirectNarrowClosureInputFamily
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedDirectMatrix.toNarrowClosureInputFamily

/-- Narrow closure inputs selected by the K23 final rows. -/
def toK23NarrowClosureInputFamily
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedK23Matrix.toNarrowClosureInputFamily

/-- Narrow closure inputs selected by the common-neighbor final rows. -/
def toCommonNeighborNarrowClosureInputFamily
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedCommonNeighborMatrix.toNarrowClosureInputFamily

/-- Checked refined inputs selected by the direct final rows. -/
def toDirectCheckedClosureInputFamily
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedDirectMatrix.toCheckedClosureInputFamily

/-- Checked refined inputs selected by the K23 final rows. -/
def toK23CheckedClosureInputFamily
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedK23Matrix.toCheckedClosureInputFamily

/-- Checked refined inputs selected by the common-neighbor final rows. -/
def toCommonNeighborCheckedClosureInputFamily
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedCommonNeighborMatrix.toCheckedClosureInputFamily

/-- W10 target facade selected by the direct final rows. -/
def toDirectTargetFacadeMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.TargetFacadeMatrix :=
  M.toGeometryIntegratedDirectMatrix.toTargetFacadeMatrix

/-- W10 target facade selected by the K23 final rows. -/
def toK23TargetFacadeMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.TargetFacadeMatrix :=
  M.toGeometryIntegratedK23Matrix.toTargetFacadeMatrix

/-- W10 target facade selected by the common-neighbor final rows. -/
def toCommonNeighborTargetFacadeMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    GeometryIntegratedW11.TargetFacadeMatrix :=
  M.toGeometryIntegratedCommonNeighborMatrix.toTargetFacadeMatrix

/-- Final rows give a pointwise eliminator through the direct route. -/
theorem minimalClearedFailureEliminator_via_direct
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureEliminator := by
  intro n C hmin
  exact (M.row C hmin).contradiction_via_direct

/-- Final rows give a pointwise eliminator through the K23 route. -/
theorem minimalClearedFailureEliminator_via_k23
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureEliminator := by
  intro n C hmin
  exact (M.row C hmin).contradiction_via_k23

/-- Final rows give a pointwise eliminator through the common-neighbor route.
-/
theorem minimalClearedFailureEliminator_via_commonNeighbor
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureEliminator := by
  intro n C hmin
  exact (M.row C hmin).contradiction_via_commonNeighbor

/-- Final rows rule out every minimal cleared failure through direct fields. -/
theorem no_minimalClearedFailure_via_direct
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureExclusion :=
  SubpolygonTargetIntegratedW11.DirectMatrix.no_minimalClearedFailure
    M.toDirectMatrix

/-- Final rows rule out every minimal cleared failure through K23 fields. -/
theorem no_minimalClearedFailure_via_k23
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureExclusion :=
  SubpolygonTargetIntegratedW11.K23Matrix.no_minimalClearedFailure
    M.toK23Matrix

/-- Final rows rule out every minimal cleared failure through common-neighbor
fields. -/
theorem no_minimalClearedFailure_via_commonNeighbor
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureExclusion :=
  SubpolygonTargetIntegratedW11.CommonNeighborMatrix.no_minimalClearedFailure
    M.toCommonNeighborMatrix

/-- Final rows clear the pipeline through direct fields. -/
theorem pipelineCleared_via_direct
    (M : FinalSubpolygonMatrix.{u}) :
    PipelineCleared :=
  SubpolygonTargetIntegratedW11.DirectMatrix.pipelineCleared
    M.toDirectMatrix

/-- Final rows clear the pipeline through K23 fields. -/
theorem pipelineCleared_via_k23
    (M : FinalSubpolygonMatrix.{u}) :
    PipelineCleared :=
  SubpolygonTargetIntegratedW11.K23Matrix.pipelineCleared
    M.toK23Matrix

/-- Final rows clear the pipeline through common-neighbor fields. -/
theorem pipelineCleared_via_commonNeighbor
    (M : FinalSubpolygonMatrix.{u}) :
    PipelineCleared :=
  SubpolygonTargetIntegratedW11.CommonNeighborMatrix.pipelineCleared
    M.toCommonNeighborMatrix

/-- Conditional Swanepoel target projection through direct subpolygon fields.
-/
theorem swanepoelTarget_via_direct
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.DirectMatrix.targetClosure M.toDirectMatrix

/-- Conditional Swanepoel target projection through K23 subpolygon fields. -/
theorem swanepoelTarget_via_k23
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.K23Matrix.targetClosure M.toK23Matrix

/-- Conditional Swanepoel target projection through common-neighbor
subpolygon fields. -/
theorem swanepoelTarget_via_commonNeighbor
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  SubpolygonTargetIntegratedW11.CommonNeighborMatrix.targetClosure
    M.toCommonNeighborMatrix

end FinalSubpolygonMatrix

/-! ## Conditional route rows -/

/-- Direct final rows as a target-closure projection. -/
def directFinalTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalSubpolygonMatrix.{u}) where
  noMinimal := FinalSubpolygonMatrix.no_minimalClearedFailure_via_direct
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_direct
  target := FinalSubpolygonMatrix.swanepoelTarget_via_direct

/-- K23 final rows as a target-closure projection. -/
def k23FinalTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalSubpolygonMatrix.{u}) where
  noMinimal := FinalSubpolygonMatrix.no_minimalClearedFailure_via_k23
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_k23
  target := FinalSubpolygonMatrix.swanepoelTarget_via_k23

/-- Common-neighbor final rows as a target-closure projection. -/
def commonNeighborFinalTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalSubpolygonMatrix.{u}) where
  noMinimal :=
    FinalSubpolygonMatrix.no_minimalClearedFailure_via_commonNeighbor
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_commonNeighbor
  target := FinalSubpolygonMatrix.swanepoelTarget_via_commonNeighbor

/-- Direct final rows as a Swanepoel integrated target projection. -/
def directFinalSwanepoelIntegratedRow :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalSubpolygonMatrix.{u}) where
  noMinimal := FinalSubpolygonMatrix.no_minimalClearedFailure_via_direct
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_direct
  target := FinalSubpolygonMatrix.swanepoelTarget_via_direct

/-- K23 final rows as a Swanepoel integrated target projection. -/
def k23FinalSwanepoelIntegratedRow :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalSubpolygonMatrix.{u}) where
  noMinimal := FinalSubpolygonMatrix.no_minimalClearedFailure_via_k23
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_k23
  target := FinalSubpolygonMatrix.swanepoelTarget_via_k23

/-- Common-neighbor final rows as a Swanepoel integrated target projection. -/
def commonNeighborFinalSwanepoelIntegratedRow :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalSubpolygonMatrix.{u}) where
  noMinimal :=
    FinalSubpolygonMatrix.no_minimalClearedFailure_via_commonNeighbor
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_commonNeighbor
  target := FinalSubpolygonMatrix.swanepoelTarget_via_commonNeighbor

/-- Direct final rows as an integrated target route. -/
def directFinalTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalSubpolygonMatrix.{u}) where
  eliminator := FinalSubpolygonMatrix.minimalClearedFailureEliminator_via_direct
  noMinimal := FinalSubpolygonMatrix.no_minimalClearedFailure_via_direct
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_direct
  target := FinalSubpolygonMatrix.swanepoelTarget_via_direct

/-- K23 final rows as an integrated target route. -/
def k23FinalTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalSubpolygonMatrix.{u}) where
  eliminator := FinalSubpolygonMatrix.minimalClearedFailureEliminator_via_k23
  noMinimal := FinalSubpolygonMatrix.no_minimalClearedFailure_via_k23
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_k23
  target := FinalSubpolygonMatrix.swanepoelTarget_via_k23

/-- Common-neighbor final rows as an integrated target route. -/
def commonNeighborFinalTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalSubpolygonMatrix.{u}) where
  eliminator :=
    FinalSubpolygonMatrix.minimalClearedFailureEliminator_via_commonNeighbor
  noMinimal :=
    FinalSubpolygonMatrix.no_minimalClearedFailure_via_commonNeighbor
  pipeline := FinalSubpolygonMatrix.pipelineCleared_via_commonNeighbor
  target := FinalSubpolygonMatrix.swanepoelTarget_via_commonNeighbor

/-- Direct final rows as an integrated W11 geometry projection. -/
def directFinalGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (FinalSubpolygonMatrix.{u}) where
  geometryClosure := FinalSubpolygonMatrix.toDirectGeometryClosureMatrix
  narrowInputs := FinalSubpolygonMatrix.toDirectNarrowClosureInputFamily
  checkedInputs := FinalSubpolygonMatrix.toDirectCheckedClosureInputFamily
  targetFacade := FinalSubpolygonMatrix.toDirectTargetFacadeMatrix
  targetProjection := directFinalTargetClosureRow

/-- K23 final rows as an integrated W11 geometry projection. -/
def k23FinalGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (FinalSubpolygonMatrix.{u}) where
  geometryClosure := FinalSubpolygonMatrix.toK23GeometryClosureMatrix
  narrowInputs := FinalSubpolygonMatrix.toK23NarrowClosureInputFamily
  checkedInputs := FinalSubpolygonMatrix.toK23CheckedClosureInputFamily
  targetFacade := FinalSubpolygonMatrix.toK23TargetFacadeMatrix
  targetProjection := k23FinalTargetClosureRow

/-- Common-neighbor final rows as an integrated W11 geometry projection. -/
def commonNeighborFinalGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (FinalSubpolygonMatrix.{u}) where
  geometryClosure :=
    FinalSubpolygonMatrix.toCommonNeighborGeometryClosureMatrix
  narrowInputs := FinalSubpolygonMatrix.toCommonNeighborNarrowClosureInputFamily
  checkedInputs :=
    FinalSubpolygonMatrix.toCommonNeighborCheckedClosureInputFamily
  targetFacade := FinalSubpolygonMatrix.toCommonNeighborTargetFacadeMatrix
  targetProjection := commonNeighborFinalTargetClosureRow

/-! ## Final aggregate ledger -/

/-- Final W11 subpolygon aggregate ledger.

This record stores checked imported ledgers and conditional route rows only.
It does not supply a uniform final subpolygon matrix. -/
structure Matrix : Type (u + 3) where
  subpolygonTargetIntegrated :
    SubpolygonTargetIntegratedW11.Matrix.{u}
  subpolygonIntegrated :
    SubpolygonIntegratedW11.Matrix.{u}
  geometryIntegrated :
    GeometryIntegratedW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}
  swanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.Matrix.{u}
  consistencySubpolygonDirect :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u} -> Target
  directTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalSubpolygonMatrix.{u})
  k23TargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalSubpolygonMatrix.{u})
  commonNeighborTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (FinalSubpolygonMatrix.{u})
  directTargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalSubpolygonMatrix.{u})
  k23TargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalSubpolygonMatrix.{u})
  commonNeighborTargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (FinalSubpolygonMatrix.{u})
  directSwanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalSubpolygonMatrix.{u})
  k23SwanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalSubpolygonMatrix.{u})
  commonNeighborSwanepoelIntegrated :
    SwanepoelW11IntegratedMatrix.TargetProjectionRow
      (FinalSubpolygonMatrix.{u})

/-- The checked final W11 subpolygon aggregate ledger. -/
def matrix : Matrix.{u} where
  subpolygonTargetIntegrated := SubpolygonTargetIntegratedW11.matrix
  subpolygonIntegrated := SubpolygonIntegratedW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  swanepoelIntegrated := SwanepoelW11IntegratedMatrix.matrix
  consistencySubpolygonDirect :=
    SwanepoelW11ConsistencyMatrix.target_of_subpolygonDirectBoundaryGeometryMatrix
  directTargetClosure := directFinalTargetClosureRow
  k23TargetClosure := k23FinalTargetClosureRow
  commonNeighborTargetClosure := commonNeighborFinalTargetClosureRow
  directTargetIntegrated := directFinalTargetIntegratedRoute
  k23TargetIntegrated := k23FinalTargetIntegratedRoute
  commonNeighborTargetIntegrated :=
    commonNeighborFinalTargetIntegratedRoute
  directSwanepoelIntegrated := directFinalSwanepoelIntegratedRow
  k23SwanepoelIntegrated := k23FinalSwanepoelIntegratedRow
  commonNeighborSwanepoelIntegrated :=
    commonNeighborFinalSwanepoelIntegratedRow

/-! ## Public conditional projections -/

/-- Minimal-failure exclusion from a uniform final row family. -/
theorem no_minimalClearedFailure_of_finalMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directTargetIntegrated.noMinimal M

/-- Cleared-pipeline projection from a uniform final row family. -/
theorem pipelineCleared_of_finalMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    PipelineCleared :=
  matrix.directTargetIntegrated.pipeline M

/-- Pointwise minimal-failure eliminator from a uniform final row family. -/
theorem minimalClearedFailureEliminator_of_finalMatrix
    (M : FinalSubpolygonMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.directTargetIntegrated.eliminator M

/-- Conditional Swanepoel target projection through direct final fields. -/
theorem swanepoelTarget_of_finalMatrix_via_direct
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  matrix.directSwanepoelIntegrated.target M

/-- Conditional Swanepoel target projection through K23 final fields. -/
theorem swanepoelTarget_of_finalMatrix_via_k23
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  matrix.k23SwanepoelIntegrated.target M

/-- Conditional Swanepoel target projection through common-neighbor final
fields. -/
theorem swanepoelTarget_of_finalMatrix_via_commonNeighbor
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  matrix.commonNeighborSwanepoelIntegrated.target M

/-- Conditional target projection through the direct geometry facade. -/
theorem swanepoelTarget_of_finalMatrix_via_directGeometry
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  directFinalGeometryProjectionRow.target M

/-- Conditional target projection through the K23 geometry facade. -/
theorem swanepoelTarget_of_finalMatrix_via_k23Geometry
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  k23FinalGeometryProjectionRow.target M

/-- Conditional target projection through the common-neighbor geometry facade.
-/
theorem swanepoelTarget_of_finalMatrix_via_commonNeighborGeometry
    (M : FinalSubpolygonMatrix.{u}) :
    Target :=
  commonNeighborFinalGeometryProjectionRow.target M

end

end SubpolygonFinalIntegratedW11
end Swanepoel
end ErdosProblems1066
