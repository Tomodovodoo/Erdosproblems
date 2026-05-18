import ErdosProblems1066.Swanepoel.SubpolygonTargetFinalW11
import ErdosProblems1066.Swanepoel.SubpolygonFinalIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryTargetFinalW11
import ErdosProblems1066.Swanepoel.TopologyFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelRouteSummaryFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 subpolygon/geometry route summary

This file records the checked final W11 subpolygon, topology, geometry, and
route-summary ledgers together with one explicit input bundle.  The public
target projections below all consume that input bundle.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonGeometryRouteSummaryFinalW11

universe u

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

/-! ## Checked ledgers -/

/-- Checked final W11 ledgers used by this summary. -/
structure CheckedMatrices : Type (u + 5) where
  subpolygonTargetFinal :
    SubpolygonTargetFinalW11.Matrix.{u}
  subpolygonFinal :
    SubpolygonFinalIntegratedW11.Matrix.{u}
  topologyFinal :
    TopologyFinalIntegratedW11.Matrix.{u}
  geometryTargetFinal :
    GeometryTargetFinalW11.Matrix.{u}

/-- The checked ledgers imported by the summary. -/
def checkedMatrices : CheckedMatrices.{u} where
  subpolygonTargetFinal := SubpolygonTargetFinalW11.matrix
  subpolygonFinal := SubpolygonFinalIntegratedW11.matrix
  topologyFinal := TopologyFinalIntegratedW11.matrix
  geometryTargetFinal := GeometryTargetFinalW11.matrix

/-! ## Explicit input matrices -/

/-- Explicit matrix bundle consumed by all public target projections. -/
structure ExplicitInputMatrices : Type (u + 5) where
  subpolygonTarget :
    SubpolygonTargetFinalW11.FinalMatrixInput.{u}
  subpolygonFinal :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}
  topology :
    TopologyFinalIntegratedW11.ExplicitGeometryMatrices.{u}
  geometry :
    GeometryTargetFinalW11.ExplicitGeometryMatrices.{u}
  k23CommonNeighbor :
    GeometryTargetFinalW11.K23CommonNeighborMatrix.{u}

namespace ExplicitInputMatrices

/-- Minimal-failure exclusion from the target-facing subpolygon rows. -/
theorem no_minimal_via_subpolygonTarget
    (M : ExplicitInputMatrices.{u}) :
    MinimalFailureExclusion :=
  SubpolygonTargetFinalW11.no_minimalClearedFailure_of_finalMatrix
    M.subpolygonTarget

/-- Pipeline closure from the target-facing subpolygon rows. -/
theorem pipeline_via_subpolygonTarget
    (M : ExplicitInputMatrices.{u}) :
    PipelineCleared :=
  SubpolygonTargetFinalW11.pipelineCleared_of_finalMatrix M.subpolygonTarget

/-- Pointwise eliminator from the target-facing subpolygon rows. -/
theorem eliminator_via_subpolygonTarget
    (M : ExplicitInputMatrices.{u}) :
    MinimalFailureEliminator :=
  SubpolygonTargetFinalW11.minimalClearedFailureEliminator_of_finalMatrix
    M.subpolygonTarget

/-- Target projection through direct target-facing subpolygon rows. -/
theorem target_via_subpolygonTarget_direct
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonTargetFinalW11.target_of_finalMatrix_via_subpolygon_direct
    M.subpolygonTarget

/-- Target projection through direct topology-facing subpolygon rows. -/
theorem target_via_subpolygonTarget_topologyDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonTargetFinalW11.target_of_finalMatrix_via_topology_direct
    M.subpolygonTarget

/-- Target projection through K23 topology-facing subpolygon rows. -/
theorem target_via_subpolygonTarget_topologyK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonTargetFinalW11.target_of_finalMatrix_via_topology_k23
    M.subpolygonTarget

/-- Target projection through common-neighbor topology-facing subpolygon rows. -/
theorem target_via_subpolygonTarget_topologyCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonTargetFinalW11.target_of_finalMatrix_via_topology_commonNeighbor
    M.subpolygonTarget

/-- Minimal-failure exclusion from final subpolygon rows. -/
theorem no_minimal_via_subpolygonFinal
    (M : ExplicitInputMatrices.{u}) :
    MinimalFailureExclusion :=
  SubpolygonFinalIntegratedW11.no_minimalClearedFailure_of_finalMatrix
    M.subpolygonFinal

/-- Pipeline closure from final subpolygon rows. -/
theorem pipeline_via_subpolygonFinal
    (M : ExplicitInputMatrices.{u}) :
    PipelineCleared :=
  SubpolygonFinalIntegratedW11.pipelineCleared_of_finalMatrix
    M.subpolygonFinal

/-- Pointwise eliminator from final subpolygon rows. -/
theorem eliminator_via_subpolygonFinal
    (M : ExplicitInputMatrices.{u}) :
    MinimalFailureEliminator :=
  SubpolygonFinalIntegratedW11.minimalClearedFailureEliminator_of_finalMatrix
    M.subpolygonFinal

/-- Target projection through direct final subpolygon rows. -/
theorem target_via_subpolygonFinal_direct
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_direct
    M.subpolygonFinal

/-- Target projection through K23 final subpolygon rows. -/
theorem target_via_subpolygonFinal_k23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_k23
    M.subpolygonFinal

/-- Target projection through common-neighbor final subpolygon rows. -/
theorem target_via_subpolygonFinal_commonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
    M.subpolygonFinal

/-- Target projection through direct final subpolygon geometry rows. -/
theorem target_via_subpolygonFinal_directGeometry
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_directGeometry
    M.subpolygonFinal

/-- Target projection through K23 final subpolygon geometry rows. -/
theorem target_via_subpolygonFinal_k23Geometry
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_k23Geometry
    M.subpolygonFinal

/-- Target projection through common-neighbor final subpolygon geometry rows. -/
theorem target_via_subpolygonFinal_commonNeighborGeometry
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_commonNeighborGeometry
    M.subpolygonFinal

/-- Target projection through topology direct subpolygon rows. -/
theorem target_via_topology_subpolygonDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_subpolygonDirect
    M.topology

/-- Target projection through topology K23 subpolygon rows. -/
theorem target_via_topology_subpolygonK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_subpolygonK23
    M.topology

/-- Target projection through topology common-neighbor subpolygon rows. -/
theorem target_via_topology_subpolygonCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_subpolygonCommonNeighbor
    M.topology

/-- Target projection through topology direct source rows. -/
theorem target_via_topology_sourceDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_sourceDirect
    M.topology

/-- Target projection through topology K23 source rows. -/
theorem target_via_topology_sourceK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_sourceK23
    M.topology

/-- Target projection through topology common-neighbor source rows. -/
theorem target_via_topology_sourceCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_sourceCommonNeighbor
    M.topology

/-- Target projection through direct final geometry rows. -/
theorem target_via_geometry_direct
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  GeometryTargetFinalW11.target_of_explicitGeometryMatrices_via_direct
    M.geometry

/-- Target projection through K23 final geometry rows. -/
theorem target_via_geometry_k23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  GeometryTargetFinalW11.target_of_explicitGeometryMatrices_via_k23
    M.geometry

/-- Target projection through common-neighbor final geometry rows. -/
theorem target_via_geometry_commonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  GeometryTargetFinalW11.target_of_explicitGeometryMatrices_via_commonNeighbor
    M.geometry

/-- Target projection through the K23 branch of the shared K23/common-neighbor
geometry matrix. -/
theorem target_via_geometry_k23CommonNeighborK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  GeometryTargetFinalW11.target_of_k23CommonNeighborMatrix_via_k23
    M.k23CommonNeighbor

/-- Target projection through the common-neighbor branch of the shared
K23/common-neighbor geometry matrix. -/
theorem target_via_geometry_k23CommonNeighborCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  GeometryTargetFinalW11.target_of_k23CommonNeighborMatrix_via_commonNeighbor
    M.k23CommonNeighbor

/-- Route-summary projection through direct final subpolygon rows. -/
theorem target_via_routeSummary_subpolygonFinalDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_subpolygonFinalMatrix_via_direct
    M.subpolygonFinal

/-- Route-summary projection through direct final geometry rows. -/
theorem target_via_routeSummary_geometryDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_geometryDirectFinalMatrix
    M.geometry.direct

/-- Route-summary projection through K23 final geometry rows. -/
theorem target_via_routeSummary_geometryK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_geometryK23FinalMatrix
    M.geometry.k23

/-- Route-summary projection through common-neighbor final geometry rows. -/
theorem target_via_routeSummary_geometryCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  SwanepoelRouteSummaryFinalW11.target_of_geometryCommonNeighborFinalMatrix
    M.geometry.commonNeighbor

end ExplicitInputMatrices

/-! ## Conditional projection matrix -/

/-- Public target projections retained by this route summary. -/
structure ConditionalTargetProjections : Type (u + 5) where
  subpolygonTargetDirect :
    ExplicitInputMatrices.{u} -> Target
  subpolygonTargetTopologyDirect :
    ExplicitInputMatrices.{u} -> Target
  subpolygonTargetTopologyK23 :
    ExplicitInputMatrices.{u} -> Target
  subpolygonTargetTopologyCommonNeighbor :
    ExplicitInputMatrices.{u} -> Target
  subpolygonFinalDirect :
    ExplicitInputMatrices.{u} -> Target
  subpolygonFinalK23 :
    ExplicitInputMatrices.{u} -> Target
  subpolygonFinalCommonNeighbor :
    ExplicitInputMatrices.{u} -> Target
  subpolygonFinalDirectGeometry :
    ExplicitInputMatrices.{u} -> Target
  subpolygonFinalK23Geometry :
    ExplicitInputMatrices.{u} -> Target
  subpolygonFinalCommonNeighborGeometry :
    ExplicitInputMatrices.{u} -> Target
  topologySubpolygonDirect :
    ExplicitInputMatrices.{u} -> Target
  topologySubpolygonK23 :
    ExplicitInputMatrices.{u} -> Target
  topologySubpolygonCommonNeighbor :
    ExplicitInputMatrices.{u} -> Target
  topologySourceDirect :
    ExplicitInputMatrices.{u} -> Target
  topologySourceK23 :
    ExplicitInputMatrices.{u} -> Target
  topologySourceCommonNeighbor :
    ExplicitInputMatrices.{u} -> Target
  geometryDirect :
    ExplicitInputMatrices.{u} -> Target
  geometryK23 :
    ExplicitInputMatrices.{u} -> Target
  geometryCommonNeighbor :
    ExplicitInputMatrices.{u} -> Target
  geometryK23CommonNeighborK23 :
    ExplicitInputMatrices.{u} -> Target
  geometryK23CommonNeighborCommonNeighbor :
    ExplicitInputMatrices.{u} -> Target
  routeSummarySubpolygonFinalDirect :
    ExplicitInputMatrices.{u} -> Target
  routeSummaryGeometryDirect :
    ExplicitInputMatrices.{u} -> Target
  routeSummaryGeometryK23 :
    ExplicitInputMatrices.{u} -> Target
  routeSummaryGeometryCommonNeighbor :
    ExplicitInputMatrices.{u} -> Target

/-- Checked conditional target projections assembled from the imported ledgers. -/
def conditionalTargetProjections :
    ConditionalTargetProjections.{u} where
  subpolygonTargetDirect :=
    ExplicitInputMatrices.target_via_subpolygonTarget_direct
  subpolygonTargetTopologyDirect :=
    ExplicitInputMatrices.target_via_subpolygonTarget_topologyDirect
  subpolygonTargetTopologyK23 :=
    ExplicitInputMatrices.target_via_subpolygonTarget_topologyK23
  subpolygonTargetTopologyCommonNeighbor :=
    ExplicitInputMatrices.target_via_subpolygonTarget_topologyCommonNeighbor
  subpolygonFinalDirect :=
    ExplicitInputMatrices.target_via_subpolygonFinal_direct
  subpolygonFinalK23 :=
    ExplicitInputMatrices.target_via_subpolygonFinal_k23
  subpolygonFinalCommonNeighbor :=
    ExplicitInputMatrices.target_via_subpolygonFinal_commonNeighbor
  subpolygonFinalDirectGeometry :=
    ExplicitInputMatrices.target_via_subpolygonFinal_directGeometry
  subpolygonFinalK23Geometry :=
    ExplicitInputMatrices.target_via_subpolygonFinal_k23Geometry
  subpolygonFinalCommonNeighborGeometry :=
    ExplicitInputMatrices.target_via_subpolygonFinal_commonNeighborGeometry
  topologySubpolygonDirect :=
    ExplicitInputMatrices.target_via_topology_subpolygonDirect
  topologySubpolygonK23 :=
    ExplicitInputMatrices.target_via_topology_subpolygonK23
  topologySubpolygonCommonNeighbor :=
    ExplicitInputMatrices.target_via_topology_subpolygonCommonNeighbor
  topologySourceDirect :=
    ExplicitInputMatrices.target_via_topology_sourceDirect
  topologySourceK23 :=
    ExplicitInputMatrices.target_via_topology_sourceK23
  topologySourceCommonNeighbor :=
    ExplicitInputMatrices.target_via_topology_sourceCommonNeighbor
  geometryDirect :=
    ExplicitInputMatrices.target_via_geometry_direct
  geometryK23 :=
    ExplicitInputMatrices.target_via_geometry_k23
  geometryCommonNeighbor :=
    ExplicitInputMatrices.target_via_geometry_commonNeighbor
  geometryK23CommonNeighborK23 :=
    ExplicitInputMatrices.target_via_geometry_k23CommonNeighborK23
  geometryK23CommonNeighborCommonNeighbor :=
    ExplicitInputMatrices.target_via_geometry_k23CommonNeighborCommonNeighbor
  routeSummarySubpolygonFinalDirect :=
    ExplicitInputMatrices.target_via_routeSummary_subpolygonFinalDirect
  routeSummaryGeometryDirect :=
    ExplicitInputMatrices.target_via_routeSummary_geometryDirect
  routeSummaryGeometryK23 :=
    ExplicitInputMatrices.target_via_routeSummary_geometryK23
  routeSummaryGeometryCommonNeighbor :=
    ExplicitInputMatrices.target_via_routeSummary_geometryCommonNeighbor

/-! ## Final summary matrix -/

/-- Final subpolygon/geometry route summary.

The matrix records checked ledgers, the explicit input shape, and conditional
projection functions.  It does not supply an input bundle.
-/
structure Matrix : Type (u + 7) where
  checked : CheckedMatrices.{u}
  inputs : Type (u + 5)
  projections : ConditionalTargetProjections.{u}

/-- The checked final subpolygon/geometry route summary matrix. -/
def matrix : Matrix.{u} where
  checked := checkedMatrices
  inputs := ExplicitInputMatrices.{u}
  projections := conditionalTargetProjections

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_subpolygonTargetFinal :
    matrix.{u}.checked.subpolygonTargetFinal =
      SubpolygonTargetFinalW11.matrix := by
  rfl

theorem checked_subpolygonFinal :
    matrix.{u}.checked.subpolygonFinal =
      SubpolygonFinalIntegratedW11.matrix := by
  rfl

theorem checked_topologyFinal :
    matrix.{u}.checked.topologyFinal =
      TopologyFinalIntegratedW11.matrix := by
  rfl

theorem checked_geometryTargetFinal :
    matrix.{u}.checked.geometryTargetFinal =
      GeometryTargetFinalW11.matrix := by
  rfl

/-! ## Public conditional target projections -/

theorem target_via_subpolygonTarget_direct
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonTarget_direct M

theorem target_via_subpolygonTarget_topologyDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonTarget_topologyDirect M

theorem target_via_subpolygonTarget_topologyK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonTarget_topologyK23 M

theorem target_via_subpolygonTarget_topologyCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonTarget_topologyCommonNeighbor M

theorem target_via_subpolygonFinal_direct
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonFinal_direct M

theorem target_via_subpolygonFinal_k23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonFinal_k23 M

theorem target_via_subpolygonFinal_commonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonFinal_commonNeighbor M

theorem target_via_subpolygonFinal_directGeometry
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonFinal_directGeometry M

theorem target_via_subpolygonFinal_k23Geometry
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonFinal_k23Geometry M

theorem target_via_subpolygonFinal_commonNeighborGeometry
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_subpolygonFinal_commonNeighborGeometry M

theorem target_via_topology_subpolygonDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_topology_subpolygonDirect M

theorem target_via_topology_subpolygonK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_topology_subpolygonK23 M

theorem target_via_topology_subpolygonCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_topology_subpolygonCommonNeighbor M

theorem target_via_topology_sourceDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_topology_sourceDirect M

theorem target_via_topology_sourceK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_topology_sourceK23 M

theorem target_via_topology_sourceCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_topology_sourceCommonNeighbor M

theorem target_via_geometry_direct
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_geometry_direct M

theorem target_via_geometry_k23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_geometry_k23 M

theorem target_via_geometry_commonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_geometry_commonNeighbor M

theorem target_via_geometry_k23CommonNeighborK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_geometry_k23CommonNeighborK23 M

theorem target_via_geometry_k23CommonNeighborCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_geometry_k23CommonNeighborCommonNeighbor M

theorem target_via_routeSummary_subpolygonFinalDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_routeSummary_subpolygonFinalDirect M

theorem target_via_routeSummary_geometryDirect
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_routeSummary_geometryDirect M

theorem target_via_routeSummary_geometryK23
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_routeSummary_geometryK23 M

theorem target_via_routeSummary_geometryCommonNeighbor
    (M : ExplicitInputMatrices.{u}) :
    Target :=
  ExplicitInputMatrices.target_via_routeSummary_geometryCommonNeighbor M

end

end SubpolygonGeometryRouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
