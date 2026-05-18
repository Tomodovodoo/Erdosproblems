import ErdosProblems1066.Swanepoel.TopologyFinalIntegratedW11
import ErdosProblems1066.Swanepoel.TopologyTargetIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleTargetFinalW11
import ErdosProblems1066.Swanepoel.SubpolygonFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalAggregate
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 topology target summary

This module is the target-facing summary for the final W11 topology pass.  It
keeps topology extraction, boundary/subpolygon geometry, boundary-angle final
rows, subpolygon final rows, and Swanepoel final ledgers visible as separate
input surfaces.  Each target projection below consumes an explicit supplied
matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyTargetFinalW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TopologyFinalIntegratedW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TopologyFinalIntegratedW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TopologyFinalIntegratedW11.PipelineCleared

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  TopologyFinalIntegratedW11.CanonicalGraph C

abbrev CheckedTopologyPackage (C : _root_.UDConfig n) :=
  TopologyFinalIntegratedW11.CheckedTopologyPackage C

abbrev TopologyFrontierPackage (C : _root_.UDConfig n) :=
  TopologyFinalIntegratedW11.TopologyFrontierPackage C

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  TopologyFinalIntegratedW11.BoundaryInput.{u} C

abbrev TopologyExtractionFields (C : _root_.UDConfig n) :=
  TopologyFinalIntegratedW11.TopologyExtractionFields C

abbrev BoundarySubpolygonAggregate (C : _root_.UDConfig n) :=
  TopologyFinalIntegratedW11.BoundarySubpolygonAggregate.{u} C

/-! ## Checked final ledgers -/

/-- Final W11 ledgers checked together by this target summary. -/
structure CheckedFinalLedgers : Type (u + 5) where
  topologyTarget :
    TopologyTargetIntegratedW11.Matrix.{u}
  topologyFinal :
    TopologyFinalIntegratedW11.Matrix.{u}
  boundaryAngleTargetFinal :
    BoundaryAngleTargetFinalW11.Matrix.{u}
  subpolygonFinal :
    SubpolygonFinalIntegratedW11.Matrix.{u}
  swanepoelFinalAggregate :
    SwanepoelW11FinalAggregate.Matrix.{u}
  swanepoelFinalConsistencyTargetIntegrated :
    SwanepoelW11FinalConsistency.matrix.checkedModules.targetIntegrated =
      TargetIntegratedMatrixW11.matrix

/-- The checked W11 ledgers imported by the final topology target summary. -/
def checkedFinalLedgers : CheckedFinalLedgers.{u} where
  topologyTarget := TopologyTargetIntegratedW11.matrix
  topologyFinal := TopologyFinalIntegratedW11.matrix
  boundaryAngleTargetFinal := BoundaryAngleTargetFinalW11.matrix
  subpolygonFinal := SubpolygonFinalIntegratedW11.matrix
  swanepoelFinalAggregate := SwanepoelW11FinalAggregate.matrix
  swanepoelFinalConsistencyTargetIntegrated := by
    rfl

/-! ## Explicit extraction matrix -/

/-- Extraction and boundary/subpolygon geometry projections exposed by the
final target summary. -/
structure ExplicitExtractionMatrix : Type (u + 3) where
  topologyOfChecked :
    forall {n : Nat} {C : _root_.UDConfig n},
      CheckedTopologyPackage C -> TopologyExtractionFields C
  topologyOfFrontier :
    forall {n : Nat} {C : _root_.UDConfig n},
      TopologyFrontierPackage C -> TopologyExtractionFields C
  boundaryAggregate :
    forall {n : Nat} {C : _root_.UDConfig n},
      TopologyFrontierPackage C ->
      BoundaryInput.{u} C ->
      BoundarySubpolygonAggregate.{u} C
  exactTopology :
    forall {n : Nat} {C : _root_.UDConfig n},
      BoundarySubpolygonAggregate.{u} C ->
        TopologyClosureW11.W10ExactFieldTarget C
  faceCounting :
    forall {n : Nat} {C : _root_.UDConfig n}
      (A : BoundarySubpolygonAggregate.{u} C),
        PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
          A.subpolygons.toPlanarBoundaryData

/-- The checked extraction matrix inherited from the final integrated
topology ledger. -/
def explicitExtractionMatrix : ExplicitExtractionMatrix.{u} where
  topologyOfChecked :=
    TopologyFinalIntegratedW11.topologyExtractionOfCheckedPackage
  topologyOfFrontier :=
    TopologyFinalIntegratedW11.topologyExtractionOfFrontier
  boundaryAggregate :=
    TopologyFinalIntegratedW11.boundarySubpolygonAggregateOfInput
  exactTopology :=
    TopologyFinalIntegratedW11.exactTopologyOfBoundarySubpolygonAggregate
  faceCounting :=
    TopologyFinalIntegratedW11.faceCountingOfBoundarySubpolygonAggregate

/-! ## Explicit geometry matrices -/

/-- Explicit matrix surfaces consumed by final target projections. -/
structure ExplicitFinalGeometryMatrices : Type (u + 3) where
  topology :
    TopologyFinalIntegratedW11.ExplicitGeometryMatrices.{u}
  boundaryAngleFinal :
    BoundaryAngleTargetFinalW11.FinalMatrixInput.{u}
  subpolygonFinal :
    SubpolygonFinalIntegratedW11.FinalSubpolygonMatrix.{u}

namespace ExplicitFinalGeometryMatrices

/-- Target projection through explicit direct subpolygon rows. -/
theorem target_via_topologySubpolygonDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_subpolygonDirect
    M.topology

/-- Target projection through explicit K23 subpolygon rows. -/
theorem target_via_topologySubpolygonK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_subpolygonK23
    M.topology

/-- Target projection through explicit common-neighbor subpolygon rows. -/
theorem target_via_topologySubpolygonCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_subpolygonCommonNeighbor
    M.topology

/-- Target projection through explicit direct boundary geometry rows. -/
theorem target_via_topologyBoundaryDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_boundaryDirect
    M.topology

/-- Target projection through explicit K23 boundary geometry rows. -/
theorem target_via_topologyBoundaryK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_boundaryK23
    M.topology

/-- Target projection through explicit common-neighbor boundary geometry rows. -/
theorem target_via_topologyBoundaryCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_boundaryCommonNeighbor
    M.topology

/-- Target projection through explicit direct boundary-angle rows. -/
theorem target_via_topologyBoundaryAngleDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_boundaryAngleDirect
    M.topology

/-- Target projection through explicit K23 boundary-angle rows. -/
theorem target_via_topologyBoundaryAngleK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_boundaryAngleK23
    M.topology

/-- Target projection through explicit common-neighbor boundary-angle rows. -/
theorem target_via_topologyBoundaryAngleCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_boundaryAngleCommonNeighbor
    M.topology

/-- Target projection through explicit direct source fields. -/
theorem target_via_topologySourceDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_sourceDirect
    M.topology

/-- Target projection through explicit K23 source fields. -/
theorem target_via_topologySourceK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_sourceK23
    M.topology

/-- Target projection through explicit common-neighbor source fields. -/
theorem target_via_topologySourceCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_sourceCommonNeighbor
    M.topology

/-- Target projection through explicit no-early rows. -/
theorem target_via_topologyNoEarly
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_noEarly
    M.topology

/-- Target projection through explicit no-start rows. -/
theorem target_via_topologyNoStart
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  TopologyFinalIntegratedW11.ExplicitGeometryMatrices.target_via_noStart
    M.topology

/-- Target projection through direct boundary-angle final rows. -/
theorem target_via_boundaryAngleFinalDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_direct
    M.boundaryAngleFinal

/-- Target projection through K23 boundary-angle final rows. -/
theorem target_via_boundaryAngleFinalK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_k23
    M.boundaryAngleFinal

/-- Target projection through common-neighbor boundary-angle final rows. -/
theorem target_via_boundaryAngleFinalCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
    M.boundaryAngleFinal

/-- Target projection through direct final subpolygon rows. -/
theorem target_via_subpolygonFinalDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_direct
    M.subpolygonFinal

/-- Target projection through K23 final subpolygon rows. -/
theorem target_via_subpolygonFinalK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_k23
    M.subpolygonFinal

/-- Target projection through common-neighbor final subpolygon rows. -/
theorem target_via_subpolygonFinalCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  SubpolygonFinalIntegratedW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
    M.subpolygonFinal

end ExplicitFinalGeometryMatrices

/-! ## Conditional target projection matrix -/

/-- The public target projection functions retained by this summary. -/
structure ConditionalTargetProjectionMatrix : Type (u + 3) where
  topologySubpolygonDirect :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologySubpolygonK23 :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologySubpolygonCommonNeighbor :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyBoundaryDirect :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyBoundaryK23 :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyBoundaryCommonNeighbor :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyBoundaryAngleDirect :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyBoundaryAngleK23 :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyBoundaryAngleCommonNeighbor :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologySourceDirect :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologySourceK23 :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologySourceCommonNeighbor :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyNoEarly :
    ExplicitFinalGeometryMatrices.{u} -> Target
  topologyNoStart :
    ExplicitFinalGeometryMatrices.{u} -> Target
  boundaryAngleFinalDirect :
    ExplicitFinalGeometryMatrices.{u} -> Target
  boundaryAngleFinalK23 :
    ExplicitFinalGeometryMatrices.{u} -> Target
  boundaryAngleFinalCommonNeighbor :
    ExplicitFinalGeometryMatrices.{u} -> Target
  subpolygonFinalDirect :
    ExplicitFinalGeometryMatrices.{u} -> Target
  subpolygonFinalK23 :
    ExplicitFinalGeometryMatrices.{u} -> Target
  subpolygonFinalCommonNeighbor :
    ExplicitFinalGeometryMatrices.{u} -> Target

/-- Conditional target projection functions assembled from checked ledgers. -/
def conditionalTargetProjectionMatrix :
    ConditionalTargetProjectionMatrix.{u} where
  topologySubpolygonDirect :=
    ExplicitFinalGeometryMatrices.target_via_topologySubpolygonDirect
  topologySubpolygonK23 :=
    ExplicitFinalGeometryMatrices.target_via_topologySubpolygonK23
  topologySubpolygonCommonNeighbor :=
    ExplicitFinalGeometryMatrices.target_via_topologySubpolygonCommonNeighbor
  topologyBoundaryDirect :=
    ExplicitFinalGeometryMatrices.target_via_topologyBoundaryDirect
  topologyBoundaryK23 :=
    ExplicitFinalGeometryMatrices.target_via_topologyBoundaryK23
  topologyBoundaryCommonNeighbor :=
    ExplicitFinalGeometryMatrices.target_via_topologyBoundaryCommonNeighbor
  topologyBoundaryAngleDirect :=
    ExplicitFinalGeometryMatrices.target_via_topologyBoundaryAngleDirect
  topologyBoundaryAngleK23 :=
    ExplicitFinalGeometryMatrices.target_via_topologyBoundaryAngleK23
  topologyBoundaryAngleCommonNeighbor :=
    ExplicitFinalGeometryMatrices.target_via_topologyBoundaryAngleCommonNeighbor
  topologySourceDirect :=
    ExplicitFinalGeometryMatrices.target_via_topologySourceDirect
  topologySourceK23 :=
    ExplicitFinalGeometryMatrices.target_via_topologySourceK23
  topologySourceCommonNeighbor :=
    ExplicitFinalGeometryMatrices.target_via_topologySourceCommonNeighbor
  topologyNoEarly :=
    ExplicitFinalGeometryMatrices.target_via_topologyNoEarly
  topologyNoStart :=
    ExplicitFinalGeometryMatrices.target_via_topologyNoStart
  boundaryAngleFinalDirect :=
    ExplicitFinalGeometryMatrices.target_via_boundaryAngleFinalDirect
  boundaryAngleFinalK23 :=
    ExplicitFinalGeometryMatrices.target_via_boundaryAngleFinalK23
  boundaryAngleFinalCommonNeighbor :=
    ExplicitFinalGeometryMatrices.target_via_boundaryAngleFinalCommonNeighbor
  subpolygonFinalDirect :=
    ExplicitFinalGeometryMatrices.target_via_subpolygonFinalDirect
  subpolygonFinalK23 :=
    ExplicitFinalGeometryMatrices.target_via_subpolygonFinalK23
  subpolygonFinalCommonNeighbor :=
    ExplicitFinalGeometryMatrices.target_via_subpolygonFinalCommonNeighbor

/-! ## Final summary matrix -/

/-- Final topology target summary: checked ledgers, extraction projections,
explicit matrix surface, and only conditional target projections. -/
structure Matrix : Type (u + 5) where
  checked : CheckedFinalLedgers.{u}
  extraction : ExplicitExtractionMatrix.{u}
  geometryInputs : Type (u + 3)
  targetProjections : ConditionalTargetProjectionMatrix.{u}

/-- The checked final topology target summary. -/
def matrix : Matrix.{u} where
  checked := checkedFinalLedgers
  extraction := explicitExtractionMatrix
  geometryInputs := ExplicitFinalGeometryMatrices.{u}
  targetProjections := conditionalTargetProjectionMatrix

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_topologyTarget :
    matrix.{u}.checked.topologyTarget =
      TopologyTargetIntegratedW11.matrix := by
  rfl

theorem checked_topologyFinal :
    matrix.{u}.checked.topologyFinal =
      TopologyFinalIntegratedW11.matrix := by
  rfl

theorem checked_boundaryAngleTargetFinal :
    matrix.{u}.checked.boundaryAngleTargetFinal =
      BoundaryAngleTargetFinalW11.matrix := by
  rfl

theorem checked_subpolygonFinal :
    matrix.{u}.checked.subpolygonFinal =
      SubpolygonFinalIntegratedW11.matrix := by
  rfl

theorem checked_swanepoelFinalAggregate :
    matrix.{u}.checked.swanepoelFinalAggregate =
      SwanepoelW11FinalAggregate.matrix := by
  rfl

theorem checked_swanepoelFinalConsistency_targetIntegrated :
    SwanepoelW11FinalConsistency.matrix.checkedModules.targetIntegrated =
      TargetIntegratedMatrixW11.matrix :=
  by
    rfl

/-! ## Public extraction projections -/

def topologyExtractionOfCheckedPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    TopologyExtractionFields C :=
  TopologyFinalIntegratedW11.topologyExtractionOfCheckedPackage T

def topologyExtractionOfFrontier
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFields C :=
  TopologyFinalIntegratedW11.topologyExtractionOfFrontier T

def boundarySubpolygonAggregateOfInput
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C)
    (B : BoundaryInput.{u} C) :
    BoundarySubpolygonAggregate.{u} C :=
  TopologyFinalIntegratedW11.boundarySubpolygonAggregateOfInput T B

theorem exactTopologyOfBoundarySubpolygonAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  TopologyFinalIntegratedW11.exactTopologyOfBoundarySubpolygonAggregate A

theorem faceCountingOfBoundarySubpolygonAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      A.subpolygons.toPlanarBoundaryData :=
  TopologyFinalIntegratedW11.faceCountingOfBoundarySubpolygonAggregate A

/-! ## Public conditional target projections -/

theorem swanepoelTarget_via_topologySubpolygonDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologySubpolygonDirect M

theorem swanepoelTarget_via_topologySubpolygonK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologySubpolygonK23 M

theorem swanepoelTarget_via_topologySubpolygonCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologySubpolygonCommonNeighbor M

theorem swanepoelTarget_via_topologyBoundaryDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyBoundaryDirect M

theorem swanepoelTarget_via_topologyBoundaryK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyBoundaryK23 M

theorem swanepoelTarget_via_topologyBoundaryCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyBoundaryCommonNeighbor M

theorem swanepoelTarget_via_topologyBoundaryAngleDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyBoundaryAngleDirect M

theorem swanepoelTarget_via_topologyBoundaryAngleK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyBoundaryAngleK23 M

theorem swanepoelTarget_via_topologyBoundaryAngleCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyBoundaryAngleCommonNeighbor M

theorem swanepoelTarget_via_topologySourceDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologySourceDirect M

theorem swanepoelTarget_via_topologySourceK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologySourceK23 M

theorem swanepoelTarget_via_topologySourceCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologySourceCommonNeighbor M

theorem swanepoelTarget_via_topologyNoEarly
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyNoEarly M

theorem swanepoelTarget_via_topologyNoStart
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_topologyNoStart M

theorem swanepoelTarget_via_boundaryAngleFinalDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_boundaryAngleFinalDirect M

theorem swanepoelTarget_via_boundaryAngleFinalK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_boundaryAngleFinalK23 M

theorem swanepoelTarget_via_boundaryAngleFinalCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_boundaryAngleFinalCommonNeighbor M

theorem swanepoelTarget_via_subpolygonFinalDirect
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_subpolygonFinalDirect M

theorem swanepoelTarget_via_subpolygonFinalK23
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_subpolygonFinalK23 M

theorem swanepoelTarget_via_subpolygonFinalCommonNeighbor
    (M : ExplicitFinalGeometryMatrices.{u}) :
    Target :=
  ExplicitFinalGeometryMatrices.target_via_subpolygonFinalCommonNeighbor M

end

end TopologyTargetFinalW11
end Swanepoel
end ErdosProblems1066
