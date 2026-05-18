import ErdosProblems1066.Swanepoel.TopologyTargetIntegratedW11
import ErdosProblems1066.Swanepoel.TopologyIntegratedW11
import ErdosProblems1066.Swanepoel.SubpolygonTargetIntegratedW11
import ErdosProblems1066.Swanepoel.SubpolygonIntegratedW11
import ErdosProblems1066.Swanepoel.BoundaryAngleIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 topology, boundary, and subpolygon aggregate

This terminal W11 ledger gathers the checked topology extraction,
boundary-angle, subpolygon, and final consistency matrices.  Geometry and
source matrices remain explicit inputs, and every Swanepoel target projection
below is conditional on one of those inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyFinalIntegratedW11

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TopologyTargetIntegratedW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TopologyTargetIntegratedW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TopologyTargetIntegratedW11.PipelineCleared

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  TopologyTargetIntegratedW11.CanonicalGraph C

abbrev CheckedTopologyPackage (C : _root_.UDConfig n) :=
  TopologyTargetIntegratedW11.CheckedTopologyPackage C

abbrev TopologyFrontierPackage (C : _root_.UDConfig n) :=
  TopologyTargetIntegratedW11.TopologyFrontierPackage C

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  TopologyTargetIntegratedW11.BoundaryInput.{u} C

abbrev TopologyExtractionFields (C : _root_.UDConfig n) :=
  TopologyTargetIntegratedW11.TopologyExtractionFields C

abbrev BoundarySubpolygonAggregate (C : _root_.UDConfig n) :=
  TopologyTargetIntegratedW11.BoundarySubpolygonAggregate.{u} C

abbrev DirectSubpolygonGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  TopologyTargetIntegratedW11.DirectSubpolygonGeometryFields.{u} C hmin

abbrev K23SubpolygonGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  TopologyTargetIntegratedW11.K23SubpolygonGeometryFields.{u} C hmin

abbrev CommonNeighborSubpolygonGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  TopologyTargetIntegratedW11.CommonNeighborSubpolygonGeometryFields.{u}
    C hmin

abbrev DirectBoundaryAngleGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  TopologyTargetIntegratedW11.DirectBoundaryAngleGeometryFields.{u} C hmin

abbrev K23BoundaryAngleGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  TopologyTargetIntegratedW11.K23BoundaryAngleGeometryFields.{u} C hmin

abbrev CommonNeighborBoundaryAngleGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  TopologyTargetIntegratedW11.CommonNeighborBoundaryAngleGeometryFields.{u}
    C hmin

abbrev ConditionalSwanepoelTargetRoutes :=
  TopologyTargetIntegratedW11.ConditionalTargetRoutes.{u}

/-! ## Explicit extraction ledger -/

/-- Extraction and boundary/subpolygon projections retained by the final
aggregate. -/
structure ExtractionProjectionLedger : Type (u + 3) where
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

/-- Checked extraction routes from the topology target aggregate. -/
def extractionProjectionLedger :
    ExtractionProjectionLedger.{u} where
  topologyOfChecked :=
    TopologyTargetIntegratedW11.topologyExtractionOfCheckedPackage
  topologyOfFrontier :=
    TopologyTargetIntegratedW11.topologyExtractionOfFrontier
  boundaryAggregate :=
    TopologyTargetIntegratedW11.boundarySubpolygonAggregateOfInput
  exactTopology :=
    TopologyTargetIntegratedW11.exactFieldTargetOfAggregate
  faceCounting :=
    TopologyTargetIntegratedW11.faceCountingTheoremsOfAggregate

/-! ## Explicit geometry and source matrices -/

/-- Caller-supplied matrices for all final conditional topology routes.

The final aggregate records this input shape only; it does not construct a
uniform matrix in any branch. -/
structure ExplicitGeometryMatrices : Type (u + 3) where
  subpolygonDirect :
    SubpolygonTargetIntegratedW11.DirectMatrix.{u}
  subpolygonK23 :
    SubpolygonTargetIntegratedW11.K23Matrix.{u}
  subpolygonCommonNeighbor :
    SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u}
  boundaryDirect :
    SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}
  boundaryK23 :
    SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u}
  boundaryCommonNeighbor :
    SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u}
  boundaryAngleDirect :
    BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u}
  boundaryAngleK23 :
    BoundaryAngleIntegratedW11.K23GeometryMatrix.{u}
  boundaryAngleCommonNeighbor :
    BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u}
  sourceDirect :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}
  sourceK23 :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u}
  sourceCommonNeighbor :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}
  noEarly :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}
  noStart :
    WindowNoEarlyRowsW11.NoStartMatrix.{u, u}

/-- Conditional Swanepoel target routes inherited from the topology target
aggregate. -/
def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} :=
  TopologyTargetIntegratedW11.conditionalTargetRoutes

namespace ExplicitGeometryMatrices

/-- Conditional target projection through explicit direct subpolygon rows. -/
theorem target_via_subpolygonDirect
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.subpolygonDirect M.subpolygonDirect

/-- Conditional target projection through explicit K23 subpolygon rows. -/
theorem target_via_subpolygonK23
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.subpolygonK23 M.subpolygonK23

/-- Conditional target projection through explicit common-neighbor subpolygon
rows. -/
theorem target_via_subpolygonCommonNeighbor
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.subpolygonCommonNeighbor
    M.subpolygonCommonNeighbor

/-- Conditional target projection through direct boundary geometry rows. -/
theorem target_via_boundaryDirect
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.boundaryDirect M.boundaryDirect

/-- Conditional target projection through K23 boundary geometry rows. -/
theorem target_via_boundaryK23
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.boundaryK23 M.boundaryK23

/-- Conditional target projection through common-neighbor boundary geometry
rows. -/
theorem target_via_boundaryCommonNeighbor
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.boundaryCommonNeighbor
    M.boundaryCommonNeighbor

/-- Conditional target projection through direct boundary-angle geometry
rows. -/
theorem target_via_boundaryAngleDirect
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.boundaryAngleDirect
    M.boundaryAngleDirect

/-- Conditional target projection through K23 boundary-angle geometry rows. -/
theorem target_via_boundaryAngleK23
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.boundaryAngleK23
    M.boundaryAngleK23

/-- Conditional target projection through common-neighbor boundary-angle
geometry rows. -/
theorem target_via_boundaryAngleCommonNeighbor
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.boundaryAngleCommonNeighbor
    M.boundaryAngleCommonNeighbor

/-- Conditional target projection through direct source fields. -/
theorem target_via_sourceDirect
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.sourceDirect M.sourceDirect

/-- Conditional target projection through K23 source fields. -/
theorem target_via_sourceK23
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.sourceK23 M.sourceK23

/-- Conditional target projection through common-neighbor source fields. -/
theorem target_via_sourceCommonNeighbor
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.sourceCommonNeighbor
    M.sourceCommonNeighbor

/-- Conditional target projection through no-early rows. -/
theorem target_via_noEarly
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.noEarly M.noEarly

/-- Conditional target projection through no-start rows. -/
theorem target_via_noStart
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  conditionalSwanepoelTargetRoutes.noStart M.noStart

end ExplicitGeometryMatrices

/-! ## Checked imported ledgers -/

/-- Checked W11 ledgers gathered by the final topology aggregate. -/
structure ImportedMatrices : Type (u + 5) where
  topologyTarget :
    TopologyTargetIntegratedW11.Matrix.{u}
  topologyIntegrated :
    TopologyIntegratedW11.Matrix.{u}
  subpolygonIntegrated :
    SubpolygonIntegratedW11.Matrix.{u}
  subpolygonTarget :
    SubpolygonTargetIntegratedW11.Matrix.{u}
  boundaryAngleIntegrated :
    BoundaryAngleIntegratedW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}

/-- The checked imported W11 ledgers. -/
def importedMatrices : ImportedMatrices.{u} where
  topologyTarget := TopologyTargetIntegratedW11.matrix
  topologyIntegrated := TopologyIntegratedW11.matrix
  subpolygonIntegrated := SubpolygonIntegratedW11.matrix
  subpolygonTarget := SubpolygonTargetIntegratedW11.matrix
  boundaryAngleIntegrated := BoundaryAngleIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix

/-! ## Final aggregate matrix -/

/-- Final topology/boundary/subpolygon aggregate.

The matrix contains checked ledgers, extraction projections, explicit input
shapes, and conditional target routes. -/
structure Matrix : Type (u + 5) where
  imported : ImportedMatrices.{u}
  extraction : ExtractionProjectionLedger.{u}
  routeInputs : Type (u + 3)
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked final aggregate. -/
def matrix : Matrix.{u} where
  imported := importedMatrices
  extraction := extractionProjectionLedger
  routeInputs := ExplicitGeometryMatrices.{u}
  routes := conditionalSwanepoelTargetRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_topologyTarget :
    matrix.{u}.imported.topologyTarget =
      TopologyTargetIntegratedW11.matrix := by
  rfl

/-- The final consistency ledger agrees with the target-integrated matrix. -/
theorem checked_finalConsistency_targetIntegrated :
    SwanepoelW11FinalConsistency.checkedModuleLedger.targetIntegrated =
      TargetIntegratedMatrixW11.matrix := by
  rfl

/-! ## Public extraction projections -/

def topologyExtractionOfCheckedPackage
    {C : _root_.UDConfig n}
    (T : CheckedTopologyPackage C) :
    TopologyExtractionFields C :=
  TopologyTargetIntegratedW11.topologyExtractionOfCheckedPackage T

def topologyExtractionOfFrontier
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C) :
    TopologyExtractionFields C :=
  TopologyTargetIntegratedW11.topologyExtractionOfFrontier T

def boundarySubpolygonAggregateOfInput
    {C : _root_.UDConfig n}
    (T : TopologyFrontierPackage C)
    (B : BoundaryInput.{u} C) :
    BoundarySubpolygonAggregate.{u} C :=
  TopologyTargetIntegratedW11.boundarySubpolygonAggregateOfInput T B

theorem exactTopologyOfBoundarySubpolygonAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    TopologyClosureW11.W10ExactFieldTarget C :=
  TopologyTargetIntegratedW11.exactFieldTargetOfAggregate A

theorem faceCountingOfBoundarySubpolygonAggregate
    {C : _root_.UDConfig n}
    (A : BoundarySubpolygonAggregate.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      A.subpolygons.toPlanarBoundaryData :=
  TopologyTargetIntegratedW11.faceCountingTheoremsOfAggregate A

/-! ## Public conditional target projections -/

theorem swanepoelTarget_of_subpolygonDirectMatrix
    (M : SubpolygonTargetIntegratedW11.DirectMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfSubpolygonDirectMatrix M

theorem swanepoelTarget_of_subpolygonK23Matrix
    (M : SubpolygonTargetIntegratedW11.K23Matrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfSubpolygonK23Matrix M

theorem swanepoelTarget_of_subpolygonCommonNeighborMatrix
    (M : SubpolygonTargetIntegratedW11.CommonNeighborMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfSubpolygonCommonNeighborMatrix M

theorem swanepoelTarget_of_boundaryDirectMatrix
    (M : SubpolygonIntegratedW11.DirectBoundaryGeometryMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfBoundaryDirectMatrix M

theorem swanepoelTarget_of_boundaryK23Matrix
    (M : SubpolygonIntegratedW11.K23BoundaryGeometryMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfBoundaryK23Matrix M

theorem swanepoelTarget_of_boundaryCommonNeighborMatrix
    (M : SubpolygonIntegratedW11.CommonNeighborBoundaryGeometryMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfBoundaryCommonNeighborMatrix M

theorem swanepoelTarget_of_boundaryAngleDirectMatrix
    (M : BoundaryAngleIntegratedW11.DirectGeometryMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfBoundaryAngleDirectMatrix M

theorem swanepoelTarget_of_boundaryAngleK23Matrix
    (M : BoundaryAngleIntegratedW11.K23GeometryMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfBoundaryAngleK23Matrix M

theorem swanepoelTarget_of_boundaryAngleCommonNeighborMatrix
    (M : BoundaryAngleIntegratedW11.CommonNeighborGeometryMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfBoundaryAngleCommonNeighborMatrix M

theorem swanepoelTarget_of_sourceDirectMatrix
    (M : BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfSourceDirectMatrix M

theorem swanepoelTarget_of_sourceK23Matrix
    (M : BrokenLatticeIntegratedW11.K23FieldMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfSourceK23Matrix M

theorem swanepoelTarget_of_sourceCommonNeighborMatrix
    (M : BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfSourceCommonNeighborMatrix M

theorem swanepoelTarget_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u, u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfNoEarlyMatrix M

theorem swanepoelTarget_of_noStartMatrix
    (M : WindowNoEarlyRowsW11.NoStartMatrix.{u, u}) :
    Target :=
  TopologyTargetIntegratedW11.targetOfNoStartMatrix M

end

end TopologyFinalIntegratedW11
end Swanepoel
end ErdosProblems1066
