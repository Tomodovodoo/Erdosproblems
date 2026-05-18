import ErdosProblems1066.Swanepoel.BoundaryAngleClosureW11
import ErdosProblems1066.Swanepoel.BoundaryLabelClosureW11
import ErdosProblems1066.Swanepoel.SubpolygonIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Integrated W11 boundary-angle matrix

This module ties the explicit W11 boundary-angle package to the W11 geometry
and target-facade surfaces.  The topology, classification, subpolygon family,
long-arc fields, boundary labels, window containment, and selected no-early
alternative remain visible fields of the row records below.

The declarations here are adapters and conditional closure projections only.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleIntegratedW11

open MinimalGraphFacts

universe u v

noncomputable section

variable {n : Nat}

abbrev BoundaryInput (C : _root_.UDConfig n) :=
  BoundaryAngleClosureW11.BoundaryAngleClosureInput.{u} C

abbrev MinimalFailureExclusion : Prop :=
  TargetClosureMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetClosureMatrixW11.PipelineCleared

/-! ## Boundary angle plus explicit labels -/

/-- Boundary-angle source data plus the matching explicit W11 boundary-label
package.

The label package is indexed by the topology/partition-angle components
obtained from the same boundary-angle source, so the topology, classification,
subpolygon, and long-arc data stay tied to the labels used downstream.
-/
structure BoundaryAngleLabelPrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryInput.{u} C
  labels :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.{u}
      C hmin boundary.toW10TopologyComponentFields
        boundary.toW10PartitionAngleComponentFields

namespace BoundaryAngleLabelPrefix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The W11 boundary-label base prefix selected by this boundary-angle row. -/
def toLabelBasePrefix
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix.{u}
      C hmin where
  topology := P.boundary.toW10TopologyComponentFields
  partitionAngle := P.boundary.toW10PartitionAngleComponentFields
  labels := P.labels

/-- The topology/angle/subpolygon row produced by the boundary-angle package. -/
def toTopologyAngleSubpolygonRow
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    SwanepoelRemainingObligationsW9.TopologyAngleSubpolygonRow.{u} C :=
  P.boundary.toTopologyAngleSubpolygonRow

/-- The W9 base row after adding the explicit boundary labels. -/
def toW9BaseRow
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    SwanepoelRemainingObligationsW9.BaseRow.{u} C hmin :=
  P.toLabelBasePrefix.toW10BaseRow

/-- Geometry source fields obtained from the same boundary-angle and label
prefix. -/
def toGeometrySourceFields
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u} C hmin :=
  BoundaryLabelClosureW11.LabelBasePrefix.toGeometrySourceFields
    P.toLabelBasePrefix

/-- The concrete boundary classification row remains visible. -/
def classification
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      P.boundary.topology.toCore :=
  P.boundary.classification

/-- The boundary-angle topology package before labels are added. -/
def toBoundaryAngleTurnTopologyPackage
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.{u}
      C :=
  P.boundary.toBoundaryAngleTurnTopologyPackage

@[simp]
theorem toTopologyAngleSubpolygonRow_Subpolygon
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    P.toTopologyAngleSubpolygonRow.Subpolygon =
      P.boundary.subpolygons.Subpolygon :=
  rfl

/-- The checked outer-boundary E12 inequality carried by the boundary-angle
source. -/
theorem boundaryAngleCountInequality
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    P.boundary.classification.counts.d5 +
          2 * P.boundary.classification.counts.d6 +
        P.boundary.classification.counts.b +
          P.boundary.classification.counts.B + 6 <=
      P.boundary.classification.counts.d3 :=
  P.boundary.boundaryAngleCountInequality

/-- The checked negative-count E12 form carried by the boundary-angle source. -/
theorem boundaryNegativeCountInequality
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    P.boundary.classification.counts.negativeCount +
        P.boundary.classification.counts.B + 6 <=
      P.boundary.classification.counts.d3 :=
  P.boundary.boundaryNegativeCountInequality

/-- The checked E13 low-degree conclusion for every explicit subpolygon. -/
theorem subpolygonLowDegree
    (P : BoundaryAngleLabelPrefix.{u} C hmin)
    (S : P.boundary.subpolygons.Subpolygon) :
    6 <= 2 * (P.boundary.subpolygonData S).counts.D2 +
      (P.boundary.subpolygonData S).counts.D3 :=
  P.boundary.subpolygonLowDegree S

/-- The selected long-arc turn bound routed through the boundary package. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three
    (P : BoundaryAngleLabelPrefix.{u} C hmin) :
    Lemma10Inequalities.totalTurn
        P.boundary.boundaryAngleTurnPackage.m8TurnBounds.turn <
      Real.pi / 3 :=
  P.boundary.m8TurnBounds_totalTurn_lt_pi_div_three

end BoundaryAngleLabelPrefix

/-! ## Geometry rows with explicit window and no-early alternatives -/

/-- Direct boundary-angle geometry row with explicit labels, window
containment, and direct no-start/no-early data. -/
structure DirectGeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundaryPrefix : BoundaryAngleLabelPrefix.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      boundaryPrefix.toGeometrySourceFields
  noStartNoEarly :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      boundaryPrefix.toGeometrySourceFields

namespace DirectGeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Direct concrete no-early data extracted from the explicit no-start row. -/
def noEarly
    (R : DirectGeometryRow.{u} C hmin) :=
  R.noStartNoEarly.noEarly

/-- Forget the integrated direct row to the W10 geometry package. -/
def toDirectGeometryPackage
    (R : DirectGeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.DirectGeometryPackage.{u} C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  noStartNoEarly := R.noStartNoEarly

/-- Route the integrated direct row into the W11 geometry closure facade. -/
def toGeometryClosureRow
    (R : DirectGeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofDirectGeometryPackage
    R.toDirectGeometryPackage

/-- View the same direct row in the source-facing geometry integrated
matrix shape. -/
def toGeometryIntegratedFields
    (R : DirectGeometryRow.{u} C hmin) :
    GeometryIntegratedW11.DirectGeometryFields.{u} C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  noStartNoEarly := R.noStartNoEarly

/-- Narrow concrete closure input induced by the integrated direct row. -/
def toNarrowClosureInput
    (R : DirectGeometryRow.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- Checked refined closure input induced by the integrated direct row. -/
def toCheckedClosureInput
    (R : DirectGeometryRow.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toGeometryClosureRow.toCheckedClosureInput

/-- A fixed integrated direct row closes the corresponding minimal failure. -/
theorem contradiction
    (R : DirectGeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

end DirectGeometryRow

/-- K23 boundary-angle geometry row with explicit labels, window containment,
and K23 obstruction data. -/
structure K23GeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundaryPrefix : BoundaryAngleLabelPrefix.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      boundaryPrefix.toGeometrySourceFields
  k23NoEarly :
    GeometryRemainingFieldsW10.K23NoEarlyFields
      boundaryPrefix.toGeometrySourceFields

namespace K23GeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The explicit K23 obstruction payload carried by this row. -/
def k23Obstruction
    (R : K23GeometryRow.{u} C hmin) :=
  R.k23NoEarly.k23Obstruction

/-- Concrete no-early data derived from the explicit K23 obstruction. -/
def noEarly
    (R : K23GeometryRow.{u} C hmin) :=
  R.k23NoEarly.noEarly

/-- Forget the integrated K23 row to the W10 K23 geometry package. -/
def toK23GeometryPackage
    (R : K23GeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  k23NoEarly := R.k23NoEarly

/-- Route the integrated K23 row into the W11 geometry closure facade. -/
def toGeometryClosureRow
    (R : K23GeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofK23GeometryPackage
    R.toK23GeometryPackage

/-- View the same data as the W11 K23 obstruction row. -/
def toK23ObstructionW10Fields
    (R : K23GeometryRow.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  k23Obstruction := R.k23NoEarly.k23Obstruction

/-- View the same K23 row in the source-facing geometry integrated matrix
shape. -/
def toGeometryIntegratedFields
    (R : K23GeometryRow.{u} C hmin) :
    GeometryIntegratedW11.K23GeometryFields.{u} C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  k23NoEarly := R.k23NoEarly

/-- Narrow concrete closure input induced by the integrated K23 row. -/
def toNarrowClosureInput
    (R : K23GeometryRow.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- Checked refined closure input induced by the integrated K23 row. -/
def toCheckedClosureInput
    (R : K23GeometryRow.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toGeometryClosureRow.toCheckedClosureInput

/-- A fixed integrated K23 row closes the corresponding minimal failure. -/
theorem contradiction
    (R : K23GeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

/-- The same K23 row closes through the W11 obstruction facade. -/
theorem contradiction_via_obstruction
    (R : K23GeometryRow.{u} C hmin) :
    False :=
  R.toK23ObstructionW10Fields.contradiction

end K23GeometryRow

/-- Common-neighbor boundary-angle geometry row with explicit labels, window
containment, and common-neighbor obstruction data. -/
structure CommonNeighborGeometryRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundaryPrefix : BoundaryAngleLabelPrefix.{u} C hmin
  window :
    GeometryRemainingFieldsW10.ContainmentFields
      boundaryPrefix.toGeometrySourceFields
  commonNeighborNoEarly :
    GeometryRemainingFieldsW10.CommonNeighborNoEarlyFields
      boundaryPrefix.toGeometrySourceFields

namespace CommonNeighborGeometryRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The explicit common-neighbor obstruction payload carried by this row. -/
def commonNeighborObstruction
    (R : CommonNeighborGeometryRow.{u} C hmin) :=
  R.commonNeighborNoEarly.commonNeighborObstruction

/-- Concrete no-early data derived from the explicit common-neighbor row. -/
def noEarly
    (R : CommonNeighborGeometryRow.{u} C hmin) :=
  R.commonNeighborNoEarly.noEarly

/-- Forget the integrated common-neighbor row to the W10 geometry package. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u}
      C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Route the integrated common-neighbor row into the W11 geometry closure
facade. -/
def toGeometryClosureRow
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u} C hmin :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.ofCommonNeighborGeometryPackage
    R.toCommonNeighborGeometryPackage

/-- View the same data as the W11 common-neighbor obstruction row. -/
def toCommonNeighborObstructionW10Fields
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u}
      C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  commonNeighborObstruction :=
    R.commonNeighborNoEarly.commonNeighborObstruction

/-- View the same common-neighbor row in the source-facing geometry
integrated matrix shape. -/
def toGeometryIntegratedFields
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    GeometryIntegratedW11.CommonNeighborGeometryFields.{u} C hmin where
  source := R.boundaryPrefix.toGeometrySourceFields
  containment := R.window
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Narrow concrete closure input induced by the integrated common-neighbor
row. -/
def toNarrowClosureInput
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toGeometryClosureRow.toConcreteObligations

/-- Checked refined closure input induced by the integrated common-neighbor
row. -/
def toCheckedClosureInput
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toGeometryClosureRow.toCheckedClosureInput

/-- A fixed integrated common-neighbor row closes the corresponding minimal
failure. -/
theorem contradiction
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

/-- The same common-neighbor row closes through the W11 obstruction facade. -/
theorem contradiction_via_obstruction
    (R : CommonNeighborGeometryRow.{u} C hmin) :
    False :=
  R.toCommonNeighborObstructionW10Fields.contradiction

end CommonNeighborGeometryRow

/-! ## Uniform row matrices -/

/-- Uniform integrated direct boundary-angle rows. -/
structure DirectGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectGeometryRow.{u} C hmin

namespace DirectGeometryMatrix

/-- Forget integrated direct rows to the W10 direct-geometry matrix. -/
def toW10DirectGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectGeometryPackage

/-- Route integrated direct rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Route integrated direct rows through the source-facing geometry integrated
matrix. -/
def toGeometryIntegratedMatrix
    (M : DirectGeometryMatrix.{u}) :
    GeometryIntegratedW11.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedFields

/-- Route integrated direct rows to the target facade. -/
def toTargetFacadeMatrix
    (M : DirectGeometryMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix where
  excludesMinimalFailures := M.toGeometryClosureMatrix.no_minimalClearedFailure

/-- Integrated direct rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toGeometryClosureMatrix.no_minimalClearedFailure

/-- Integrated direct rows supply the cleared-pipeline facade. -/
theorem pipelineCleared
    (M : DirectGeometryMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

end DirectGeometryMatrix

/-- Uniform integrated K23 boundary-angle rows. -/
structure K23GeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23GeometryRow.{u} C hmin

namespace K23GeometryMatrix

/-- Forget integrated K23 rows to the W10 K23-geometry matrix. -/
def toW10K23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23GeometryPackage

/-- Route integrated K23 rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Route integrated K23 rows through the source-facing geometry integrated
matrix. -/
def toGeometryIntegratedMatrix
    (M : K23GeometryMatrix.{u}) :
    GeometryIntegratedW11.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedFields

/-- Route integrated K23 rows to the target facade. -/
def toTargetFacadeMatrix
    (M : K23GeometryMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix where
  excludesMinimalFailures := M.toGeometryClosureMatrix.no_minimalClearedFailure

/-- Integrated K23 rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toGeometryClosureMatrix.no_minimalClearedFailure

/-- Integrated K23 rows supply the cleared-pipeline facade. -/
theorem pipelineCleared
    (M : K23GeometryMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

end K23GeometryMatrix

/-- Uniform integrated common-neighbor boundary-angle rows. -/
structure CommonNeighborGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborGeometryRow.{u} C hmin

namespace CommonNeighborGeometryMatrix

/-- Forget integrated common-neighbor rows to the W10 geometry matrix. -/
def toW10CommonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toCommonNeighborGeometryPackage

/-- Route integrated common-neighbor rows to the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Route integrated common-neighbor rows through the source-facing geometry
integrated matrix. -/
def toGeometryIntegratedMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedFields

/-- Route integrated common-neighbor rows to the target facade. -/
def toTargetFacadeMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    SwanepoelTargetFacadeW10.Matrix where
  excludesMinimalFailures := M.toGeometryClosureMatrix.no_minimalClearedFailure

/-- Integrated common-neighbor rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  M.toGeometryClosureMatrix.no_minimalClearedFailure

/-- Integrated common-neighbor rows supply the cleared-pipeline facade. -/
theorem pipelineCleared
    (M : CommonNeighborGeometryMatrix.{u}) :
    PipelineCleared :=
  SwanepoelTargetFacadeW10.pipelineCleared_of_no_minimalClearedFailure
    M.no_minimalClearedFailure

end CommonNeighborGeometryMatrix

/-! ## Integrated route ledger -/

/-- A target-facade route exposing only minimal-failure and pipeline
projections from an explicit source matrix. -/
structure FacadeRoute (alpha : Sort v) : Sort (max 1 v) where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared

/-- Checked geometry and facade routes for boundary-angle source matrices. -/
structure Matrix : Type (u + 3) where
  subpolygonIntegrated : SubpolygonIntegratedW11.Matrix.{u}
  geometryIntegrated : GeometryIntegratedW11.Matrix.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}
  directFacade : FacadeRoute (DirectGeometryMatrix.{u})
  k23Facade : FacadeRoute (K23GeometryMatrix.{u})
  commonNeighborFacade :
    FacadeRoute (CommonNeighborGeometryMatrix.{u})

/-- The checked integrated W11 boundary-angle matrix. -/
def matrix : Matrix.{u} where
  subpolygonIntegrated := SubpolygonIntegratedW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  directFacade := {
    noMinimal := DirectGeometryMatrix.no_minimalClearedFailure
    pipeline := DirectGeometryMatrix.pipelineCleared
  }
  k23Facade := {
    noMinimal := K23GeometryMatrix.no_minimalClearedFailure
    pipeline := K23GeometryMatrix.pipelineCleared
  }
  commonNeighborFacade := {
    noMinimal := CommonNeighborGeometryMatrix.no_minimalClearedFailure
    pipeline := CommonNeighborGeometryMatrix.pipelineCleared
  }

/-! ## Public conditional projections -/

theorem no_minimalClearedFailure_of_directGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directFacade.noMinimal M

theorem pipelineCleared_of_directGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.directFacade.pipeline M

theorem no_minimalClearedFailure_of_k23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23Facade.noMinimal M

theorem pipelineCleared_of_k23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.k23Facade.pipeline M

theorem no_minimalClearedFailure_of_commonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborFacade.noMinimal M

theorem pipelineCleared_of_commonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.commonNeighborFacade.pipeline M

end

end BoundaryAngleIntegratedW11
end Swanepoel
end ErdosProblems1066
