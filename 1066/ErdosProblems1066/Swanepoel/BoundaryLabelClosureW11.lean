import ErdosProblems1066.Swanepoel.BoundaryLabelRowsW11
import ErdosProblems1066.Swanepoel.WindowNoEarlyRowsW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryMatrixW11
import ErdosProblems1066.Swanepoel.BoundaryLabelInstantiationW10

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 boundary-label closure rows

This module is the closure layer above the explicit W11 boundary-label rows.
It keeps the remaining inputs visible: topology and angle data live in the
label prefix, while window containment and the selected no-early route are row
fields.  The checked projections then feed the W11 no-early and geometry
matrices, plus the target-facing row families.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryLabelClosureW11

open BoundaryLabelRowsW11
open BoundaryLabelRowsW11.BoundaryLabelRowPackage
open BoundaryLabelInstantiationW10
open GeometryRemainingFieldsW10
open MinimalFailureDirectMatrixW10
open MinimalFailureGeometryMatrixW11
open MinimalGraphFacts
open M8LabelsFromBoundaryInterface
open WindowNoEarlyRowsW11

universe u v

noncomputable section

variable {n : Nat}

/-- W11 boundary-label prefixes: topology, angle, and explicit labels. -/
abbrev LabelBasePrefix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BoundaryLabelRowsW11.BoundaryLabelRowPackage.BasePrefix C hmin

namespace LabelBasePrefix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Split the topology component in the form expected by the W10 geometry
source facade. -/
def toTopologyEnclosureFields
    (B : LabelBasePrefix C hmin) :
    TopologyEnclosureFields C where
  outerFaceData := B.topology.topology.outerFaceData
  enclosureData := B.topology.topology.enclosureData

/-- Repackage the prefix topology and angle rows as W10 geometry source
fields. -/
def toTopologyAngleLongArcFields
    (B : LabelBasePrefix C hmin) :
    TopologyAngleLongArcFields.{u} C where
  topology := B.toTopologyEnclosureFields
  outerAngleBounds := B.partitionAngle.outerAngleBounds
  Subpolygon := B.partitionAngle.Subpolygon
  subpolygonData := B.partitionAngle.subpolygonData
  longArc := by
    simpa [toTopologyEnclosureFields] using B.partitionAngle.longArc

/-- Boundary-label fields in the W10 geometry-source spelling. -/
def toBoundaryLabelFields
    (B : LabelBasePrefix C hmin) :
    BoundaryLabelFields.{u} C hmin B.toTopologyAngleLongArcFields where
  remainingNoCutSlack := B.labels.explicit.remainingNoCutSlack
  spineCertificate := by
    simpa [toTopologyAngleLongArcFields, toTopologyEnclosureFields] using
      B.labels.explicit.spineCertificate
  lemma8Existence := by
    simpa [toTopologyAngleLongArcFields, toTopologyEnclosureFields,
      BoundaryLabelRowsW11.ExplicitBoundaryLabelData.spine,
      BoundaryLabelRowsW11.ExplicitBoundaryLabelData.spineCertificate,
      BoundaryLabelRowsW11.ExplicitBoundaryLabelData.connectedNoCut,
      BoundaryLabelRowsW11.connectedNoCutOfSlack,
      BoundaryLabelRowsW11.cutVertexFactsOfSlack] using
      B.labels.lemma8Existence

/-- The full W10 geometry source row determined by a W11 label prefix. -/
def toGeometrySourceFields
    (B : LabelBasePrefix C hmin) :
    GeometrySourceFields.{u} C hmin where
  geometry := B.toTopologyAngleLongArcFields
  boundaryLabels := B.toBoundaryLabelFields

/-- Extra-neighbor data extracted through the W10 boundary-label
instantiation adapter. -/
def toFiniteExtraNeighborData
    (B : LabelBasePrefix C hmin) :
    Lemma8NeighborExtractionConcrete.M8ExtraNeighborData
      B.labels.explicit.spine :=
  FiniteBoundaryLabelCertificateAdapters.extraNeighborData
    B.labels.explicit.toFiniteBoundaryLabelCertificate

@[simp]
theorem toFiniteExtraNeighborData_r
    (B : LabelBasePrefix C hmin) (i : M8ExtraIndex) :
    B.toFiniteExtraNeighborData.r i = B.labels.explicit.lemma8.r i := by
  rfl

@[simp]
theorem toFiniteExtraNeighborData_s
    (B : LabelBasePrefix C hmin) (i : M8ExtraIndex) :
    B.toFiniteExtraNeighborData.s i = B.labels.explicit.lemma8.s i := by
  rfl

end LabelBasePrefix

/-! ## One-row closure from labels to geometry and no-early rows -/

/-- A boundary-label closure row: explicit label prefix, explicit containment,
and one selected no-early route for the same source labels. -/
structure Row
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labelPrefix : LabelBasePrefix C hmin
  containment : ContainmentFields labelPrefix.toGeometrySourceFields
  noEarly : NoEarlyRoute labelPrefix.toGeometrySourceFields

namespace Row

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The W11 geometry row selected by the boundary-label closure row. -/
def toGeometryClosureRow
    (R : Row C hmin) :
    GeometryClosureRow.{u} C hmin where
  source := R.labelPrefix.toGeometrySourceFields
  window := R.containment
  noEarly := R.noEarly

/-- The W11 window row selected by the same data. -/
def toWindowRow
    (R : Row C hmin) :
    WindowNoEarlyRowsW11.WindowRow.{u} C hmin where
  base := R.labelPrefix.toGeometrySourceFields.toW9BaseRow
  windowFields := R.containment.localContainment

/-- The W11 concrete no-early row selected by the same data. -/
def toNoEarlyRow
    (R : Row C hmin) :
    WindowNoEarlyRowsW11.NoEarlyRow.{u} C hmin where
  window := R.toWindowRow
  noEarly := R.noEarly.concreteNoEarly

/-- The W10 direct component row reached through the checked W11 geometry
adapter. -/
def toDirectComponentRow
    (R : Row C hmin) :
    DirectComponentRow.{u} C hmin :=
  R.toGeometryClosureRow.toDirectComponentRow

/-- The target-facing no-early row reached through the W11 no-early adapter. -/
def toNoEarlyTargetRow
    (R : Row C hmin) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRow C hmin :=
  R.toNoEarlyRow.toNoEarlyTargetRow

/-- The W10 no-early obstruction row reached through the W11 no-early
adapter. -/
def toNoEarlyObstructionRow
    (R : Row C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRow C hmin :=
  R.toNoEarlyRow.toNoEarlyObstructionRow

/-- The concrete target row selected by the closure row. -/
def toMinimalFailureConcreteRow
    (R : Row C hmin) :
    MinimalFailureToTargetConcrete.MinimalFailureConcreteRow C hmin :=
  R.toNoEarlyRow.toMinimalFailureConcreteRow

/-- A fixed minimal cleared failure closes once the row data are supplied. -/
theorem contradiction
    (R : Row C hmin) :
    False :=
  R.toGeometryClosureRow.contradiction

@[simp]
theorem toGeometryClosureRow_source
    (R : Row C hmin) :
    R.toGeometryClosureRow.source = R.labelPrefix.toGeometrySourceFields :=
  rfl

@[simp]
theorem toWindowRow_base
    (R : Row C hmin) :
    R.toWindowRow.base =
      R.labelPrefix.toGeometrySourceFields.toW9BaseRow :=
  rfl

@[simp]
theorem toNoEarlyRow_noEarly
    (R : Row C hmin) :
    R.toNoEarlyRow.noEarly = R.noEarly.concreteNoEarly :=
  rfl

end Row

/-! ## Uniform matrices -/

/-- Uniform boundary-label closure rows for every minimal cleared failure. -/
structure Matrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        Row C hmin

namespace Matrix

/-- Route boundary-label closure rows to W11 geometry rows. -/
def toGeometryClosureMatrix
    (M : Matrix) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryClosureRow

/-- Route boundary-label closure rows to W11 no-early rows. -/
def toNoEarlyMatrix
    (M : Matrix) :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toNoEarlyRow

/-- Route boundary-label closure rows to W10 direct component rows. -/
def toDirectComponentMatrix
    (M : Matrix) :
    DirectComponentMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectComponentRow

/-- Route boundary-label closure rows to the target-facing no-early family. -/
def toNoEarlyTargetRowFamily
    (M : Matrix) :
    NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily where
  row := fun C hmin => (M.row C hmin).toNoEarlyTargetRow

/-- Route boundary-label closure rows to the W10 no-early obstruction family.
-/
def toNoEarlyObstructionRowFamily
    (M : Matrix) :
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily where
  row := fun C hmin => (M.row C hmin).toNoEarlyObstructionRow

/-- Boundary-label closure rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : Matrix) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toGeometryClosureMatrix.no_minimalClearedFailure

/-- Conditional target projection from boundary-label closure rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : Matrix) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toGeometryClosureMatrix.targetLowerBoundEightThirtyOne

end Matrix

/-! ## Target-facing route ledger -/

/-- Projection row spelling reused from the W11 geometry closure matrix. -/
abbrev ProjectionRow (alpha : Type v) : Type v :=
  SwanepoelW10ClosureMatrix.ProjectionRow alpha

/-- Projection row for boundary-label closure matrices. -/
def boundaryLabelClosureMatrixRow :
    ProjectionRow Matrix where
  noMinimal := Matrix.no_minimalClearedFailure
  target := Matrix.targetLowerBoundEightThirtyOne

/-- Projection row for the resulting W11 no-early matrices. -/
def noEarlyMatrixRow :
    ProjectionRow (WindowNoEarlyRowsW11.NoEarlyMatrix.{u}) where
  noMinimal := WindowNoEarlyRowsW11.NoEarlyMatrix.no_minimalClearedFailure
  target := WindowNoEarlyRowsW11.NoEarlyMatrix.targetLowerBoundEightThirtyOne

/-- Projection row for the resulting target-facing no-early families. -/
def noEarlyTargetRowFamilyRow :
    ProjectionRow
      NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily where
  noMinimal := NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily.no_minimalClearedFailure
  target := NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily.targetLowerBoundEightThirtyOne

/-- Projection row for the resulting W10 no-early obstruction families. -/
def noEarlyObstructionRowFamilyRow :
    ProjectionRow
      NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily where
  noMinimal :=
    NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily.no_minimalClearedFailure
  target := fun H =>
    H.toNoEarlyTargetRowFamily.targetLowerBoundEightThirtyOne

/-- Projection row for the W10 direct component matrix reached from the same
closure rows. -/
def directComponentMatrixRow :
    ProjectionRow (DirectComponentMatrix.{u}) where
  noMinimal :=
    MinimalFailureDirectMatrixW10.DirectComponentMatrix.no_minimalClearedFailure
  target :=
    MinimalFailureGeometryMatrixW11.directComponentMatrixRow.target

/-- The checked W11 route matrix for boundary-label closure rows. -/
structure RouteMatrix where
  boundaryLabelClosure : ProjectionRow Matrix
  noEarlyRows : ProjectionRow (WindowNoEarlyRowsW11.NoEarlyMatrix.{u})
  geometryRows : ProjectionRow (GeometryClosureMatrix.{u})
  noEarlyTargets :
    ProjectionRow
      NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily
  noEarlyObstructions :
    ProjectionRow
      NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily
  directComponents : ProjectionRow (DirectComponentMatrix.{u})

/-- All checked target-facing routes exposed by this closure layer. -/
def routeMatrix : RouteMatrix where
  boundaryLabelClosure := boundaryLabelClosureMatrixRow
  noEarlyRows := noEarlyMatrixRow
  geometryRows := MinimalFailureGeometryMatrixW11.geometryClosureMatrixRow
  noEarlyTargets := noEarlyTargetRowFamilyRow
  noEarlyObstructions := noEarlyObstructionRowFamilyRow
  directComponents := directComponentMatrixRow

/-! ## Public conditional projections -/

/-- Public target projection from boundary-label closure rows. -/
theorem targetLowerBoundEightThirtyOne_of_boundaryLabelClosureMatrix
    (M : Matrix) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Public target projection from the no-early matrix produced by this layer.
-/
theorem targetLowerBoundEightThirtyOne_of_noEarlyMatrix
    (M : WindowNoEarlyRowsW11.NoEarlyMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Public target projection from the no-early target-row family produced by
this layer. -/
theorem targetLowerBoundEightThirtyOne_of_noEarlyTargetRowFamily
    (M : NoStartInstantiation.MinimalFailureNoEarlyTargetRowFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Public target projection from the W10 no-early obstruction family produced
by this layer. -/
theorem targetLowerBoundEightThirtyOne_of_noEarlyObstructionRowFamily
    (M : NoEarlyK23AssemblyW10.MinimalFailureNoEarlyObstructionRowFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  noEarlyObstructionRowFamilyRow.target M

end

end BoundaryLabelClosureW11
end Swanepoel
end ErdosProblems1066
