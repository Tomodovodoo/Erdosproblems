import ErdosProblems1066.Swanepoel.MinimalFailureGeometrySourcesW21
import ErdosProblems1066.Swanepoel.BoundaryLabelClosureW11
import ErdosProblems1066.Swanepoel.WindowContainmentW10
import ErdosProblems1066.Swanepoel.Figure8ContainmentW12
import ErdosProblems1066.Swanepoel.Figure9ContainmentW12
import ErdosProblems1066.Swanepoel.NoEarlyTripleFromLemma9
import ErdosProblems1066.Swanepoel.M8BrokenLatticeSourcesW21

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W22 geometry-closure source inhabitation

This file fills the W21 geometry-closure source package directly from a W20
Swanepoel source package.  The construction keeps the boundary labels,
containment, and no-early route visible, and records that they are over the
same local labels and turn bounds as the W20 pointwise row.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryClosureSourcesInhabitationW22

open MinimalGraphFacts
open MinimalFailureGeometrySourcesW21

universe u

noncomputable section

variable {n : Nat}
variable {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

abbrev W20SourcePackage : Type (u + 1) :=
  MinimalFailureGeometrySourcesW21.W20SourcePackage.{u}

abbrev GeometryClosureSourcesForPackage
    (P : W20SourcePackage.{u}) : Type (u + 1) :=
  MinimalFailureGeometrySourcesW21.GeometryClosureSourcesForPackage.{u} P

/-- Boundary-label fields selected by the W20 topology and Lemma 8 rows. -/
def boundaryLabelFieldsOfW20Package
    (P : W20SourcePackage.{u}) :
    GeometryRemainingFieldsW10.BoundaryLabelFields.{u, 0}
      C hmin (topologyAngleLongArcFieldsOfPackage P C hmin) where
  remainingNoCutSlack :=
    MinimalFailureClosureW13.remainingSlackOfNoCut hmin
      (P.payForCutProducer.noCutVertex C hmin)
  spineCertificate :=
    ((P.topologyArc.row C hmin).toActualTopologyArcInputs).spineCertificate
  lemma8Existence :=
    (P.lemma8.row C hmin).lemma8Existence

@[simp]
theorem boundaryLabelFieldsOfW20Package_spineCertificate
    (P : W20SourcePackage.{u}) :
    (boundaryLabelFieldsOfW20Package
      (C := C) (hmin := hmin) P).spineCertificate =
      ((P.topologyArc.row C hmin).toActualTopologyArcInputs).spineCertificate :=
  rfl

@[simp]
theorem boundaryLabelFieldsOfW20Package_lemma8Existence
    (P : W20SourcePackage.{u}) :
    (boundaryLabelFieldsOfW20Package
      (C := C) (hmin := hmin) P).lemma8Existence =
      (P.lemma8.row C hmin).lemma8Existence :=
  rfl

/-- The W10 geometry source row induced by a W20 source package. -/
def geometrySourceFieldsOfW20Package
    (P : W20SourcePackage.{u}) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u, 0} C hmin :=
  geometrySourceFieldsOfPackage P C hmin
    (boundaryLabelFieldsOfW20Package P)

@[simp]
theorem geometrySourceFieldsOfW20Package_geometry
    (P : W20SourcePackage.{u}) :
    (geometrySourceFieldsOfW20Package
      (C := C) (hmin := hmin) P).geometry =
      topologyAngleLongArcFieldsOfPackage P C hmin :=
  rfl

@[simp]
theorem geometrySourceFieldsOfW20Package_localLabels_eq_pointwise
    (P : W20SourcePackage.{u}) :
    (geometrySourceFieldsOfW20Package
      (C := C) (hmin := hmin) P).localLabels =
      (P.pointwiseAssemblyRow C hmin).localLabels :=
  rfl

@[simp]
theorem geometrySourceFieldsOfW20Package_turnBounds_eq_pointwise
    (P : W20SourcePackage.{u}) :
    (geometrySourceFieldsOfW20Package
      (C := C) (hmin := hmin) P).turnBounds =
      (P.pointwiseAssemblyRow C hmin).turnBounds :=
  rfl

/-- W20 Figure 8/Figure 9 angle containment over the geometry-source labels. -/
def localAngleContainmentFieldsOfW20Package
    (P : W20SourcePackage.{u}) :
    WindowContainmentW10.LocalAngleContainmentFields
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P).localLabels
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P).turnBounds where
  angleContainment := P.figures.angleContainment C hmin

/-- Figure 8 containment interface over the matched W20 local labels. -/
def figure8ContainmentOfW20Package
    (P : W20SourcePackage.{u}) :
    AngleContainmentInterface.Figure8SeparatedContainmentInterface
      (Lemma10Bridge.M8BrokenLatticeGood
        (geometrySourceFieldsOfW20Package
          (C := C) (hmin := hmin) P).localLabels.predicates.data)
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P).turnBounds.turn :=
  (localAngleContainmentFieldsOfW20Package
    (C := C) (hmin := hmin) P).figure8ContainmentInterface

/-- Figure 9 adjacent-left containment interface over the matched labels. -/
def figure9LeftContainmentOfW20Package
    (P : W20SourcePackage.{u}) :
    AngleContainmentInterface.Figure9AdjacentLeftContainmentInterface
      (Lemma10Bridge.M8BrokenLatticeGood
        (geometrySourceFieldsOfW20Package
          (C := C) (hmin := hmin) P).localLabels.predicates.data)
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P).turnBounds.turn :=
  (localAngleContainmentFieldsOfW20Package
    (C := C) (hmin := hmin) P).figure9LeftContainmentInterface

/-- Window-containment fields for the W21 geometry source. -/
def containmentFieldsOfW20Package
    (P : W20SourcePackage.{u}) :
    GeometryRemainingFieldsW10.ContainmentFields
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P) where
  localContainment :=
    (localAngleContainmentFieldsOfW20Package
      (C := C) (hmin := hmin) P).windowFields

@[simp]
theorem containmentFieldsOfW20Package_localContainment_eq_pointwise
    (P : W20SourcePackage.{u}) :
    (containmentFieldsOfW20Package
      (C := C) (hmin := hmin) P).localContainment =
      (P.pointwiseAssemblyRow C hmin).localWindowContainment :=
  rfl

/-- The W20 Figure rows give the E22/E23 lower-bound pair for this source. -/
theorem containmentFieldsOfW20Package_E22_E23
    (P : W20SourcePackage.{u}) :
    Lemma10AnalyticBridge.HonestFigure8SeparatedWindowLowerE22
        (geometrySourceFieldsOfW20Package
          (C := C) (hmin := hmin) P).localLabels.predicates
        (geometrySourceFieldsOfW20Package
          (C := C) (hmin := hmin) P).turnBounds.turn /\
      Lemma10AnalyticBridge.HonestFigure9AdjacentWindowLowerE23
        (geometrySourceFieldsOfW20Package
          (C := C) (hmin := hmin) P).localLabels.predicates
        (geometrySourceFieldsOfW20Package
          (C := C) (hmin := hmin) P).turnBounds.turn :=
  (containmentFieldsOfW20Package (C := C) (hmin := hmin) P).E22_E23

/-- Concrete no-early data obtained from the W20 Lemma 9 row. -/
def concreteNoEarlyOfW20Package
    (P : W20SourcePackage.{u}) :
    NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P).localLabels.predicates.data :=
  (P.pointwiseAssemblyRow C hmin).lemma9FiveStartLateFacts
    |>.toConcreteNoEarlyTripleEquality

/-- Direct no-start/no-early fields over the matched geometry-source labels. -/
def noStartNoEarlyFieldsOfW20Package
    (P : W20SourcePackage.{u}) :
    GeometryRemainingFieldsW10.NoStartNoEarlyFields
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P) where
  noStart :=
    NoStartInstantiation.constructionExplicitNoStartFields_of_concreteNoEarly
      (localLabels :=
        (geometrySourceFieldsOfW20Package
          (C := C) (hmin := hmin) P).localLabels)
      (concreteNoEarlyOfW20Package (C := C) (hmin := hmin) P)

/-- The W11 no-early route selected for the W21 geometry closure package. -/
def noEarlyRouteOfW20Package
    (P : W20SourcePackage.{u}) :
    MinimalFailureGeometryMatrixW11.NoEarlyRoute
      (geometrySourceFieldsOfW20Package
        (C := C) (hmin := hmin) P) :=
  MinimalFailureGeometryMatrixW11.NoEarlyRoute.direct
    (noStartNoEarlyFieldsOfW20Package
      (C := C) (hmin := hmin) P)

@[simp]
theorem noEarlyRouteOfW20Package_concreteNoEarly
    (P : W20SourcePackage.{u}) :
    (noEarlyRouteOfW20Package
      (C := C) (hmin := hmin) P).concreteNoEarly =
      concreteNoEarlyOfW20Package (C := C) (hmin := hmin) P :=
  rfl

/-- A W20 source package supplies all W21 geometry-closure source fields. -/
def geometryClosureSourcesOfW20Package
    (P : W20SourcePackage.{u}) :
    GeometryClosureSourcesForPackage.{u} P where
  boundaryLabels := fun C hmin =>
    boundaryLabelFieldsOfW20Package (C := C) (hmin := hmin) P
  containment := fun C hmin =>
    containmentFieldsOfW20Package (C := C) (hmin := hmin) P
  noEarly := fun C hmin =>
    noEarlyRouteOfW20Package (C := C) (hmin := hmin) P

theorem geometryClosureSourcesForPackage_nonempty
    (P : W20SourcePackage.{u}) :
    Nonempty (GeometryClosureSourcesForPackage.{u} P) :=
  Nonempty.intro (geometryClosureSourcesOfW20Package P)

/-- The corresponding W11 geometry-closure row for one minimal failure. -/
def geometryClosureRowOfW20Package
    (P : W20SourcePackage.{u}) :
    MinimalFailureGeometrySourcesW21.GeometryClosureRow.{u} C hmin :=
  (geometryClosureSourcesOfW20Package P).row C hmin

@[simp]
theorem geometryClosureRowOfW20Package_source
    (P : W20SourcePackage.{u}) :
    (geometryClosureRowOfW20Package
      (C := C) (hmin := hmin) P).source =
      geometrySourceFieldsOfW20Package (C := C) (hmin := hmin) P :=
  rfl

@[simp]
theorem geometryClosureRowOfW20Package_window
    (P : W20SourcePackage.{u}) :
    (geometryClosureRowOfW20Package
      (C := C) (hmin := hmin) P).window =
      containmentFieldsOfW20Package (C := C) (hmin := hmin) P :=
  rfl

@[simp]
theorem geometryClosureRowOfW20Package_noEarly
    (P : W20SourcePackage.{u}) :
    (geometryClosureRowOfW20Package
      (C := C) (hmin := hmin) P).noEarly =
      noEarlyRouteOfW20Package (C := C) (hmin := hmin) P :=
  rfl

/-- Uniform W11 geometry-closure matrix induced by a W20 source package. -/
def geometryClosureMatrixOfW20Package
    (P : W20SourcePackage.{u}) :
    MinimalFailureGeometrySourcesW21.GeometryClosureMatrix.{u} :=
  (geometryClosureSourcesOfW20Package P).toGeometryClosureMatrix

end

end GeometryClosureSourcesInhabitationW22
end Swanepoel
end ErdosProblems1066
