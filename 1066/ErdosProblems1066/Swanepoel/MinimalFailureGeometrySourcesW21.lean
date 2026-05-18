import ErdosProblems1066.Swanepoel.MinimalFailureGeometryClosureW11
import ErdosProblems1066.Swanepoel.SwanepoelSourcePackageW20

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W21 minimal-failure geometry source adapters

This file connects the W20 Swanepoel source package to the
`MinimalGraphFacts` eliminator interface, and records the exact extra geometry
source fields needed to route those source rows through the W11
minimal-failure geometry matrix.

The pointwise W20 package already contains the concrete contradiction
ingredients.  The W11 geometry route additionally wants a `GeometrySourceFields`
row, so the final section names the missing boundary-label, containment, and
no-early rows instead of hiding them behind a target endpoint.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureGeometrySourcesW21

open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}
variable {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

abbrev W20SourcePackage : Type (u + 1) :=
  SwanepoelSourcePackageW20.SwanepoelSourcePackage.{u}

abbrev W20PointwiseAssemblyRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) :=
  PointwiseRemainingRowAssemblyW17.PointwiseW16AssemblyInputs.{u} C hmin

abbrev GeometryClosureRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    Type (u + 1) :=
  MinimalFailureGeometryMatrixW11.GeometryClosureRow.{u, 0} C hmin

abbrev GeometryClosureMatrix : Type (u + 1) :=
  MinimalFailureGeometryMatrixW11.GeometryClosureMatrix.{u, 0}

/-! ## MinimalGraphFacts eliminators from concrete contradiction rows -/

def minimalClearedFailureEliminatorOfGeometryClosureMatrix
    (M : GeometryClosureMatrix.{u}) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  exact (M.row C hmin).contradiction

theorem no_minimalClearedFailure_of_geometryClosureMatrix
    (M : GeometryClosureMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    (minimalClearedFailureEliminatorOfGeometryClosureMatrix M)

namespace W20SourcePackage

def pointwiseAssemblyRow
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    W20PointwiseAssemblyRow.{u} C hmin :=
  P.toPointwiseW16AssemblyFamily.row C hmin

theorem pointwiseAssemblyRow_contradiction
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    False :=
  (P.pointwiseAssemblyRow C hmin).contradiction

def toMinimalClearedFailureEliminator
    (P : W20SourcePackage.{u}) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  exact P.pointwiseAssemblyRow_contradiction C hmin

theorem no_minimalClearedFailure_via_MinimalGraphFacts
    (P : W20SourcePackage.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    P.toMinimalClearedFailureEliminator

end W20SourcePackage

/-! ## W20 topology source rows as W10/W11 geometry topology rows -/

def topologyEnclosureFieldsOfTopologyArcSource
    (T :
      TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u}
        C hmin) :
    GeometryRemainingFieldsW10.TopologyEnclosureFields.{0} C where
  outerFaceData := T.topology.outerFaceData
  enclosureData := T.topology.enclosureData

theorem topologyEnclosureFieldsOfTopologyArcSource_toTopologyFacts
    (T :
      TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u}
        C hmin) :
    (topologyEnclosureFieldsOfTopologyArcSource T).toTopologyFacts =
      T.topology := by
  cases T with
  | mk topology outerAngleBounds Subpolygon subpolygonData longArc triangleRun =>
    cases topology
    rfl

def topologyAngleLongArcFieldsOfTopologyArcSource
    (T :
      TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u}
        C hmin) :
    GeometryRemainingFieldsW10.TopologyAngleLongArcFields.{u, 0} C where
  topology := topologyEnclosureFieldsOfTopologyArcSource T
  outerAngleBounds := T.outerAngleBounds
  Subpolygon := T.Subpolygon
  subpolygonData := T.subpolygonData
  longArc := by
    rw [topologyEnclosureFieldsOfTopologyArcSource_toTopologyFacts]
    exact T.longArc

def topologyAngleLongArcFieldsOfPackage
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    GeometryRemainingFieldsW10.TopologyAngleLongArcFields.{u, 0} C :=
  topologyAngleLongArcFieldsOfTopologyArcSource
    (P.topologyArc.row C hmin)

/-! ## Exact geometry assumptions still needed above W20 source rows -/

def geometrySourceFieldsOfPackage
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C)
    (labels :
      GeometryRemainingFieldsW10.BoundaryLabelFields.{u, 0}
        C hmin (topologyAngleLongArcFieldsOfPackage P C hmin)) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u, 0} C hmin where
  geometry := topologyAngleLongArcFieldsOfPackage P C hmin
  boundaryLabels := labels

/--
The exact extra W11 geometry-source assumptions over a W20 source package.

The W20 package supplies pointwise contradiction rows.  To route the same
source package through `MinimalFailureGeometryMatrixW11`, one still needs:

* boundary-label fields for the topology/angle/long-arc row selected by W20;
* window containment for the resulting `GeometrySourceFields`;
* one concrete no-early route over the same local labels.
-/
structure GeometryClosureSourcesForPackage
    (P : W20SourcePackage.{u}) : Type (u + 1) where
  boundaryLabels :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryRemainingFieldsW10.BoundaryLabelFields.{u, 0}
          C hmin (topologyAngleLongArcFieldsOfPackage P C hmin)
  containment :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryRemainingFieldsW10.ContainmentFields
          (geometrySourceFieldsOfPackage P C hmin
            (boundaryLabels C hmin))
  noEarly :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureGeometryMatrixW11.NoEarlyRoute
          (geometrySourceFieldsOfPackage P C hmin
            (boundaryLabels C hmin))

namespace GeometryClosureSourcesForPackage

variable {P : W20SourcePackage.{u}}

def geometrySource
    (H : GeometryClosureSourcesForPackage.{u} P)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    GeometryRemainingFieldsW10.GeometrySourceFields.{u, 0} C hmin :=
  geometrySourceFieldsOfPackage P C hmin (H.boundaryLabels C hmin)

def row
    (H : GeometryClosureSourcesForPackage.{u} P)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    GeometryClosureRow.{u} C hmin where
  source := H.geometrySource C hmin
  window := H.containment C hmin
  noEarly := H.noEarly C hmin

def toGeometryClosureMatrix
    (H : GeometryClosureSourcesForPackage.{u} P) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin => H.row C hmin

theorem row_contradiction
    (H : GeometryClosureSourcesForPackage.{u} P)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    False :=
  (H.row C hmin).contradiction

def toMinimalClearedFailureEliminator
    (H : GeometryClosureSourcesForPackage.{u} P) :
    MinimalClearedFailureEliminator := by
  intro n C hmin
  exact H.row_contradiction C hmin

theorem no_minimalClearedFailure
    (H : GeometryClosureSourcesForPackage.{u} P) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    H.toMinimalClearedFailureEliminator

theorem no_minimalClearedFailure_via_geometryMatrix
    (H : GeometryClosureSourcesForPackage.{u} P) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_geometryClosureMatrix
    H.toGeometryClosureMatrix

end GeometryClosureSourcesForPackage

end

end MinimalFailureGeometrySourcesW21
end Swanepoel
end ErdosProblems1066
