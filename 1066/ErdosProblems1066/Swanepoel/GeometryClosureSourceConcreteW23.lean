import ErdosProblems1066.Swanepoel.GeometryClosureSourcesInhabitationW22
import ErdosProblems1066.Swanepoel.M8BlockersInhabitationW22

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W23 concrete geometry-closure source route

This file keeps the W22 geometry-closure construction visible and routes that
same source package through the minimal-failure eliminator interface.  The lane
route first assembles the exact W20 source package and then reuses the same
constructor.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryClosureSourceConcreteW23

open MinimalGraphFacts
open MinimalFailureGeometrySourcesW21

universe u

noncomputable section

abbrev W20SourcePackage : Type (u + 1) :=
  GeometryClosureSourcesInhabitationW22.W20SourcePackage.{u}

abbrev GeometryClosureSourcesForPackage
    (P : W20SourcePackage.{u}) : Type (u + 1) :=
  GeometryClosureSourcesInhabitationW22.GeometryClosureSourcesForPackage.{u} P

abbrev GeometryClosureRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type (u + 1) :=
  MinimalFailureGeometrySourcesW21.GeometryClosureRow.{u} C hmin

abbrev GeometryClosureMatrix : Type (u + 1) :=
  MinimalFailureGeometrySourcesW21.GeometryClosureMatrix.{u}

abbrev LaneProduct : Type (u + 1) :=
  M8BlockersInhabitationW22.ComponentLanes.{u}

/-- The exact W22 geometry-source constructor, named as the W23 concrete source. -/
def exactSourcesOfW20Package
    (P : W20SourcePackage.{u}) :
    GeometryClosureSourcesForPackage.{u} P :=
  GeometryClosureSourcesInhabitationW22.geometryClosureSourcesOfW20Package P

@[simp]
theorem exactSourcesOfW20Package_ctor
    (P : W20SourcePackage.{u}) :
    exactSourcesOfW20Package P =
      ({ boundaryLabels := fun C hmin =>
            GeometryClosureSourcesInhabitationW22.boundaryLabelFieldsOfW20Package
              (C := C) (hmin := hmin) P
         containment := fun C hmin =>
            GeometryClosureSourcesInhabitationW22.containmentFieldsOfW20Package
              (C := C) (hmin := hmin) P
         noEarly := fun C hmin =>
            GeometryClosureSourcesInhabitationW22.noEarlyRouteOfW20Package
              (C := C) (hmin := hmin) P } :
        GeometryClosureSourcesForPackage.{u} P) :=
  rfl

@[simp]
theorem exactSourcesOfW20Package_boundaryLabels
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (exactSourcesOfW20Package P).boundaryLabels C hmin =
      GeometryClosureSourcesInhabitationW22.boundaryLabelFieldsOfW20Package
        (C := C) (hmin := hmin) P :=
  rfl

@[simp]
theorem exactSourcesOfW20Package_containment
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (exactSourcesOfW20Package P).containment C hmin =
      GeometryClosureSourcesInhabitationW22.containmentFieldsOfW20Package
        (C := C) (hmin := hmin) P :=
  rfl

@[simp]
theorem exactSourcesOfW20Package_noEarly
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (exactSourcesOfW20Package P).noEarly C hmin =
      GeometryClosureSourcesInhabitationW22.noEarlyRouteOfW20Package
        (C := C) (hmin := hmin) P :=
  rfl

theorem geometryClosureSources_nonempty_of_w20Package
    (P : W20SourcePackage.{u}) :
    Nonempty (GeometryClosureSourcesForPackage.{u} P) :=
  Nonempty.intro (exactSourcesOfW20Package P)

/-- The exact W11 row obtained from the W20 source-package constructor. -/
def exactRowOfW20Package
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    GeometryClosureRow.{u} C hmin :=
  (exactSourcesOfW20Package P).row C hmin

@[simp]
theorem exactRowOfW20Package_eq_w22
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    exactRowOfW20Package P C hmin =
      GeometryClosureSourcesInhabitationW22.geometryClosureRowOfW20Package
        (C := C) (hmin := hmin) P :=
  rfl

/-- Uniform W11 geometry rows produced by the exact W20 constructor. -/
def exactMatrixOfW20Package
    (P : W20SourcePackage.{u}) :
    GeometryClosureMatrix.{u} :=
  (exactSourcesOfW20Package P).toGeometryClosureMatrix

@[simp]
theorem exactMatrixOfW20Package_row
    (P : W20SourcePackage.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (exactMatrixOfW20Package P).row C hmin =
      exactRowOfW20Package P C hmin :=
  rfl

/-- Minimal-failure eliminator obtained by feeding the exact constructor to W21. -/
def minimalClearedFailureEliminatorOfW20Package
    (P : W20SourcePackage.{u}) :
    MinimalClearedFailureEliminator :=
  (exactSourcesOfW20Package P).toMinimalClearedFailureEliminator

theorem no_minimalClearedFailure_of_w20Package
    (P : W20SourcePackage.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    (minimalClearedFailureEliminatorOfW20Package P)

theorem no_minimalClearedFailure_of_w20Package_via_matrix
    (P : W20SourcePackage.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalFailureGeometrySourcesW21.no_minimalClearedFailure_of_geometryClosureMatrix
    (exactMatrixOfW20Package P)

/-- Convert the W22 M8 component lanes to the exact W20 source package. -/
def w20SourcePackageOfLaneProduct
    (P : LaneProduct.{u}) :
    W20SourcePackage.{u} :=
  P.toW20SourcePackage

/-- The exact geometry-source constructor obtained from a lane product. -/
def exactSourcesOfLaneProduct
    (P : LaneProduct.{u}) :
    GeometryClosureSourcesForPackage.{u}
      (w20SourcePackageOfLaneProduct P) :=
  exactSourcesOfW20Package (w20SourcePackageOfLaneProduct P)

@[simp]
theorem exactSourcesOfLaneProduct_eq_w20
    (P : LaneProduct.{u}) :
    exactSourcesOfLaneProduct P =
      exactSourcesOfW20Package (w20SourcePackageOfLaneProduct P) :=
  rfl

theorem geometryClosureSources_nonempty_of_laneProduct
    (P : LaneProduct.{u}) :
    Nonempty
      (GeometryClosureSourcesForPackage.{u}
        (w20SourcePackageOfLaneProduct P)) :=
  Nonempty.intro (exactSourcesOfLaneProduct P)

/-- Uniform W11 geometry rows produced by the lane product. -/
def exactMatrixOfLaneProduct
    (P : LaneProduct.{u}) :
    GeometryClosureMatrix.{u} :=
  exactMatrixOfW20Package (w20SourcePackageOfLaneProduct P)

@[simp]
theorem exactMatrixOfLaneProduct_row
    (P : LaneProduct.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    (exactMatrixOfLaneProduct P).row C hmin =
      exactRowOfW20Package (w20SourcePackageOfLaneProduct P) C hmin :=
  rfl

/-- Minimal-failure eliminator obtained from the lane product through W20. -/
def minimalClearedFailureEliminatorOfLaneProduct
    (P : LaneProduct.{u}) :
    MinimalClearedFailureEliminator :=
  minimalClearedFailureEliminatorOfW20Package
    (w20SourcePackageOfLaneProduct P)

theorem no_minimalClearedFailure_of_laneProduct
    (P : LaneProduct.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphFacts.no_minimalClearedFailure
    (minimalClearedFailureEliminatorOfLaneProduct P)

theorem no_minimalClearedFailure_of_laneProduct_via_matrix
    (P : LaneProduct.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  no_minimalClearedFailure_of_w20Package_via_matrix
    (w20SourcePackageOfLaneProduct P)

end

end GeometryClosureSourceConcreteW23
end Swanepoel
end ErdosProblems1066
