import ErdosProblems1066.Swanepoel.K23CommonNeighborW11
import ErdosProblems1066.Swanepoel.NoEarlyK23AssemblyW10
import ErdosProblems1066.Swanepoel.GeometryRemainingFieldsW10
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W11 K23/common-neighbor closure facade

This file is a narrow closure layer over the W11 K23/common-neighbor row
families.  The row families keep the missing topology, containment, and
obstruction data explicit in `K23CommonNeighborW11`; this module only records
the checked routes from those rows to:

* the K23/no-early closure eliminators;
* the W10 no-early/K23 assembly row families;
* the W10 geometry closure matrices; and
* the conditional Swanepoel target where the existing W10 matrix provides it.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23ClosureW11

open MinimalGraphFacts

universe u v

noncomputable section

abbrev Target : Prop :=
  _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

abbrev MinimalFailureExclusion : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    Not (IsMinimalClearedFailure C)

abbrev K23ClosureFields {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin

abbrev CommonNeighborClosureFields {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u} C hmin

abbrev K23RowFamily :=
  K23CommonNeighborW11.K23ObstructionW10RowFamily.{u}

abbrev CommonNeighborRowFamily :=
  K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.{u}

/-! ## Pointwise routes -/

namespace K23ClosureFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Pointwise K23 fields as a W10 K23 geometry package. -/
def toK23GeometryPackage
    (R : K23ClosureFields.{u} C hmin) :
    GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin :=
  K23CommonNeighborW11.K23ObstructionW10Fields.toK23GeometryPackage R

/-- Pointwise K23 fields as a W10 assembly row. -/
def toAssemblyK23ObstructionRow
    (R : K23ClosureFields.{u} C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureK23ObstructionRow C hmin :=
  K23CommonNeighborW11.K23ObstructionW10Fields.toAssemblyK23ObstructionRow R

/-- Pointwise K23 fields as the checked K23/no-early closure fields. -/
def toK23NoEarlyClosureFields
    (R : K23ClosureFields.{u} C hmin) :
    K23NoEarlyClosure.MinimalFailureK23TurnWindowFields C hmin :=
  K23CommonNeighborW11.K23ObstructionW10Fields.toK23NoEarlyClosureFields R

/-- Pointwise K23 fields close the selected minimal failure. -/
theorem contradiction
    (R : K23ClosureFields.{u} C hmin) :
    False :=
  K23CommonNeighborW11.K23ObstructionW10Fields.contradiction R

end K23ClosureFields

namespace CommonNeighborClosureFields

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- Pointwise common-neighbor fields as a W10 common-neighbor geometry
package. -/
def toCommonNeighborGeometryPackage
    (R : CommonNeighborClosureFields.{u} C hmin) :
    GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin :=
  K23CommonNeighborW11.CommonNeighborObstructionW10Fields.toCommonNeighborGeometryPackage
    R

/-- Pointwise common-neighbor fields as a W10 assembly row. -/
def toAssemblyCommonNeighborObstructionRow
    (R : CommonNeighborClosureFields.{u} C hmin) :
    NoEarlyK23AssemblyW10.MinimalFailureCommonNeighborObstructionRow
      C hmin :=
  K23CommonNeighborW11.CommonNeighborObstructionW10Fields.toAssemblyCommonNeighborObstructionRow
    R

/-- Pointwise common-neighbor fields as checked common-neighbor/no-early
closure fields. -/
def toCommonNeighborNoEarlyClosureFields
    (R : CommonNeighborClosureFields.{u} C hmin) :
    K23NoEarlyClosure.MinimalFailureCommonNeighborTurnWindowFields C hmin :=
  K23CommonNeighborW11.CommonNeighborObstructionW10Fields.toCommonNeighborNoEarlyClosureFields
    R

/-- Common-neighbor fields forget to the pointwise K23 closure row. -/
def toK23ClosureFields
    (R : CommonNeighborClosureFields.{u} C hmin) :
    K23ClosureFields.{u} C hmin :=
  K23CommonNeighborW11.CommonNeighborObstructionW10Fields.toK23ObstructionW10Fields
    R

/-- Pointwise common-neighbor fields close the selected minimal failure. -/
theorem contradiction
    (R : CommonNeighborClosureFields.{u} C hmin) :
    False :=
  K23CommonNeighborW11.CommonNeighborObstructionW10Fields.contradiction R

end CommonNeighborClosureFields

/-! ## Uniform row-family routes -/

namespace K23RowFamily

/-- W11 K23 row families as W10 K23 geometry matrices. -/
def toK23GeometryMatrix
    (H : K23RowFamily.{u}) :
    SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u} where
  row := fun C hmin => (H.row C hmin).toK23GeometryPackage

/-- W11 K23 row families as W10 no-early/K23 assembly families. -/
def toAssemblyK23ObstructionRowFamily
    (H : K23RowFamily.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureK23ObstructionRowFamily :=
  K23CommonNeighborW11.K23ObstructionW10RowFamily.toAssemblyK23ObstructionRowFamily
    H

/-- W11 K23 row families as checked K23/no-early closure eliminators. -/
def toK23NoEarlyClosureEliminator
    (H : K23RowFamily.{u}) :
    K23NoEarlyClosure.MinimalFailureM8K23NoEarlyClosureEliminator :=
  K23CommonNeighborW11.K23ObstructionW10RowFamily.toK23NoEarlyClosureEliminator
    H

/-- W11 K23 row families give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : K23RowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  K23CommonNeighborW11.K23ObstructionW10RowFamily.minimalClearedFailureEliminator
    H

/-- W11 K23 row families rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : K23RowFamily.{u}) :
    MinimalFailureExclusion :=
  K23CommonNeighborW11.K23ObstructionW10RowFamily.no_minimalClearedFailure H

/-- W11 K23 row families reach the conditional Swanepoel target through the
existing W10 K23 geometry matrix route. -/
theorem targetLowerBoundEightThirtyOne
    (H : K23RowFamily.{u}) :
    Target :=
  H.toK23GeometryMatrix.targetLowerBoundEightThirtyOne

end K23RowFamily

namespace CommonNeighborRowFamily

/-- W11 common-neighbor row families as W10 common-neighbor geometry
matrices. -/
def toCommonNeighborGeometryMatrix
    (H : CommonNeighborRowFamily.{u}) :
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (H.row C hmin).toCommonNeighborGeometryPackage

/-- W11 common-neighbor row families forget to W11 K23 row families. -/
def toK23RowFamily
    (H : CommonNeighborRowFamily.{u}) :
    K23RowFamily.{u} :=
  K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.toK23ObstructionW10RowFamily
    H

/-- W11 common-neighbor row families as W10 no-early/K23 assembly families. -/
def toAssemblyCommonNeighborObstructionRowFamily
    (H : CommonNeighborRowFamily.{u}) :
    NoEarlyK23AssemblyW10.MinimalFailureCommonNeighborObstructionRowFamily :=
  open K23CommonNeighborW11 in
  CommonNeighborObstructionW10RowFamily.toAssemblyCommonNeighborObstructionRowFamily H

/-- W11 common-neighbor row families as checked common-neighbor/no-early
closure eliminators. -/
def toCommonNeighborNoEarlyClosureEliminator
    (H : CommonNeighborRowFamily.{u}) :
    K23NoEarlyClosure.MinimalFailureM8CommonNeighborNoEarlyClosureEliminator :=
  open K23CommonNeighborW11 in
  CommonNeighborObstructionW10RowFamily.toCommonNeighborNoEarlyClosureEliminator H

/-- W11 common-neighbor row families also give the K23/no-early closure
eliminator. -/
def toK23NoEarlyClosureEliminator
    (H : CommonNeighborRowFamily.{u}) :
    K23NoEarlyClosure.MinimalFailureM8K23NoEarlyClosureEliminator :=
  K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.toK23NoEarlyClosureEliminator
    H

/-- W11 common-neighbor row families give the minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (H : CommonNeighborRowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.minimalClearedFailureEliminator
    H

/-- W11 common-neighbor row families rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : CommonNeighborRowFamily.{u}) :
    MinimalFailureExclusion :=
  K23CommonNeighborW11.CommonNeighborObstructionW10RowFamily.no_minimalClearedFailure
    H

/-- W11 common-neighbor row families reach the conditional Swanepoel target
through the existing W10 common-neighbor geometry matrix route. -/
theorem targetLowerBoundEightThirtyOne
    (H : CommonNeighborRowFamily.{u}) :
    Target :=
  H.toCommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne

end CommonNeighborRowFamily

/-! ## Closure projection rows -/

/-- A W11 projection row from an explicit input package to the checked
minimal-failure and target conclusions. -/
structure ClosureProjectionRow (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  target : alpha -> Target

/-- K23 W11 row-family projection. -/
def k23RowFamilyProjection :
    ClosureProjectionRow (K23RowFamily.{u}) where
  noMinimal := K23RowFamily.no_minimalClearedFailure
  target := K23RowFamily.targetLowerBoundEightThirtyOne

/-- Common-neighbor W11 row-family projection. -/
def commonNeighborRowFamilyProjection :
    ClosureProjectionRow (CommonNeighborRowFamily.{u}) where
  noMinimal := CommonNeighborRowFamily.no_minimalClearedFailure
  target := CommonNeighborRowFamily.targetLowerBoundEightThirtyOne

/-- W10 K23 geometry projection retained for downstream target-closure
callers. -/
def w10K23GeometryProjection :
    ClosureProjectionRow
      (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}) where
  noMinimal := SwanepoelW10ClosureMatrix.K23GeometryMatrix.no_minimalClearedFailure
  target := SwanepoelW10ClosureMatrix.K23GeometryMatrix.targetLowerBoundEightThirtyOne

/-- W10 common-neighbor geometry projection retained for downstream
target-closure callers. -/
def w10CommonNeighborGeometryProjection :
    ClosureProjectionRow
      (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) where
  noMinimal :=
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.no_minimalClearedFailure
  target :=
    SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne

/-- Consolidated W11 K23/common-neighbor closure matrix. -/
structure Matrix : Type (u + 1) where
  k23Rows : ClosureProjectionRow (K23RowFamily.{u})
  commonNeighborRows : ClosureProjectionRow (CommonNeighborRowFamily.{u})
  w10K23Geometry :
    ClosureProjectionRow
      (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u})
  w10CommonNeighborGeometry :
    ClosureProjectionRow
      (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u})

/-- The checked W11 K23/common-neighbor closure matrix. -/
def matrix : Matrix.{u} where
  k23Rows := k23RowFamilyProjection
  commonNeighborRows := commonNeighborRowFamilyProjection
  w10K23Geometry := w10K23GeometryProjection
  w10CommonNeighborGeometry := w10CommonNeighborGeometryProjection

/-! ## Public theorem forms -/

theorem minimalClearedFailureEliminator_of_k23Rows
    (H : K23RowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

theorem minimalClearedFailureEliminator_of_commonNeighborRows
    (H : CommonNeighborRowFamily.{u}) :
    MinimalClearedFailureEliminator :=
  H.minimalClearedFailureEliminator

theorem targetLowerBoundEightThirtyOne_of_k23Rows
    (H : K23RowFamily.{u}) :
    Target :=
  H.targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_commonNeighborRows
    (H : CommonNeighborRowFamily.{u}) :
    Target :=
  H.targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    (M : SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}) :
    Target :=
  M.targetLowerBoundEightThirtyOne

theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    (M : SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) :
    Target :=
  M.targetLowerBoundEightThirtyOne

end

end K23ClosureW11
end Swanepoel
end ErdosProblems1066
