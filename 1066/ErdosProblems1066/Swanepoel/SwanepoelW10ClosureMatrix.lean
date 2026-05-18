import ErdosProblems1066.Swanepoel.GeometryRemainingFieldsW10
import ErdosProblems1066.Swanepoel.M8SeparatedConstructionConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureDirectMatrixW10
import ErdosProblems1066.Swanepoel.SwanepoelRemainingObligationsW9
import ErdosProblems1066.Swanepoel.SwanepoelW8ClosureMatrix

set_option autoImplicit false

/-!
# Swanepoel W10 closure matrix

This file is the tenth-wave audit layer for the Swanepoel route.  It does not
construct any final lower-bound theorem on its own.  Instead, it records the
checked conditional routes that are available once explicit component data are
supplied.

The preferred W10 routes go through the W9 `DirectMatrix` and `K23Matrix`
interfaces.  Base-compatible component packages are therefore converted to
those matrices whenever their fields are precise enough:

* direct component rows carry the W9 base row, the exact window containment,
  and construction-level no-early triples for the same labels;
* K23 component rows carry the W9 base row, the exact window containment, and
  K23 obstruction inputs for the same labels.

The older W8 matrix is retained as a projection row for comparison and for
downstream audit tooling.  All public target projections below remain
conditional on one of the explicit matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelW10ClosureMatrix

open LateTriplesInterface
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8LateTriplesFromNoEarly
open M8SeparatedConstructionConcrete
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete
open SwanepoelRemainingObligationsW9

universe u v

noncomputable section

variable {n : Nat}

/-! ## Exact W9 field spellings -/

/-- W10 spelling for the W9 topology/angle/subpolygon field. -/
abbrev TopologyAngleSubpolygonField (C : _root_.UDConfig n) :=
  TopologyAngleSubpolygonRow.{u} C

/-- W10 spelling for the W9 boundary-label field, dependent on the exact
topology/angle/subpolygon row. -/
abbrev BoundaryLabelField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (topologyRow : TopologyAngleSubpolygonField.{u} C) :=
  BoundaryLabelRow.{u} C hmin topologyRow

/-- W10 spelling for the W9 base row. -/
abbrev BaseField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  BaseRow.{u} C hmin

/-- W10 spelling for the exact W9 window field. -/
abbrev WindowField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (base : BaseField.{u} C hmin) :=
  WindowRow.{u} C hmin base

/-- W10 spelling for the exact direct five-start no-early field. -/
abbrev DirectNoStartField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (base : BaseField.{u} C hmin) :=
  NoStartRow.{u} C hmin base

/-- W10 spelling for the exact K23/no-early field. -/
abbrev K23NoEarlyField
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C)
    (base : BaseField.{u} C hmin) :=
  K23NoEarlyRow.{u} C hmin base

/-! ## Construction no-early packages as direct five-start rows -/

/-- Construction-level no-early triples contain the five concrete early-start
exclusions required by the direct W9 row. -/
def concreteNoEarlyTripleEquality_of_constructionNoEarlyTriples
    {C : _root_.UDConfig n}
    {localLabels : M8LocalLabels C}
    (H : M8ConstructionNoEarlyTriples localLabels) :
    M8ConcreteNoEarlyTripleEquality localLabels.predicates.data where
  no_start1 := H.noEarlyTripleEquality start1 (by
    unfold M8TripleStartEarly
    rw [start1_val]
    omega)
  no_start2 := H.noEarlyTripleEquality start2 (by
    unfold M8TripleStartEarly
    rw [start2_val]
    omega)
  no_start3 := H.noEarlyTripleEquality start3 (by
    unfold M8TripleStartEarly
    rw [start3_val]
    omega)
  no_start4 := H.noEarlyTripleEquality start4 (by
    unfold M8TripleStartEarly
    rw [start4_val]
    omega)
  no_start5 := H.noEarlyTripleEquality start5 (by
    unfold M8TripleStartEarly
    rw [start5_val])

/-! ## Base-compatible component rows -/

/-- Direct W10 component row for one minimal cleared failure.

The fields are deliberately indexed by the W9 base row, so the route can be
sent to `DirectMatrix` without label or turn casts. -/
structure DirectComponentPackageRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : BaseField.{u} C hmin
  noEarlyTriples : M8ConstructionNoEarlyTriples base.localLabels
  windowContainment : M8WindowContainment base.localLabels base.turnBounds

namespace DirectComponentPackageRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The direct component row as the standard separated component package. -/
def toSeparatedComponentPackage
    (R : DirectComponentPackageRow.{u} C hmin) :
    M8SeparatedConstructionComponentPackage C hmin where
  labels := R.base.labels
  arc := R.base.arc
  noEarlyTriples := R.noEarlyTriples
  windowContainment := by
    simpa [BaseRow.localLabels, BaseRow.turnBounds] using R.windowContainment

/-- Concrete five-start no-early data extracted from the construction-level
component package. -/
def concreteNoEarly
    (R : DirectComponentPackageRow.{u} C hmin) :
    M8ConcreteNoEarlyTripleEquality R.base.localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_constructionNoEarlyTriples
    R.noEarlyTriples

/-- The exact W9 window row carried by the direct component package. -/
def toWindowRow
    (R : DirectComponentPackageRow.{u} C hmin) :
    WindowRow.{u} C hmin R.base where
  containment := R.windowContainment

/-- The exact W9 direct no-start row carried by the direct component package.
-/
def toNoStartRow
    (R : DirectComponentPackageRow.{u} C hmin) :
    NoStartRow.{u} C hmin R.base where
  no_start1 := R.concreteNoEarly.no_start1
  no_start2 := R.concreteNoEarly.no_start2
  no_start3 := R.concreteNoEarly.no_start3
  no_start4 := R.concreteNoEarly.no_start4
  no_start5 := R.concreteNoEarly.no_start5

/-- Route the component package through the W9 direct row. -/
def toDirectRow
    (R : DirectComponentPackageRow.{u} C hmin) :
    MinimalFailureDirectRow.{u} C hmin where
  base := R.base
  window := R.toWindowRow
  noStart := R.toNoStartRow

/-- Route the component package to the concrete minimal-failure row through
the W9 direct row. -/
def toMinimalFailureConcreteRow
    (R : DirectComponentPackageRow.{u} C hmin) :
    MinimalFailureToTargetConcrete.MinimalFailureConcreteRow C hmin :=
  R.toDirectRow.toMinimalFailureConcreteRow

/-- A fixed direct component row closes through the checked W9 direct route.
-/
theorem contradiction
    (R : DirectComponentPackageRow.{u} C hmin) :
    False :=
  R.toDirectRow.contradiction

end DirectComponentPackageRow

/-- K23 W10 component row for one minimal cleared failure.

The fields are deliberately indexed by the W9 base row, so the route can be
sent to `K23Matrix` without label or turn casts. -/
structure K23ComponentPackageRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : BaseField.{u} C hmin
  k23Obstruction :
    M8ConcreteK23ObstructionInputs base.localLabels.predicates.data
  windowContainment : M8WindowContainment base.localLabels base.turnBounds

namespace K23ComponentPackageRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The exact W9 window row carried by the K23 component package. -/
def toWindowRow
    (R : K23ComponentPackageRow.{u} C hmin) :
    WindowRow.{u} C hmin R.base where
  containment := R.windowContainment

/-- The exact W9 K23/no-early row carried by the K23 component package. -/
def toK23NoEarlyRow
    (R : K23ComponentPackageRow.{u} C hmin) :
    K23NoEarlyRow.{u} C hmin R.base where
  k23Obstruction := R.k23Obstruction

/-- Route the component package through the W9 K23 row. -/
def toK23Row
    (R : K23ComponentPackageRow.{u} C hmin) :
    MinimalFailureK23Row.{u} C hmin where
  base := R.base
  window := R.toWindowRow
  k23NoEarly := R.toK23NoEarlyRow

/-- Forget the K23 component package to the direct W9 row. -/
def toDirectRow
    (R : K23ComponentPackageRow.{u} C hmin) :
    MinimalFailureDirectRow.{u} C hmin :=
  R.toK23Row.toDirectRow

/-- Route the K23 component package to the concrete minimal-failure row
through the W9 K23 row. -/
def toMinimalFailureConcreteRow
    (R : K23ComponentPackageRow.{u} C hmin) :
    MinimalFailureToTargetConcrete.MinimalFailureConcreteRow C hmin :=
  R.toK23Row.toMinimalFailureConcreteRow

/-- A fixed K23 component row closes through the checked W9 K23 route. -/
theorem contradiction
    (R : K23ComponentPackageRow.{u} C hmin) :
    False :=
  R.toK23Row.contradiction

end K23ComponentPackageRow

/-! ## Uniform component matrices -/

/-- Uniform base-compatible direct component rows. -/
structure DirectComponentMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectComponentPackageRow.{u} C hmin

namespace DirectComponentMatrix

/-- Route base-compatible direct component rows to the W9 `DirectMatrix`. -/
def toDirectMatrix
    (M : DirectComponentMatrix.{u}) :
    DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toDirectRow

/-- The corresponding separated component package family. -/
def toSeparatedComponents
    (M : DirectComponentMatrix.{u}) :
    M8SeparatedConstructionComponents where
  componentPackage := fun C hmin =>
    (M.row C hmin).toSeparatedComponentPackage

/-- Direct component rows rule out every minimal cleared failure through W9.
-/
theorem no_minimalClearedFailure
    (M : DirectComponentMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toDirectMatrix.no_minimalClearedFailure

/-- Conditional target projection from base-compatible direct component rows.
-/
theorem targetLowerBoundEightThirtyOne
    (M : DirectComponentMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toDirectMatrix.targetLowerBoundEightThirtyOne

end DirectComponentMatrix

/-- Uniform base-compatible K23 component rows. -/
structure K23ComponentMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23ComponentPackageRow.{u} C hmin

namespace K23ComponentMatrix

/-- Route base-compatible K23 component rows to the W9 `K23Matrix`. -/
def toK23Matrix
    (M : K23ComponentMatrix.{u}) :
    K23Matrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23Row

/-- Forget base-compatible K23 component rows to W9 direct rows. -/
def toDirectMatrix
    (M : K23ComponentMatrix.{u}) :
    DirectMatrix.{u} :=
  M.toK23Matrix.toDirectMatrix

/-- K23 component rows rule out every minimal cleared failure through W9. -/
theorem no_minimalClearedFailure
    (M : K23ComponentMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toK23Matrix.no_minimalClearedFailure

/-- Conditional target projection from base-compatible K23 component rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23ComponentMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toK23Matrix.targetLowerBoundEightThirtyOne

end K23ComponentMatrix

/-! ## W10 output matrices -/

/-- Uniform rows from `MinimalFailureDirectMatrixW10`, routed through its
checked W9 direct-matrix adapter. -/
abbrev MinimalFailureDirectW10Matrix :=
  MinimalFailureDirectMatrixW10.DirectComponentMatrix

namespace MinimalFailureDirectW10Matrix

/-- Route the existing W10 direct matrix to the W9 `DirectMatrix`. -/
def toDirectMatrix
    (M : MinimalFailureDirectW10Matrix.{u}) :
    DirectMatrix.{u} :=
  M.toW9DirectMatrix

/-- Existing W10 direct rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : MinimalFailureDirectW10Matrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toDirectMatrix.no_minimalClearedFailure

/-- Conditional target projection from the existing W10 direct matrix. -/
theorem targetLowerBoundEightThirtyOne
    (M : MinimalFailureDirectW10Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toDirectMatrix.targetLowerBoundEightThirtyOne

end MinimalFailureDirectW10Matrix

/-- Uniform direct geometry rows from `GeometryRemainingFieldsW10`. -/
structure DirectGeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryRemainingFieldsW10.DirectGeometryPackage.{u} C hmin

namespace DirectGeometryMatrix

/-- Route direct geometry packages to the W9 `DirectMatrix`. -/
def toDirectMatrix
    (M : DirectGeometryMatrix.{u}) :
    DirectMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toW9DirectRow

/-- Direct geometry packages rule out every minimal cleared failure through
W9. -/
theorem no_minimalClearedFailure
    (M : DirectGeometryMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toDirectMatrix.no_minimalClearedFailure

/-- Conditional target projection from direct geometry packages. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectGeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toDirectMatrix.targetLowerBoundEightThirtyOne

end DirectGeometryMatrix

/-- Uniform K23 geometry rows from `GeometryRemainingFieldsW10`. -/
structure K23GeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryRemainingFieldsW10.K23GeometryPackage.{u} C hmin

namespace K23GeometryMatrix

/-- Route K23 geometry packages to the W9 `K23Matrix`. -/
def toK23Matrix
    (M : K23GeometryMatrix.{u}) :
    K23Matrix.{u} where
  row := fun C hmin => (M.row C hmin).toW9K23Row

/-- Forget K23 geometry packages to W9 direct rows. -/
def toDirectMatrix
    (M : K23GeometryMatrix.{u}) :
    DirectMatrix.{u} :=
  M.toK23Matrix.toDirectMatrix

/-- K23 geometry packages rule out every minimal cleared failure through W9.
-/
theorem no_minimalClearedFailure
    (M : K23GeometryMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toK23Matrix.no_minimalClearedFailure

/-- Conditional target projection from K23 geometry packages. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23GeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toK23Matrix.targetLowerBoundEightThirtyOne

end K23GeometryMatrix

/-- Uniform common-neighbor geometry rows from `GeometryRemainingFieldsW10`. -/
structure CommonNeighborGeometryMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryRemainingFieldsW10.CommonNeighborGeometryPackage.{u} C hmin

namespace CommonNeighborGeometryMatrix

/-- Route common-neighbor geometry packages to the W9 `K23Matrix`. -/
def toK23Matrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    K23Matrix.{u} where
  row := fun C hmin => (M.row C hmin).toW9K23Row

/-- Forget common-neighbor geometry packages to W9 direct rows. -/
def toDirectMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    DirectMatrix.{u} :=
  M.toK23Matrix.toDirectMatrix

/-- Common-neighbor geometry packages rule out every minimal cleared failure
through W9. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborGeometryMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  M.toK23Matrix.no_minimalClearedFailure

/-- Conditional target projection from common-neighbor geometry packages. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborGeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.toK23Matrix.targetLowerBoundEightThirtyOne

end CommonNeighborGeometryMatrix

/-! ## Projection matrix -/

/-- A target-producing projection row.  The input package remains explicit;
the row only records checked eliminator and target projections. -/
structure ProjectionRow (alpha : Type v) : Type v where
  noMinimal :
    alpha -> forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C)
  target :
    alpha -> _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

/-- W8 projection row retained for audit comparison. -/
def w8MatrixRow :
    ProjectionRow (SwanepoelW8ClosureMatrix.Matrix.{u}) where
  noMinimal := SwanepoelW8ClosureMatrix.Matrix.no_minimalClearedFailure
  target := SwanepoelW8ClosureMatrix.Matrix.targetLowerBoundEightThirtyOne

/-- W9 direct projection row. -/
def w9DirectMatrixRow :
    ProjectionRow (DirectMatrix.{u}) where
  noMinimal := DirectMatrix.no_minimalClearedFailure
  target := DirectMatrix.targetLowerBoundEightThirtyOne

/-- W9 K23 projection row. -/
def w9K23MatrixRow :
    ProjectionRow (K23Matrix.{u}) where
  noMinimal := K23Matrix.no_minimalClearedFailure
  target := K23Matrix.targetLowerBoundEightThirtyOne

/-- W10 direct component projection row, routed through W9 `DirectMatrix`. -/
def directComponentMatrixRow :
    ProjectionRow (DirectComponentMatrix.{u}) where
  noMinimal := DirectComponentMatrix.no_minimalClearedFailure
  target := DirectComponentMatrix.targetLowerBoundEightThirtyOne

/-- W10 K23 component projection row, routed through W9 `K23Matrix`. -/
def k23ComponentMatrixRow :
    ProjectionRow (K23ComponentMatrix.{u}) where
  noMinimal := K23ComponentMatrix.no_minimalClearedFailure
  target := K23ComponentMatrix.targetLowerBoundEightThirtyOne

/-- Existing W10 direct-facade projection row, routed through W9
`DirectMatrix`. -/
def minimalFailureDirectW10MatrixRow :
    ProjectionRow (MinimalFailureDirectW10Matrix.{u}) where
  noMinimal := MinimalFailureDirectW10Matrix.no_minimalClearedFailure
  target := MinimalFailureDirectW10Matrix.targetLowerBoundEightThirtyOne

/-- W10 direct geometry projection row, routed through W9 `DirectMatrix`. -/
def directGeometryMatrixRow :
    ProjectionRow (DirectGeometryMatrix.{u}) where
  noMinimal := DirectGeometryMatrix.no_minimalClearedFailure
  target := DirectGeometryMatrix.targetLowerBoundEightThirtyOne

/-- W10 K23 geometry projection row, routed through W9 `K23Matrix`. -/
def k23GeometryMatrixRow :
    ProjectionRow (K23GeometryMatrix.{u}) where
  noMinimal := K23GeometryMatrix.no_minimalClearedFailure
  target := K23GeometryMatrix.targetLowerBoundEightThirtyOne

/-- W10 common-neighbor geometry projection row, routed through W9
`K23Matrix`. -/
def commonNeighborGeometryMatrixRow :
    ProjectionRow (CommonNeighborGeometryMatrix.{u}) where
  noMinimal := CommonNeighborGeometryMatrix.no_minimalClearedFailure
  target := CommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne

/-- Consolidated W10 closure matrix.

Every target-producing entry is conditional on its explicit input package.
The matrix itself is only an index of checked routes. -/
structure Matrix where
  w8 : ProjectionRow (SwanepoelW8ClosureMatrix.Matrix.{u})
  w9Direct : ProjectionRow (DirectMatrix.{u})
  w9K23 : ProjectionRow (K23Matrix.{u})
  directComponents : ProjectionRow (DirectComponentMatrix.{u})
  k23Components : ProjectionRow (K23ComponentMatrix.{u})
  minimalFailureDirectW10 :
    ProjectionRow (MinimalFailureDirectW10Matrix.{u})
  directGeometry : ProjectionRow (DirectGeometryMatrix.{u})
  k23Geometry : ProjectionRow (K23GeometryMatrix.{u})
  commonNeighborGeometry :
    ProjectionRow (CommonNeighborGeometryMatrix.{u})

/-- The checked W10 closure matrix of conditional projection routes. -/
def matrix : Matrix where
  w8 := w8MatrixRow
  w9Direct := w9DirectMatrixRow
  w9K23 := w9K23MatrixRow
  directComponents := directComponentMatrixRow
  k23Components := k23ComponentMatrixRow
  minimalFailureDirectW10 := minimalFailureDirectW10MatrixRow
  directGeometry := directGeometryMatrixRow
  k23Geometry := k23GeometryMatrixRow
  commonNeighborGeometry := commonNeighborGeometryMatrixRow

/-! ## Public conditional projections -/

/-- Target projection from the retained W8 matrix row. -/
theorem targetLowerBoundEightThirtyOne_of_w8Matrix
    (M : SwanepoelW8ClosureMatrix.Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from W9 direct rows. -/
theorem targetLowerBoundEightThirtyOne_of_directMatrix
    (M : DirectMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from W9 K23 rows. -/
theorem targetLowerBoundEightThirtyOne_of_k23Matrix
    (M : K23Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from base-compatible direct component rows, routed
through W9 `DirectMatrix`. -/
theorem targetLowerBoundEightThirtyOne_of_directComponentMatrix
    (M : DirectComponentMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from base-compatible K23 component rows, routed through
W9 `K23Matrix`. -/
theorem targetLowerBoundEightThirtyOne_of_k23ComponentMatrix
    (M : K23ComponentMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from the existing W10 direct component matrix, routed
through W9 `DirectMatrix`. -/
theorem targetLowerBoundEightThirtyOne_of_minimalFailureDirectW10Matrix
    (M : MinimalFailureDirectW10Matrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from W10 direct geometry packages, routed through W9
`DirectMatrix`. -/
theorem targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    (M : DirectGeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from W10 K23 geometry packages, routed through W9
`K23Matrix`. -/
theorem targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    (M : K23GeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Target projection from W10 common-neighbor geometry packages, routed
through W9 `K23Matrix`. -/
theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    (M : CommonNeighborGeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

end

end SwanepoelW10ClosureMatrix
end Swanepoel
end ErdosProblems1066
