import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.TargetClosureMatrixW11
import ErdosProblems1066.Swanepoel.MinimalFailureGeometryClosureW11
import ErdosProblems1066.Swanepoel.K23IntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Target-facing W11 geometry matrix

This module is a target-facing wrapper around the W11 geometry source rows.
It keeps the direct, K23, and common-neighbor source fields explicit, then
records checked conditional projections through the geometry, target-closure,
integrated target, minimal-failure geometry, and K23/common-neighbor ledgers.

Every public target statement below takes an explicit uniform input matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryTargetIntegratedW11

open GeometryRemainingFieldsW10
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev GeometryClosureMatrix :=
  GeometryIntegratedW11.GeometryClosureMatrix

abbrev NarrowClosureInputFamily :=
  GeometryIntegratedW11.NarrowClosureInputFamily

abbrev CheckedClosureInputFamily :=
  GeometryIntegratedW11.CheckedClosureInputFamily

abbrev TargetFacadeMatrix :=
  GeometryIntegratedW11.TargetFacadeMatrix

/-! ## Pointwise target-facing geometry rows -/

/-- Target-facing direct geometry row for one fixed minimal cleared failure. -/
structure DirectTargetFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  noStartNoEarly : NoStartNoEarlyFields source

namespace DirectTargetFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage direct target fields for the integrated W11 geometry facade. -/
def toGeometryIntegratedDirectFields
    (R : DirectTargetFields.{u} C hmin) :
    GeometryIntegratedW11.DirectGeometryFields.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Repackage direct target fields for the integrated broken-lattice facade. -/
def toBrokenLatticeIntegratedDirectFieldPackage
    (R : DirectTargetFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.DirectFieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- Repackage direct target fields for the minimal-failure geometry facade. -/
def toMinimalFailureDirectGeometryFields
    (R : DirectTargetFields.{u} C hmin) :
    MinimalFailureGeometryClosureW11.DirectGeometryFields.{u} C hmin :=
  R.toGeometryIntegratedDirectFields.toMinimalFailureDirectGeometryFields

/-- Repackage direct target fields for the W11 target-closure predicate row. -/
def toTargetClosureDirectGeometryPredicateFields
    (R : DirectTargetFields.{u} C hmin) :
    BrokenLatticeFieldsW11.DirectGeometryPredicateFields.{u} C hmin :=
  R.toGeometryIntegratedDirectFields
    |>.toBrokenLatticeDirectGeometryPredicateFields

/-- A fixed direct target row closes through the geometry integration layer. -/
theorem contradiction_via_geometryIntegrated
    (R : DirectTargetFields.{u} C hmin) :
    False :=
  R.toGeometryIntegratedDirectFields.contradiction

/-- A fixed direct target row closes through the broken-lattice layer. -/
theorem contradiction_via_brokenLatticeIntegrated
    (R : DirectTargetFields.{u} C hmin) :
    False :=
  R.toBrokenLatticeIntegratedDirectFieldPackage.contradiction

end DirectTargetFields

/-- Target-facing K23 geometry row for one fixed minimal cleared failure. -/
structure K23TargetFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  k23NoEarly : K23NoEarlyFields source

namespace K23TargetFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage K23 target fields for the source-facing K23 integration layer. -/
def toK23IntegratedFields
    (R : K23TargetFields.{u} C hmin) :
    K23IntegratedMatrixW11.K23IntegratedFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23NoEarly.k23Obstruction

/-- Repackage K23 target fields as the checked K23 obstruction row. -/
def toK23ObstructionW10Fields
    (R : K23TargetFields.{u} C hmin) :
    K23CommonNeighborW11.K23ObstructionW10Fields.{u} C hmin :=
  R.toK23IntegratedFields.toK23ObstructionW10Fields

/-- Repackage K23 target fields for the integrated W11 geometry facade. -/
def toGeometryIntegratedK23Fields
    (R : K23TargetFields.{u} C hmin) :
    GeometryIntegratedW11.K23GeometryFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Repackage K23 target fields for the integrated broken-lattice facade. -/
def toBrokenLatticeIntegratedK23FieldPackage
    (R : K23TargetFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.K23FieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- Repackage K23 target fields for the minimal-failure geometry facade. -/
def toMinimalFailureK23GeometryFields
    (R : K23TargetFields.{u} C hmin) :
    MinimalFailureGeometryClosureW11.K23GeometryFields.{u} C hmin :=
  R.toGeometryIntegratedK23Fields.toMinimalFailureK23GeometryFields

/-- Repackage K23 target fields for the W11 target-closure predicate row. -/
def toTargetClosureK23GeometryPredicateFields
    (R : K23TargetFields.{u} C hmin) :
    BrokenLatticeFieldsW11.K23GeometryPredicateFields.{u} C hmin :=
  R.toK23IntegratedFields.toBrokenLatticeK23GeometryPredicateFields

/-- A fixed K23 target row closes through the K23 integration layer. -/
theorem contradiction_via_k23Integrated
    (R : K23TargetFields.{u} C hmin) :
    False :=
  R.toK23IntegratedFields.contradiction_via_k23Closure

/-- A fixed K23 target row closes through the geometry integration layer. -/
theorem contradiction_via_geometryIntegrated
    (R : K23TargetFields.{u} C hmin) :
    False :=
  R.toGeometryIntegratedK23Fields.contradiction

end K23TargetFields

/-- Target-facing common-neighbor geometry row for one fixed minimal cleared
failure. -/
structure CommonNeighborTargetFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  commonNeighborNoEarly : CommonNeighborNoEarlyFields source

namespace CommonNeighborTargetFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Repackage common-neighbor target fields for the source-facing integration
layer. -/
def toCommonNeighborIntegratedFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    K23IntegratedMatrixW11.CommonNeighborIntegratedFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction :=
    R.commonNeighborNoEarly.commonNeighborObstruction

/-- Repackage common-neighbor target fields as the checked obstruction row. -/
def toCommonNeighborObstructionW10Fields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    K23CommonNeighborW11.CommonNeighborObstructionW10Fields.{u}
      C hmin :=
  R.toCommonNeighborIntegratedFields.toCommonNeighborObstructionW10Fields

/-- Forget common-neighbor target fields to the checked K23 target row. -/
def toK23TargetFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    K23TargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.commonNeighborNoEarly.toK23NoEarlyFields

/-- Repackage common-neighbor target fields for the integrated geometry facade. -/
def toGeometryIntegratedCommonNeighborFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    GeometryIntegratedW11.CommonNeighborGeometryFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage common-neighbor target fields for the broken-lattice facade. -/
def toBrokenLatticeIntegratedCommonNeighborFieldPackage
    (R : CommonNeighborTargetFields.{u} C hmin) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- Repackage common-neighbor target fields for minimal-failure geometry. -/
def toMinimalFailureCommonNeighborGeometryFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    MinimalFailureGeometryClosureW11.CommonNeighborGeometryFields.{u}
      C hmin :=
  R.toGeometryIntegratedCommonNeighborFields
    |>.toMinimalFailureCommonNeighborGeometryFields

/-- Repackage common-neighbor target fields for the target-closure predicate
row. -/
def toTargetClosureCommonNeighborGeometryPredicateFields
    (R : CommonNeighborTargetFields.{u} C hmin) :
    BrokenLatticeFieldsW11.CommonNeighborGeometryPredicateFields.{u}
      C hmin :=
  R.toCommonNeighborIntegratedFields
    |>.toBrokenLatticeCommonNeighborGeometryPredicateFields

/-- A fixed common-neighbor target row closes through the K23 integration
layer. -/
theorem contradiction_via_k23Integrated
    (R : CommonNeighborTargetFields.{u} C hmin) :
    False :=
  R.toCommonNeighborIntegratedFields.contradiction_via_k23Closure

/-- A fixed common-neighbor target row closes through the geometry integration
layer. -/
theorem contradiction_via_geometryIntegrated
    (R : CommonNeighborTargetFields.{u} C hmin) :
    False :=
  R.toGeometryIntegratedCommonNeighborFields.contradiction

end CommonNeighborTargetFields

/-! ## Uniform explicit target matrices -/

/-- Uniform target-facing direct rows for every minimal cleared failure. -/
structure DirectTargetMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectTargetFields.{u} C hmin

namespace DirectTargetMatrix

/-- View direct target rows as the integrated W11 geometry matrix. -/
def toGeometryIntegratedDirectGeometryMatrix
    (M : DirectTargetMatrix.{u}) :
    GeometryIntegratedW11.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedDirectFields

/-- View direct target rows as the integrated broken-lattice field matrix. -/
def toBrokenLatticeIntegratedDirectFieldMatrix
    (M : DirectTargetMatrix.{u}) :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeIntegratedDirectFieldPackage

/-- View direct target rows as the target-closure predicate matrix. -/
def toTargetClosureDirectGeometryPredicateMatrix
    (M : DirectTargetMatrix.{u}) :
    TargetClosureMatrixW11.DirectGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toTargetClosureDirectGeometryPredicateFields

/-- View direct target rows as the minimal-failure geometry direct matrix. -/
def toMinimalFailureDirectGeometryMatrix
    (M : DirectTargetMatrix.{u}) :
    MinimalFailureGeometryClosureW11.DirectGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toMinimalFailureDirectGeometryFields

/-- View direct target rows as the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : DirectTargetMatrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedDirectGeometryMatrix.toGeometryClosureMatrix

/-- View direct target rows as narrow concrete closure input families. -/
def toNarrowClosureInputFamily
    (M : DirectTargetMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedDirectGeometryMatrix.toNarrowClosureInputFamily

/-- View direct target rows as checked refined closure input families. -/
def toCheckedClosureInputFamily
    (M : DirectTargetMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedDirectGeometryMatrix.toCheckedClosureInputFamily

/-- View direct target rows as the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : DirectTargetMatrix.{u}) :
    TargetFacadeMatrix :=
  M.toGeometryIntegratedDirectGeometryMatrix.toTargetFacadeMatrix

/-- Uniform direct target rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : DirectTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_directFieldMatrix
    M.toBrokenLatticeIntegratedDirectFieldMatrix

/-- Uniform direct target rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : DirectTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_directFieldMatrix
    M.toBrokenLatticeIntegratedDirectFieldMatrix

/-- Uniform direct target rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : DirectTargetMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_directFieldMatrix
    M.toBrokenLatticeIntegratedDirectFieldMatrix

/-- Conditional target projection through the integrated target facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : DirectTargetMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix
    M.toBrokenLatticeIntegratedDirectFieldMatrix

/-- Conditional target projection through the target-closure facade. -/
theorem target_via_targetClosureMatrix
    (M : DirectTargetMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_directGeometryPredicateMatrix
    M.toTargetClosureDirectGeometryPredicateMatrix

/-- Conditional target projection through the geometry integration facade. -/
theorem target_via_geometryIntegrated
    (M : DirectTargetMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M.toGeometryIntegratedDirectGeometryMatrix

/-- Conditional target projection through the minimal-failure geometry facade. -/
theorem target_via_minimalFailureGeometry
    (M : DirectTargetMatrix.{u}) :
    Target :=
  MinimalFailureGeometryClosureW11.DirectGeometryMatrix.targetLowerBoundEightThirtyOne
    M.toMinimalFailureDirectGeometryMatrix

end DirectTargetMatrix

/-- Uniform target-facing K23 rows for every minimal cleared failure. -/
structure K23TargetMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23TargetFields.{u} C hmin

namespace K23TargetMatrix

/-- Forget to the source-facing K23 integration matrix. -/
def toK23IntegratedMatrix
    (M : K23TargetMatrix.{u}) :
    K23IntegratedMatrixW11.K23IntegratedMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23IntegratedFields

/-- View K23 target rows as the integrated W11 geometry matrix. -/
def toGeometryIntegratedK23GeometryMatrix
    (M : K23TargetMatrix.{u}) :
    GeometryIntegratedW11.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedK23Fields

/-- View K23 target rows as the integrated broken-lattice field matrix. -/
def toBrokenLatticeIntegratedK23FieldMatrix
    (M : K23TargetMatrix.{u}) :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeIntegratedK23FieldPackage

/-- View K23 target rows as the target-closure predicate matrix. -/
def toTargetClosureK23GeometryPredicateMatrix
    (M : K23TargetMatrix.{u}) :
    TargetClosureMatrixW11.K23GeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toTargetClosureK23GeometryPredicateFields

/-- View K23 target rows as the minimal-failure geometry K23 matrix. -/
def toMinimalFailureK23GeometryMatrix
    (M : K23TargetMatrix.{u}) :
    MinimalFailureGeometryClosureW11.K23GeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toMinimalFailureK23GeometryFields

/-- View K23 target rows as the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : K23TargetMatrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedK23GeometryMatrix.toGeometryClosureMatrix

/-- View K23 target rows as narrow concrete closure input families. -/
def toNarrowClosureInputFamily
    (M : K23TargetMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedK23GeometryMatrix.toNarrowClosureInputFamily

/-- View K23 target rows as checked refined closure input families. -/
def toCheckedClosureInputFamily
    (M : K23TargetMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedK23GeometryMatrix.toCheckedClosureInputFamily

/-- View K23 target rows as the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : K23TargetMatrix.{u}) :
    TargetFacadeMatrix :=
  M.toGeometryIntegratedK23GeometryMatrix.toTargetFacadeMatrix

/-- Uniform K23 target rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : K23TargetMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Uniform K23 target rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : K23TargetMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Uniform K23 target rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : K23TargetMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Conditional target projection through the integrated target facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : K23TargetMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix
    M.toBrokenLatticeIntegratedK23FieldMatrix

/-- Conditional target projection through the target-closure facade. -/
theorem target_via_targetClosureMatrix
    (M : K23TargetMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_k23GeometryPredicateMatrix
    M.toTargetClosureK23GeometryPredicateMatrix

/-- Conditional target projection through the geometry integration facade. -/
theorem target_via_geometryIntegrated
    (M : K23TargetMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M.toGeometryIntegratedK23GeometryMatrix

/-- Conditional target projection through the source-facing K23 integration
facade. -/
theorem target_via_k23Integrated
    (M : K23TargetMatrix.{u}) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_k23IntegratedMatrix
    M.toK23IntegratedMatrix

/-- Conditional target projection through the minimal-failure geometry facade. -/
theorem target_via_minimalFailureGeometry
    (M : K23TargetMatrix.{u}) :
    Target :=
  MinimalFailureGeometryClosureW11.K23GeometryMatrix.targetLowerBoundEightThirtyOne
    M.toMinimalFailureK23GeometryMatrix

end K23TargetMatrix

/-- Uniform target-facing common-neighbor rows for every minimal cleared
failure. -/
structure CommonNeighborTargetMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborTargetFields.{u} C hmin

namespace CommonNeighborTargetMatrix

/-- Forget to the source-facing common-neighbor integration matrix. -/
def toCommonNeighborIntegratedMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    K23IntegratedMatrixW11.CommonNeighborIntegratedMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toCommonNeighborIntegratedFields

/-- Forget common-neighbor rows to the checked K23 target matrix. -/
def toK23TargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    K23TargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23TargetFields

/-- View common-neighbor target rows as the integrated W11 geometry matrix. -/
def toGeometryIntegratedCommonNeighborGeometryMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toGeometryIntegratedCommonNeighborFields

/-- View common-neighbor target rows as the integrated broken-lattice matrix. -/
def toBrokenLatticeIntegratedCommonNeighborFieldMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toBrokenLatticeIntegratedCommonNeighborFieldPackage

/-- View common-neighbor target rows as the target-closure predicate matrix. -/
def toTargetClosureCommonNeighborGeometryPredicateMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    TargetClosureMatrixW11.CommonNeighborGeometryPredicateMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toTargetClosureCommonNeighborGeometryPredicateFields

/-- View common-neighbor target rows as the minimal-failure geometry matrix. -/
def toMinimalFailureCommonNeighborGeometryMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureGeometryClosureW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin =>
    (M.row C hmin).toMinimalFailureCommonNeighborGeometryFields

/-- View common-neighbor target rows as the W11 geometry closure matrix. -/
def toGeometryClosureMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    GeometryClosureMatrix.{u} :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix.toGeometryClosureMatrix

/-- View common-neighbor target rows as narrow concrete closure inputs. -/
def toNarrowClosureInputFamily
    (M : CommonNeighborTargetMatrix.{u}) :
    NarrowClosureInputFamily.{u} :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix
    |>.toNarrowClosureInputFamily

/-- View common-neighbor target rows as checked refined closure inputs. -/
def toCheckedClosureInputFamily
    (M : CommonNeighborTargetMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix
    |>.toCheckedClosureInputFamily

/-- View common-neighbor target rows as the W10 target facade matrix. -/
def toTargetFacadeMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    TargetFacadeMatrix :=
  M.toGeometryIntegratedCommonNeighborGeometryMatrix.toTargetFacadeMatrix

/-- Uniform common-neighbor target rows give a minimal-failure eliminator. -/
theorem minimalClearedFailureEliminator
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Uniform common-neighbor target rows rule out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Uniform common-neighbor target rows clear the conditional target pipeline. -/
theorem pipelineCleared
    (M : CommonNeighborTargetMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Conditional target projection through the integrated target facade. -/
theorem targetLowerBoundEightThirtyOne
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix
    M.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- Conditional target projection through the target-closure facade. -/
theorem target_via_targetClosureMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  TargetClosureMatrixW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryPredicateMatrix
    M.toTargetClosureCommonNeighborGeometryPredicateMatrix

/-- Conditional target projection through the geometry integration facade. -/
theorem target_via_geometryIntegrated
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M.toGeometryIntegratedCommonNeighborGeometryMatrix

/-- Conditional target projection through the source-facing common-neighbor
integration facade. -/
theorem target_via_k23Integrated
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  K23IntegratedMatrixW11.targetLowerBoundEightThirtyOne_of_commonNeighborIntegratedMatrix
    M.toCommonNeighborIntegratedMatrix

/-- Conditional target projection through the minimal-failure geometry facade. -/
theorem target_via_minimalFailureGeometry
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  MinimalFailureGeometryClosureW11.CommonNeighborGeometryMatrix.targetLowerBoundEightThirtyOne
    M.toMinimalFailureCommonNeighborGeometryMatrix

end CommonNeighborTargetMatrix

/-! ## Checked target projection rows -/

/-- Direct target rows as a target-closure projection. -/
def directTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (DirectTargetMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    DirectTargetMatrix.no_minimalClearedFailure
    DirectTargetMatrix.targetLowerBoundEightThirtyOne

/-- K23 target rows as a target-closure projection. -/
def k23TargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23TargetMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    K23TargetMatrix.no_minimalClearedFailure
    K23TargetMatrix.targetLowerBoundEightThirtyOne

/-- Common-neighbor target rows as a target-closure projection. -/
def commonNeighborTargetClosureRow :
    TargetClosureMatrixW11.TargetProjectionRow
      (CommonNeighborTargetMatrix.{u}) :=
  TargetClosureMatrixW11.TargetProjectionRow.ofNoMinimalAndTarget
    CommonNeighborTargetMatrix.no_minimalClearedFailure
    CommonNeighborTargetMatrix.targetLowerBoundEightThirtyOne

/-- Direct target rows as an integrated target route with eliminator. -/
def directTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (DirectTargetMatrix.{u}) where
  eliminator := DirectTargetMatrix.minimalClearedFailureEliminator
  noMinimal := DirectTargetMatrix.no_minimalClearedFailure
  pipeline := DirectTargetMatrix.pipelineCleared
  target := DirectTargetMatrix.targetLowerBoundEightThirtyOne

/-- K23 target rows as an integrated target route with eliminator. -/
def k23TargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23TargetMatrix.{u}) where
  eliminator := K23TargetMatrix.minimalClearedFailureEliminator
  noMinimal := K23TargetMatrix.no_minimalClearedFailure
  pipeline := K23TargetMatrix.pipelineCleared
  target := K23TargetMatrix.targetLowerBoundEightThirtyOne

/-- Common-neighbor target rows as an integrated target route with eliminator. -/
def commonNeighborTargetIntegratedRoute :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (CommonNeighborTargetMatrix.{u}) where
  eliminator := CommonNeighborTargetMatrix.minimalClearedFailureEliminator
  noMinimal := CommonNeighborTargetMatrix.no_minimalClearedFailure
  pipeline := CommonNeighborTargetMatrix.pipelineCleared
  target := CommonNeighborTargetMatrix.targetLowerBoundEightThirtyOne

/-- Direct target rows as an integrated W11 geometry projection row. -/
def directGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (DirectTargetMatrix.{u}) where
  geometryClosure := DirectTargetMatrix.toGeometryClosureMatrix
  narrowInputs := DirectTargetMatrix.toNarrowClosureInputFamily
  checkedInputs := DirectTargetMatrix.toCheckedClosureInputFamily
  targetFacade := DirectTargetMatrix.toTargetFacadeMatrix
  targetProjection := directTargetClosureRow

/-- K23 target rows as an integrated W11 geometry projection row. -/
def k23GeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23TargetMatrix.{u}) where
  geometryClosure := K23TargetMatrix.toGeometryClosureMatrix
  narrowInputs := K23TargetMatrix.toNarrowClosureInputFamily
  checkedInputs := K23TargetMatrix.toCheckedClosureInputFamily
  targetFacade := K23TargetMatrix.toTargetFacadeMatrix
  targetProjection := k23TargetClosureRow

/-- Common-neighbor target rows as an integrated W11 geometry projection row. -/
def commonNeighborGeometryProjectionRow :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (CommonNeighborTargetMatrix.{u}) where
  geometryClosure := CommonNeighborTargetMatrix.toGeometryClosureMatrix
  narrowInputs := CommonNeighborTargetMatrix.toNarrowClosureInputFamily
  checkedInputs := CommonNeighborTargetMatrix.toCheckedClosureInputFamily
  targetFacade := CommonNeighborTargetMatrix.toTargetFacadeMatrix
  targetProjection := commonNeighborTargetClosureRow

/-! ## Target-facing integrated geometry matrix -/

/-- Checked W11 target-facing geometry integration ledger.

The ledger stores route functions only; it does not construct any direct,
K23, or common-neighbor input matrix. -/
structure Matrix : Type (u + 1) where
  geometryIntegrated :
    GeometryIntegratedW11.Matrix.{u}
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}
  targetClosure :
    TargetClosureMatrixW11.Matrix.{u}
  minimalFailureGeometry :
    MinimalFailureGeometryClosureW11.Matrix.{u}
  k23Integrated :
    K23IntegratedMatrixW11.Matrix.{u}
  directTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (DirectTargetMatrix.{u})
  k23TargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (K23TargetMatrix.{u})
  commonNeighborTargetClosure :
    TargetClosureMatrixW11.TargetProjectionRow
      (CommonNeighborTargetMatrix.{u})
  directTargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (DirectTargetMatrix.{u})
  k23TargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (K23TargetMatrix.{u})
  commonNeighborTargetIntegrated :
    TargetIntegratedMatrixW11.EliminatorTargetRoute
      (CommonNeighborTargetMatrix.{u})
  directGeometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (DirectTargetMatrix.{u})
  k23Geometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (K23TargetMatrix.{u})
  commonNeighborGeometry :
    GeometryIntegratedW11.GeometryProjectionRow.{u, u + 1}
      (CommonNeighborTargetMatrix.{u})

/-- The checked target-facing integrated geometry ledger. -/
def matrix : Matrix.{u} where
  geometryIntegrated := GeometryIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix
  minimalFailureGeometry := MinimalFailureGeometryClosureW11.matrix
  k23Integrated := K23IntegratedMatrixW11.matrix
  directTargetClosure := directTargetClosureRow
  k23TargetClosure := k23TargetClosureRow
  commonNeighborTargetClosure := commonNeighborTargetClosureRow
  directTargetIntegrated := directTargetIntegratedRoute
  k23TargetIntegrated := k23TargetIntegratedRoute
  commonNeighborTargetIntegrated := commonNeighborTargetIntegratedRoute
  directGeometry := directGeometryProjectionRow
  k23Geometry := k23GeometryProjectionRow
  commonNeighborGeometry := commonNeighborGeometryProjectionRow

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_directTargetMatrix
    (M : DirectTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.directTargetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_directTargetMatrix
    (M : DirectTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.directTargetIntegrated.noMinimal M

theorem pipelineCleared_of_directTargetMatrix
    (M : DirectTargetMatrix.{u}) :
    PipelineCleared :=
  matrix.directTargetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_directTargetMatrix
    (M : DirectTargetMatrix.{u}) :
    Target :=
  matrix.directTargetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_directTargetMatrix_via_targetClosure
    (M : DirectTargetMatrix.{u}) :
    Target :=
  matrix.directTargetClosure.target M

theorem targetLowerBoundEightThirtyOne_of_directTargetMatrix_via_geometry
    (M : DirectTargetMatrix.{u}) :
    Target :=
  matrix.directGeometry.target M

theorem minimalClearedFailureEliminator_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.k23TargetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.k23TargetIntegrated.noMinimal M

theorem pipelineCleared_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    PipelineCleared :=
  matrix.k23TargetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_k23TargetMatrix
    (M : K23TargetMatrix.{u}) :
    Target :=
  matrix.k23TargetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_k23TargetMatrix_via_targetClosure
    (M : K23TargetMatrix.{u}) :
    Target :=
  matrix.k23TargetClosure.target M

theorem targetLowerBoundEightThirtyOne_of_k23TargetMatrix_via_geometry
    (M : K23TargetMatrix.{u}) :
    Target :=
  matrix.k23Geometry.target M

theorem minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.commonNeighborTargetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.commonNeighborTargetIntegrated.noMinimal M

theorem pipelineCleared_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    PipelineCleared :=
  matrix.commonNeighborTargetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  matrix.commonNeighborTargetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix_via_targetClosure
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  matrix.commonNeighborTargetClosure.target M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix_via_geometry
    (M : CommonNeighborTargetMatrix.{u}) :
    Target :=
  matrix.commonNeighborGeometry.target M

end

end GeometryTargetIntegratedW11
end Swanepoel
end ErdosProblems1066
