import ErdosProblems1066.Swanepoel.GeometryTargetIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryIntegratedW11
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11
import ErdosProblems1066.Swanepoel.K23TargetIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeFinalIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 geometry aggregate matrix

This module gathers the checked W11 geometry-facing target routes behind one
final aggregate.  The direct, K23, and common-neighbor inputs remain explicit:
every target projection below is conditional on a caller-supplied uniform
matrix of the relevant fields.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace GeometryFinalIntegratedW11

open MinimalGraphFacts
open GeometryRemainingFieldsW10

universe u v

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

/-! ## Shared route shapes -/

/-- A conditional Swanepoel target route from an explicit input package. -/
structure TargetRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

/-- A conditional target route that also exposes the pointwise eliminator. -/
structure EliminatorTargetRoute (alpha : Type v) : Type v where
  eliminator : alpha -> MinimalFailureEliminator
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace EliminatorTargetRoute

/-- Forget the eliminator while keeping the target route. -/
def toTargetRoute
    {alpha : Type v}
    (R : EliminatorTargetRoute alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end EliminatorTargetRoute

/-! ## Explicit pointwise geometry fields -/

/-- One direct final geometry row for a fixed minimal cleared failure. -/
structure DirectFinalGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  noStartNoEarly : NoStartNoEarlyFields source

namespace DirectFinalGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View direct final geometry fields as target-facing geometry fields. -/
def toGeometryTargetFields
    (R : DirectFinalGeometryFields.{u} C hmin) :
    GeometryTargetIntegratedW11.DirectTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- View direct final geometry fields as integrated W11 geometry fields. -/
def toGeometryIntegratedFields
    (R : DirectFinalGeometryFields.{u} C hmin) :
    GeometryIntegratedW11.DirectGeometryFields.{u} C hmin :=
  R.toGeometryTargetFields.toGeometryIntegratedDirectFields

/-- View direct final geometry fields as broken-lattice field packages. -/
def toBrokenLatticeFieldPackage
    (R : DirectFinalGeometryFields.{u} C hmin) :
    BrokenLatticeFinalIntegratedW11.DirectFieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

/-- A fixed direct row closes through the geometry-target route. -/
theorem contradiction_via_geometryTarget
    (R : DirectFinalGeometryFields.{u} C hmin) :
    False :=
  R.toGeometryTargetFields.contradiction_via_geometryIntegrated

/-- A fixed direct row closes through the broken-lattice route. -/
theorem contradiction_via_brokenLattice
    (R : DirectFinalGeometryFields.{u} C hmin) :
    False :=
  R.toBrokenLatticeFieldPackage.contradiction

end DirectFinalGeometryFields

/-- One K23 final geometry row for a fixed minimal cleared failure. -/
structure K23FinalGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  k23NoEarly : K23NoEarlyFields source

namespace K23FinalGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View K23 final geometry fields as target-facing geometry fields. -/
def toGeometryTargetFields
    (R : K23FinalGeometryFields.{u} C hmin) :
    GeometryTargetIntegratedW11.K23TargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- View K23 final geometry fields as target-facing K23 obstruction fields. -/
def toK23TargetFields
    (R : K23FinalGeometryFields.{u} C hmin) :
    K23TargetIntegratedW11.K23TargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23NoEarly.k23Obstruction

/-- View K23 final geometry fields as integrated W11 geometry fields. -/
def toGeometryIntegratedFields
    (R : K23FinalGeometryFields.{u} C hmin) :
    GeometryIntegratedW11.K23GeometryFields.{u} C hmin :=
  R.toGeometryTargetFields.toGeometryIntegratedK23Fields

/-- View K23 final geometry fields as broken-lattice field packages. -/
def toBrokenLatticeFieldPackage
    (R : K23FinalGeometryFields.{u} C hmin) :
    BrokenLatticeFinalIntegratedW11.K23FieldPackage.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- A fixed K23 row closes through the geometry-target route. -/
theorem contradiction_via_geometryTarget
    (R : K23FinalGeometryFields.{u} C hmin) :
    False :=
  R.toGeometryTargetFields.contradiction_via_geometryIntegrated

/-- A fixed K23 row closes through the K23-target route. -/
theorem contradiction_via_k23Target
    (R : K23FinalGeometryFields.{u} C hmin) :
    False :=
  R.toK23TargetFields.contradiction_via_k23Integrated

/-- A fixed K23 row closes through the broken-lattice route. -/
theorem contradiction_via_brokenLattice
    (R : K23FinalGeometryFields.{u} C hmin) :
    False :=
  R.toBrokenLatticeFieldPackage.contradiction

end K23FinalGeometryFields

/-- One common-neighbor final geometry row for a fixed minimal cleared
failure. -/
structure CommonNeighborFinalGeometryFields
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  containment : ContainmentFields source
  commonNeighborNoEarly : CommonNeighborNoEarlyFields source

namespace CommonNeighborFinalGeometryFields

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View common-neighbor fields as target-facing geometry fields. -/
def toGeometryTargetFields
    (R : CommonNeighborFinalGeometryFields.{u} C hmin) :
    GeometryTargetIntegratedW11.CommonNeighborTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- View common-neighbor fields as target-facing obstruction fields. -/
def toK23TargetFields
    (R : CommonNeighborFinalGeometryFields.{u} C hmin) :
    K23TargetIntegratedW11.CommonNeighborTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction :=
    R.commonNeighborNoEarly.commonNeighborObstruction

/-- View common-neighbor fields as integrated W11 geometry fields. -/
def toGeometryIntegratedFields
    (R : CommonNeighborFinalGeometryFields.{u} C hmin) :
    GeometryIntegratedW11.CommonNeighborGeometryFields.{u} C hmin :=
  R.toGeometryTargetFields.toGeometryIntegratedCommonNeighborFields

/-- View common-neighbor fields as broken-lattice field packages. -/
def toBrokenLatticeFieldPackage
    (R : CommonNeighborFinalGeometryFields.{u} C hmin) :
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldPackage.{u}
      C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- A fixed common-neighbor row closes through the geometry-target route. -/
theorem contradiction_via_geometryTarget
    (R : CommonNeighborFinalGeometryFields.{u} C hmin) :
    False :=
  R.toGeometryTargetFields.contradiction_via_geometryIntegrated

/-- A fixed common-neighbor row closes through the K23-target route. -/
theorem contradiction_via_k23Target
    (R : CommonNeighborFinalGeometryFields.{u} C hmin) :
    False :=
  R.toK23TargetFields.contradiction_via_k23Integrated

/-- A fixed common-neighbor row closes through the broken-lattice route. -/
theorem contradiction_via_brokenLattice
    (R : CommonNeighborFinalGeometryFields.{u} C hmin) :
    False :=
  R.toBrokenLatticeFieldPackage.contradiction

end CommonNeighborFinalGeometryFields

/-! ## Uniform explicit matrices -/

/-- Uniform direct final geometry rows for every minimal cleared failure. -/
structure DirectFinalGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        DirectFinalGeometryFields.{u} C hmin

namespace DirectFinalGeometryMatrix

/-- Forget final direct rows to the target-facing geometry matrix. -/
def toGeometryTargetMatrix
    (M : DirectFinalGeometryMatrix.{u}) :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryTargetFields

/-- Forget final direct rows to the integrated geometry matrix. -/
def toGeometryIntegratedMatrix
    (M : DirectFinalGeometryMatrix.{u}) :
    GeometryIntegratedW11.DirectGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedFields

/-- Forget final direct rows to the broken-lattice field matrix. -/
def toBrokenLatticeFieldMatrix
    (M : DirectFinalGeometryMatrix.{u}) :
    BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toBrokenLatticeFieldPackage

/-- Direct rows give the eliminator through geometry-target fields. -/
theorem minimalClearedFailureEliminator_via_geometryTarget
    (M : DirectFinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_directTargetMatrix
    M.toGeometryTargetMatrix

/-- Direct rows rule out all minimal cleared failures through geometry-target
fields. -/
theorem no_minimalClearedFailure_via_geometryTarget
    (M : DirectFinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  GeometryTargetIntegratedW11.no_minimalClearedFailure_of_directTargetMatrix
    M.toGeometryTargetMatrix

/-- Direct rows clear the target pipeline through geometry-target fields. -/
theorem pipelineCleared_via_geometryTarget
    (M : DirectFinalGeometryMatrix.{u}) :
    PipelineCleared :=
  GeometryTargetIntegratedW11.pipelineCleared_of_directTargetMatrix
    M.toGeometryTargetMatrix

/-- Conditional target projection through geometry-target fields. -/
theorem targetLowerBoundEightThirtyOne_via_geometryTarget
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_directTargetMatrix
    M.toGeometryTargetMatrix

/-- Conditional target projection through integrated geometry fields. -/
theorem targetLowerBoundEightThirtyOne_via_geometryIntegrated
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    M.toGeometryIntegratedMatrix

/-- Direct rows give the eliminator through the integrated target route. -/
theorem minimalClearedFailureEliminator_via_targetIntegrated
    (M : DirectFinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_directFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Direct rows rule out minimal cleared failures through the integrated
target route. -/
theorem no_minimalClearedFailure_via_targetIntegrated
    (M : DirectFinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_directFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Direct rows clear the pipeline through the integrated target route. -/
theorem pipelineCleared_via_targetIntegrated
    (M : DirectFinalGeometryMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_directFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Conditional target projection through the integrated target route. -/
theorem targetLowerBoundEightThirtyOne_via_targetIntegrated
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Conditional target projection through the final broken-lattice ledger. -/
theorem targetLowerBoundEightThirtyOne_via_brokenLatticeFinal
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_directFieldMatrix
    M.toBrokenLatticeFieldMatrix

end DirectFinalGeometryMatrix

/-- Uniform K23 final geometry rows for every minimal cleared failure. -/
structure K23FinalGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        K23FinalGeometryFields.{u} C hmin

namespace K23FinalGeometryMatrix

/-- Forget final K23 rows to the target-facing geometry matrix. -/
def toGeometryTargetMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    GeometryTargetIntegratedW11.K23TargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryTargetFields

/-- Forget final K23 rows to the target-facing K23 obstruction matrix. -/
def toK23TargetMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    K23TargetIntegratedW11.K23TargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23TargetFields

/-- Forget final K23 rows to the integrated geometry matrix. -/
def toGeometryIntegratedMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    GeometryIntegratedW11.K23GeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedFields

/-- Forget final K23 rows to the broken-lattice field matrix. -/
def toBrokenLatticeFieldMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toBrokenLatticeFieldPackage

/-- K23 rows give the eliminator through geometry-target fields. -/
theorem minimalClearedFailureEliminator_via_geometryTarget
    (M : K23FinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_k23TargetMatrix
    M.toGeometryTargetMatrix

/-- K23 rows rule out all minimal cleared failures through geometry-target
fields. -/
theorem no_minimalClearedFailure_via_geometryTarget
    (M : K23FinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  GeometryTargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
    M.toGeometryTargetMatrix

/-- K23 rows clear the target pipeline through geometry-target fields. -/
theorem pipelineCleared_via_geometryTarget
    (M : K23FinalGeometryMatrix.{u}) :
    PipelineCleared :=
  GeometryTargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
    M.toGeometryTargetMatrix

/-- Conditional target projection through geometry-target K23 fields. -/
theorem targetLowerBoundEightThirtyOne_via_geometryTarget
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
    M.toGeometryTargetMatrix

/-- Conditional target projection through integrated K23 geometry fields. -/
theorem targetLowerBoundEightThirtyOne_via_geometryIntegrated
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    M.toGeometryIntegratedMatrix

/-- K23 rows give the eliminator through the integrated target route. -/
theorem minimalClearedFailureEliminator_via_targetIntegrated
    (M : K23FinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_k23FieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- K23 rows rule out minimal cleared failures through the integrated target
route. -/
theorem no_minimalClearedFailure_via_targetIntegrated
    (M : K23FinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_k23FieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- K23 rows clear the pipeline through the integrated target route. -/
theorem pipelineCleared_via_targetIntegrated
    (M : K23FinalGeometryMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_k23FieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Conditional target projection through the integrated target route. -/
theorem targetLowerBoundEightThirtyOne_via_targetIntegrated
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Conditional target projection through the target-facing K23 route. -/
theorem targetLowerBoundEightThirtyOne_via_k23Target
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
    M.toK23TargetMatrix

/-- Conditional target projection through the final broken-lattice ledger. -/
theorem targetLowerBoundEightThirtyOne_via_brokenLatticeFinal
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_k23FieldMatrix
    M.toBrokenLatticeFieldMatrix

end K23FinalGeometryMatrix

/-- Uniform common-neighbor final geometry rows for every minimal cleared
failure. -/
structure CommonNeighborFinalGeometryMatrix : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        CommonNeighborFinalGeometryFields.{u} C hmin

namespace CommonNeighborFinalGeometryMatrix

/-- Forget common-neighbor rows to the target-facing geometry matrix. -/
def toGeometryTargetMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryTargetFields

/-- Forget common-neighbor rows to the target-facing obstruction matrix. -/
def toK23TargetMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toK23TargetFields

/-- Forget common-neighbor rows to the integrated geometry matrix. -/
def toGeometryIntegratedMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toGeometryIntegratedFields

/-- Forget common-neighbor rows to the broken-lattice field matrix. -/
def toBrokenLatticeFieldMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u} where
  row := fun C hmin => (M.row C hmin).toBrokenLatticeFieldPackage

/-- Common-neighbor rows give the eliminator through geometry-target fields. -/
theorem minimalClearedFailureEliminator_via_geometryTarget
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
    M.toGeometryTargetMatrix

/-- Common-neighbor rows rule out minimal cleared failures through
geometry-target fields. -/
theorem no_minimalClearedFailure_via_geometryTarget
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  GeometryTargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
    M.toGeometryTargetMatrix

/-- Common-neighbor rows clear the pipeline through geometry-target fields. -/
theorem pipelineCleared_via_geometryTarget
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    PipelineCleared :=
  GeometryTargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
    M.toGeometryTargetMatrix

/-- Conditional target projection through geometry-target fields. -/
theorem targetLowerBoundEightThirtyOne_via_geometryTarget
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    M.toGeometryTargetMatrix

/-- Conditional target projection through integrated common-neighbor geometry. -/
theorem targetLowerBoundEightThirtyOne_via_geometryIntegrated
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  GeometryIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    M.toGeometryIntegratedMatrix

/-- Common-neighbor rows give the eliminator through the integrated target
route. -/
theorem minimalClearedFailureEliminator_via_targetIntegrated
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Common-neighbor rows rule out minimal cleared failures through the
integrated target route. -/
theorem no_minimalClearedFailure_via_targetIntegrated
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  TargetIntegratedMatrixW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Common-neighbor rows clear the pipeline through the integrated target
route. -/
theorem pipelineCleared_via_targetIntegrated
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    PipelineCleared :=
  TargetIntegratedMatrixW11.pipelineCleared_of_commonNeighborFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Conditional target projection through the integrated target route. -/
theorem targetLowerBoundEightThirtyOne_via_targetIntegrated
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix
    M.toBrokenLatticeFieldMatrix

/-- Conditional target projection through the target-facing common-neighbor
route. -/
theorem targetLowerBoundEightThirtyOne_via_k23Target
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
    M.toK23TargetMatrix

/-- Conditional target projection through the final broken-lattice ledger. -/
theorem targetLowerBoundEightThirtyOne_via_brokenLatticeFinal
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  BrokenLatticeFinalIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix
    M.toBrokenLatticeFieldMatrix

end CommonNeighborFinalGeometryMatrix

/-! ## Explicit field-package ledger -/

/-- The explicit field-package surfaces owned by this aggregate. -/
structure ExplicitGeometryFieldLedger : Type (u + 2) where
  directPointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : IsMinimalClearedFailure C), Type (u + 1)
  k23Pointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : IsMinimalClearedFailure C), Type (u + 1)
  commonNeighborPointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (_hmin : IsMinimalClearedFailure C), Type (u + 1)
  directUniform : Type (u + 1)
  k23Uniform : Type (u + 1)
  commonNeighborUniform : Type (u + 1)

/-- The direct, K23, and common-neighbor geometry package shapes used below. -/
def explicitGeometryFieldLedger : ExplicitGeometryFieldLedger.{u} where
  directPointwise := fun C hmin =>
    DirectFinalGeometryFields.{u} C hmin
  k23Pointwise := fun C hmin =>
    K23FinalGeometryFields.{u} C hmin
  commonNeighborPointwise := fun C hmin =>
    CommonNeighborFinalGeometryFields.{u} C hmin
  directUniform := DirectFinalGeometryMatrix.{u}
  k23Uniform := K23FinalGeometryMatrix.{u}
  commonNeighborUniform := CommonNeighborFinalGeometryMatrix.{u}

/-- A caller-supplied bundle of all three uniform geometry alternatives. -/
structure ExplicitGeometryMatrices : Type (u + 1) where
  direct : DirectFinalGeometryMatrix.{u}
  k23 : K23FinalGeometryMatrix.{u}
  commonNeighbor : CommonNeighborFinalGeometryMatrix.{u}

/-! ## Conditional route rows -/

def directGeometryTargetRoute :
    EliminatorTargetRoute (DirectFinalGeometryMatrix.{u}) where
  eliminator :=
    DirectFinalGeometryMatrix.minimalClearedFailureEliminator_via_geometryTarget
  noMinimal :=
    DirectFinalGeometryMatrix.no_minimalClearedFailure_via_geometryTarget
  pipeline := DirectFinalGeometryMatrix.pipelineCleared_via_geometryTarget
  target :=
    DirectFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_geometryTarget

def directGeometryIntegratedRoute :
    TargetRoute (DirectFinalGeometryMatrix.{u}) where
  noMinimal := fun M =>
    GeometryIntegratedW11.no_minimalClearedFailure_of_directGeometryMatrix
      M.toGeometryIntegratedMatrix
  pipeline := fun M =>
    GeometryIntegratedW11.pipelineCleared_of_directGeometryMatrix
      M.toGeometryIntegratedMatrix
  target := DirectFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_geometryIntegrated

def directTargetIntegratedRoute :
    EliminatorTargetRoute (DirectFinalGeometryMatrix.{u}) where
  eliminator :=
    DirectFinalGeometryMatrix.minimalClearedFailureEliminator_via_targetIntegrated
  noMinimal :=
    DirectFinalGeometryMatrix.no_minimalClearedFailure_via_targetIntegrated
  pipeline := DirectFinalGeometryMatrix.pipelineCleared_via_targetIntegrated
  target :=
    DirectFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_targetIntegrated

def directBrokenLatticeFinalRoute :
    EliminatorTargetRoute (DirectFinalGeometryMatrix.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.minimalClearedFailureEliminator_of_directFieldMatrix
      M.toBrokenLatticeFieldMatrix
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.no_minimalClearedFailure_of_directFieldMatrix
      M.toBrokenLatticeFieldMatrix
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.pipelineCleared_of_directFieldMatrix
      M.toBrokenLatticeFieldMatrix
  target :=
    DirectFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_brokenLatticeFinal

def k23GeometryTargetRoute :
    EliminatorTargetRoute (K23FinalGeometryMatrix.{u}) where
  eliminator :=
    K23FinalGeometryMatrix.minimalClearedFailureEliminator_via_geometryTarget
  noMinimal := K23FinalGeometryMatrix.no_minimalClearedFailure_via_geometryTarget
  pipeline := K23FinalGeometryMatrix.pipelineCleared_via_geometryTarget
  target := K23FinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_geometryTarget

def k23GeometryIntegratedRoute :
    TargetRoute (K23FinalGeometryMatrix.{u}) where
  noMinimal := fun M =>
    GeometryIntegratedW11.no_minimalClearedFailure_of_k23GeometryMatrix
      M.toGeometryIntegratedMatrix
  pipeline := fun M =>
    GeometryIntegratedW11.pipelineCleared_of_k23GeometryMatrix
      M.toGeometryIntegratedMatrix
  target := K23FinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_geometryIntegrated

def k23TargetIntegratedRoute :
    EliminatorTargetRoute (K23FinalGeometryMatrix.{u}) where
  eliminator :=
    K23FinalGeometryMatrix.minimalClearedFailureEliminator_via_targetIntegrated
  noMinimal := K23FinalGeometryMatrix.no_minimalClearedFailure_via_targetIntegrated
  pipeline := K23FinalGeometryMatrix.pipelineCleared_via_targetIntegrated
  target := K23FinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_targetIntegrated

def k23TargetRoute :
    EliminatorTargetRoute (K23FinalGeometryMatrix.{u}) where
  eliminator := fun M =>
    K23TargetIntegratedW11.minimalClearedFailureEliminator_of_k23TargetMatrix
      M.toK23TargetMatrix
  noMinimal := fun M =>
    K23TargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
      M.toK23TargetMatrix
  pipeline := fun M =>
    K23TargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
      M.toK23TargetMatrix
  target := K23FinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_k23Target

def k23BrokenLatticeFinalRoute :
    EliminatorTargetRoute (K23FinalGeometryMatrix.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.minimalClearedFailureEliminator_of_k23FieldMatrix
      M.toBrokenLatticeFieldMatrix
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.no_minimalClearedFailure_of_k23FieldMatrix
      M.toBrokenLatticeFieldMatrix
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.pipelineCleared_of_k23FieldMatrix
      M.toBrokenLatticeFieldMatrix
  target :=
    K23FinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_brokenLatticeFinal

def commonNeighborGeometryTargetRoute :
    EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u}) where
  eliminator :=
    CommonNeighborFinalGeometryMatrix.minimalClearedFailureEliminator_via_geometryTarget
  noMinimal :=
    CommonNeighborFinalGeometryMatrix.no_minimalClearedFailure_via_geometryTarget
  pipeline :=
    CommonNeighborFinalGeometryMatrix.pipelineCleared_via_geometryTarget
  target :=
    CommonNeighborFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_geometryTarget

def commonNeighborGeometryIntegratedRoute :
    TargetRoute (CommonNeighborFinalGeometryMatrix.{u}) where
  noMinimal := fun M =>
    GeometryIntegratedW11.no_minimalClearedFailure_of_commonNeighborGeometryMatrix
      M.toGeometryIntegratedMatrix
  pipeline := fun M =>
    GeometryIntegratedW11.pipelineCleared_of_commonNeighborGeometryMatrix
      M.toGeometryIntegratedMatrix
  target :=
    CommonNeighborFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_geometryIntegrated

def commonNeighborTargetIntegratedRoute :
    EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u}) where
  eliminator :=
    CommonNeighborFinalGeometryMatrix.minimalClearedFailureEliminator_via_targetIntegrated
  noMinimal :=
    CommonNeighborFinalGeometryMatrix.no_minimalClearedFailure_via_targetIntegrated
  pipeline :=
    CommonNeighborFinalGeometryMatrix.pipelineCleared_via_targetIntegrated
  target :=
    CommonNeighborFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_targetIntegrated

def commonNeighborTargetRoute :
    EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u}) where
  eliminator := fun M =>
    K23TargetIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
      M.toK23TargetMatrix
  noMinimal := fun M =>
    K23TargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
      M.toK23TargetMatrix
  pipeline := fun M =>
    K23TargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
      M.toK23TargetMatrix
  target :=
    CommonNeighborFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_k23Target

def commonNeighborBrokenLatticeFinalRoute :
    EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
      M.toBrokenLatticeFieldMatrix
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
      M.toBrokenLatticeFieldMatrix
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.pipelineCleared_of_commonNeighborFieldMatrix
      M.toBrokenLatticeFieldMatrix
  target :=
    CommonNeighborFinalGeometryMatrix.targetLowerBoundEightThirtyOne_via_brokenLatticeFinal

/-! ## Aggregate route matrix -/

structure DirectTargetRoutes : Type (u + 1) where
  geometryTarget : EliminatorTargetRoute (DirectFinalGeometryMatrix.{u})
  geometryIntegrated : TargetRoute (DirectFinalGeometryMatrix.{u})
  targetIntegrated : EliminatorTargetRoute (DirectFinalGeometryMatrix.{u})
  brokenLatticeFinal : EliminatorTargetRoute (DirectFinalGeometryMatrix.{u})

def directTargetRoutes : DirectTargetRoutes.{u} where
  geometryTarget := directGeometryTargetRoute
  geometryIntegrated := directGeometryIntegratedRoute
  targetIntegrated := directTargetIntegratedRoute
  brokenLatticeFinal := directBrokenLatticeFinalRoute

structure K23TargetRoutes : Type (u + 1) where
  geometryTarget : EliminatorTargetRoute (K23FinalGeometryMatrix.{u})
  geometryIntegrated : TargetRoute (K23FinalGeometryMatrix.{u})
  targetIntegrated : EliminatorTargetRoute (K23FinalGeometryMatrix.{u})
  k23Target : EliminatorTargetRoute (K23FinalGeometryMatrix.{u})
  brokenLatticeFinal : EliminatorTargetRoute (K23FinalGeometryMatrix.{u})

def k23TargetRoutes : K23TargetRoutes.{u} where
  geometryTarget := k23GeometryTargetRoute
  geometryIntegrated := k23GeometryIntegratedRoute
  targetIntegrated := k23TargetIntegratedRoute
  k23Target := k23TargetRoute
  brokenLatticeFinal := k23BrokenLatticeFinalRoute

structure CommonNeighborTargetRoutes : Type (u + 1) where
  geometryTarget :
    EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u})
  geometryIntegrated : TargetRoute (CommonNeighborFinalGeometryMatrix.{u})
  targetIntegrated :
    EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u})
  k23Target : EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u})
  brokenLatticeFinal :
    EliminatorTargetRoute (CommonNeighborFinalGeometryMatrix.{u})

def commonNeighborTargetRoutes : CommonNeighborTargetRoutes.{u} where
  geometryTarget := commonNeighborGeometryTargetRoute
  geometryIntegrated := commonNeighborGeometryIntegratedRoute
  targetIntegrated := commonNeighborTargetIntegratedRoute
  k23Target := commonNeighborTargetRoute
  brokenLatticeFinal := commonNeighborBrokenLatticeFinalRoute

/-- All conditional Swanepoel target routes exposed by the aggregate. -/
structure ConditionalSwanepoelTargetRoutes : Type (u + 1) where
  direct : DirectTargetRoutes.{u}
  k23 : K23TargetRoutes.{u}
  commonNeighbor : CommonNeighborTargetRoutes.{u}

def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} where
  direct := directTargetRoutes
  k23 := k23TargetRoutes
  commonNeighbor := commonNeighborTargetRoutes

/-- Imported W11 ledgers gathered by the aggregate. -/
structure ImportedLedgers : Type (u + 1) where
  geometryTarget : GeometryTargetIntegratedW11.Matrix.{u}
  geometryIntegrated : GeometryIntegratedW11.Matrix.{u}
  targetIntegrated : TargetIntegratedMatrixW11.Matrix.{u}
  k23Target : K23TargetIntegratedW11.Matrix.{u}
  brokenLatticeFinal :
    Nonempty BrokenLatticeFinalIntegratedW11.Matrix.{u}

def importedLedgers : ImportedLedgers.{u} where
  geometryTarget := GeometryTargetIntegratedW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  k23Target := K23TargetIntegratedW11.matrix
  brokenLatticeFinal := BrokenLatticeFinalIntegratedW11.matrix_nonempty

/-- Final W11 geometry aggregate matrix.

The matrix records checked adapters and route rows.  It does not supply any
uniform direct, K23, or common-neighbor geometry matrix. -/
structure Matrix : Type (u + 2) where
  fieldPackages : ExplicitGeometryFieldLedger.{u}
  imported : ImportedLedgers.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked aggregate matrix of conditional W11 geometry routes. -/
def matrix : Matrix.{u} where
  fieldPackages := explicitGeometryFieldLedger
  imported := importedLedgers
  routes := conditionalSwanepoelTargetRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_directFinalGeometryMatrix
    (M : DirectFinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.routes.direct.targetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_directFinalGeometryMatrix
    (M : DirectFinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.routes.direct.targetIntegrated.noMinimal M

theorem pipelineCleared_of_directFinalGeometryMatrix
    (M : DirectFinalGeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.routes.direct.targetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.targetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix_via_geometryTarget
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.geometryTarget.target M

theorem
    targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix_via_geometryIntegrated
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.geometryIntegrated.target M

theorem
    targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix_via_brokenLatticeFinal
    (M : DirectFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.brokenLatticeFinal.target M

theorem minimalClearedFailureEliminator_of_k23FinalGeometryMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.routes.k23.targetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_k23FinalGeometryMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.routes.k23.targetIntegrated.noMinimal M

theorem pipelineCleared_of_k23FinalGeometryMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.routes.k23.targetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.targetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix_via_geometryTarget
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.geometryTarget.target M

theorem
    targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix_via_geometryIntegrated
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.geometryIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix_via_k23Target
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.k23Target.target M

theorem
    targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix_via_brokenLatticeFinal
    (M : K23FinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.brokenLatticeFinal.target M

theorem minimalClearedFailureEliminator_of_commonNeighborFinalGeometryMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_commonNeighborFinalGeometryMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.noMinimal M

theorem pipelineCleared_of_commonNeighborFinalGeometryMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix_via_geometryTarget
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.geometryTarget.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix_via_geometryIntegrated
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.geometryIntegrated.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix_via_k23Target
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.k23Target.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix_via_brokenLatticeFinal
    (M : CommonNeighborFinalGeometryMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.brokenLatticeFinal.target M

theorem targetLowerBoundEightThirtyOne_of_explicitGeometryMatrices_via_direct
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_directFinalGeometryMatrix M.direct

theorem targetLowerBoundEightThirtyOne_of_explicitGeometryMatrices_via_k23
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_k23FinalGeometryMatrix M.k23

theorem
    targetLowerBoundEightThirtyOne_of_explicitGeometryMatrices_via_commonNeighbor
    (M : ExplicitGeometryMatrices.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_commonNeighborFinalGeometryMatrix
    M.commonNeighbor

end

end GeometryFinalIntegratedW11
end Swanepoel
end ErdosProblems1066
