import ErdosProblems1066.Swanepoel.BrokenLatticeTargetIntegratedW11
import ErdosProblems1066.Swanepoel.K23TargetIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryTargetIntegratedW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

/-!
# Final W11 broken-lattice aggregate matrix

This module collects the checked W11 broken-lattice source, target, K23, and
geometry-facing ledgers into one aggregate.  The direct, K23, and
common-neighbor field packages stay explicit: every target projection below
requires a caller-supplied uniform matrix of those fields.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BrokenLatticeFinalIntegratedW11

open MinimalGraphFacts

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

abbrev DirectFieldPackage
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  BrokenLatticeIntegratedW11.DirectFieldPackage C hmin

abbrev K23FieldPackage
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  BrokenLatticeIntegratedW11.K23FieldPackage C hmin

abbrev CommonNeighborFieldPackage
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  BrokenLatticeIntegratedW11.CommonNeighborFieldPackage C hmin

abbrev DirectFieldMatrix :=
  BrokenLatticeIntegratedW11.DirectFieldMatrix

abbrev K23FieldMatrix :=
  BrokenLatticeIntegratedW11.K23FieldMatrix

abbrev CommonNeighborFieldMatrix :=
  BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix

/-! ## Shared route shapes -/

/-- A conditional Swanepoel target route from an explicit input package. -/
structure TargetRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetRoute

/-- Reuse a checked target-closure projection row. -/
def ofTargetClosureRow
    {alpha : Type v}
    (R : TargetClosureMatrixW11.TargetProjectionRow alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end TargetRoute

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

/-! ## Pointwise adapters from broken-lattice fields -/

namespace DirectFieldPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View direct broken-lattice fields as geometry-target direct fields. -/
def toGeometryTargetFields
    (R : DirectFieldPackage.{u} C hmin) :
    GeometryTargetIntegratedW11.DirectTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  noStartNoEarly := R.noStartNoEarly

@[simp]
theorem toGeometryTargetFields_source
    (R : DirectFieldPackage.{u} C hmin) :
    (toGeometryTargetFields R).source = R.source :=
  rfl

end DirectFieldPackage

namespace K23FieldPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View K23 broken-lattice fields as geometry-target K23 fields. -/
def toGeometryTargetFields
    (R : K23FieldPackage.{u} C hmin) :
    GeometryTargetIntegratedW11.K23TargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23NoEarly := R.k23NoEarly

/-- View K23 broken-lattice fields as K23-target obstruction fields. -/
def toK23TargetFields
    (R : K23FieldPackage.{u} C hmin) :
    K23TargetIntegratedW11.K23TargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  k23Obstruction := R.k23NoEarly.k23Obstruction

@[simp]
theorem toGeometryTargetFields_source
    (R : K23FieldPackage.{u} C hmin) :
    (toGeometryTargetFields R).source = R.source :=
  rfl

@[simp]
theorem toK23TargetFields_source
    (R : K23FieldPackage.{u} C hmin) :
    (toK23TargetFields R).source = R.source :=
  rfl

end K23FieldPackage

namespace CommonNeighborFieldPackage

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- View common-neighbor broken-lattice fields as geometry-target fields. -/
def toGeometryTargetFields
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    GeometryTargetIntegratedW11.CommonNeighborTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborNoEarly := R.commonNeighborNoEarly

/-- View common-neighbor broken-lattice fields as K23-target obstruction
fields. -/
def toK23TargetFields
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    K23TargetIntegratedW11.CommonNeighborTargetFields.{u} C hmin where
  source := R.source
  containment := R.containment
  commonNeighborObstruction :=
    R.commonNeighborNoEarly.commonNeighborObstruction

@[simp]
theorem toGeometryTargetFields_source
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    (toGeometryTargetFields R).source = R.source :=
  rfl

@[simp]
theorem toK23TargetFields_source
    (R : CommonNeighborFieldPackage.{u} C hmin) :
    (toK23TargetFields R).source = R.source :=
  rfl

end CommonNeighborFieldPackage

/-! ## Uniform adapters from broken-lattice matrices -/

def directFieldMatrixToGeometryTargetMatrix
    (M : DirectFieldMatrix.{u}) :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u} where
  row := fun C hmin =>
    DirectFieldPackage.toGeometryTargetFields (M.row C hmin)

def k23FieldMatrixToGeometryTargetMatrix
    (M : K23FieldMatrix.{u}) :
    GeometryTargetIntegratedW11.K23TargetMatrix.{u} where
  row := fun C hmin =>
    K23FieldPackage.toGeometryTargetFields (M.row C hmin)

def k23FieldMatrixToK23TargetMatrix
    (M : K23FieldMatrix.{u}) :
    K23TargetIntegratedW11.K23TargetMatrix.{u} where
  row := fun C hmin =>
    K23FieldPackage.toK23TargetFields (M.row C hmin)

def commonNeighborFieldMatrixToGeometryTargetMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u} where
  row := fun C hmin =>
    CommonNeighborFieldPackage.toGeometryTargetFields (M.row C hmin)

def commonNeighborFieldMatrixToK23TargetMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u} where
  row := fun C hmin =>
    CommonNeighborFieldPackage.toK23TargetFields (M.row C hmin)

/-! ## Explicit package ledger -/

/-- The explicit field-package surfaces owned by this aggregate. -/
structure ExplicitFieldPackageLedger : Type (u + 2) where
  directPointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  k23Pointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  commonNeighborPointwise :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C), Type (u + 1)
  directUniform : Type (u + 1)
  k23Uniform : Type (u + 1)
  commonNeighborUniform : Type (u + 1)

/-- The direct, K23, and common-neighbor package shapes used below. -/
def explicitFieldPackageLedger : ExplicitFieldPackageLedger.{u} where
  directPointwise := fun C hmin => DirectFieldPackage.{u} C hmin
  k23Pointwise := fun C hmin => K23FieldPackage.{u} C hmin
  commonNeighborPointwise := fun C hmin =>
    CommonNeighborFieldPackage.{u} C hmin
  directUniform := DirectFieldMatrix.{u}
  k23Uniform := K23FieldMatrix.{u}
  commonNeighborUniform := CommonNeighborFieldMatrix.{u}

/-- A caller-supplied bundle of all three uniform broken-lattice routes. -/
structure ExplicitFieldMatrices : Type (u + 1) where
  direct : DirectFieldMatrix.{u}
  k23 : K23FieldMatrix.{u}
  commonNeighbor : CommonNeighborFieldMatrix.{u}

/-! ## Conditional route rows -/

def directTargetIntegratedRoute :
    EliminatorTargetRoute (DirectFieldMatrix.{u}) where
  eliminator := TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_directFieldMatrix
  noMinimal := TargetIntegratedMatrixW11.no_minimalClearedFailure_of_directFieldMatrix
  pipeline := TargetIntegratedMatrixW11.pipelineCleared_of_directFieldMatrix
  target := TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix

def directBrokenLatticeTargetRoute :
    TargetRoute (DirectFieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.directFieldMatrixViaBrokenLatticeRow :
      TargetClosureMatrixW11.TargetProjectionRow (DirectFieldMatrix.{u}))

def directE22E23TargetRoute :
    TargetRoute (DirectFieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.directFieldMatrixViaE22E23Row :
      TargetClosureMatrixW11.TargetProjectionRow (DirectFieldMatrix.{u}))

def directSourceGeometryTargetRoute :
    TargetRoute (DirectFieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.directFieldMatrixViaSourceGeometryRow :
      TargetClosureMatrixW11.TargetProjectionRow (DirectFieldMatrix.{u}))

def directGeometryTargetRoute :
    EliminatorTargetRoute (DirectFieldMatrix.{u}) where
  eliminator := fun M =>
    GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_directTargetMatrix
      (directFieldMatrixToGeometryTargetMatrix M)
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_directTargetMatrix
      (directFieldMatrixToGeometryTargetMatrix M)
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_directTargetMatrix
      (directFieldMatrixToGeometryTargetMatrix M)
  target := fun M =>
    GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_directTargetMatrix
      (directFieldMatrixToGeometryTargetMatrix M)

def k23TargetIntegratedRoute :
    EliminatorTargetRoute (K23FieldMatrix.{u}) where
  eliminator := TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_k23FieldMatrix
  noMinimal := TargetIntegratedMatrixW11.no_minimalClearedFailure_of_k23FieldMatrix
  pipeline := TargetIntegratedMatrixW11.pipelineCleared_of_k23FieldMatrix
  target := TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix

def k23BrokenLatticeTargetRoute :
    TargetRoute (K23FieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.k23FieldMatrixViaBrokenLatticeRow :
      TargetClosureMatrixW11.TargetProjectionRow (K23FieldMatrix.{u}))

def k23E22E23TargetRoute :
    TargetRoute (K23FieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.k23FieldMatrixViaE22E23Row :
      TargetClosureMatrixW11.TargetProjectionRow (K23FieldMatrix.{u}))

def k23SourceGeometryTargetRoute :
    TargetRoute (K23FieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.k23FieldMatrixViaSourceGeometryRow :
      TargetClosureMatrixW11.TargetProjectionRow (K23FieldMatrix.{u}))

def k23ObstructionTargetRoute :
    TargetRoute (K23FieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.k23FieldMatrixViaObstructionRow :
      TargetClosureMatrixW11.TargetProjectionRow (K23FieldMatrix.{u}))

def k23GeometryTargetRoute :
    EliminatorTargetRoute (K23FieldMatrix.{u}) where
  eliminator := fun M =>
    GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_k23TargetMatrix
      (k23FieldMatrixToGeometryTargetMatrix M)
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
      (k23FieldMatrixToGeometryTargetMatrix M)
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
      (k23FieldMatrixToGeometryTargetMatrix M)
  target := fun M =>
    GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
      (k23FieldMatrixToGeometryTargetMatrix M)

def k23ObstructionIntegratedTargetRoute :
    EliminatorTargetRoute (K23FieldMatrix.{u}) where
  eliminator := fun M =>
    K23TargetIntegratedW11.minimalClearedFailureEliminator_of_k23TargetMatrix
      (k23FieldMatrixToK23TargetMatrix M)
  noMinimal := fun M =>
    K23TargetIntegratedW11.no_minimalClearedFailure_of_k23TargetMatrix
      (k23FieldMatrixToK23TargetMatrix M)
  pipeline := fun M =>
    K23TargetIntegratedW11.pipelineCleared_of_k23TargetMatrix
      (k23FieldMatrixToK23TargetMatrix M)
  target := fun M =>
    K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_k23TargetMatrix
      (k23FieldMatrixToK23TargetMatrix M)

def commonNeighborTargetIntegratedRoute :
    EliminatorTargetRoute (CommonNeighborFieldMatrix.{u}) where
  eliminator := TargetIntegratedMatrixW11.minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
  noMinimal := TargetIntegratedMatrixW11.no_minimalClearedFailure_of_commonNeighborFieldMatrix
  pipeline := TargetIntegratedMatrixW11.pipelineCleared_of_commonNeighborFieldMatrix
  target := TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix

def commonNeighborBrokenLatticeTargetRoute :
    TargetRoute (CommonNeighborFieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.commonNeighborFieldMatrixViaBrokenLatticeRow :
      TargetClosureMatrixW11.TargetProjectionRow
        (CommonNeighborFieldMatrix.{u}))

def commonNeighborE22E23TargetRoute :
    TargetRoute (CommonNeighborFieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.commonNeighborFieldMatrixViaE22E23Row :
      TargetClosureMatrixW11.TargetProjectionRow
        (CommonNeighborFieldMatrix.{u}))

def commonNeighborSourceGeometryTargetRoute :
    TargetRoute (CommonNeighborFieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.commonNeighborFieldMatrixViaSourceGeometryRow :
      TargetClosureMatrixW11.TargetProjectionRow
        (CommonNeighborFieldMatrix.{u}))

def commonNeighborObstructionTargetRoute :
    TargetRoute (CommonNeighborFieldMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    (BrokenLatticeTargetIntegratedW11.commonNeighborFieldMatrixViaObstructionRow :
      TargetClosureMatrixW11.TargetProjectionRow
        (CommonNeighborFieldMatrix.{u}))

def commonNeighborGeometryTargetRoute :
    EliminatorTargetRoute (CommonNeighborFieldMatrix.{u}) where
  eliminator := fun M =>
    GeometryTargetIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToGeometryTargetMatrix M)
  noMinimal := fun M =>
    GeometryTargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToGeometryTargetMatrix M)
  pipeline := fun M =>
    GeometryTargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToGeometryTargetMatrix M)
  target := fun M =>
    GeometryTargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToGeometryTargetMatrix M)

def commonNeighborObstructionIntegratedTargetRoute :
    EliminatorTargetRoute (CommonNeighborFieldMatrix.{u}) where
  eliminator := fun M =>
    K23TargetIntegratedW11.minimalClearedFailureEliminator_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToK23TargetMatrix M)
  noMinimal := fun M =>
    K23TargetIntegratedW11.no_minimalClearedFailure_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToK23TargetMatrix M)
  pipeline := fun M =>
    K23TargetIntegratedW11.pipelineCleared_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToK23TargetMatrix M)
  target := fun M =>
    K23TargetIntegratedW11.targetLowerBoundEightThirtyOne_of_commonNeighborTargetMatrix
      (commonNeighborFieldMatrixToK23TargetMatrix M)

/-! ## Aggregate route matrix -/

structure DirectTargetRoutes : Type (u + 1) where
  targetIntegrated : EliminatorTargetRoute (DirectFieldMatrix.{u})
  brokenLattice : TargetRoute (DirectFieldMatrix.{u})
  e22e23 : TargetRoute (DirectFieldMatrix.{u})
  sourceGeometry : TargetRoute (DirectFieldMatrix.{u})
  geometryTarget : EliminatorTargetRoute (DirectFieldMatrix.{u})

def directTargetRoutes : DirectTargetRoutes.{u} where
  targetIntegrated := directTargetIntegratedRoute
  brokenLattice := directBrokenLatticeTargetRoute
  e22e23 := directE22E23TargetRoute
  sourceGeometry := directSourceGeometryTargetRoute
  geometryTarget := directGeometryTargetRoute

structure K23TargetRoutes : Type (u + 1) where
  targetIntegrated : EliminatorTargetRoute (K23FieldMatrix.{u})
  brokenLattice : TargetRoute (K23FieldMatrix.{u})
  e22e23 : TargetRoute (K23FieldMatrix.{u})
  sourceGeometry : TargetRoute (K23FieldMatrix.{u})
  obstruction : TargetRoute (K23FieldMatrix.{u})
  geometryTarget : EliminatorTargetRoute (K23FieldMatrix.{u})
  obstructionIntegrated :
    EliminatorTargetRoute (K23FieldMatrix.{u})

def k23TargetRoutes : K23TargetRoutes.{u} where
  targetIntegrated := k23TargetIntegratedRoute
  brokenLattice := k23BrokenLatticeTargetRoute
  e22e23 := k23E22E23TargetRoute
  sourceGeometry := k23SourceGeometryTargetRoute
  obstruction := k23ObstructionTargetRoute
  geometryTarget := k23GeometryTargetRoute
  obstructionIntegrated := k23ObstructionIntegratedTargetRoute

structure CommonNeighborTargetRoutes : Type (u + 1) where
  targetIntegrated :
    EliminatorTargetRoute (CommonNeighborFieldMatrix.{u})
  brokenLattice : TargetRoute (CommonNeighborFieldMatrix.{u})
  e22e23 : TargetRoute (CommonNeighborFieldMatrix.{u})
  sourceGeometry : TargetRoute (CommonNeighborFieldMatrix.{u})
  obstruction : TargetRoute (CommonNeighborFieldMatrix.{u})
  geometryTarget :
    EliminatorTargetRoute (CommonNeighborFieldMatrix.{u})
  obstructionIntegrated :
    EliminatorTargetRoute (CommonNeighborFieldMatrix.{u})

def commonNeighborTargetRoutes : CommonNeighborTargetRoutes.{u} where
  targetIntegrated := commonNeighborTargetIntegratedRoute
  brokenLattice := commonNeighborBrokenLatticeTargetRoute
  e22e23 := commonNeighborE22E23TargetRoute
  sourceGeometry := commonNeighborSourceGeometryTargetRoute
  obstruction := commonNeighborObstructionTargetRoute
  geometryTarget := commonNeighborGeometryTargetRoute
  obstructionIntegrated := commonNeighborObstructionIntegratedTargetRoute

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
  targetIntegrated : TargetIntegratedMatrixW11.Matrix.{u}
  brokenLatticeIntegrated : BrokenLatticeIntegratedW11.Matrix.{u}
  brokenLatticeTarget : BrokenLatticeTargetIntegratedW11.Matrix.{u}
  geometryTarget : GeometryTargetIntegratedW11.Matrix.{u}
  k23Target : K23TargetIntegratedW11.Matrix.{u}
  geometryIntegrated : GeometryIntegratedW11.Matrix.{u}
  k23Integrated : K23IntegratedMatrixW11.Matrix.{u}
  targetClosure : TargetClosureMatrixW11.Matrix.{u}

def importedLedgers : ImportedLedgers.{u} where
  targetIntegrated := TargetIntegratedMatrixW11.matrix
  brokenLatticeIntegrated := BrokenLatticeIntegratedW11.matrix
  brokenLatticeTarget := BrokenLatticeTargetIntegratedW11.matrix
  geometryTarget := GeometryTargetIntegratedW11.matrix
  k23Target := K23TargetIntegratedW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix
  k23Integrated := K23IntegratedMatrixW11.matrix
  targetClosure := TargetClosureMatrixW11.matrix

/-- Final W11 broken-lattice aggregate matrix.

The matrix records checked adapters and route rows.  It does not construct
any uniform direct, K23, or common-neighbor field matrix. -/
structure Matrix : Type (u + 2) where
  fieldPackages : ExplicitFieldPackageLedger.{u}
  imported : ImportedLedgers.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked aggregate matrix of conditional W11 broken-lattice routes. -/
def matrix : Matrix.{u} where
  fieldPackages := explicitFieldPackageLedger
  imported := importedLedgers
  routes := conditionalSwanepoelTargetRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem minimalClearedFailureEliminator_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.routes.direct.targetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.routes.direct.targetIntegrated.noMinimal M

theorem pipelineCleared_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.routes.direct.targetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_directFieldMatrix
    (M : DirectFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.targetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_directFieldMatrix_via_brokenLattice
    (M : DirectFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.brokenLattice.target M

theorem targetLowerBoundEightThirtyOne_of_directFieldMatrix_via_e22e23
    (M : DirectFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.e22e23.target M

theorem targetLowerBoundEightThirtyOne_of_directFieldMatrix_via_sourceGeometry
    (M : DirectFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.sourceGeometry.target M

theorem targetLowerBoundEightThirtyOne_of_directFieldMatrix_via_geometryTarget
    (M : DirectFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.direct.geometryTarget.target M

theorem minimalClearedFailureEliminator_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.routes.k23.targetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.routes.k23.targetIntegrated.noMinimal M

theorem pipelineCleared_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.routes.k23.targetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.targetIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix_via_brokenLattice
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.brokenLattice.target M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix_via_e22e23
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.e22e23.target M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix_via_sourceGeometry
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.sourceGeometry.target M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix_via_obstruction
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.obstruction.target M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix_via_geometryTarget
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.geometryTarget.target M

theorem targetLowerBoundEightThirtyOne_of_k23FieldMatrix_via_k23Target
    (M : K23FieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.k23.obstructionIntegrated.target M

theorem minimalClearedFailureEliminator_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureEliminator :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.eliminator M

theorem no_minimalClearedFailure_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    MinimalFailureExclusion :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.noMinimal M

theorem pipelineCleared_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    PipelineCleared :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.pipeline M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.targetIntegrated.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix_via_brokenLattice
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.brokenLattice.target M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix_via_e22e23
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.e22e23.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix_via_sourceGeometry
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.sourceGeometry.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix_via_obstruction
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.obstruction.target M

theorem
    targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix_via_geometryTarget
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.geometryTarget.target M

theorem targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix_via_k23Target
    (M : CommonNeighborFieldMatrix.{u}) :
    Target :=
  matrix.{u}.routes.commonNeighbor.obstructionIntegrated.target M

theorem targetLowerBoundEightThirtyOne_of_explicitFieldMatrices_via_direct
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_directFieldMatrix M.direct

theorem targetLowerBoundEightThirtyOne_of_explicitFieldMatrices_via_k23
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_k23FieldMatrix M.k23

theorem
    targetLowerBoundEightThirtyOne_of_explicitFieldMatrices_via_commonNeighbor
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  targetLowerBoundEightThirtyOne_of_commonNeighborFieldMatrix M.commonNeighbor

end

end BrokenLatticeFinalIntegratedW11
end Swanepoel
end ErdosProblems1066
