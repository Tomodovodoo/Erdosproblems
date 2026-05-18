import ErdosProblems1066.Swanepoel.K23FinalIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelW11ConsistencyMatrix

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 K23, common-neighbor, and broken-lattice consistency matrix

This file is an additive consistency ledger for the checked W11 final modules.
It keeps the direct broken-lattice fields explicit and ties the K23 and
common-neighbor broken-lattice matrices to the shared final
K23/common-neighbor aggregate matrix by projection.

Every Swanepoel target route below remains conditional on caller-supplied
field matrices.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23BrokenLatticeFinalW11

universe u v

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev MinimalFailureExclusion : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureExclusion

abbrev PipelineCleared : Prop :=
  TargetIntegratedMatrixW11.PipelineCleared

abbrev MinimalFailureEliminator : Prop :=
  TargetIntegratedMatrixW11.MinimalFailureEliminator

abbrev DirectFieldMatrix :=
  BrokenLatticeFinalIntegratedW11.DirectFieldMatrix

abbrev K23FieldMatrix :=
  BrokenLatticeFinalIntegratedW11.K23FieldMatrix

abbrev CommonNeighborFieldMatrix :=
  BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix

abbrev K23CommonNeighborFinalMatrix :=
  K23FinalIntegratedW11.K23CommonNeighborFinalMatrix

/-! ## Shared route records -/

/-- A conditional Swanepoel target route from an explicit input package. -/
structure TargetRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetRoute

/-- Reuse a checked target-closure row. -/
def ofTargetClosureRow
    {alpha : Type v}
    (R : TargetClosureMatrixW11.TargetProjectionRow alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a checked integrated geometry row. -/
def ofGeometryProjectionRow
    {alpha : Type v}
    (R : GeometryIntegratedW11.GeometryProjectionRow.{u, v} alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a checked broken-lattice final route row. -/
def ofBrokenLatticeRoute
    {alpha : Type v}
    (R : BrokenLatticeFinalIntegratedW11.TargetRoute alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end TargetRoute

/-- A conditional Swanepoel target route that also exposes the pointwise
minimal-failure eliminator. -/
structure EliminatorTargetRoute (alpha : Type v) : Type v where
  eliminator : alpha -> MinimalFailureEliminator
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace EliminatorTargetRoute

/-- Forget the eliminator while retaining the target route. -/
def toTargetRoute
    {alpha : Type v}
    (R : EliminatorTargetRoute alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a route row from the target-integrated matrix. -/
def ofTargetIntegratedRoute
    {alpha : Type v}
    (R : TargetIntegratedMatrixW11.EliminatorTargetRoute alpha) :
    EliminatorTargetRoute alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a route row from the broken-lattice final matrix. -/
def ofBrokenLatticeRoute
    {alpha : Type v}
    (R : BrokenLatticeFinalIntegratedW11.EliminatorTargetRoute alpha) :
    EliminatorTargetRoute alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end EliminatorTargetRoute

/-! ## Explicit field matrices -/

/-- The caller-supplied field matrices used by the combined ledger.

The direct route is supplied as a broken-lattice field matrix.  The K23 and
common-neighbor broken-lattice routes are obtained from the same final
K23/common-neighbor aggregate matrix, keeping those two projections aligned. -/
structure ExplicitFieldMatrices : Type (u + 1) where
  direct : DirectFieldMatrix.{u}
  k23CommonNeighbor : K23CommonNeighborFinalMatrix.{u}

namespace ExplicitFieldMatrices

/-- The K23 broken-lattice field matrix selected by the aggregate row. -/
def k23BrokenLattice
    (M : ExplicitFieldMatrices.{u}) :
    K23FieldMatrix.{u} :=
  M.k23CommonNeighbor.toBrokenLatticeIntegratedK23FieldMatrix

/-- The common-neighbor broken-lattice field matrix selected by the
aggregate row. -/
def commonNeighborBrokenLattice
    (M : ExplicitFieldMatrices.{u}) :
    CommonNeighborFieldMatrix.{u} :=
  M.k23CommonNeighbor.toBrokenLatticeIntegratedCommonNeighborFieldMatrix

/-- The full broken-lattice explicit field bundle selected by the combined
input. -/
def toBrokenLatticeExplicitFieldMatrices
    (M : ExplicitFieldMatrices.{u}) :
    BrokenLatticeFinalIntegratedW11.ExplicitFieldMatrices.{u} where
  direct := M.direct
  k23 := M.k23BrokenLattice
  commonNeighbor := M.commonNeighborBrokenLattice

/-- The K23 target matrix selected by the aggregate row. -/
def k23Target
    (M : ExplicitFieldMatrices.{u}) :
    K23TargetIntegratedW11.K23TargetMatrix.{u} :=
  M.k23CommonNeighbor.toK23TargetMatrix

/-- The common-neighbor target matrix selected by the aggregate row. -/
def commonNeighborTarget
    (M : ExplicitFieldMatrices.{u}) :
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u} :=
  M.k23CommonNeighbor.toCommonNeighborTargetMatrix

/-- The K23 integrated geometry matrix selected by the aggregate row. -/
def k23Geometry
    (M : ExplicitFieldMatrices.{u}) :
    GeometryIntegratedW11.K23GeometryMatrix.{u} :=
  M.k23CommonNeighbor.toGeometryIntegratedK23GeometryMatrix

/-- The common-neighbor integrated geometry matrix selected by the aggregate
row. -/
def commonNeighborGeometry
    (M : ExplicitFieldMatrices.{u}) :
    GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u} :=
  M.k23CommonNeighbor.toGeometryIntegratedCommonNeighborGeometryMatrix

@[simp]
theorem toBrokenLatticeExplicitFieldMatrices_direct
    (M : ExplicitFieldMatrices.{u}) :
    M.toBrokenLatticeExplicitFieldMatrices.direct = M.direct :=
  rfl

@[simp]
theorem toBrokenLatticeExplicitFieldMatrices_k23
    (M : ExplicitFieldMatrices.{u}) :
    M.toBrokenLatticeExplicitFieldMatrices.k23 = M.k23BrokenLattice :=
  rfl

@[simp]
theorem toBrokenLatticeExplicitFieldMatrices_commonNeighbor
    (M : ExplicitFieldMatrices.{u}) :
    M.toBrokenLatticeExplicitFieldMatrices.commonNeighbor =
      M.commonNeighborBrokenLattice :=
  rfl

end ExplicitFieldMatrices

/-- Projection functions displaying every explicit matrix surface used by the
combined consistency ledger. -/
structure ExplicitFieldMatrixSurface : Type (u + 1) where
  direct :
    ExplicitFieldMatrices.{u} -> DirectFieldMatrix.{u}
  k23CommonNeighbor :
    ExplicitFieldMatrices.{u} -> K23CommonNeighborFinalMatrix.{u}
  k23BrokenLattice :
    ExplicitFieldMatrices.{u} -> K23FieldMatrix.{u}
  commonNeighborBrokenLattice :
    ExplicitFieldMatrices.{u} -> CommonNeighborFieldMatrix.{u}
  brokenLatticeBundle :
    ExplicitFieldMatrices.{u} ->
      BrokenLatticeFinalIntegratedW11.ExplicitFieldMatrices.{u}
  k23Target :
    ExplicitFieldMatrices.{u} ->
      K23TargetIntegratedW11.K23TargetMatrix.{u}
  commonNeighborTarget :
    ExplicitFieldMatrices.{u} ->
      K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  k23Geometry :
    ExplicitFieldMatrices.{u} ->
      GeometryIntegratedW11.K23GeometryMatrix.{u}
  commonNeighborGeometry :
    ExplicitFieldMatrices.{u} ->
      GeometryIntegratedW11.CommonNeighborGeometryMatrix.{u}

/-- The displayed field-matrix projections for the combined input package. -/
def explicitFieldMatrixSurface :
    ExplicitFieldMatrixSurface.{u} where
  direct := ExplicitFieldMatrices.direct
  k23CommonNeighbor := ExplicitFieldMatrices.k23CommonNeighbor
  k23BrokenLattice := ExplicitFieldMatrices.k23BrokenLattice
  commonNeighborBrokenLattice :=
    ExplicitFieldMatrices.commonNeighborBrokenLattice
  brokenLatticeBundle :=
    ExplicitFieldMatrices.toBrokenLatticeExplicitFieldMatrices
  k23Target := ExplicitFieldMatrices.k23Target
  commonNeighborTarget := ExplicitFieldMatrices.commonNeighborTarget
  k23Geometry := ExplicitFieldMatrices.k23Geometry
  commonNeighborGeometry := ExplicitFieldMatrices.commonNeighborGeometry

/-! ## K23/common-neighbor final route rows -/

/-- K23-selected route through the final K23/common-neighbor aggregate. -/
def k23FinalRoute :
    EliminatorTargetRoute (K23CommonNeighborFinalMatrix.{u}) :=
  EliminatorTargetRoute.ofTargetIntegratedRoute
    K23FinalIntegratedW11.k23FinalIntegratedRoute

/-- Common-neighbor-selected route through the final aggregate. -/
def commonNeighborFinalRoute :
    EliminatorTargetRoute (K23CommonNeighborFinalMatrix.{u}) :=
  EliminatorTargetRoute.ofTargetIntegratedRoute
    K23FinalIntegratedW11.commonNeighborFinalIntegratedRoute

/-- K23-selected target-closure route through the final aggregate. -/
def k23FinalTargetClosureRoute :
    TargetRoute (K23CommonNeighborFinalMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    K23FinalIntegratedW11.k23FinalTargetClosureRow

/-- Common-neighbor-selected target-closure route through the final
aggregate. -/
def commonNeighborFinalTargetClosureRoute :
    TargetRoute (K23CommonNeighborFinalMatrix.{u}) :=
  TargetRoute.ofTargetClosureRow
    K23FinalIntegratedW11.commonNeighborFinalTargetClosureRow

/-- K23-selected integrated-geometry route through the final aggregate. -/
def k23FinalGeometryRoute :
    TargetRoute (K23CommonNeighborFinalMatrix.{u}) :=
  TargetRoute.ofGeometryProjectionRow
    K23FinalIntegratedW11.k23FinalGeometryProjectionRow

/-- Common-neighbor-selected integrated-geometry route through the final
aggregate. -/
def commonNeighborFinalGeometryRoute :
    TargetRoute (K23CommonNeighborFinalMatrix.{u}) :=
  TargetRoute.ofGeometryProjectionRow
    K23FinalIntegratedW11.commonNeighborFinalGeometryProjectionRow

/-- Final K23/common-neighbor route ledger. -/
structure K23CommonNeighborRoutes : Type (u + 1) where
  k23 : EliminatorTargetRoute (K23CommonNeighborFinalMatrix.{u})
  commonNeighbor :
    EliminatorTargetRoute (K23CommonNeighborFinalMatrix.{u})
  k23TargetClosure :
    TargetRoute (K23CommonNeighborFinalMatrix.{u})
  commonNeighborTargetClosure :
    TargetRoute (K23CommonNeighborFinalMatrix.{u})
  k23Geometry :
    TargetRoute (K23CommonNeighborFinalMatrix.{u})
  commonNeighborGeometry :
    TargetRoute (K23CommonNeighborFinalMatrix.{u})

/-- Checked final K23/common-neighbor route ledger. -/
def k23CommonNeighborRoutes :
    K23CommonNeighborRoutes.{u} where
  k23 := k23FinalRoute
  commonNeighbor := commonNeighborFinalRoute
  k23TargetClosure := k23FinalTargetClosureRoute
  commonNeighborTargetClosure := commonNeighborFinalTargetClosureRoute
  k23Geometry := k23FinalGeometryRoute
  commonNeighborGeometry := commonNeighborFinalGeometryRoute

/-! ## Routes from the combined explicit field bundle -/

/-- Direct broken-lattice route from the combined explicit input. -/
def explicitDirectRoute :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.directTargetIntegratedRoute.eliminator
      M.direct
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.directTargetIntegratedRoute.noMinimal
      M.direct
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.directTargetIntegratedRoute.pipeline
      M.direct
  target := fun M =>
    BrokenLatticeFinalIntegratedW11.directTargetIntegratedRoute.target M.direct

/-- K23 route from the final aggregate carried by the combined input. -/
def explicitK23FinalRoute :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u}) where
  eliminator := fun M => k23FinalRoute.eliminator M.k23CommonNeighbor
  noMinimal := fun M => k23FinalRoute.noMinimal M.k23CommonNeighbor
  pipeline := fun M => k23FinalRoute.pipeline M.k23CommonNeighbor
  target := fun M => k23FinalRoute.target M.k23CommonNeighbor

/-- Common-neighbor route from the final aggregate carried by the combined
input. -/
def explicitCommonNeighborFinalRoute :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u}) where
  eliminator := fun M =>
    commonNeighborFinalRoute.eliminator M.k23CommonNeighbor
  noMinimal := fun M =>
    commonNeighborFinalRoute.noMinimal M.k23CommonNeighbor
  pipeline := fun M =>
    commonNeighborFinalRoute.pipeline M.k23CommonNeighbor
  target := fun M => commonNeighborFinalRoute.target M.k23CommonNeighbor

/-- K23 broken-lattice route from the K23 projection of the final aggregate. -/
def explicitK23BrokenLatticeRoute :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.k23TargetIntegratedRoute.eliminator
      M.k23BrokenLattice
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.k23TargetIntegratedRoute.noMinimal
      M.k23BrokenLattice
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.k23TargetIntegratedRoute.pipeline
      M.k23BrokenLattice
  target := fun M =>
    BrokenLatticeFinalIntegratedW11.k23TargetIntegratedRoute.target
      M.k23BrokenLattice

/-- Common-neighbor broken-lattice route from the common-neighbor projection
of the final aggregate. -/
def explicitCommonNeighborBrokenLatticeRoute :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u}) where
  eliminator := fun M =>
    BrokenLatticeFinalIntegratedW11.commonNeighborTargetIntegratedRoute.eliminator
      M.commonNeighborBrokenLattice
  noMinimal := fun M =>
    BrokenLatticeFinalIntegratedW11.commonNeighborTargetIntegratedRoute.noMinimal
      M.commonNeighborBrokenLattice
  pipeline := fun M =>
    BrokenLatticeFinalIntegratedW11.commonNeighborTargetIntegratedRoute.pipeline
      M.commonNeighborBrokenLattice
  target := fun M =>
    BrokenLatticeFinalIntegratedW11.commonNeighborTargetIntegratedRoute.target
      M.commonNeighborBrokenLattice

/-- K23 target-closure route from the final aggregate carried by the combined
input. -/
def explicitK23TargetClosureRoute :
    TargetRoute (ExplicitFieldMatrices.{u}) where
  noMinimal := fun M =>
    k23FinalTargetClosureRoute.noMinimal M.k23CommonNeighbor
  pipeline := fun M =>
    k23FinalTargetClosureRoute.pipeline M.k23CommonNeighbor
  target := fun M => k23FinalTargetClosureRoute.target M.k23CommonNeighbor

/-- Common-neighbor target-closure route from the final aggregate carried by
the combined input. -/
def explicitCommonNeighborTargetClosureRoute :
    TargetRoute (ExplicitFieldMatrices.{u}) where
  noMinimal := fun M =>
    commonNeighborFinalTargetClosureRoute.noMinimal M.k23CommonNeighbor
  pipeline := fun M =>
    commonNeighborFinalTargetClosureRoute.pipeline M.k23CommonNeighbor
  target := fun M =>
    commonNeighborFinalTargetClosureRoute.target M.k23CommonNeighbor

/-- K23 integrated-geometry route from the final aggregate carried by the
combined input. -/
def explicitK23GeometryRoute :
    TargetRoute (ExplicitFieldMatrices.{u}) where
  noMinimal := fun M => k23FinalGeometryRoute.noMinimal M.k23CommonNeighbor
  pipeline := fun M => k23FinalGeometryRoute.pipeline M.k23CommonNeighbor
  target := fun M => k23FinalGeometryRoute.target M.k23CommonNeighbor

/-- Common-neighbor integrated-geometry route from the final aggregate carried
by the combined input. -/
def explicitCommonNeighborGeometryRoute :
    TargetRoute (ExplicitFieldMatrices.{u}) where
  noMinimal := fun M =>
    commonNeighborFinalGeometryRoute.noMinimal M.k23CommonNeighbor
  pipeline := fun M =>
    commonNeighborFinalGeometryRoute.pipeline M.k23CommonNeighbor
  target := fun M =>
    commonNeighborFinalGeometryRoute.target M.k23CommonNeighbor

/-- Conditional routes exposed from the combined explicit field bundle. -/
structure ExplicitFieldRoutes : Type (u + 1) where
  direct :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u})
  k23Final :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u})
  commonNeighborFinal :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u})
  k23BrokenLattice :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u})
  commonNeighborBrokenLattice :
    EliminatorTargetRoute (ExplicitFieldMatrices.{u})
  k23TargetClosure :
    TargetRoute (ExplicitFieldMatrices.{u})
  commonNeighborTargetClosure :
    TargetRoute (ExplicitFieldMatrices.{u})
  k23Geometry :
    TargetRoute (ExplicitFieldMatrices.{u})
  commonNeighborGeometry :
    TargetRoute (ExplicitFieldMatrices.{u})

/-- Checked conditional routes from the combined explicit field bundle. -/
def explicitFieldRoutes :
    ExplicitFieldRoutes.{u} where
  direct := explicitDirectRoute
  k23Final := explicitK23FinalRoute
  commonNeighborFinal := explicitCommonNeighborFinalRoute
  k23BrokenLattice := explicitK23BrokenLatticeRoute
  commonNeighborBrokenLattice := explicitCommonNeighborBrokenLatticeRoute
  k23TargetClosure := explicitK23TargetClosureRoute
  commonNeighborTargetClosure := explicitCommonNeighborTargetClosureRoute
  k23Geometry := explicitK23GeometryRoute
  commonNeighborGeometry := explicitCommonNeighborGeometryRoute

/-! ## Imported final ledgers -/

/-- Imported W11 ledgers used by this final consistency matrix. -/
structure ImportedLedgers : Type (u + 3) where
  k23Final : K23FinalIntegratedW11.Matrix.{u}
  brokenLatticeFinal : BrokenLatticeFinalIntegratedW11.Matrix.{u}
  geometryIntegrated : GeometryIntegratedW11.Matrix.{u}

/-- Checked imported W11 ledgers. -/
def importedLedgers :
    ImportedLedgers.{u} where
  k23Final := K23FinalIntegratedW11.matrix
  brokenLatticeFinal := BrokenLatticeFinalIntegratedW11.matrix
  geometryIntegrated := GeometryIntegratedW11.matrix

/-- Marker for the broader W11 consistency import used by this file. -/
theorem swanepoelConsistencyImportChecked : True :=
  True.intro

/-! ## Final combined consistency matrix -/

/-- Final combined W11 K23/common-neighbor/broken-lattice consistency matrix.

This record stores field-matrix projections and conditional route rows only.
It does not construct a target proof without an explicit field input. -/
structure Matrix : Type (u + 3) where
  imported : ImportedLedgers.{u}
  fields : ExplicitFieldMatrixSurface.{u}
  k23CommonNeighbor : K23CommonNeighborRoutes.{u}
  brokenLattice :
    BrokenLatticeFinalIntegratedW11.ConditionalSwanepoelTargetRoutes.{u}
  explicit : ExplicitFieldRoutes.{u}

/-- The checked final combined consistency matrix. -/
def matrix : Matrix.{u} where
  imported := importedLedgers
  fields := explicitFieldMatrixSurface
  k23CommonNeighbor := k23CommonNeighborRoutes
  brokenLattice :=
    BrokenLatticeFinalIntegratedW11.conditionalSwanepoelTargetRoutes
  explicit := explicitFieldRoutes

theorem matrix_nonempty : Nonempty Matrix.{u} :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem no_minimalClearedFailure_of_fields_via_direct
    (M : ExplicitFieldMatrices.{u}) :
    MinimalFailureExclusion :=
  matrix.explicit.direct.noMinimal M

theorem pipelineCleared_of_fields_via_direct
    (M : ExplicitFieldMatrices.{u}) :
    PipelineCleared :=
  matrix.explicit.direct.pipeline M

theorem target_of_fields_via_direct
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.direct.target M

theorem no_minimalClearedFailure_of_fields_via_k23Final
    (M : ExplicitFieldMatrices.{u}) :
    MinimalFailureExclusion :=
  matrix.explicit.k23Final.noMinimal M

theorem pipelineCleared_of_fields_via_k23Final
    (M : ExplicitFieldMatrices.{u}) :
    PipelineCleared :=
  matrix.explicit.k23Final.pipeline M

theorem target_of_fields_via_k23Final
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.k23Final.target M

theorem no_minimalClearedFailure_of_fields_via_commonNeighborFinal
    (M : ExplicitFieldMatrices.{u}) :
    MinimalFailureExclusion :=
  matrix.explicit.commonNeighborFinal.noMinimal M

theorem pipelineCleared_of_fields_via_commonNeighborFinal
    (M : ExplicitFieldMatrices.{u}) :
    PipelineCleared :=
  matrix.explicit.commonNeighborFinal.pipeline M

theorem target_of_fields_via_commonNeighborFinal
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.commonNeighborFinal.target M

theorem target_of_fields_via_k23BrokenLattice
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.k23BrokenLattice.target M

theorem target_of_fields_via_commonNeighborBrokenLattice
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.commonNeighborBrokenLattice.target M

theorem target_of_fields_via_k23TargetClosure
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.k23TargetClosure.target M

theorem target_of_fields_via_commonNeighborTargetClosure
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.commonNeighborTargetClosure.target M

theorem target_of_fields_via_k23Geometry
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.k23Geometry.target M

theorem target_of_fields_via_commonNeighborGeometry
    (M : ExplicitFieldMatrices.{u}) :
    Target :=
  matrix.explicit.commonNeighborGeometry.target M

end

end K23BrokenLatticeFinalW11
end Swanepoel
end ErdosProblems1066
