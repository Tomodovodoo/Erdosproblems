import ErdosProblems1066.Swanepoel.K23BrokenLatticeFinalW11
import ErdosProblems1066.Swanepoel.K23FinalIntegratedW11
import ErdosProblems1066.Swanepoel.BrokenLatticeFinalIntegratedW11
import ErdosProblems1066.Swanepoel.GeometryFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 K23, broken-lattice, and geometry target consistency layer

This file is an additive target-facing consistency layer for the checked W11
K23/common-neighbor, broken-lattice, and geometry finals.  It records explicit
matrix inputs and conditional target routes only: every public target
projection below takes a caller-supplied matrix bundle.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23BrokenTargetFinalW11

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

abbrev K23BrokenFieldMatrices :=
  K23BrokenLatticeFinalW11.ExplicitFieldMatrices

abbrev K23CommonNeighborFinalMatrix :=
  K23FinalIntegratedW11.K23CommonNeighborFinalMatrix

abbrev BrokenLatticeFieldMatrices :=
  BrokenLatticeFinalIntegratedW11.ExplicitFieldMatrices

abbrev GeometryMatrices :=
  GeometryFinalIntegratedW11.ExplicitGeometryMatrices

abbrev DirectGeometryMatrix :=
  GeometryFinalIntegratedW11.DirectFinalGeometryMatrix

abbrev K23GeometryMatrix :=
  GeometryFinalIntegratedW11.K23FinalGeometryMatrix

abbrev CommonNeighborGeometryMatrix :=
  GeometryFinalIntegratedW11.CommonNeighborFinalGeometryMatrix

/-! ## Route shapes -/

/-- A conditional Swanepoel target route from an explicit matrix package. -/
structure TargetRoute (alpha : Type v) : Type v where
  noMinimal : alpha -> MinimalFailureExclusion
  pipeline : alpha -> PipelineCleared
  target : alpha -> Target

namespace TargetRoute

/-- Reuse a route from the K23/broken-lattice final layer. -/
def ofK23BrokenRoute
    {alpha : Type v}
    (R : K23BrokenLatticeFinalW11.TargetRoute alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse a route from the geometry final layer. -/
def ofGeometryRoute
    {alpha : Type v}
    (R : GeometryFinalIntegratedW11.TargetRoute alpha) :
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

/-- Forget the eliminator while retaining the conditional target route. -/
def toTargetRoute
    {alpha : Type v}
    (R : EliminatorTargetRoute alpha) :
    TargetRoute alpha where
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse an eliminator route from the K23/broken-lattice final layer. -/
def ofK23BrokenRoute
    {alpha : Type v}
    (R : K23BrokenLatticeFinalW11.EliminatorTargetRoute alpha) :
    EliminatorTargetRoute alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

/-- Reuse an eliminator route from the geometry final layer. -/
def ofGeometryRoute
    {alpha : Type v}
    (R : GeometryFinalIntegratedW11.EliminatorTargetRoute alpha) :
    EliminatorTargetRoute alpha where
  eliminator := R.eliminator
  noMinimal := R.noMinimal
  pipeline := R.pipeline
  target := R.target

end EliminatorTargetRoute

/-! ## Explicit combined matrices -/

/-- The caller-supplied matrices for the final K23/broken-lattice/geometry
target ledger. -/
structure ExplicitMatrices : Type (u + 1) where
  k23Broken : K23BrokenFieldMatrices.{u}
  geometry : GeometryMatrices.{u}

namespace ExplicitMatrices

/-- The K23/common-neighbor final aggregate selected by the K23-broken input. -/
def k23CommonNeighbor
    (M : ExplicitMatrices.{u}) :
    K23CommonNeighborFinalMatrix.{u} :=
  M.k23Broken.k23CommonNeighbor

/-- The broken-lattice direct field matrix selected by the K23-broken input. -/
def directBrokenLattice
    (M : ExplicitMatrices.{u}) :
    BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u} :=
  M.k23Broken.direct

/-- The K23 broken-lattice field matrix projected from the final aggregate. -/
def k23BrokenLattice
    (M : ExplicitMatrices.{u}) :
    BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u} :=
  M.k23Broken.k23BrokenLattice

/-- The common-neighbor broken-lattice field matrix projected from the final
aggregate. -/
def commonNeighborBrokenLattice
    (M : ExplicitMatrices.{u}) :
    BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u} :=
  M.k23Broken.commonNeighborBrokenLattice

/-- The complete broken-lattice field bundle selected by the K23-broken input. -/
def k23BrokenAsBrokenLattice
    (M : ExplicitMatrices.{u}) :
    BrokenLatticeFieldMatrices.{u} :=
  M.k23Broken.toBrokenLatticeExplicitFieldMatrices

/-- The direct final geometry matrix selected by the geometry input. -/
def directGeometry
    (M : ExplicitMatrices.{u}) :
    DirectGeometryMatrix.{u} :=
  M.geometry.direct

/-- The K23 final geometry matrix selected by the geometry input. -/
def k23Geometry
    (M : ExplicitMatrices.{u}) :
    K23GeometryMatrix.{u} :=
  M.geometry.k23

/-- The common-neighbor final geometry matrix selected by the geometry input. -/
def commonNeighborGeometry
    (M : ExplicitMatrices.{u}) :
    CommonNeighborGeometryMatrix.{u} :=
  M.geometry.commonNeighbor

/-- The geometry matrices viewed as a broken-lattice field bundle. -/
def geometryAsBrokenLattice
    (M : ExplicitMatrices.{u}) :
    BrokenLatticeFieldMatrices.{u} where
  direct := M.geometry.direct.toBrokenLatticeFieldMatrix
  k23 := M.geometry.k23.toBrokenLatticeFieldMatrix
  commonNeighbor := M.geometry.commonNeighbor.toBrokenLatticeFieldMatrix

@[simp]
theorem k23BrokenAsBrokenLattice_direct
    (M : ExplicitMatrices.{u}) :
    M.k23BrokenAsBrokenLattice.direct = M.directBrokenLattice :=
  rfl

@[simp]
theorem k23BrokenAsBrokenLattice_k23
    (M : ExplicitMatrices.{u}) :
    M.k23BrokenAsBrokenLattice.k23 = M.k23BrokenLattice :=
  rfl

@[simp]
theorem k23BrokenAsBrokenLattice_commonNeighbor
    (M : ExplicitMatrices.{u}) :
    M.k23BrokenAsBrokenLattice.commonNeighbor =
      M.commonNeighborBrokenLattice :=
  rfl

@[simp]
theorem geometryAsBrokenLattice_direct
    (M : ExplicitMatrices.{u}) :
    M.geometryAsBrokenLattice.direct =
      M.directGeometry.toBrokenLatticeFieldMatrix :=
  rfl

@[simp]
theorem geometryAsBrokenLattice_k23
    (M : ExplicitMatrices.{u}) :
    M.geometryAsBrokenLattice.k23 =
      M.k23Geometry.toBrokenLatticeFieldMatrix :=
  rfl

@[simp]
theorem geometryAsBrokenLattice_commonNeighbor
    (M : ExplicitMatrices.{u}) :
    M.geometryAsBrokenLattice.commonNeighbor =
      M.commonNeighborGeometry.toBrokenLatticeFieldMatrix :=
  rfl

end ExplicitMatrices

/-- Projection functions displaying every explicit matrix surface used by the
final target consistency ledger. -/
structure ExplicitMatrixSurface : Type (u + 1) where
  k23Broken :
    ExplicitMatrices.{u} -> K23BrokenFieldMatrices.{u}
  geometry :
    ExplicitMatrices.{u} -> GeometryMatrices.{u}
  k23CommonNeighbor :
    ExplicitMatrices.{u} -> K23CommonNeighborFinalMatrix.{u}
  directBrokenLattice :
    ExplicitMatrices.{u} ->
      BrokenLatticeFinalIntegratedW11.DirectFieldMatrix.{u}
  k23BrokenLattice :
    ExplicitMatrices.{u} ->
      BrokenLatticeFinalIntegratedW11.K23FieldMatrix.{u}
  commonNeighborBrokenLattice :
    ExplicitMatrices.{u} ->
      BrokenLatticeFinalIntegratedW11.CommonNeighborFieldMatrix.{u}
  k23BrokenAsBrokenLattice :
    ExplicitMatrices.{u} -> BrokenLatticeFieldMatrices.{u}
  directGeometry :
    ExplicitMatrices.{u} -> DirectGeometryMatrix.{u}
  k23Geometry :
    ExplicitMatrices.{u} -> K23GeometryMatrix.{u}
  commonNeighborGeometry :
    ExplicitMatrices.{u} -> CommonNeighborGeometryMatrix.{u}
  geometryAsBrokenLattice :
    ExplicitMatrices.{u} -> BrokenLatticeFieldMatrices.{u}

/-- The displayed explicit matrix projections for the final input package. -/
def explicitMatrixSurface :
    ExplicitMatrixSurface.{u} where
  k23Broken := ExplicitMatrices.k23Broken
  geometry := ExplicitMatrices.geometry
  k23CommonNeighbor := ExplicitMatrices.k23CommonNeighbor
  directBrokenLattice := ExplicitMatrices.directBrokenLattice
  k23BrokenLattice := ExplicitMatrices.k23BrokenLattice
  commonNeighborBrokenLattice :=
    ExplicitMatrices.commonNeighborBrokenLattice
  k23BrokenAsBrokenLattice :=
    ExplicitMatrices.k23BrokenAsBrokenLattice
  directGeometry := ExplicitMatrices.directGeometry
  k23Geometry := ExplicitMatrices.k23Geometry
  commonNeighborGeometry := ExplicitMatrices.commonNeighborGeometry
  geometryAsBrokenLattice := ExplicitMatrices.geometryAsBrokenLattice

/-! ## Conditional routes from the K23/broken-lattice final -/

def route_via_k23Broken_direct :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    K23BrokenLatticeFinalW11.explicitDirectRoute.eliminator M.k23Broken
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitDirectRoute.noMinimal M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitDirectRoute.pipeline M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitDirectRoute.target M.k23Broken

def route_via_k23Broken_k23Final :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    K23BrokenLatticeFinalW11.explicitK23FinalRoute.eliminator M.k23Broken
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitK23FinalRoute.noMinimal M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitK23FinalRoute.pipeline M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitK23FinalRoute.target M.k23Broken

def route_via_k23Broken_commonNeighborFinal :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborFinalRoute.eliminator
      M.k23Broken
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborFinalRoute.noMinimal
      M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborFinalRoute.pipeline
      M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborFinalRoute.target
      M.k23Broken

def route_via_k23Broken_k23BrokenLattice :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    K23BrokenLatticeFinalW11.explicitK23BrokenLatticeRoute.eliminator
      M.k23Broken
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitK23BrokenLatticeRoute.noMinimal
      M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitK23BrokenLatticeRoute.pipeline
      M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitK23BrokenLatticeRoute.target
      M.k23Broken

def route_via_k23Broken_commonNeighborBrokenLattice :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborBrokenLatticeRoute.eliminator
      M.k23Broken
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborBrokenLatticeRoute.noMinimal
      M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborBrokenLatticeRoute.pipeline
      M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborBrokenLatticeRoute.target
      M.k23Broken

def route_via_k23Broken_k23TargetClosure :
    TargetRoute (ExplicitMatrices.{u}) where
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitK23TargetClosureRoute.noMinimal
      M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitK23TargetClosureRoute.pipeline
      M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitK23TargetClosureRoute.target
      M.k23Broken

def route_via_k23Broken_commonNeighborTargetClosure :
    TargetRoute (ExplicitMatrices.{u}) where
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborTargetClosureRoute.noMinimal
      M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborTargetClosureRoute.pipeline
      M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborTargetClosureRoute.target
      M.k23Broken

def route_via_k23Broken_k23Geometry :
    TargetRoute (ExplicitMatrices.{u}) where
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitK23GeometryRoute.noMinimal M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitK23GeometryRoute.pipeline M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitK23GeometryRoute.target M.k23Broken

def route_via_k23Broken_commonNeighborGeometry :
    TargetRoute (ExplicitMatrices.{u}) where
  noMinimal := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborGeometryRoute.noMinimal
      M.k23Broken
  pipeline := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborGeometryRoute.pipeline
      M.k23Broken
  target := fun M =>
    K23BrokenLatticeFinalW11.explicitCommonNeighborGeometryRoute.target
      M.k23Broken

/-- Conditional target routes sourced from the K23/broken-lattice final. -/
structure K23BrokenRoutes : Type (u + 1) where
  direct : EliminatorTargetRoute (ExplicitMatrices.{u})
  k23Final : EliminatorTargetRoute (ExplicitMatrices.{u})
  commonNeighborFinal : EliminatorTargetRoute (ExplicitMatrices.{u})
  k23BrokenLattice : EliminatorTargetRoute (ExplicitMatrices.{u})
  commonNeighborBrokenLattice :
    EliminatorTargetRoute (ExplicitMatrices.{u})
  k23TargetClosure : TargetRoute (ExplicitMatrices.{u})
  commonNeighborTargetClosure : TargetRoute (ExplicitMatrices.{u})
  k23Geometry : TargetRoute (ExplicitMatrices.{u})
  commonNeighborGeometry : TargetRoute (ExplicitMatrices.{u})

def k23BrokenRoutes :
    K23BrokenRoutes.{u} where
  direct := route_via_k23Broken_direct
  k23Final := route_via_k23Broken_k23Final
  commonNeighborFinal := route_via_k23Broken_commonNeighborFinal
  k23BrokenLattice := route_via_k23Broken_k23BrokenLattice
  commonNeighborBrokenLattice :=
    route_via_k23Broken_commonNeighborBrokenLattice
  k23TargetClosure := route_via_k23Broken_k23TargetClosure
  commonNeighborTargetClosure :=
    route_via_k23Broken_commonNeighborTargetClosure
  k23Geometry := route_via_k23Broken_k23Geometry
  commonNeighborGeometry := route_via_k23Broken_commonNeighborGeometry

/-! ## Conditional routes from the geometry final -/

def route_via_geometry_directTarget :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.targetIntegrated.eliminator
      M.geometry.direct
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.targetIntegrated.noMinimal
      M.geometry.direct
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.targetIntegrated.pipeline
      M.geometry.direct
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.targetIntegrated.target
      M.geometry.direct

def route_via_geometry_directGeometryTarget :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.geometryTarget.eliminator
      M.geometry.direct
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.geometryTarget.noMinimal
      M.geometry.direct
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.geometryTarget.pipeline
      M.geometry.direct
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.geometryTarget.target
      M.geometry.direct

def route_via_geometry_directGeometryIntegrated :
    TargetRoute (ExplicitMatrices.{u}) where
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.geometryIntegrated.noMinimal
      M.geometry.direct
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.geometryIntegrated.pipeline
      M.geometry.direct
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.geometryIntegrated.target
      M.geometry.direct

def route_via_geometry_directBrokenLattice :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.brokenLatticeFinal.eliminator
      M.geometry.direct
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.brokenLatticeFinal.noMinimal
      M.geometry.direct
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.brokenLatticeFinal.pipeline
      M.geometry.direct
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.direct.brokenLatticeFinal.target
      M.geometry.direct

def route_via_geometry_k23Target :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.targetIntegrated.eliminator
      M.geometry.k23
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.targetIntegrated.noMinimal
      M.geometry.k23
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.targetIntegrated.pipeline
      M.geometry.k23
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.targetIntegrated.target
      M.geometry.k23

def route_via_geometry_k23GeometryTarget :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.geometryTarget.eliminator
      M.geometry.k23
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.geometryTarget.noMinimal
      M.geometry.k23
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.geometryTarget.pipeline
      M.geometry.k23
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.geometryTarget.target
      M.geometry.k23

def route_via_geometry_k23GeometryIntegrated :
    TargetRoute (ExplicitMatrices.{u}) where
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.geometryIntegrated.noMinimal
      M.geometry.k23
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.geometryIntegrated.pipeline
      M.geometry.k23
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.geometryIntegrated.target
      M.geometry.k23

def route_via_geometry_k23Obstruction :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.k23Target.eliminator
      M.geometry.k23
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.k23Target.noMinimal
      M.geometry.k23
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.k23Target.pipeline
      M.geometry.k23
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.k23Target.target
      M.geometry.k23

def route_via_geometry_k23BrokenLattice :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.brokenLatticeFinal.eliminator
      M.geometry.k23
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.brokenLatticeFinal.noMinimal
      M.geometry.k23
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.brokenLatticeFinal.pipeline
      M.geometry.k23
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.k23.brokenLatticeFinal.target
      M.geometry.k23

def route_via_geometry_commonNeighborTarget :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.targetIntegrated.eliminator
      M.geometry.commonNeighbor
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.targetIntegrated.noMinimal
      M.geometry.commonNeighbor
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.targetIntegrated.pipeline
      M.geometry.commonNeighbor
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.targetIntegrated.target
      M.geometry.commonNeighbor

def route_via_geometry_commonNeighborGeometryTarget :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.geometryTarget.eliminator
      M.geometry.commonNeighbor
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.geometryTarget.noMinimal
      M.geometry.commonNeighbor
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.geometryTarget.pipeline
      M.geometry.commonNeighbor
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.geometryTarget.target
      M.geometry.commonNeighbor

def route_via_geometry_commonNeighborGeometryIntegrated :
    TargetRoute (ExplicitMatrices.{u}) where
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.geometryIntegrated.noMinimal
      M.geometry.commonNeighbor
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.geometryIntegrated.pipeline
      M.geometry.commonNeighbor
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.geometryIntegrated.target
      M.geometry.commonNeighbor

def route_via_geometry_commonNeighborObstruction :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.k23Target.eliminator
      M.geometry.commonNeighbor
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.k23Target.noMinimal
      M.geometry.commonNeighbor
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.k23Target.pipeline
      M.geometry.commonNeighbor
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.k23Target.target
      M.geometry.commonNeighbor

def route_via_geometry_commonNeighborBrokenLattice :
    EliminatorTargetRoute (ExplicitMatrices.{u}) where
  eliminator := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.brokenLatticeFinal.eliminator
      M.geometry.commonNeighbor
  noMinimal := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.brokenLatticeFinal.noMinimal
      M.geometry.commonNeighbor
  pipeline := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.brokenLatticeFinal.pipeline
      M.geometry.commonNeighbor
  target := fun M =>
    GeometryFinalIntegratedW11.matrix.routes.commonNeighbor.brokenLatticeFinal.target
      M.geometry.commonNeighbor

/-- Conditional target routes sourced from the geometry final. -/
structure GeometryRoutes : Type (u + 1) where
  directTarget : EliminatorTargetRoute (ExplicitMatrices.{u})
  directGeometryTarget : EliminatorTargetRoute (ExplicitMatrices.{u})
  directGeometryIntegrated : TargetRoute (ExplicitMatrices.{u})
  directBrokenLattice : EliminatorTargetRoute (ExplicitMatrices.{u})
  k23Target : EliminatorTargetRoute (ExplicitMatrices.{u})
  k23GeometryTarget : EliminatorTargetRoute (ExplicitMatrices.{u})
  k23GeometryIntegrated : TargetRoute (ExplicitMatrices.{u})
  k23Obstruction : EliminatorTargetRoute (ExplicitMatrices.{u})
  k23BrokenLattice : EliminatorTargetRoute (ExplicitMatrices.{u})
  commonNeighborTarget : EliminatorTargetRoute (ExplicitMatrices.{u})
  commonNeighborGeometryTarget :
    EliminatorTargetRoute (ExplicitMatrices.{u})
  commonNeighborGeometryIntegrated :
    TargetRoute (ExplicitMatrices.{u})
  commonNeighborObstruction :
    EliminatorTargetRoute (ExplicitMatrices.{u})
  commonNeighborBrokenLattice :
    EliminatorTargetRoute (ExplicitMatrices.{u})

def geometryRoutes :
    GeometryRoutes.{u} where
  directTarget := route_via_geometry_directTarget
  directGeometryTarget := route_via_geometry_directGeometryTarget
  directGeometryIntegrated := route_via_geometry_directGeometryIntegrated
  directBrokenLattice := route_via_geometry_directBrokenLattice
  k23Target := route_via_geometry_k23Target
  k23GeometryTarget := route_via_geometry_k23GeometryTarget
  k23GeometryIntegrated := route_via_geometry_k23GeometryIntegrated
  k23Obstruction := route_via_geometry_k23Obstruction
  k23BrokenLattice := route_via_geometry_k23BrokenLattice
  commonNeighborTarget := route_via_geometry_commonNeighborTarget
  commonNeighborGeometryTarget :=
    route_via_geometry_commonNeighborGeometryTarget
  commonNeighborGeometryIntegrated :=
    route_via_geometry_commonNeighborGeometryIntegrated
  commonNeighborObstruction := route_via_geometry_commonNeighborObstruction
  commonNeighborBrokenLattice :=
    route_via_geometry_commonNeighborBrokenLattice

/-! ## Final consistency matrix -/

/-- Imported W11 ledgers used by this final target consistency layer. -/
structure ImportedLedgers : Type (u + 3) where
  k23BrokenLattice : K23BrokenLatticeFinalW11.Matrix.{u}
  k23Final : K23FinalIntegratedW11.Matrix.{u}
  brokenLatticeFinal : BrokenLatticeFinalIntegratedW11.Matrix.{u}
  geometryFinal : GeometryFinalIntegratedW11.Matrix.{u}
  swanepoelFinalConsistency : True

def importedLedgers :
    ImportedLedgers.{u} where
  k23BrokenLattice := K23BrokenLatticeFinalW11.matrix
  k23Final := K23FinalIntegratedW11.matrix
  brokenLatticeFinal := BrokenLatticeFinalIntegratedW11.matrix
  geometryFinal := GeometryFinalIntegratedW11.matrix
  swanepoelFinalConsistency := True.intro

/-- All conditional Swanepoel target routes exposed by this final layer. -/
structure ConditionalSwanepoelTargetRoutes : Type (u + 1) where
  k23Broken : K23BrokenRoutes.{u}
  geometry : GeometryRoutes.{u}

def conditionalSwanepoelTargetRoutes :
    ConditionalSwanepoelTargetRoutes.{u} where
  k23Broken := k23BrokenRoutes
  geometry := geometryRoutes

/-- Final combined W11 K23/broken-lattice/geometry target consistency matrix.

This record stores imported ledgers, explicit matrix surfaces, and conditional
route rows only. -/
structure Matrix : Type (u + 3) where
  imported : ImportedLedgers.{u}
  explicit : ExplicitMatrixSurface.{u}
  routes : ConditionalSwanepoelTargetRoutes.{u}

/-- The checked final combined conditional target matrix. -/
def matrix :
    Matrix.{u} where
  imported := importedLedgers
  explicit := explicitMatrixSurface
  routes := conditionalSwanepoelTargetRoutes

theorem matrix_nonempty :
    Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_k23BrokenLatticeFinal :
    matrix.imported.k23BrokenLattice = K23BrokenLatticeFinalW11.matrix := by
  rfl

theorem checked_k23Final :
    matrix.imported.k23Final = K23FinalIntegratedW11.matrix := by
  rfl

theorem checked_brokenLatticeFinal :
    matrix.imported.brokenLatticeFinal = BrokenLatticeFinalIntegratedW11.matrix := by
  rfl

theorem checked_geometryFinal :
    matrix.imported.geometryFinal = GeometryFinalIntegratedW11.matrix := by
  rfl

theorem checked_swanepoelFinalConsistency :
    matrix.imported.swanepoelFinalConsistency = True.intro := by
  rfl

/-! ## Public conditional projections -/

theorem no_minimalClearedFailure_of_matrices_via_k23Broken_direct
    (M : ExplicitMatrices.{u}) :
    MinimalFailureExclusion :=
  matrix.routes.k23Broken.direct.noMinimal M

theorem pipelineCleared_of_matrices_via_k23Broken_direct
    (M : ExplicitMatrices.{u}) :
    PipelineCleared :=
  matrix.routes.k23Broken.direct.pipeline M

theorem target_of_matrices_via_k23Broken_direct
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.direct.target M

theorem target_of_matrices_via_k23Broken_k23Final
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.k23Final.target M

theorem target_of_matrices_via_k23Broken_commonNeighborFinal
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.commonNeighborFinal.target M

theorem target_of_matrices_via_k23Broken_k23BrokenLattice
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.k23BrokenLattice.target M

theorem target_of_matrices_via_k23Broken_commonNeighborBrokenLattice
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.commonNeighborBrokenLattice.target M

theorem target_of_matrices_via_k23Broken_k23TargetClosure
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.k23TargetClosure.target M

theorem target_of_matrices_via_k23Broken_commonNeighborTargetClosure
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.commonNeighborTargetClosure.target M

theorem target_of_matrices_via_k23Broken_k23Geometry
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.k23Geometry.target M

theorem target_of_matrices_via_k23Broken_commonNeighborGeometry
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.k23Broken.commonNeighborGeometry.target M

theorem target_of_matrices_via_geometry_directTarget
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.directTarget.target M

theorem target_of_matrices_via_geometry_directGeometryTarget
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.directGeometryTarget.target M

theorem target_of_matrices_via_geometry_directGeometryIntegrated
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.directGeometryIntegrated.target M

theorem target_of_matrices_via_geometry_directBrokenLattice
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.directBrokenLattice.target M

theorem target_of_matrices_via_geometry_k23Target
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.k23Target.target M

theorem target_of_matrices_via_geometry_k23GeometryTarget
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.k23GeometryTarget.target M

theorem target_of_matrices_via_geometry_k23GeometryIntegrated
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.k23GeometryIntegrated.target M

theorem target_of_matrices_via_geometry_k23Obstruction
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.k23Obstruction.target M

theorem target_of_matrices_via_geometry_k23BrokenLattice
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.k23BrokenLattice.target M

theorem target_of_matrices_via_geometry_commonNeighborTarget
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.commonNeighborTarget.target M

theorem target_of_matrices_via_geometry_commonNeighborGeometryTarget
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.commonNeighborGeometryTarget.target M

theorem target_of_matrices_via_geometry_commonNeighborGeometryIntegrated
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.commonNeighborGeometryIntegrated.target M

theorem target_of_matrices_via_geometry_commonNeighborObstruction
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.commonNeighborObstruction.target M

theorem target_of_matrices_via_geometry_commonNeighborBrokenLattice
    (M : ExplicitMatrices.{u}) :
    Target :=
  matrix.routes.geometry.commonNeighborBrokenLattice.target M

end

end K23BrokenTargetFinalW11
end Swanepoel
end ErdosProblems1066
