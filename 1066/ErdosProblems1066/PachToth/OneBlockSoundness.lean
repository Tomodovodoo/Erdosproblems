import ErdosProblems1066.PachToth.BlockPartition
import ErdosProblems1066.PachToth.ExactLocalGeometry
import ErdosProblems1066.UnitDistanceBounds

set_option autoImplicit false

/-!
# Pach--Toth One-Block Geometric Soundness

This module reindexes the exact sixteen-vertex local realization from
`ExactLocalGeometry` along the canonical `BlockPartition.localVertexEquivFin16`
equivalence, producing a concrete `UDConfig 16`.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace OneBlockSoundness

open FiniteGraph
open BlockPartition
open ExactLocalGeometry

/-- The canonical `Fin 16` point map induced by the local Pach--Toth vertices. -/
def oneBlockPoint (i : Fin 16) : Real × Real :=
  localPoint (localVertexEquivFin16.symm i)

/-- Distinct `Fin 16` vertices in the one-block realization are separated. -/
theorem oneBlock_separated :
    forall i j : Fin 16, i ≠ j ->
      1 <= _root_.eucDist (oneBlockPoint i) (oneBlockPoint j) := by
  intro i j hij
  have hlocal :
      localVertexEquivFin16.symm i ≠ localVertexEquivFin16.symm j := by
    intro h
    exact hij (localVertexEquivFin16.symm.injective h)
  simpa [_root_.eucDist, Geometry.Distance.eucDist, oneBlockPoint] using
    (ExactLocalGeometry.local_separated
      (localVertexEquivFin16.symm i) (localVertexEquivFin16.symm j) hlocal)

/-- The exact one-block Pach--Toth realization as a `UDConfig 16`. -/
def oneBlockConfig : _root_.UDConfig 16 where
  pts := oneBlockPoint
  sep := oneBlock_separated

/-- Every finite graph edge is a unit-distance edge after `Fin 16` reindexing. -/
theorem oneBlock_adj_unit_distance (i j : Fin 16)
    (hadj :
      adj (localVertexEquivFin16.symm i) (localVertexEquivFin16.symm j) = true) :
    _root_.eucDist (oneBlockConfig.pts i) (oneBlockConfig.pts j) = 1 := by
  simpa [_root_.eucDist, Geometry.Distance.eucDist, oneBlockConfig, oneBlockPoint] using
    (ExactLocalGeometry.adj_unit_distance
      (localVertexEquivFin16.symm i) (localVertexEquivFin16.symm j) hadj)

/-- Local-vertex phrasing of same-block edge soundness for the one-block config. -/
theorem oneBlock_local_adj_unit_distance (u v : LocalVertex)
    (hadj : adj u v = true) :
    _root_.eucDist
      (oneBlockConfig.pts (localVertexEquivFin16 u))
      (oneBlockConfig.pts (localVertexEquivFin16 v)) = 1 := by
  simpa [_root_.eucDist, Geometry.Distance.eucDist, oneBlockConfig, oneBlockPoint] using
    (ExactLocalGeometry.adj_unit_distance u v hadj)

/-- A compact certificate for the one-block Pach--Toth realization. -/
structure OneBlockCertificate where
  config : _root_.UDConfig 16
  separated :
    forall i j : Fin 16, i ≠ j ->
      1 <= _root_.eucDist (config.pts i) (config.pts j)
  same_block_edges_unit :
    forall u v : LocalVertex, adj u v = true ->
      _root_.eucDist
        (config.pts (localVertexEquivFin16 u))
        (config.pts (localVertexEquivFin16 v)) = 1

/-- The checked one-block Pach--Toth realization certificate. -/
def oneBlockCertificate : OneBlockCertificate where
  config := oneBlockConfig
  separated := oneBlockConfig.sep
  same_block_edges_unit := oneBlock_local_adj_unit_distance

end OneBlockSoundness
end PachToth
end ErdosProblems1066

end
