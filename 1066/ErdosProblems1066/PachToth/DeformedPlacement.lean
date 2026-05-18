import ErdosProblems1066.PachToth.GeometricSoundness
import ErdosProblems1066.PachToth.TargetReduction

/-!
# Pach--Toth Deformed Placements

This module packages the non-rigid placement interface closest to the
Pach--Toth construction: each block has its own actual point map.  The hard
geometry is kept as explicit fields: global separation, same-block unit edges,
and cyclic cross-connector unit edges.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DeformedPlacement

open BlockPartition
open FiniteGraph
open Arithmetic

noncomputable section

abbrev R2 := Prod Real Real

/-- A closed cyclic Pach--Toth placement with blockwise deformed coordinates.

The fields are exactly the geometric facts consumed by the indexed-chain
soundness layer.  Same-block unit edges are not derived from a rigid local
copy; they are direct obligations about the provided point map. -/
structure ClosedPlacement (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1
  cross_connector_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1

namespace ClosedPlacement

/-- Encode a deformed closed placement as the canonical global `UDConfig`. -/
def config {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) : _root_.UDConfig (16 * k) where
  pts := fun x =>
    let p := vertexBlockLocal k x
    P.point p.1 p.2
  sep := by
    intro x y hxy
    let px := vertexBlockLocal k x
    let py := vertexBlockLocal k y
    have hpair : Ne px py := by
      intro hp
      apply hxy
      calc
        x = blockLocalEquiv k px := by
          change x = blockLocalEquiv k (vertexBlockLocal k x)
          exact ((blockLocalEquiv k).apply_symm_apply x).symm
        _ = blockLocalEquiv k py := by
          rw [hp]
        _ = y := by
          change blockLocalEquiv k (vertexBlockLocal k y) = y
          exact (blockLocalEquiv k).apply_symm_apply y
    exact P.separated px.1 px.2 py.1 py.2 hpair

@[simp]
theorem config_pts_globalVertex {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) (i : Fin k) (v : LocalVertex) :
    P.config.pts (GeometricSoundness.globalVertex k i v) = P.point i v := by
  simp [config, GeometricSoundness.globalVertex, vertexBlockLocal]

/-- A deformed placement directly supplies the explicit edge-soundness
certificate used by `GeometricSoundness`. -/
def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk where
  config := P.config
  same_block_edges_unit := by
    intro i u v huv hadj
    rw [config_pts_globalVertex, config_pts_globalVertex]
    exact P.same_block_edges_unit i u v huv hadj
  cross_block_edges_unit := by
    intro i u v hconn
    rw [config_pts_globalVertex, config_pts_globalVertex]
    exact P.cross_connector_edges_unit i u v hconn

/-- A deformed placement gives the canonical indexed-chain realization. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (P : ClosedPlacement k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  P.toExplicitEdgeSoundness.toIndexedChainRealization

end ClosedPlacement

/-- The Pach--Toth block target follows from deformed closed placements for
every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_deformedPlacements
    (H : forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteen := by
  apply targetUpperConstructionFiveSixteen_of_indexedChainRealizations
  intro k hk
  exact (H k hk).toIndexedChainRealization

end

end DeformedPlacement
end PachToth
end ErdosProblems1066
