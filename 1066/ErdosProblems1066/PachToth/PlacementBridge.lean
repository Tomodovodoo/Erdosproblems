import ErdosProblems1066.PachToth.AffineLocalGeometry
import ErdosProblems1066.PachToth.GeometricSoundness
import ErdosProblems1066.PachToth.OneBlockSoundness

/-!
# Pach--Toth Placement Bridge

This module packages an actual cyclic placement of Pach--Toth blocks as the
geometric edge-soundness certificate used by the indexed-chain counting layer.

The hard global geometry remains explicit: a placement must prove global
separation and unit cross-connector edges.  Same-block unit edges are derived
from the checked one-block realization, either through a local isometry field
or, for translated local blocks, from the affine translation lemmas.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PlacementBridge

open Arithmetic
open BlockPartition
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

namespace OneBlock

@[simp]
theorem certificate_pts_localVertex (v : LocalVertex) :
    OneBlockSoundness.oneBlockCertificate.config.pts
        (localVertexEquivFin16 v) =
      ExactLocalGeometry.localPoint v := by
  simp [OneBlockSoundness.oneBlockCertificate,
    OneBlockSoundness.oneBlockConfig, OneBlockSoundness.oneBlockPoint]

end OneBlock

/-- A point placement for `k` Pach--Toth blocks.  The placement carries all
global separation facts and a same-block isometry to the checked one-block
configuration. -/
structure BlockPlacement (k : Nat) where
  point : Fin k -> LocalVertex -> R2
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_isometry :
    forall (i : Fin k) (u v : LocalVertex),
      _root_.eucDist (point i u) (point i v) =
        _root_.eucDist
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (localVertexEquivFin16 u))
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (localVertexEquivFin16 v))

namespace BlockPlacement

/-- Encode a block placement as the canonical global `UDConfig`. -/
def config {k : Nat} (P : BlockPlacement k) : _root_.UDConfig (16 * k) where
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
theorem config_pts_globalVertex {k : Nat} (P : BlockPlacement k)
    (i : Fin k) (v : LocalVertex) :
    P.config.pts (GeometricSoundness.globalVertex k i v) = P.point i v := by
  simp [config, GeometricSoundness.globalVertex, vertexBlockLocal]

/-- The same-block finite Pach--Toth edges are unit edges in the encoded
configuration. -/
theorem same_block_edges_unit {k : Nat} (P : BlockPlacement k)
    (i : Fin k) (u v : LocalVertex) (_huv : Ne u v)
    (hadj : adj u v = true) :
    _root_.eucDist
        (P.config.pts (GeometricSoundness.globalVertex k i u))
        (P.config.pts (GeometricSoundness.globalVertex k i v)) = 1 := by
  rw [config_pts_globalVertex, config_pts_globalVertex]
  calc
    _root_.eucDist (P.point i u) (P.point i v) =
        _root_.eucDist
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (localVertexEquivFin16 u))
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (localVertexEquivFin16 v)) := P.same_block_isometry i u v
    _ = 1 := OneBlockSoundness.oneBlockCertificate.same_block_edges_unit u v hadj

end BlockPlacement

/-- A closed cyclic block placement with explicit successor connector
soundness. -/
structure ClosedChainPlacement (k : Nat) (hk : 0 < k) extends BlockPlacement k where
  cross_connector_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1

namespace ClosedChainPlacement

/-- A closed placement supplies the explicit edge-soundness certificate needed
by `GeometricSoundness`. -/
def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (P : ClosedChainPlacement k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk where
  config := P.toBlockPlacement.config
  same_block_edges_unit := by
    intro i u v huv hadj
    exact P.toBlockPlacement.same_block_edges_unit i u v huv hadj
  cross_block_edges_unit := by
    intro i u v hconn
    rw [BlockPlacement.config_pts_globalVertex,
      BlockPlacement.config_pts_globalVertex]
    exact P.cross_connector_edges_unit i u v hconn

/-- A closed placement therefore gives the existing indexed-chain
realization interface. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (P : ClosedChainPlacement k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  P.toExplicitEdgeSoundness.toIndexedChainRealization

end ClosedChainPlacement

/-- A common specialization: every block is an affine translate of the checked
exact local block.  Only global separation and connector geometry remain as
explicit obligations. -/
structure TranslatedClosedChainPlacement (k : Nat) (hk : 0 < k) where
  offset : Fin k -> AffineLocalGeometry.Point
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) ->
        1 <= _root_.eucDist
          (AffineLocalGeometry.translatedLocalPoint (offset i) u)
          (AffineLocalGeometry.translatedLocalPoint (offset j) v)
  cross_connector_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist
          (AffineLocalGeometry.translatedLocalPoint (offset i) u)
          (AffineLocalGeometry.translatedLocalPoint (offset (cyclicSucc hk i)) v) = 1

namespace TranslatedClosedChainPlacement

/-- A translated closed-chain placement is a closed placement; same-block
isometry is supplied by affine translation invariance. -/
def toClosedChainPlacement {k : Nat} {hk : 0 < k}
    (P : TranslatedClosedChainPlacement k hk) :
    ClosedChainPlacement k hk where
  point := fun i v => AffineLocalGeometry.translatedLocalPoint (P.offset i) v
  separated := P.separated
  same_block_isometry := by
    intro i u v
    simp [AffineLocalGeometry.translatedLocalPoint,
      (AffineLocalGeometry.root_dist_translate_translate (P.offset i)
        (ExactLocalGeometry.localPoint u) (ExactLocalGeometry.localPoint v))]
  cross_connector_edges_unit := P.cross_connector_edges_unit

def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (P : TranslatedClosedChainPlacement k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  P.toClosedChainPlacement.toExplicitEdgeSoundness

def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (P : TranslatedClosedChainPlacement k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  P.toClosedChainPlacement.toIndexedChainRealization

end TranslatedClosedChainPlacement

end

end PlacementBridge
end PachToth
end ErdosProblems1066
