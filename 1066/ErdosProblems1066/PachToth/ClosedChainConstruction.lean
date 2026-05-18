import ErdosProblems1066.PachToth.ClosedPlacementInterface
import ErdosProblems1066.PachToth.Figure2Certificate

/-!
# Pach--Toth closed-chain construction bridges

This module contains only repackaging lemmas for honest coordinate data.  It
does not assert that the Pach--Toth non-rigid closed chain exists.  Instead it
turns already-certified oriented/transition chain data into the explicit
closed-placement certificates consumed by `ClosedPlacementInterface`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedChainConstruction

open Arithmetic
open FiniteGraph
open ClosedPlacementInterface

noncomputable section

abbrev R2 := Prod Real Real

/-- A `PlacementBridge.ClosedChainPlacement` already contains enough data for
the explicit deformed closed-placement certificate.  The same-block unit
edges are obtained from its same-block isometry to the checked one-block
realization. -/
def explicitCertificateOfClosedChainPlacement
    {k : Nat} {hk : 0 < k}
    (P : PlacementBridge.ClosedChainPlacement k hk) :
    ExplicitClosedPlacementCertificate k hk where
  point := P.point
  separated := P.separated
  same_block_edges_unit := by
    intro i u v _huv hadj
    calc
      _root_.eucDist (P.point i u) (P.point i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)) :=
        P.same_block_isometry i u v
      _ = 1 :=
        OneBlockSoundness.oneBlockCertificate.same_block_edges_unit u v hadj
  cross_connector_edges_unit := P.cross_connector_edges_unit

@[simp]
theorem explicitCertificateOfClosedChainPlacement_point
    {k : Nat} {hk : 0 < k}
    (P : PlacementBridge.ClosedChainPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (explicitCertificateOfClosedChainPlacement P).point i v = P.point i v :=
  rfl

/-- An oriented closed-chain placement is a transition certificate in the
explicit closed-placement interface.  Same-block unit edges are again derived
from the checked one-block realization. -/
def explicitTransitionCertificateOfOrientedClosedChainPlacement
    {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk) :
    ExplicitTransitionClosedPlacementCertificate k hk where
  point := P.point
  transition := P.transition
  separated := P.separated
  same_block_edges_unit := by
    intro i u v _huv hadj
    calc
      _root_.eucDist (P.point i u) (P.point i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v)) :=
        P.same_block_isometry i u v
      _ = 1 :=
        OneBlockSoundness.oneBlockCertificate.same_block_edges_unit u v hadj

@[simp]
theorem explicitTransitionCertificateOfOrientedClosedChainPlacement_point
    {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (explicitTransitionCertificateOfOrientedClosedChainPlacement P).point i v =
      P.point i v :=
  rfl

/-- The same oriented placement, with transition structure forgotten, as an
explicit closed-placement certificate. -/
def explicitCertificateOfOrientedClosedChainPlacement
    {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk) :
    ExplicitClosedPlacementCertificate k hk :=
  (explicitTransitionCertificateOfOrientedClosedChainPlacement P)
    |>.toExplicitClosedPlacementCertificate

@[simp]
theorem explicitCertificateOfOrientedClosedChainPlacement_point
    {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (explicitCertificateOfOrientedClosedChainPlacement P).point i v =
      P.point i v :=
  rfl

/-- Same/opposite transition obligations, together with a cyclic orientation
sequence and explicit metric fields, produce the transition-based certificate
needed by `ClosedPlacementInterface`. -/
def explicitTransitionCertificateOfSameOpposite
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1) :
    ExplicitTransitionClosedPlacementCertificate k hk where
  point := point
  transition := by
    intro i
    exact O.transitionCertificateFor (orientation i)
      (point i) (point (cyclicSucc hk i))
      (target_eq_placeNext i)
  separated := separated
  same_block_edges_unit := same_block_edges_unit

@[simp]
theorem explicitTransitionCertificateOfSameOpposite_point
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (i : Fin k) (v : LocalVertex) :
    (explicitTransitionCertificateOfSameOpposite O point orientation
        target_eq_placeNext separated same_block_edges_unit).point i v =
      point i v :=
  rfl

/-- A version of `explicitTransitionCertificateOfSameOpposite` where
same-block unit edges are supplied through isometry to the checked one-block
certificate, matching the oriented-chain interface. -/
def explicitTransitionCertificateOfSameOppositeIsometry
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (target_eq_placeNext :
      forall i : Fin k, forall v : LocalVertex,
        point (cyclicSucc hk i) v =
          (O.transitionFor (orientation i)).placeNext (point i) v)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_isometry :
      forall (i : Fin k) (u v : LocalVertex),
        _root_.eucDist (point i u) (point i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (BlockPartition.localVertexEquivFin16 v))) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionCertificateOfSameOpposite O point orientation
    target_eq_placeNext separated
    (by
      intro i u v _huv hadj
      calc
        _root_.eucDist (point i u) (point i v) =
            _root_.eucDist
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 u))
              (OneBlockSoundness.oneBlockCertificate.config.pts
                (BlockPartition.localVertexEquivFin16 v)) :=
          same_block_isometry i u v
        _ = 1 :=
          OneBlockSoundness.oneBlockCertificate.same_block_edges_unit u v hadj)

end

end ClosedChainConstruction
end PachToth
end ErdosProblems1066
