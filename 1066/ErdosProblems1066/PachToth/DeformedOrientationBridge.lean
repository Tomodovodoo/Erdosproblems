import ErdosProblems1066.PachToth.DeformedPlacement
import ErdosProblems1066.PachToth.OrientationData

/-!
# Bridge from oriented transition data to deformed placements

This module adapts the source-backed orientation and transition certificates
to the newer non-rigid `DeformedPlacement.ClosedPlacement` interface.

The transition certificates supply exactly the successor connector unit
edges.  A fully deformed closed placement also needs global separation and
same-block unit edges; these remain explicit in the generic bridge, and are
derived from the stored one-block isometry for
`OrientationData.OrientedClosedChainPlacement`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DeformedOrientationBridge

open Arithmetic
open BlockPartition
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Transition certificates plus the two deformed-placement metric
obligations give a closed deformed placement.

The extra hypotheses are precisely the facts not contained in an individual
orientation/connector certificate: global separation of all placed vertices
and unit distances for finite same-block edges. -/
def toClosedPlacementOfTransitionCertificates {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (transition :
      forall i : Fin k,
        OrientationData.TransitionCertificate
          (point i) (point (cyclicSucc hk i)))
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1) :
    DeformedPlacement.ClosedPlacement k hk where
  point := point
  separated := separated
  same_block_edges_unit := same_block_edges_unit
  cross_connector_edges_unit := by
    intro i u v hconn
    exact (transition i).connector_unit_target hconn

@[simp]
theorem toClosedPlacementOfTransitionCertificates_point
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (transition :
      forall i : Fin k,
        OrientationData.TransitionCertificate
          (point i) (point (cyclicSucc hk i)))
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (i : Fin k) (v : LocalVertex) :
    (toClosedPlacementOfTransitionCertificates point transition separated
        same_block_edges_unit).point i v = point i v :=
  rfl

/-- The generic transition-certificate bridge, followed by the deformed
placement realization map. -/
def toIndexedChainRealizationOfTransitionCertificates {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (transition :
      forall i : Fin k,
        OrientationData.TransitionCertificate
          (point i) (point (cyclicSucc hk i)))
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1) :
    IndexedChain.IndexedChainRealization k hk :=
  (toClosedPlacementOfTransitionCertificates point transition separated
    same_block_edges_unit).toIndexedChainRealization

/-- An oriented closed chain is a closed deformed placement.

The successor connector edges come from the transition certificates.  The
same-block deformed unit-edge field is obtained from the chain's isometry to
the checked one-block realization. -/
def toDeformedClosedPlacement {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk) :
    DeformedPlacement.ClosedPlacement k hk where
  point := P.point
  separated := P.separated
  same_block_edges_unit := by
    intro i u v _huv hadj
    calc
      _root_.eucDist (P.point i u) (P.point i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (localVertexEquivFin16 v)) := P.same_block_isometry i u v
      _ = 1 :=
          OneBlockSoundness.oneBlockCertificate.same_block_edges_unit u v hadj
  cross_connector_edges_unit := by
    intro i u v hconn
    exact (P.transition i).connector_unit_target hconn

@[simp]
theorem toDeformedClosedPlacement_point {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk)
    (i : Fin k) (v : LocalVertex) :
    (toDeformedClosedPlacement P).point i v = P.point i v :=
  rfl

/-- Route an oriented closed chain through the non-rigid placement interface
to the indexed-chain realization layer. -/
def toDeformedIndexedChainRealization {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  (toDeformedClosedPlacement P).toIndexedChainRealization

/-- If oriented closed-chain placements are available for every positive
block count, the target upper construction follows through the deformed
placement interface. -/
theorem targetUpperConstructionFiveSixteen_of_orientedClosedChainPlacements
    (H : forall (k : Nat) (hk : 0 < k),
      OrientationData.OrientedClosedChainPlacement k hk) :
    targetUpperConstructionFiveSixteen := by
  exact DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
    (fun k hk => toDeformedClosedPlacement (H k hk))

end

end DeformedOrientationBridge
end PachToth
end ErdosProblems1066
