import ErdosProblems1066.PachToth.PlacementBridge

/-!
# Pach--Toth Orientation Data

This module records the source-backed same/opposite transition data without
claiming any unproved geometry.  The audit identifies the two relative
orientations and the need for explicit deformation/placement certificates in
`proof_workings/pach_toth_postscript_audit.md:13-21,83-90,132-143`.
The Lean-ready geometry obligations are listed in
`proof_workings/pach_toth_1996_lean_ready.md:264-298`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace OrientationData

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The two relative block orientations recorded by the source audit. -/
inductive BlockOrientation where
  | same
  | opposite
  deriving DecidableEq, Repr, Fintype

/-- A named transition map for one relative orientation.

The `placeNext` field is data only: this record does not assert that either
orientation preserves local distances or realizes connector edges.  Those
facts are supplied by `TransitionCertificate` when available; see
`proof_workings/pach_toth_postscript_audit.md:134-143`.
-/
structure OrientedTransition where
  orientation : BlockOrientation
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2

namespace OrientedTransition

/-- Apply the transition map to a source block placement. -/
def target (T : OrientedTransition) (source : LocalVertex -> R2) :
    LocalVertex -> R2 :=
  T.placeNext source

@[simp]
theorem target_apply (T : OrientedTransition)
    (source : LocalVertex -> R2) (v : LocalVertex) :
    T.target source v = T.placeNext source v :=
  rfl

end OrientedTransition

/-- A certified oriented transition from one placed block to the next.

The connector unit distances are explicit hypotheses, matching the
Lean-ready `placeNext`/`GEO.next_edges_unit` obligation in
`proof_workings/pach_toth_1996_lean_ready.md:264-275`.
-/
structure TransitionCertificate
    (source target : LocalVertex -> R2) where
  transition : OrientedTransition
  target_eq_placeNext :
    forall v : LocalVertex, target v = transition.placeNext source v
  connector_unit_edges :
    forall u v : LocalVertex,
      CrossBlock.NextConnector u v ->
        _root_.eucDist (source u) (transition.placeNext source v) = 1

namespace TransitionCertificate

/-- The explicit connector certificate also applies to the stored target
placement. -/
theorem connector_unit_target
    {source target : LocalVertex -> R2}
    (C : TransitionCertificate source target)
    {u v : LocalVertex}
    (hconn : CrossBlock.NextConnector u v) :
    _root_.eucDist (source u) (target v) = 1 := by
  rw [C.target_eq_placeNext v]
  exact C.connector_unit_edges u v hconn

end TransitionCertificate

/-- A closed cyclic chain of placed blocks with an oriented transition
certificate on every successor edge.

The metric fields are intentionally explicit.  This interface records the
orientation sequence and certified `placeNext` steps, then delegates the
global geometric consequences to `PlacementBridge`; see
`proof_workings/pach_toth_1996_lean_ready.md:277-298`.
-/
structure OrientedClosedChainPlacement (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  transition :
    forall i : Fin k,
      TransitionCertificate (point i) (point (Arithmetic.cyclicSucc hk i))
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_isometry :
    forall (i : Fin k) (u v : LocalVertex),
      _root_.eucDist (point i u) (point i v) =
        _root_.eucDist
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 u))
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 v))

namespace OrientedClosedChainPlacement

/-- The relative orientation chosen for the transition from block `i` to its
cyclic successor. -/
def orientationSequence {k : Nat} {hk : 0 < k}
    (P : OrientedClosedChainPlacement k hk) (i : Fin k) :
    BlockOrientation :=
  (P.transition i).transition.orientation

/-- Repackage the oriented chain data as the existing placement bridge.

No orientation geometry is inferred here: same-block isometry, global
separation, and connector unit distances are exactly the fields carried by
`OrientedClosedChainPlacement`.
-/
def toClosedChainPlacement {k : Nat} {hk : 0 < k}
    (P : OrientedClosedChainPlacement k hk) :
    PlacementBridge.ClosedChainPlacement k hk where
  point := P.point
  separated := P.separated
  same_block_isometry := P.same_block_isometry
  cross_connector_edges_unit := by
    intro i u v hconn
    exact (P.transition i).connector_unit_target hconn

/-- The oriented chain data supplies the geometric edge-soundness interface. -/
def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (P : OrientedClosedChainPlacement k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  P.toClosedChainPlacement.toExplicitEdgeSoundness

/-- The oriented chain data supplies the indexed-chain realization interface. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (P : OrientedClosedChainPlacement k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  P.toClosedChainPlacement.toIndexedChainRealization

end OrientedClosedChainPlacement

end

end OrientationData
end PachToth
end ErdosProblems1066
