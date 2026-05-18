import ErdosProblems1066.PachToth.ClosedPlacementInterface
import ErdosProblems1066.PachToth.OneBlockSoundness

set_option autoImplicit false

/-!
# Closed-chain existence bridges

This module packages a successor-compatible cyclic point orbit as the existing
closed-placement certificates.  It does not assert that such an orbit exists:
the orbit data still carries the geometric separation, connector, and
same-block obligations needed by the downstream interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedChainExistence

open Arithmetic
open BlockPartition
open ClosedPlacementInterface
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- A cyclic orbit of placed Pach--Toth blocks together with certified
successor step maps.

The `successor_compatible` field is the closure/orbit condition: every cyclic
successor block is obtained by applying the stored transition map to the
current block, including the wrap from the last block back to the first. -/
structure SuccessorCompatibleCyclicPointOrbit
    (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  step : Fin k -> OrientationData.OrientedTransition
  successor_compatible :
    forall i : Fin k, forall v : LocalVertex,
      point (cyclicSucc hk i) v = (step i).placeNext (point i) v
  connector_unit_edges :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) ((step i).placeNext (point i) v) = 1
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1

namespace SuccessorCompatibleCyclicPointOrbit

/-- A successor-compatible orbit supplies the transition certificate on each
cyclic successor edge. -/
def transitionCertificate {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk) (i : Fin k) :
    OrientationData.TransitionCertificate
      (O.point i) (O.point (cyclicSucc hk i)) where
  transition := O.step i
  target_eq_placeNext := O.successor_compatible i
  connector_unit_edges := O.connector_unit_edges i

@[simp]
theorem transitionCertificate_transition {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk) (i : Fin k) :
    (O.transitionCertificate i).transition = O.step i :=
  rfl

@[simp]
theorem transitionCertificate_target_eq_placeNext {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk)
    (i : Fin k) (v : LocalVertex) :
    (O.transitionCertificate i).target_eq_placeNext v =
      O.successor_compatible i v :=
  rfl

/-- Repackage a successor-compatible cyclic orbit as the transition-based
closed-placement certificate used by `ClosedPlacementInterface`. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk) :
    ExplicitTransitionClosedPlacementCertificate k hk where
  point := O.point
  transition := O.transitionCertificate
  separated := O.separated
  same_block_edges_unit := O.same_block_edges_unit

@[simp]
theorem toExplicitTransitionClosedPlacementCertificate_point
    {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk)
    (i : Fin k) (v : LocalVertex) :
    O.toExplicitTransitionClosedPlacementCertificate.point i v =
      O.point i v :=
  rfl

@[simp]
theorem toExplicitTransitionClosedPlacementCertificate_step
    {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk) (i : Fin k) :
    (O.toExplicitTransitionClosedPlacementCertificate.transition i).transition =
      O.step i :=
  rfl

/-- A successor-compatible cyclic orbit gives the downstream deformed
closed-placement certificate. -/
def toClosedPlacement {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  O.toExplicitTransitionClosedPlacementCertificate.toClosedPlacement

@[simp]
theorem toClosedPlacement_point {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk)
    (i : Fin k) (v : LocalVertex) :
    O.toClosedPlacement.point i v = O.point i v :=
  rfl

/-- The named existence bridge from a successor-compatible orbit into the
downstream closed-placement interface. -/
theorem exists_closedPlacement_of_successorCompatibleCyclicPointOrbit
    {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = O.point := by
  exact Exists.intro O.toClosedPlacement rfl

end SuccessorCompatibleCyclicPointOrbit

/-- A common orbit interface where same-block unit edges are provided by an
isometry to the checked one-block Pach--Toth certificate. -/
structure IsometricSuccessorCompatibleCyclicPointOrbit
    (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  step : Fin k -> OrientationData.OrientedTransition
  successor_compatible :
    forall i : Fin k, forall v : LocalVertex,
      point (cyclicSucc hk i) v = (step i).placeNext (point i) v
  connector_unit_edges :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) ((step i).placeNext (point i) v) = 1
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

namespace IsometricSuccessorCompatibleCyclicPointOrbit

/-- Derive the direct unit-edge orbit interface from the isometric one. -/
def toSuccessorCompatibleCyclicPointOrbit
    {k : Nat} {hk : 0 < k}
    (O : IsometricSuccessorCompatibleCyclicPointOrbit k hk) :
    SuccessorCompatibleCyclicPointOrbit k hk where
  point := O.point
  step := O.step
  successor_compatible := O.successor_compatible
  connector_unit_edges := O.connector_unit_edges
  separated := O.separated
  same_block_edges_unit := by
    intro i u v _huv hadj
    calc
      _root_.eucDist (O.point i u) (O.point i v) =
          _root_.eucDist
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (localVertexEquivFin16 u))
            (OneBlockSoundness.oneBlockCertificate.config.pts
              (localVertexEquivFin16 v)) := O.same_block_isometry i u v
      _ = 1 :=
          OneBlockSoundness.oneBlockCertificate.same_block_edges_unit u v hadj

@[simp]
theorem toSuccessorCompatibleCyclicPointOrbit_point
    {k : Nat} {hk : 0 < k}
    (O : IsometricSuccessorCompatibleCyclicPointOrbit k hk)
    (i : Fin k) (v : LocalVertex) :
    O.toSuccessorCompatibleCyclicPointOrbit.point i v = O.point i v :=
  rfl

/-- The isometric orbit also gives the explicit transition closed-placement
certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (O : IsometricSuccessorCompatibleCyclicPointOrbit k hk) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  O.toSuccessorCompatibleCyclicPointOrbit
    |>.toExplicitTransitionClosedPlacementCertificate

/-- The isometric orbit gives the downstream closed-placement certificate. -/
def toClosedPlacement {k : Nat} {hk : 0 < k}
    (O : IsometricSuccessorCompatibleCyclicPointOrbit k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  O.toExplicitTransitionClosedPlacementCertificate.toClosedPlacement

@[simp]
theorem toClosedPlacement_point {k : Nat} {hk : 0 < k}
    (O : IsometricSuccessorCompatibleCyclicPointOrbit k hk)
    (i : Fin k) (v : LocalVertex) :
    O.toClosedPlacement.point i v = O.point i v :=
  rfl

/-- The named existence bridge from an isometric successor-compatible orbit
into the downstream closed-placement interface. -/
theorem exists_closedPlacement_of_isometricSuccessorCompatibleCyclicPointOrbit
    {k : Nat} {hk : 0 < k}
    (O : IsometricSuccessorCompatibleCyclicPointOrbit k hk) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = O.point := by
  exact Exists.intro O.toClosedPlacement rfl

end IsometricSuccessorCompatibleCyclicPointOrbit

end

end ClosedChainExistence
end PachToth
end ErdosProblems1066
