import ErdosProblems1066.PachToth.DeformedPlacement

set_option autoImplicit false

/-!
# Non-rigid closed-placement components

This module packages the concrete non-rigid geometric fields directly:
blockwise point functions, global separation, same-block unit edges, and
successor connector unit edges.  The downstream wrappers deliberately reuse
`DeformedPlacement.ClosedPlacement`, so no transition equations or generated
chain closure data are required here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementNonRigidComponents

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- Concrete non-rigid data for one closed Pach--Toth block cycle. -/
structure Components (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1
  successor_connector_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1

namespace Components

/-- Package direct concrete fields as the canonical deformed closed placement. -/
def toClosedPlacement {k : Nat} {hk : 0 < k}
    (C : Components k hk) :
    DeformedPlacement.ClosedPlacement k hk where
  point := C.point
  separated := C.separated
  same_block_edges_unit := C.same_block_edges_unit
  cross_connector_edges_unit := C.successor_connector_edges_unit

@[simp]
theorem toClosedPlacement_point {k : Nat} {hk : 0 < k}
    (C : Components k hk) (i : Fin k) (v : LocalVertex) :
    C.toClosedPlacement.point i v = C.point i v :=
  rfl

/-- The canonical global unit-distance configuration supplied by the
underlying deformed closed placement. -/
def config {k : Nat} {hk : 0 < k}
    (C : Components k hk) : _root_.UDConfig (16 * k) :=
  C.toClosedPlacement.config

@[simp]
theorem config_pts_globalVertex {k : Nat} {hk : 0 < k}
    (C : Components k hk) (i : Fin k) (v : LocalVertex) :
    C.config.pts (GeometricSoundness.globalVertex k i v) = C.point i v := by
  simp [config, toClosedPlacement]

/-- Direct concrete fields provide the explicit edge-soundness wrapper. -/
def toExplicitEdgeSoundness {k : Nat} {hk : 0 < k}
    (C : Components k hk) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  C.toClosedPlacement.toExplicitEdgeSoundness

/-- Direct concrete fields provide the indexed-chain realization wrapper. -/
def toIndexedChainRealization {k : Nat} {hk : 0 < k}
    (C : Components k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  C.toClosedPlacement.toIndexedChainRealization

/-- Direct concrete fields give the exact block-count target statement. -/
theorem exactBlockTarget {k : Nat} {hk : 0 < k}
    (C : Components k hk) :
    Exists fun U : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), U.IsIndep s -> s.card <= 5 * k := by
  exact IndexedChain.exists_config_with_independent_card_le_five_mul
    hk C.toIndexedChainRealization

end Components

/-- Raw-field constructor for the canonical deformed closed placement. -/
def closedPlacementOfFields
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (successor_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1) :
    DeformedPlacement.ClosedPlacement k hk :=
  (Components.mk point separated same_block_edges_unit
    successor_connector_edges_unit).toClosedPlacement

/-- Raw-field constructor for the explicit edge-soundness wrapper. -/
def explicitEdgeSoundnessOfFields
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (successor_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  (Components.mk point separated same_block_edges_unit
    successor_connector_edges_unit).toExplicitEdgeSoundness

/-- Raw-field exact block-count target wrapper. -/
theorem exactBlockTargetOfFields
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (same_block_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point i u) (point i v) = 1)
    (successor_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1) :
    Exists fun U : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), U.IsIndep s -> s.card <= 5 * k := by
  exact
    (Components.mk point separated same_block_edges_unit
      successor_connector_edges_unit).exactBlockTarget

/-- Family wrapper from direct components to the block-form Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_components
    (H : forall (k : Nat) (hk : 0 < k), Components k hk) :
    targetUpperConstructionFiveSixteen := by
  exact DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
    (fun k hk => (H k hk).toClosedPlacement)

/-- Family wrapper from raw concrete fields to the block-form Pach--Toth
target. -/
theorem targetUpperConstructionFiveSixteen_of_fields
    (point :
      forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2)
    (separated :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          1 <= _root_.eucDist (point k hk i u) (point k hk j v))
    (same_block_edges_unit :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u v : LocalVertex),
        Ne u v ->
        adj u v = true ->
          _root_.eucDist (point k hk i u) (point k hk i v) = 1)
    (successor_connector_edges_unit :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point k hk i u)
            (point k hk (cyclicSucc hk i) v) = 1) :
    targetUpperConstructionFiveSixteen := by
  exact targetUpperConstructionFiveSixteen_of_components
    (fun k hk =>
      { point := point k hk
        separated := separated k hk
        same_block_edges_unit := same_block_edges_unit k hk
        successor_connector_edges_unit :=
          successor_connector_edges_unit k hk })

end

end ClosedPlacementNonRigidComponents
end PachToth
end ErdosProblems1066
