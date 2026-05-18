import ErdosProblems1066.PachToth.ClosedPlacementNonRigidComponents
import ErdosProblems1066.PachToth.SplitArbitraryNNonRigidBridge

set_option autoImplicit false

/-!
# Closed-placement component assembly

This module is the final thin facade for the direct non-rigid component route.
It packages the smallest explicit family fields used by
`ClosedPlacementNonRigidComponents.Components` and routes them to both the
exact block target and the arbitrary-vertex target through the checked split
bridge.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementComponentsAssembly

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The smallest explicit family data for the direct non-rigid closed
placement route: blockwise points, global separation, same-block unit edges,
and successor connector unit edges, uniformly for every positive block count.
-/
structure ComponentFamilyFields where
  point :
    forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2
  separated :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) ->
        1 <= _root_.eucDist (point k hk i u) (point k hk j v)
  same_block_edges_unit :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point k hk i u) (point k hk i v) = 1
  successor_connector_edges_unit :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point k hk i u)
          (point k hk (Arithmetic.cyclicSucc hk i) v) = 1

namespace ComponentFamilyFields

/-- Repackage the family fields as the component bundle for one block count. -/
def components (H : ComponentFamilyFields)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementNonRigidComponents.Components k hk where
  point := H.point k hk
  separated := H.separated k hk
  same_block_edges_unit := H.same_block_edges_unit k hk
  successor_connector_edges_unit := H.successor_connector_edges_unit k hk

/-- The checked closed placement carried by the assembled component fields. -/
def closedPlacement (H : ComponentFamilyFields)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  (H.components k hk).toClosedPlacement

/-- The exact block-form Pach--Toth target from assembled component fields. -/
theorem targetUpperConstructionFiveSixteen
    (H : ComponentFamilyFields) :
    targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementNonRigidComponents.targetUpperConstructionFiveSixteen_of_components
      H.components

/-- The arbitrary-vertex Pach--Toth target from assembled component fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (H : ComponentFamilyFields) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    SplitArbitraryNNonRigidBridge.targetUpperConstructionFiveSixteenArbitrary_of_components
      H.components

end ComponentFamilyFields

/-- Bundled-field exact block-form wrapper. -/
theorem targetUpperConstructionFiveSixteen_of_componentFamilyFields
    (H : ComponentFamilyFields) :
    targetUpperConstructionFiveSixteen := by
  exact H.targetUpperConstructionFiveSixteen

/-- Bundled-field arbitrary-vertex wrapper. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_componentFamilyFields
    (H : ComponentFamilyFields) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact H.targetUpperConstructionFiveSixteenArbitrary

/-- Raw-field exact block-form wrapper. -/
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
            (point k hk (Arithmetic.cyclicSucc hk i) v) = 1) :
    targetUpperConstructionFiveSixteen := by
  exact
    ComponentFamilyFields.targetUpperConstructionFiveSixteen
      { point := point
        separated := separated
        same_block_edges_unit := same_block_edges_unit
        successor_connector_edges_unit := successor_connector_edges_unit }

/-- Raw-field arbitrary-vertex wrapper. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_fields
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
            (point k hk (Arithmetic.cyclicSucc hk i) v) = 1) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ComponentFamilyFields.targetUpperConstructionFiveSixteenArbitrary
      { point := point
        separated := separated
        same_block_edges_unit := same_block_edges_unit
        successor_connector_edges_unit := successor_connector_edges_unit }

end

end ClosedPlacementComponentsAssembly
end PachToth
end ErdosProblems1066
