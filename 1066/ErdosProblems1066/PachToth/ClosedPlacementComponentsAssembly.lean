import ErdosProblems1066.PachToth.ClosedPlacementNonRigidComponents
import ErdosProblems1066.PachToth.ClosedPlacementClosure
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

/-- Repackage an already checked family of closed placements as component
family fields. -/
def ofClosedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    ComponentFamilyFields where
  point := fun k hk => (H k hk).point
  separated := fun k hk => (H k hk).separated
  same_block_edges_unit := fun k hk => (H k hk).same_block_edges_unit
  successor_connector_edges_unit := fun k hk =>
    (H k hk).cross_connector_edges_unit

/-- If each point block is realized by some checked closed placement, all
component-family metric fields are inherited from that placement. -/
def of_exists_closedPlacement_eq
    (point :
      forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2)
    (H :
      forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point = point k hk) :
    ComponentFamilyFields where
  point := point
  separated := by
    intro k hk i u j v hne
    cases H k hk with
    | intro P hP =>
        simpa [hP] using P.separated i u j v hne
  same_block_edges_unit := by
    intro k hk i u v huv hadj
    cases H k hk with
    | intro P hP =>
        simpa [hP] using P.same_block_edges_unit i u v huv hadj
  successor_connector_edges_unit := by
    intro k hk i u v hconn
    cases H k hk with
    | intro P hP =>
        simpa [hP] using P.cross_connector_edges_unit i u v hconn

/-- Repackage a generated-closure family with full metric hypotheses as
component-family fields. -/
def of_generatedClosure_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    ComponentFamilyFields :=
  ofClosedPlacements
    (ClosedPlacementClosure.closedPlacementFamily_of_generatedClosure
      F closure H)

/-- Repackage a generated-closure family with reduced metric hypotheses as
component-family fields. -/
def of_generatedClosure_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    ComponentFamilyFields :=
  ofClosedPlacements
    (ClosedPlacementClosure.closedPlacementFamily_of_generatedClosure_reduced
      F closure H)

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

/-- Exact block-form target from any family of checked closed placements,
routed through the component-family facade. -/
theorem targetUpperConstructionFiveSixteen_of_closedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen := by
  exact (ofClosedPlacements H).targetUpperConstructionFiveSixteen

/-- Arbitrary-vertex target from any family of checked closed placements,
routed through the component-family facade. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    (H :
      forall (k : Nat) (hk : 0 < k),
        DeformedPlacement.ClosedPlacement k hk) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact (ofClosedPlacements H).targetUpperConstructionFiveSixteenArbitrary

/-- Exact block-form target from pointwise closed-placement existence. -/
theorem targetUpperConstructionFiveSixteen_of_exists_closedPlacement_eq
    (point :
      forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2)
    (H :
      forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point = point k hk) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen := by
  exact
    (of_exists_closedPlacement_eq point H).targetUpperConstructionFiveSixteen

/-- Arbitrary-vertex target from pointwise closed-placement existence. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exists_closedPlacement_eq
    (point :
      forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2)
    (H :
      forall (k : Nat) (hk : 0 < k),
        exists P : DeformedPlacement.ClosedPlacement k hk,
          P.point = point k hk) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (of_exists_closedPlacement_eq point H).targetUpperConstructionFiveSixteenArbitrary

/-- Exact block-form target from all-positive generated closure and full
metric hypotheses, routed through component-family fields. -/
theorem targetUpperConstructionFiveSixteen_of_generatedClosure_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen := by
  exact
    (of_generatedClosure_family F closure H).targetUpperConstructionFiveSixteen

/-- Arbitrary-vertex target from all-positive generated closure and full
metric hypotheses, routed through component-family fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedClosure_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (of_generatedClosure_family F closure H).targetUpperConstructionFiveSixteenArbitrary

/-- Exact block-form target from all-positive generated closure and reduced
metric hypotheses, routed through component-family fields. -/
theorem targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen := by
  exact
    (of_generatedClosure_family_reduced F closure H).targetUpperConstructionFiveSixteen

/-- Arbitrary-vertex target from all-positive generated closure and reduced
metric hypotheses, routed through component-family fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedClosure_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (of_generatedClosure_family_reduced F closure H).targetUpperConstructionFiveSixteenArbitrary

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

/-- Generated-closure exact block-form wrapper through component-family
fields, using full metric hypotheses. -/
theorem targetUpperConstructionFiveSixteen_of_generatedClosure_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    targetUpperConstructionFiveSixteen := by
  exact
    ComponentFamilyFields.targetUpperConstructionFiveSixteen_of_generatedClosure_family
      F closure H

/-- Generated-closure arbitrary-vertex wrapper through component-family
fields, using full metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedClosure_family
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H : GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ComponentFamilyFields.targetUpperConstructionFiveSixteenArbitrary_of_generatedClosure_family
      F closure H

/-- Generated-closure exact block-form wrapper through component-family
fields, using reduced metric hypotheses. -/
theorem targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteen := by
  exact
    ComponentFamilyFields.targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
      F closure H

/-- Generated-closure arbitrary-vertex wrapper through component-family
fields, using reduced metric hypotheses. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_generatedClosure_family_reduced
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let Hcomp :=
    ComponentFamilyFields.of_generatedClosure_family_reduced F closure H
  exact Hcomp.targetUpperConstructionFiveSixteenArbitrary

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
