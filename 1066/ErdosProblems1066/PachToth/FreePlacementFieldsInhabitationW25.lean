import ErdosProblems1066.PachToth.FreePlacementSourceFieldsW24

set_option autoImplicit false

/-!
# W25 free-placement field inhabitation bridge

The W24 source surface isolates the exact geometric fields needed for the
free/non-rigid closed-placement route.  This file checks whether the existing
lower-level interfaces already inhabit that surface.

There is still no unconditional producer of the all-`k` geometric family in
the current tree.  What is available is exact, conditional equivalence with
the existing deformed closed-placement, component, and explicit cyclic
point/edge family surfaces, plus a one-way bridge from explicit edge
soundness by reading its canonical global configuration on block-local
vertices.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FreePlacementFieldsInhabitationW25

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementSourceFieldsW24.MinimalFreePlacementFields

abbrev ComponentFamily : Type :=
  NonRigidClosedPlacementDataW19.ComponentFamily

abbrev ClosedPlacementFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    DeformedPlacement.ClosedPlacement k hk

abbrev ExplicitCyclicPointEdgeDataFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk

abbrev ExplicitCyclicOrbitEdgeDataFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk

abbrev ExplicitEdgeSoundnessFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    GeometricSoundness.ExplicitEdgeSoundness k hk

/-- The raw point/separation/edge fields, stated without any downstream
closed-placement packaging.  This is definitionally the same data as the W24
minimal source surface. -/
structure PointSeparationConnectorFacts where
  point : forall (k : Nat) (_hk : 0 < k), Fin k -> LocalVertex -> R2
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
  cross_connector_edges_unit :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (point k hk i u)
          (point k hk (cyclicSucc hk i) v) = 1

namespace PointSeparationConnectorFacts

def toMinimalFreePlacementFields
    (F : PointSeparationConnectorFacts) :
    MinimalFreePlacementFields where
  point := F.point
  separated := F.separated
  same_block_edges_unit := F.same_block_edges_unit
  cross_connector_edges_unit := F.cross_connector_edges_unit

def ofMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    PointSeparationConnectorFacts where
  point := S.point
  separated := S.separated
  same_block_edges_unit := S.same_block_edges_unit
  cross_connector_edges_unit := S.cross_connector_edges_unit

@[simp]
theorem toMinimalFreePlacementFields_point
    (F : PointSeparationConnectorFacts)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    F.toMinimalFreePlacementFields.point k hk i v = F.point k hk i v :=
  rfl

@[simp]
theorem ofMinimalFreePlacementFields_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (ofMinimalFreePlacementFields S).point k hk i v =
      S.point k hk i v :=
  rfl

end PointSeparationConnectorFacts

/-- Exact equivalence between W24 minimal fields and their raw
point/separation/connector statement. -/
def minimalEquivPointSeparationConnectorFacts :
    MinimalFreePlacementFields ≃ PointSeparationConnectorFacts where
  toFun := PointSeparationConnectorFacts.ofMinimalFreePlacementFields
  invFun := PointSeparationConnectorFacts.toMinimalFreePlacementFields
  left_inv := by
    intro S
    cases S
    rfl
  right_inv := by
    intro F
    cases F
    simp [PointSeparationConnectorFacts.ofMinimalFreePlacementFields,
      PointSeparationConnectorFacts.toMinimalFreePlacementFields]

/-- Exact equivalence with the existing non-rigid component family. -/
def minimalEquivComponentFamily :
    MinimalFreePlacementFields ≃ ComponentFamily where
  toFun := fun S => { components := fun k hk => S.toComponents k hk }
  invFun := FreePlacementSourceFieldsW24.ofComponentFamily
  left_inv := by
    intro S
    cases S
    rfl
  right_inv := by
    intro C
    cases C
    rfl

/-- Exact equivalence with all checked deformed closed placements. -/
def minimalEquivClosedPlacementFamily :
    MinimalFreePlacementFields ≃ ClosedPlacementFamily where
  toFun := fun S k hk => S.toClosedPlacement k hk
  invFun := FreePlacementSourceFieldsW24.ofClosedPlacements
  left_inv := by
    intro S
    cases S
    rfl
  right_inv := by
    intro P
    funext k hk
    rcases hP : P k hk with ⟨point, separated, same, cross⟩
    simp [FreePlacementSourceFieldsW24.ofClosedPlacements,
      FreePlacementSourceFieldsW24.MinimalFreePlacementFields.toClosedPlacement,
      FreePlacementSourceFieldsW24.MinimalFreePlacementFields.toComponents,
      ClosedPlacementNonRigidComponents.Components.toClosedPlacement,
      hP]

/-- Exact equivalence with the smallest explicit cyclic point/edge data
family. -/
def minimalEquivExplicitCyclicPointEdgeDataFamily :
    MinimalFreePlacementFields ≃ ExplicitCyclicPointEdgeDataFamily where
  toFun := fun S k hk => S.toExplicitCyclicPointEdgeData k hk
  invFun := FreePlacementSourceFieldsW24.ofExplicitCyclicPointEdgeData
  left_inv := by
    intro S
    cases S
    rfl
  right_inv := by
    intro D
    funext k hk
    rcases hD : D k hk with ⟨point, separated, same, cross⟩
    simp [FreePlacementSourceFieldsW24.ofExplicitCyclicPointEdgeData,
      FreePlacementSourceFieldsW24.ofClosedPlacements,
      FreePlacementSourceFieldsW24.MinimalFreePlacementFields.toExplicitCyclicPointEdgeData,
      NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData.toClosedPlacement,
      NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData.toExplicitClosedPlacementCertificate,
      ClosedPlacementInterface.ExplicitClosedPlacementCertificate.toClosedPlacement,
      hD]

theorem nonempty_minimal_iff_pointSeparationConnectorFacts :
    Nonempty MinimalFreePlacementFields ↔
      Nonempty PointSeparationConnectorFacts :=
  minimalEquivPointSeparationConnectorFacts.nonempty_congr

theorem nonempty_minimal_iff_componentFamily :
    Nonempty MinimalFreePlacementFields ↔ Nonempty ComponentFamily :=
  minimalEquivComponentFamily.nonempty_congr

theorem nonempty_minimal_iff_closedPlacementFamily :
    Nonempty MinimalFreePlacementFields ↔ Nonempty ClosedPlacementFamily :=
  minimalEquivClosedPlacementFamily.nonempty_congr

theorem nonempty_minimal_iff_explicitCyclicPointEdgeDataFamily :
    Nonempty MinimalFreePlacementFields ↔
      Nonempty ExplicitCyclicPointEdgeDataFamily :=
  minimalEquivExplicitCyclicPointEdgeDataFamily.nonempty_congr

/-- Existing successor-orbit non-rigid data conditionally inhabits the W24
minimal free-placement fields after forgetting the transition equations. -/
def minimalOfExplicitCyclicOrbitEdgeDataFamily
    (D : ExplicitCyclicOrbitEdgeDataFamily) :
    MinimalFreePlacementFields :=
  FreePlacementSourceFieldsW24.ofExplicitCyclicOrbitEdgeData D

theorem nonempty_minimal_of_explicitCyclicOrbitEdgeDataFamily :
    Nonempty ExplicitCyclicOrbitEdgeDataFamily ->
      Nonempty MinimalFreePlacementFields := by
  rintro ⟨D⟩
  exact ⟨minimalOfExplicitCyclicOrbitEdgeDataFamily D⟩

/-- Read an explicit edge-soundness family as W24 minimal fields by using the
canonical global vertex encoding as the block-local point map. -/
def minimalOfExplicitEdgeSoundnessFamily
    (G : ExplicitEdgeSoundnessFamily) :
    MinimalFreePlacementFields where
  point := fun k hk i v =>
    (G k hk).config.pts (GeometricSoundness.globalVertex k i v)
  separated := by
    intro k hk i u j v hne
    exact
      (G k hk).config.sep
        (GeometricSoundness.globalVertex k i u)
        (GeometricSoundness.globalVertex k j v)
        (by
          intro hglobal
          exact hne ((BlockPartition.blockLocalEquiv k).injective hglobal))
  same_block_edges_unit := by
    intro k hk i u v huv hadj
    exact (G k hk).same_block_edges_unit i u v huv hadj
  cross_connector_edges_unit := by
    intro k hk i u v hconn
    exact (G k hk).cross_block_edges_unit i u v hconn

@[simp]
theorem minimalOfExplicitEdgeSoundnessFamily_point
    (G : ExplicitEdgeSoundnessFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalOfExplicitEdgeSoundnessFamily G).point k hk i v =
      (G k hk).config.pts (GeometricSoundness.globalVertex k i v) :=
  rfl

theorem nonempty_minimal_iff_explicitEdgeSoundnessFamily :
    Nonempty MinimalFreePlacementFields ↔
      Nonempty ExplicitEdgeSoundnessFamily := by
  constructor
  · rintro ⟨S⟩
    exact ⟨fun k hk => S.toExplicitEdgeSoundness k hk⟩
  · rintro ⟨G⟩
    exact ⟨minimalOfExplicitEdgeSoundnessFamily G⟩

/-- Conditional bridge back to checked deformed closed placements. -/
def closedPlacementFamilyOfMinimal
    (S : MinimalFreePlacementFields) :
    ClosedPlacementFamily :=
  minimalEquivClosedPlacementFamily S

/-- Conditional bridge to explicit edge soundness. -/
def explicitEdgeSoundnessFamilyOfMinimal
    (S : MinimalFreePlacementFields) :
    ExplicitEdgeSoundnessFamily :=
  fun k hk => S.toExplicitEdgeSoundness k hk

@[simp]
theorem closedPlacementFamilyOfMinimal_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementFamilyOfMinimal S k hk).point i v =
      S.point k hk i v :=
  rfl

@[simp]
theorem explicitEdgeSoundnessFamilyOfMinimal_config_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (explicitEdgeSoundnessFamilyOfMinimal S k hk).config.pts
        (GeometricSoundness.globalVertex k i v) =
      S.point k hk i v := by
  change (S.toClosedPlacement k hk).config.pts
      (GeometricSoundness.globalVertex k i v) =
    S.point k hk i v
  rw [DeformedPlacement.ClosedPlacement.config_pts_globalVertex]
  rfl

theorem targetUpperConstructionFiveSixteen_of_pointSeparationConnectorFacts
    (F : PointSeparationConnectorFacts) :
    targetUpperConstructionFiveSixteen :=
  F.toMinimalFreePlacementFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_of_closedPlacementFamily
    (P : ClosedPlacementFamily) :
    targetUpperConstructionFiveSixteen :=
  (FreePlacementSourceFieldsW24.ofClosedPlacements P).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteen_of_explicitEdgeSoundnessFamily
    (G : ExplicitEdgeSoundnessFamily) :
    targetUpperConstructionFiveSixteen :=
  (minimalOfExplicitEdgeSoundnessFamily G).targetUpperConstructionFiveSixteen

end

end FreePlacementFieldsInhabitationW25
end PachToth

namespace Verified

abbrev PachTothW25FreePlacementFields :=
  PachToth.FreePlacementFieldsInhabitationW25.MinimalFreePlacementFields

theorem pachtoth_w25_freePlacementFields_iff_closedPlacementFamily :
    Nonempty PachTothW25FreePlacementFields ↔
      Nonempty PachToth.FreePlacementFieldsInhabitationW25.ClosedPlacementFamily :=
  PachToth.FreePlacementFieldsInhabitationW25.nonempty_minimal_iff_closedPlacementFamily

theorem pachtoth_w25_freePlacementFields_iff_explicitEdgeSoundnessFamily :
    Nonempty PachTothW25FreePlacementFields ↔
      Nonempty PachToth.FreePlacementFieldsInhabitationW25.ExplicitEdgeSoundnessFamily :=
  PachToth.FreePlacementFieldsInhabitationW25.nonempty_minimal_iff_explicitEdgeSoundnessFamily

end Verified
end ErdosProblems1066
