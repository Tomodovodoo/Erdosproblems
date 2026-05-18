import ErdosProblems1066.PachToth.ExplicitClosedPlacementInputPackageW20
import ErdosProblems1066.PachToth.GeneratedChainFamilyProducerW20
import ErdosProblems1066.PachToth.NonRigidClosedPlacementDataW19

set_option autoImplicit false

/-!
# W24 free placement source fields

This file records the source-field surface for a free/non-rigid placement
route, away from the blocked rigid translation and connector role-hinge
specialization.  The tree already contains several conditional non-rigid
interfaces:

* `DeformedPlacement.ClosedPlacement`;
* `GeometricSoundness.ExplicitEdgeSoundness`;
* `ClosedPlacementNonRigidComponents.Components`;
* `NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData`;
* generated-chain W20 fields with closure and reduced metric hypotheses.

There is no unconditional producer of those geometric facts in the current
tree.  The minimal missing hypotheses are therefore named below as direct
free-placement fields, and all downstream bridges are proved from them.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FreePlacementSourceFieldsW24

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev ExplicitEdgeSoundness (k : Nat) (hk : 0 < k) : Type :=
  GeometricSoundness.ExplicitEdgeSoundness k hk

abbrev ClosedPlacement (k : Nat) (hk : 0 < k) : Type :=
  DeformedPlacement.ClosedPlacement k hk

abbrev ExplicitCyclicPointEdgeData (k : Nat) (hk : 0 < k) : Type :=
  NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk

abbrev Components (k : Nat) (hk : 0 < k) : Type :=
  ClosedPlacementNonRigidComponents.Components k hk

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  NonRigidClosedPlacementDataW19.ExplicitClosedPlacementCertificateFamily

abbrev W20SourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev W20ReducedSourceFields : Type :=
  ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields

abbrev W20InputPackage : Type :=
  ExplicitClosedPlacementInputPackageW20.W19InputPackage

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

/-- The exact missing free-placement hypotheses for every positive block
count.  These fields are intentionally direct geometric facts about the
provided point maps; they do not mention translated rigid copies, connector
roles, or role-hinge realizations. -/
structure MinimalFreePlacementFields where
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

namespace MinimalFreePlacementFields

/-- Direct free-placement fields as non-rigid component data at a fixed block
count. -/
def toComponents
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) :
    Components k hk where
  point := S.point k hk
  separated := S.separated k hk
  same_block_edges_unit := S.same_block_edges_unit k hk
  successor_connector_edges_unit := S.cross_connector_edges_unit k hk

@[simp]
theorem toComponents_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (S.toComponents k hk).point i v = S.point k hk i v :=
  rfl

/-- Direct free-placement fields as the canonical deformed closed placement. -/
def toClosedPlacement
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacement k hk :=
  (S.toComponents k hk).toClosedPlacement

@[simp]
theorem toClosedPlacement_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (S.toClosedPlacement k hk).point i v = S.point k hk i v :=
  rfl

/-- Direct free-placement fields as explicit edge soundness. -/
def toExplicitEdgeSoundness
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) :
    ExplicitEdgeSoundness k hk :=
  (S.toClosedPlacement k hk).toExplicitEdgeSoundness

/-- Direct free-placement fields as the smallest existing non-rigid point and
edge data interface. -/
def toExplicitCyclicPointEdgeData
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) :
    ExplicitCyclicPointEdgeData k hk where
  point := S.point k hk
  separated := S.separated k hk
  same_block_edges_unit := S.same_block_edges_unit k hk
  cross_connector_edges_unit := S.cross_connector_edges_unit k hk

@[simp]
theorem toExplicitCyclicPointEdgeData_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (S.toExplicitCyclicPointEdgeData k hk).point i v =
      S.point k hk i v :=
  rfl

/-- Direct free-placement fields as the W19 explicit certificate family. -/
def toCertificateFamily
    (S : MinimalFreePlacementFields) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk =>
    NonRigidClosedPlacementDataW19.certificateOfComponents
      (S.toComponents k hk)

@[simp]
theorem toCertificateFamily_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (S.toCertificateFamily k hk).point i v = S.point k hk i v :=
  rfl

/-- Exact-block Pach--Toth target from direct free-placement fields. -/
theorem targetUpperConstructionFiveSixteen
    (S : MinimalFreePlacementFields) :
    ExactTarget :=
  DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
    S.toClosedPlacement

/-- Arbitrary-vertex Pach--Toth target from direct free-placement fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (S : MinimalFreePlacementFields) :
    ArbitraryTarget :=
  NonRigidClosedPlacementInterface.targetUpperConstructionFiveSixteenArbitrary_of_closedPlacements
    S.toClosedPlacement

/-- Pointwise arbitrary upper bound from direct free-placement fields. -/
theorem upper_bound_five_sixteen_arbitrary
    (S : MinimalFreePlacementFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= ceilDiv (5 * n) 16 :=
  S.targetUpperConstructionFiveSixteenArbitrary n

end MinimalFreePlacementFields

/-! ## Adapters from existing non-rigid/free placement surfaces -/

/-- Any family of checked deformed placements is already a free-placement
source. -/
def ofClosedPlacements
    (H : forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk) :
    MinimalFreePlacementFields where
  point := fun k hk => (H k hk).point
  separated := fun k hk => (H k hk).separated
  same_block_edges_unit := fun k hk => (H k hk).same_block_edges_unit
  cross_connector_edges_unit := fun k hk =>
    (H k hk).cross_connector_edges_unit

@[simp]
theorem ofClosedPlacements_point
    (H : forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (ofClosedPlacements H).point k hk i v = (H k hk).point i v :=
  rfl

/-- Component families from `ClosedPlacementNonRigidComponents` are free
placement source fields. -/
def ofComponentFamily
    (F : NonRigidClosedPlacementDataW19.ComponentFamily) :
    MinimalFreePlacementFields :=
  ofClosedPlacements F.toClosedPlacements

/-- Raw W19 closed-placement family fields are free placement source fields. -/
def ofRawClosedPlacementFamilyFields
    (F : NonRigidClosedPlacementDataW19.RawClosedPlacementFamilyFields) :
    MinimalFreePlacementFields where
  point := F.point
  separated := F.separated
  same_block_edges_unit := F.same_block_edges_unit
  cross_connector_edges_unit := F.successor_connector_edges_unit

/-- Existing explicit cyclic point/edge data is exactly the same free
placement source surface. -/
def ofExplicitCyclicPointEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      ExplicitCyclicPointEdgeData k hk) :
    MinimalFreePlacementFields :=
  ofClosedPlacements (fun k hk => (H k hk).toClosedPlacement)

/-- Existing successor-orbit non-rigid data also supplies free placement
source fields after forgetting the transition equation. -/
def ofExplicitCyclicOrbitEdgeData
    (H : forall (k : Nat) (hk : 0 < k),
      NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk) :
    MinimalFreePlacementFields :=
  ofClosedPlacements (fun k hk => (H k hk).toClosedPlacement)

/-- Existing same/opposite orbit data supplies free placement source fields
after forgetting the transition word. -/
def ofSameOppositeCyclicOrbitData
    {O : Figure2Certificate.SameOppositeTransitionObligations}
    (H : forall (k : Nat) (hk : 0 < k),
      NonRigidClosedPlacementInterface.SameOppositeCyclicOrbitData O k hk) :
    MinimalFreePlacementFields :=
  ofClosedPlacements (fun k hk => (H k hk).toClosedPlacement)

/-- Reduced generated closed-placement obligations are a free placement source
once their generated periods and metric fields are supplied. -/
def ofGeneratedReducedClosedPlacementFamilyObligations
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (B :
      NonRigidClosedPlacementDataW19.GeneratedReducedClosedPlacementFamilyObligations
        F) :
    MinimalFreePlacementFields :=
  ofClosedPlacements B.toClosedPlacements

/-! ## W20 handoffs -/

namespace W20SourceFields

/-- Raw W20 generated-chain source fields as the reduced W20 source bundle
used by `ExplicitClosedPlacementInputPackageW20`. -/
def toReducedSourceFields
    (S : W20SourceFields) :
    W20ReducedSourceFields where
  family := S.family
  closure := S.closures
  reducedMetric := S.reducedMetric

/-- Raw W20 generated-chain source fields as the W19 input package. -/
def toInputPackage
    (S : W20SourceFields) :
    W20InputPackage :=
  S.toReducedSourceFields.toInputPackage

/-- Raw W20 generated-chain source fields produce the W19 certificate family. -/
def toCertificateFamily
    (S : W20SourceFields) :
    ExplicitClosedPlacementCertificateFamily :=
  S.toInputPackage.explicitClosedPlacementCertificate

/-- Raw W20 generated-chain source fields produce checked deformed
placements. -/
def toClosedPlacements
    (S : W20SourceFields) :
    forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk :=
  S.toInputPackage.closedPlacementFamily

/-- Raw W20 generated-chain source fields are also free-placement fields after
the W19 certificate-family handoff. -/
def toMinimalFreePlacementFields
    (S : W20SourceFields) :
    MinimalFreePlacementFields :=
  ofClosedPlacements S.toClosedPlacements

theorem targetUpperConstructionFiveSixteen
    (S : W20SourceFields) :
    ExactTarget :=
  S.toReducedSourceFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (S : W20SourceFields) :
    ArbitraryTarget :=
  S.toReducedSourceFields.targetUpperConstructionFiveSixteenArbitrary

end W20SourceFields

namespace W20ReducedSourceFields

/-- The W20 reduced source bundle produces checked deformed placements via
the W19 input package. -/
def toClosedPlacements
    (S : W20ReducedSourceFields) :
    forall (k : Nat) (hk : 0 < k), ClosedPlacement k hk :=
  S.toInputPackage.closedPlacementFamily

/-- The W20 reduced source bundle is a free-placement source after its W19
handoff. -/
def toMinimalFreePlacementFields
    (S : W20ReducedSourceFields) :
    MinimalFreePlacementFields :=
  ofClosedPlacements S.toClosedPlacements

@[simp]
theorem toMinimalFreePlacementFields_point
    (S : W20ReducedSourceFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (S.toMinimalFreePlacementFields).point k hk i v =
      (S.toInputPackage.closedPlacementFamily k hk).point i v :=
  rfl

end W20ReducedSourceFields

/-- Public exact target from the minimal free-placement source fields. -/
theorem targetUpperConstructionFiveSixteen_of_freePlacementSourceFields
    (S : MinimalFreePlacementFields) :
    targetUpperConstructionFiveSixteen :=
  S.targetUpperConstructionFiveSixteen

/-- Public arbitrary target from the minimal free-placement source fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_freePlacementSourceFields
    (S : MinimalFreePlacementFields) :
    targetUpperConstructionFiveSixteenArbitrary :=
  S.targetUpperConstructionFiveSixteenArbitrary

/-- Public upper-bound wrapper from the minimal free-placement source fields. -/
theorem upper_bound_five_sixteen_arbitrary_of_freePlacementSourceFields
    (S : MinimalFreePlacementFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= ceilDiv (5 * n) 16 :=
  S.upper_bound_five_sixteen_arbitrary n

end

end FreePlacementSourceFieldsW24
end PachToth

namespace Verified

abbrev PachTothW24FreePlacementSourceFields :=
  PachToth.FreePlacementSourceFieldsW24.MinimalFreePlacementFields

theorem targetUpperConstructionFiveSixteen_of_pachtoth_w24_freePlacementSourceFields
    (S : PachTothW24FreePlacementSourceFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PachToth.FreePlacementSourceFieldsW24.targetUpperConstructionFiveSixteen_of_freePlacementSourceFields
    S

theorem targetUpperConstructionFiveSixteenArbitrary_of_pachtoth_w24_freePlacementSourceFields
    (S : PachTothW24FreePlacementSourceFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  PachToth.FreePlacementSourceFieldsW24.targetUpperConstructionFiveSixteenArbitrary_of_freePlacementSourceFields
    S

theorem upper_bound_five_sixteen_arbitrary_of_pachtoth_w24_freePlacementSourceFields
    (S : PachTothW24FreePlacementSourceFields) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16 :=
  PachToth.FreePlacementSourceFieldsW24.upper_bound_five_sixteen_arbitrary_of_freePlacementSourceFields
    S n

end Verified
end ErdosProblems1066
