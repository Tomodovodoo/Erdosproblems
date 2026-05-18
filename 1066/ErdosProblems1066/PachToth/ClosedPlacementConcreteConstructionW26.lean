import ErdosProblems1066.PachToth.ClosedPlacementCrossConnectorEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementWitnessAssemblyW25
import ErdosProblems1066.PachToth.FreePlacementFieldsInhabitationW25

set_option autoImplicit false

/-!
# W26 concrete closed-placement construction

This file gives the direct non-rigid Pach--Toth construction target a smaller
Lean-facing surface.  For one block count, the concrete orbit data consists of
a cyclic point map, successor transition maps, global separation, same-block
unit edges, and the four named successor connector unit equations.  The finite
connector relation is then discharged by the checked four-case lemma from W19.

At family level, this is repackaged into the W24 free-placement fields, the
W25 closed-placement family, and the existing exact/arbitrary Pach--Toth target
reducers.  The final remaining construction target is therefore exposed as
`Nonempty ConcreteClosedOrbitFamily`, equivalently W24 minimal free-placement
fields plus a successor orbit equation for their point maps.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementConcreteConstructionW26

open Arithmetic
open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementSourceFieldsW24.MinimalFreePlacementFields

abbrev ClosedPlacementFamily : Type :=
  ClosedPlacementWitnessAssemblyW25.ClosedPlacementFamily

abbrev ExplicitCyclicOrbitEdgeDataFamily : Type :=
  FreePlacementFieldsInhabitationW25.ExplicitCyclicOrbitEdgeDataFamily

abbrev ExactCrossConnectorUnitCertificate
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2) : Prop :=
  ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate
    hk point

/-- Concrete cyclic point-orbit data for one positive block count.  The
successor connector field stores only the four named unit equations; W19 turns
those four equations into the quantified `CrossBlock.NextConnector` field. -/
structure ConcreteClosedOrbitData (k : Nat) (hk : 0 < k) where
  point : Fin k -> LocalVertex -> R2
  step : Fin k -> OrientationData.OrientedTransition
  successor_eq :
    forall i : Fin k, forall v : LocalVertex,
      point (cyclicSucc hk i) v = (step i).placeNext (point i) v
  separated :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)
  same_block_edges_unit :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
      adj u v = true ->
        _root_.eucDist (point i u) (point i v) = 1
  cross_connector_named_units :
    ExactCrossConnectorUnitCertificate hk point

namespace ConcreteClosedOrbitData

/-- The four named connector equations imply the quantified connector field
used by `DeformedPlacement.ClosedPlacement`. -/
def crossConnectorEdgesUnit
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk) :
    forall (i : Fin k) (u v : LocalVertex),
      CrossBlock.NextConnector u v ->
        _root_.eucDist (D.point i u)
          (D.point (cyclicSucc hk i) v) = 1 :=
  D.cross_connector_named_units.crossConnectorEdgesUnit

/-- Forget the successor maps and keep the direct point/edge certificate. -/
def toExplicitCyclicPointEdgeData
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk) :
    NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData k hk where
  point := D.point
  separated := D.separated
  same_block_edges_unit := D.same_block_edges_unit
  cross_connector_edges_unit := D.crossConnectorEdgesUnit

/-- Keep the successor maps and expose the orbit-style certificate. -/
def toExplicitCyclicOrbitEdgeData
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk) :
    NonRigidClosedPlacementInterface.ExplicitCyclicOrbitEdgeData k hk where
  point := D.point
  step := D.step
  successor_eq := D.successor_eq
  connector_unit_edges := by
    intro i u v hconn
    have hunit := D.crossConnectorEdgesUnit i u v hconn
    simpa [D.successor_eq i v] using hunit
  separated := D.separated
  same_block_edges_unit := D.same_block_edges_unit

/-- Concrete orbit data gives the checked deformed closed placement. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  D.toExplicitCyclicPointEdgeData.toClosedPlacement

@[simp]
theorem toExplicitCyclicPointEdgeData_point
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk)
    (i : Fin k) (v : LocalVertex) :
    D.toExplicitCyclicPointEdgeData.point i v = D.point i v :=
  rfl

@[simp]
theorem toExplicitCyclicOrbitEdgeData_point
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk)
    (i : Fin k) (v : LocalVertex) :
    D.toExplicitCyclicOrbitEdgeData.point i v = D.point i v :=
  rfl

@[simp]
theorem toClosedPlacement_point
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk)
    (i : Fin k) (v : LocalVertex) :
    D.toClosedPlacement.point i v = D.point i v :=
  rfl

/-- The four named equations can be recovered from the checked closed
placement produced by this data. -/
def recoveredNamedConnectorUnits
    {k : Nat} {hk : 0 < k}
    (D : ConcreteClosedOrbitData k hk) :
    ExactCrossConnectorUnitCertificate hk D.toClosedPlacement.point :=
  ClosedPlacementCrossConnectorEdgesW19.ofClosedPlacement D.toClosedPlacement

end ConcreteClosedOrbitData

/-- Concrete closed-orbit data for every positive block count. -/
structure ConcreteClosedOrbitFamily where
  data :
    forall (k : Nat) (hk : 0 < k), ConcreteClosedOrbitData k hk

namespace ConcreteClosedOrbitFamily

def point
    (F : ConcreteClosedOrbitFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> LocalVertex -> R2 :=
  (F.data k hk).point

def toExplicitCyclicOrbitEdgeDataFamily
    (F : ConcreteClosedOrbitFamily) :
    ExplicitCyclicOrbitEdgeDataFamily :=
  fun k hk => (F.data k hk).toExplicitCyclicOrbitEdgeData

def toClosedPlacementFamily
    (F : ConcreteClosedOrbitFamily) :
    ClosedPlacementFamily :=
  fun k hk => (F.data k hk).toClosedPlacement

/-- Family-level concrete orbit data is exactly the W24 free-placement source
surface after forgetting the successor maps. -/
def toMinimalFreePlacementFields
    (F : ConcreteClosedOrbitFamily) :
    MinimalFreePlacementFields where
  point := F.point
  separated := fun k hk => (F.data k hk).separated
  same_block_edges_unit := fun k hk =>
    (F.data k hk).same_block_edges_unit
  cross_connector_edges_unit := fun k hk =>
    (F.data k hk).crossConnectorEdgesUnit

@[simp]
theorem toMinimalFreePlacementFields_point
    (F : ConcreteClosedOrbitFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    F.toMinimalFreePlacementFields.point k hk i v =
      (F.data k hk).point i v :=
  rfl

@[simp]
theorem toClosedPlacementFamily_point
    (F : ConcreteClosedOrbitFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (F.toClosedPlacementFamily k hk).point i v =
      (F.data k hk).point i v :=
  rfl

theorem exactTarget
    (F : ConcreteClosedOrbitFamily) :
    targetUpperConstructionFiveSixteen :=
  F.toMinimalFreePlacementFields.targetUpperConstructionFiveSixteen

theorem arbitraryTarget
    (F : ConcreteClosedOrbitFamily) :
    targetUpperConstructionFiveSixteenArbitrary :=
  F.toMinimalFreePlacementFields.targetUpperConstructionFiveSixteenArbitrary

theorem exactTarget_of_nonempty :
    Nonempty ConcreteClosedOrbitFamily ->
      targetUpperConstructionFiveSixteen := by
  rintro ⟨F⟩
  exact F.exactTarget

theorem arbitraryTarget_of_nonempty :
    Nonempty ConcreteClosedOrbitFamily ->
      targetUpperConstructionFiveSixteenArbitrary := by
  rintro ⟨F⟩
  exact F.arbitraryTarget

end ConcreteClosedOrbitFamily

/-- The extra algebraic data needed to view W24 minimal free-placement fields
as an actual successor orbit: a transition step for each block and the
successor equation for the existing point maps. -/
structure MinimalFieldsWithOrbitClosure where
  fields : MinimalFreePlacementFields
  step :
    forall (k : Nat) (_hk : 0 < k),
      Fin k -> OrientationData.OrientedTransition
  successor_eq :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (v : LocalVertex),
      fields.point k hk (cyclicSucc hk i) v =
        (step k hk i).placeNext (fields.point k hk i) v

namespace MinimalFieldsWithOrbitClosure

/-- Extract the four named connector equations already present in W24 minimal
free-placement fields. -/
def namedConnectorUnits
    (M : MinimalFieldsWithOrbitClosure)
    (k : Nat) (hk : 0 < k) :
    ExactCrossConnectorUnitCertificate hk (M.fields.point k hk) where
  t2_2_t1_1 := fun i =>
    M.fields.cross_connector_edges_unit k hk i T2_2 T1_1
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T2_2_T1_1
  t2_2_t1_2 := fun i =>
    M.fields.cross_connector_edges_unit k hk i T2_2 T1_2
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T2_2_T1_2
  t4_0_t0_0 := fun i =>
    M.fields.cross_connector_edges_unit k hk i T4_0 T0_0
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T4_0_T0_0
  t4_0_t0_2 := fun i =>
    M.fields.cross_connector_edges_unit k hk i T4_0 T0_2
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T4_0_T0_2

/-- W24 minimal free-placement fields plus successor closure give concrete
closed-orbit data. -/
def toConcreteClosedOrbitFamily
    (M : MinimalFieldsWithOrbitClosure) :
    ConcreteClosedOrbitFamily where
  data := fun k hk =>
    { point := M.fields.point k hk
      step := M.step k hk
      successor_eq := M.successor_eq k hk
      separated := M.fields.separated k hk
      same_block_edges_unit := M.fields.same_block_edges_unit k hk
      cross_connector_named_units := M.namedConnectorUnits k hk }

@[simp]
theorem toConcreteClosedOrbitFamily_point
    (M : MinimalFieldsWithOrbitClosure)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (M.toConcreteClosedOrbitFamily.data k hk).point i v =
      M.fields.point k hk i v :=
  rfl

end MinimalFieldsWithOrbitClosure

namespace ConcreteClosedOrbitFamily

/-- Concrete closed-orbit data can be read back as W24 minimal fields plus the
stored successor closure equations. -/
def toMinimalFieldsWithOrbitClosure
    (F : ConcreteClosedOrbitFamily) :
    MinimalFieldsWithOrbitClosure where
  fields := F.toMinimalFreePlacementFields
  step := fun k hk => (F.data k hk).step
  successor_eq := by
    intro k hk i v
    exact (F.data k hk).successor_eq i v

@[simp]
theorem toMinimalFieldsWithOrbitClosure_fields_point
    (F : ConcreteClosedOrbitFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    F.toMinimalFieldsWithOrbitClosure.fields.point k hk i v =
      (F.data k hk).point i v :=
  rfl

end ConcreteClosedOrbitFamily

/-- The W26 direct concrete-orbit subgoal is equivalent to W24 minimal
free-placement fields plus successor orbit closure for the same point maps. -/
theorem nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure :
    Nonempty ConcreteClosedOrbitFamily <->
      Nonempty MinimalFieldsWithOrbitClosure := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.toMinimalFieldsWithOrbitClosure⟩
  · rintro ⟨M⟩
    exact ⟨M.toConcreteClosedOrbitFamily⟩

theorem exactTarget_of_minimalFieldsWithOrbitClosure :
    Nonempty MinimalFieldsWithOrbitClosure ->
      targetUpperConstructionFiveSixteen := by
  intro h
  exact
    ConcreteClosedOrbitFamily.exactTarget_of_nonempty
      ((nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure).2 h)

theorem arbitraryTarget_of_minimalFieldsWithOrbitClosure :
    Nonempty MinimalFieldsWithOrbitClosure ->
      targetUpperConstructionFiveSixteenArbitrary := by
  intro h
  exact
    ConcreteClosedOrbitFamily.arbitraryTarget_of_nonempty
      ((nonempty_concreteClosedOrbitFamily_iff_minimalFieldsWithOrbitClosure).2 h)

end

end ClosedPlacementConcreteConstructionW26
end PachToth
end ErdosProblems1066
