import ErdosProblems1066.Swanepoel.PlanarTopologyExtractionBridgeW25

set_option autoImplicit false

/-!
# W26 actual planar-topology extraction frontier

The noncrossing unit-distance graph is already available for every
configuration.  This file packages the next genuinely missing object in the
outer-boundary route: a selected outer face of the canonical graph together
with the enclosure predicates for that face.

The package below is intentionally small.  It contains no counting, angle, long
arc, or triangle-run data; those are later boundary-analysis rows.  Its
nonemptiness is proved equivalent to each existing exact-topology target, so a
future construction can focus on this one planar-topology datum.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarTopologyActualExtractionW26

open PlanarTopologyExtractionBridgeW25
open TopologyExtractionFromNoncrossing

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  PlanarTopologyExtractionBridgeW25.CanonicalGraph C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  PlanarTopologyExtractionBridgeW25.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  PlanarTopologyExtractionBridgeW25.SelectedEnclosureData D

/-- The smallest actual topology object still missing after the graph
noncrossing theorem: choose the outer face and prove the enclosure predicates
for that same face. -/
structure ActualSelectedTopologyData (C : _root_.UDConfig n) where
  selectedOuterFace : SelectedOuterFaceData C
  enclosure : SelectedEnclosureData selectedOuterFace

namespace ActualSelectedTopologyData

variable {C : _root_.UDConfig n}

def faceBoundary
    (A : ActualSelectedTopologyData C) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (CanonicalGraph C) :=
  A.selectedOuterFace.faceBoundary

def outerFace
    (A : ActualSelectedTopologyData C) :
    A.faceBoundary.Face :=
  A.selectedOuterFace.outerFace

theorem outerFace_isOuter
    (A : ActualSelectedTopologyData C) :
    A.faceBoundary.IsOuterFace A.outerFace :=
  A.selectedOuterFace.outerFace_isOuter

def outerCycle
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  A.selectedOuterFace.outerCycle

def outerSimplePolygon
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryInterface.SimplePolygon (CanonicalGraph C) A.outerCycle :=
  A.selectedOuterFace.outerSimplePolygon

def outerEnclosure
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) A.faceBoundary A.outerFace :=
  A.enclosure.outerEnclosure

def toSplitExactTopologyFields
    (A : ActualSelectedTopologyData C) :
    SplitExactTopologyFields C :=
  Exists.intro A.selectedOuterFace (Nonempty.intro A.enclosure)

def toExactTopologyFields
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  TopologyExtractionFromNoncrossing.exactTopologyFields_of_split A.enclosure

def toConcreteNoncrossingTopologyFrontier
    (A : ActualSelectedTopologyData C) :
    ConcreteNoncrossingTopologyFrontier C :=
  TopologyExtractionFromNoncrossing.concreteNoncrossingTopologyFrontier_of_exactTopologyFields
    A.toExactTopologyFields

def toRemainingCoreTopologyRequirements
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  TopologyExtractionFromNoncrossing.remainingCoreTopologyRequirements_of_frontier
    A.toConcreteNoncrossingTopologyFrontier

def toMissingTopologyFacts
    (A : ActualSelectedTopologyData C) :
    JordanBoundaryConcrete.MissingTopologyFacts C :=
  A.enclosure.toMissingTopologyFacts

def toConcreteTopologyFacts
    (A : ActualSelectedTopologyData C) :
    PlanarTopologyExtractionBridgeW25.ConcreteTopologyFacts C :=
  A.enclosure.toConcreteTopologyFacts

@[simp]
theorem faceBoundary_eq
    (A : ActualSelectedTopologyData C) :
    A.faceBoundary = A.selectedOuterFace.faceBoundary :=
  rfl

@[simp]
theorem outerFace_eq
    (A : ActualSelectedTopologyData C) :
    A.outerFace = A.selectedOuterFace.outerFace :=
  rfl

@[simp]
theorem outerCycle_eq
    (A : ActualSelectedTopologyData C) :
    A.outerCycle = A.selectedOuterFace.outerCycle :=
  rfl

@[simp]
theorem outerCycle_length
    (A : ActualSelectedTopologyData C) :
    A.outerCycle.length =
      A.selectedOuterFace.faceBoundary.boundaryLength
        A.selectedOuterFace.outerFace :=
  rfl

theorem outerCycle_vertex_injective
    (A : ActualSelectedTopologyData C) :
    Function.Injective A.outerCycle.vertex :=
  A.selectedOuterFace.outerCycle_vertex_injective

theorem outerCycle_adjacent_unitDistanceAdj
    (A : ActualSelectedTopologyData C) (k : Fin A.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (CanonicalGraph C).config
      (A.outerCycle.vertex k)
      (A.outerCycle.vertex
        (PlanarInterface.cyclicSucc A.outerCycle.length_pos k)) :=
  A.selectedOuterFace.outerCycle_adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (A : ActualSelectedTopologyData C) (k : Fin A.outerCycle.length) :
    Geometry.Distance.eucDist (A.outerCycle.point k)
      (A.outerCycle.point
        (PlanarInterface.cyclicSucc A.outerCycle.length_pos k)) = 1 :=
  A.selectedOuterFace.outerCycle_edge_geometry_dist_eq_one k

theorem boundary_vertex_onBoundary
    (A : ActualSelectedTopologyData C) (k : Fin A.outerCycle.length) :
    A.outerEnclosure.onBoundary (A.outerCycle.vertex k) :=
  A.enclosure.outerCycle_vertex_onBoundary k

theorem boundary_point_insideOrOn
    (A : ActualSelectedTopologyData C) (k : Fin A.outerCycle.length) :
    A.outerEnclosure.insideOrOn (A.outerCycle.point k) :=
  A.enclosure.outerCycle_point_insideOrOn k

theorem all_vertices_insideOrOn
    (A : ActualSelectedTopologyData C) (v : Fin n) :
    A.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  A.enclosure.all_vertices_insideOrOn v

theorem onBoundary_iff_outerCycle
    (A : ActualSelectedTopologyData C) (v : Fin n) :
    A.outerEnclosure.onBoundary v <->
      Exists fun k : Fin A.outerCycle.length => A.outerCycle.vertex k = v :=
  A.enclosure.onBoundary_iff_outerCycle v

@[simp]
theorem toMissingTopologyFacts_faceBoundary
    (A : ActualSelectedTopologyData C) :
    A.toMissingTopologyFacts.faceBoundary = A.faceBoundary :=
  rfl

@[simp]
theorem toMissingTopologyFacts_outerFace
    (A : ActualSelectedTopologyData C) :
    A.toMissingTopologyFacts.outerFace = A.outerFace :=
  rfl

@[simp]
theorem toConcreteTopologyFacts_toCore
    (A : ActualSelectedTopologyData C) :
    A.toConcreteTopologyFacts.toCore = A.enclosure.toCore :=
  rfl

end ActualSelectedTopologyData

/-- The graph-theoretic noncrossing side is already theorem-proved for every
configuration and needs no topology assumptions. -/
theorem concreteGraphFacts_available
    (C : _root_.UDConfig n) :
    OuterBoundaryExistenceConcrete.ConcreteGraphFacts C :=
  TopologyExtractionFromNoncrossing.concreteGraphFacts C

/-- Nonempty `ActualSelectedTopologyData` is exactly the split selected
outer-face/enclosure field list exposed by the W25 frontier. -/
theorem nonempty_actualSelectedTopologyData_iff_splitExactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (ActualSelectedTopologyData C) <->
      SplitExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro A => exact A.toSplitExactTopologyFields
  case mpr =>
    intro h
    cases h with
    | intro D hE =>
      cases hE with
      | intro E =>
        exact Nonempty.intro { selectedOuterFace := D, enclosure := E }

/-- The exact topology field is no more and no less than the actual selected
outer-face plus enclosure package. -/
theorem exactTopologyFields_iff_nonempty_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    OuterBoundaryExistenceConcrete.ExactTopologyFields C <->
      Nonempty (ActualSelectedTopologyData C) := by
  exact
    Iff.trans
      (TopologyExtractionFromNoncrossing.splitExactTopologyFields_iff_exactTopologyFields
        C).symm
      (nonempty_actualSelectedTopologyData_iff_splitExactTopologyFields C).symm

/-- The concrete noncrossing frontier is blocked exactly by the actual
selected topology package, since the graph facts are automatic. -/
theorem concreteNoncrossingTopologyFrontier_iff_nonempty_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    ConcreteNoncrossingTopologyFrontier C <->
      Nonempty (ActualSelectedTopologyData C) := by
  rw [TopologyExtractionFromNoncrossing.concreteNoncrossingTopologyFrontier_iff_exactTopologyFields]
  exact exactTopologyFields_iff_nonempty_actualSelectedTopologyData C

/-- The core-topology target used downstream is equivalent to the same minimal
actual topology datum. -/
theorem remainingCoreTopologyRequirements_iff_nonempty_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C <->
      Nonempty (ActualSelectedTopologyData C) := by
  rw [OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_exactTopologyFields]
  exact exactTopologyFields_iff_nonempty_actualSelectedTopologyData C

/-- A global formulation of the precise missing planar-topology construction:
for every configuration, produce the actual selected outer face and its
enclosure predicates. -/
def GlobalActualSelectedTopologyExtractionTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (ActualSelectedTopologyData C)

theorem globalActualSelectedTopologyExtractionTarget_iff_outerBoundaryCoreTarget :
    GlobalActualSelectedTopologyExtractionTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget := by
  constructor
  case mp =>
    intro h n C
    exact
      (remainingCoreTopologyRequirements_iff_nonempty_actualSelectedTopologyData
        C).2 (h n C)
  case mpr =>
    intro h n C
    exact
      (remainingCoreTopologyRequirements_iff_nonempty_actualSelectedTopologyData
        C).1 (h n C)

theorem globalActualSelectedTopologyExtractionTarget_iff_nonCrossingFrontier :
    GlobalActualSelectedTopologyExtractionTarget <->
      forall (n : Nat) (C : _root_.UDConfig n),
        ConcreteNoncrossingTopologyFrontier C := by
  constructor
  case mp =>
    intro h n C
    exact
      (concreteNoncrossingTopologyFrontier_iff_nonempty_actualSelectedTopologyData
        C).2 (h n C)
  case mpr =>
    intro h n C
    exact
      (concreteNoncrossingTopologyFrontier_iff_nonempty_actualSelectedTopologyData
        C).1 (h n C)

end

end PlanarTopologyActualExtractionW26
end Swanepoel

namespace Verified

abbrev SwanepoelW26ActualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.PlanarTopologyActualExtractionW26.ActualSelectedTopologyData C

theorem swanepoelW26_actualSelectedTopologyData_exactly_remainingCoreTopology
    {n : Nat} (C : _root_.UDConfig n) :
    Swanepoel.OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C <->
      Nonempty (SwanepoelW26ActualSelectedTopologyData C) :=
  Swanepoel.PlanarTopologyActualExtractionW26.remainingCoreTopologyRequirements_iff_nonempty_actualSelectedTopologyData
    C

end Verified
end ErdosProblems1066
