import ErdosProblems1066.Swanepoel.ActualSelectedTopologyDataW27

set_option autoImplicit false

/-!
# W28 outer-boundary core source

This file sharpens the topology source needed by
`ActualSelectedTopologyDataW27`: an actual checked `OuterBoundaryCore` for the
canonical unit-distance graph.

The graph side is not part of this source.  For every `UDConfig`, the canonical
unit-distance graph and its pairwise noncrossing fact are already available.
The remaining topology blocker is exactly the selected outer face together
with enclosure data for that same face.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryCoreConstructionW28

open PlanarTopologyActualExtractionW26
open PlanarTopologyExtractionBridgeW25
open TopologyExtractionFromNoncrossing

noncomputable section

universe u

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.CanonicalGraph C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

/--
The concrete W28 source for the outer-boundary topology route.

This packages only the checked core.  The canonical graph facts are projected
separately, since they are already theorems of `UDConfig`.
-/
structure OuterBoundaryCoreSource (C : _root_.UDConfig n) where
  core : OuterBoundaryCore.{0} (CanonicalGraph C)

namespace OuterBoundaryCoreSource

variable {C : _root_.UDConfig n}

def toActualSelectedTopologyData
    (S : OuterBoundaryCoreSource C) :
    ActualSelectedTopologyData C :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
    S.core

def ofActualSelectedTopologyData
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryCoreSource C where
  core :=
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
      A

def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    OuterBoundaryCoreSource C where
  core := P

def ofSelectedOuterFaceAndEnclosure
    (D : PlanarTopologyExtractionBridgeW25.SelectedOuterFaceData C)
    (E : PlanarTopologyExtractionBridgeW25.SelectedEnclosureData D) :
    OuterBoundaryCoreSource C where
  core := PlanarTopologyExtractionBridgeW25.SelectedEnclosureData.toCore E

def ofMissingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    OuterBoundaryCoreSource C where
  core := T.toCore

def ofConcreteTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    OuterBoundaryCoreSource C where
  core := T.toCore

def ofPlanarBoundaryData
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (CanonicalGraph C)) :
    OuterBoundaryCoreSource C where
  core := P.core

def toMissingTopologyFacts
    (S : OuterBoundaryCoreSource C) :
    JordanBoundaryConcrete.MissingTopologyFacts.{0} C :=
  JordanBoundaryConcrete.MissingTopologyFacts.ofCore S.core

def toConcreteTopologyFacts
    (S : OuterBoundaryCoreSource C) :
    JordanTopologyFactsConcrete.TopologyFacts.{0} C :=
  JordanTopologyFactsConcrete.TopologyFacts.ofCore S.core

def toRemainingCoreTopologyRequirements
    (S : OuterBoundaryCoreSource C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_of_core
    S.core

def toConcreteNoncrossingTopologyFrontier
    (S : OuterBoundaryCoreSource C) :
    ConcreteNoncrossingTopologyFrontier C :=
  PlanarTopologyActualExtractionW26.ActualSelectedTopologyData.toConcreteNoncrossingTopologyFrontier
    S.toActualSelectedTopologyData

def toBoundaryCycleCertificate
    (S : OuterBoundaryCoreSource C) :
    OuterBoundaryCoreConstruction.BoundaryCycleCertificate
      (CanonicalGraph C) :=
  OuterBoundaryCoreConstruction.BoundaryCycleCertificate.ofCore S.core

@[simp]
theorem toActualSelectedTopologyData_toOuterBoundaryCore
    (S : OuterBoundaryCoreSource C) :
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
        S.toActualSelectedTopologyData =
      S.core := by
  cases S
  rfl

@[simp]
theorem ofActualSelectedTopologyData_core
    (A : ActualSelectedTopologyData C) :
    (ofActualSelectedTopologyData A).core =
      ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
        A :=
  rfl

@[simp]
theorem ofOuterBoundaryCore_core
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (ofOuterBoundaryCore P).core = P :=
  rfl

@[simp]
theorem ofSelectedOuterFaceAndEnclosure_core
    (D : PlanarTopologyExtractionBridgeW25.SelectedOuterFaceData C)
    (E : PlanarTopologyExtractionBridgeW25.SelectedEnclosureData D) :
    (ofSelectedOuterFaceAndEnclosure D E).core =
      PlanarTopologyExtractionBridgeW25.SelectedEnclosureData.toCore E :=
  rfl

@[simp]
theorem ofMissingTopologyFacts_core
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    (ofMissingTopologyFacts T).core = T.toCore :=
  rfl

@[simp]
theorem ofConcreteTopologyFacts_core
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    (ofConcreteTopologyFacts T).core = T.toCore :=
  rfl

@[simp]
theorem ofPlanarBoundaryData_core
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (CanonicalGraph C)) :
    (ofPlanarBoundaryData P).core = P.core :=
  rfl

@[simp]
theorem toMissingTopologyFacts_toCore
    (S : OuterBoundaryCoreSource C) :
    S.toMissingTopologyFacts.toCore = S.core := by
  cases S
  rfl

@[simp]
theorem toConcreteTopologyFacts_toCore
    (S : OuterBoundaryCoreSource C) :
    S.toConcreteTopologyFacts.toCore = S.core := by
  cases S
  rfl

@[simp]
theorem toBoundaryCycleCertificate_cycle
    (S : OuterBoundaryCoreSource C) :
    S.toBoundaryCycleCertificate.cycle = S.core.outerCycle :=
  rfl

theorem pairwiseNoncrossing
    (S : OuterBoundaryCoreSource C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  S.core.pairwiseNoncrossing

theorem outerCycle_vertex_injective
    (S : OuterBoundaryCoreSource C) :
    Function.Injective S.core.outerCycle.vertex :=
  S.core.outerCycle_vertex_injective

theorem outerCycle_edge_geometry_dist_eq_one
    (S : OuterBoundaryCoreSource C)
    (k : Fin S.core.outerCycle.length) :
    Geometry.Distance.eucDist (S.core.outerCycle.point k)
      (S.core.outerCycle.point
        (PlanarInterface.cyclicSucc S.core.outerCycle.length_pos k)) = 1 :=
  S.core.outerCycle_edge_geometry_dist_eq_one k

theorem all_vertices_insideOrOn
    (S : OuterBoundaryCoreSource C) (v : Fin n) :
    S.core.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  S.core.all_vertices_insideOrOn v

theorem onBoundary_iff_outerCycle
    (S : OuterBoundaryCoreSource C) (v : Fin n) :
    S.core.outerEnclosure.onBoundary v <->
      Exists fun k : Fin S.core.outerCycle.length =>
        S.core.outerCycle.vertex k = v :=
  S.core.onBoundary_iff_outer_cycle v

end OuterBoundaryCoreSource

variable (C : _root_.UDConfig n)

/-- The canonical graph-level facts are already available before any topology
source is supplied. -/
theorem concreteGraphFacts_available :
    OuterBoundaryExistenceConcrete.ConcreteGraphFacts C :=
  PlanarTopologyActualExtractionW26.concreteGraphFacts_available C

/-- The W28 source is exactly a checked outer-boundary core. -/
theorem nonempty_outerBoundaryCoreSource_iff_outerBoundaryCore :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.core
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (OuterBoundaryCoreSource.ofOuterBoundaryCore P)

/-- The W28 source is exactly the W27 actual selected-topology datum. -/
theorem nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (ActualSelectedTopologyData C) :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_outerBoundaryCore C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_outerBoundaryCore
      C).symm

/-- The W28 source is exactly the split selected-face/enclosure payload. -/
theorem nonempty_outerBoundaryCoreSource_iff_splitExactTopologyFields :
    Nonempty (OuterBoundaryCoreSource C) <->
      SplitExactTopologyFields C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (PlanarTopologyActualExtractionW26.nonempty_actualSelectedTopologyData_iff_splitExactTopologyFields
      C)

/-- The W28 source is exactly the raw exact topology field list. -/
theorem nonempty_outerBoundaryCoreSource_iff_exactTopologyFields :
    Nonempty (OuterBoundaryCoreSource C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_exactTopologyFields
      C)

/-- The W28 source is exactly the old missing-topology wrapper. -/
theorem nonempty_outerBoundaryCoreSource_iff_missingTopologyFacts :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_missingTopologyFacts
      C)

/-- The W28 source is exactly the concrete topology-facts wrapper. -/
theorem nonempty_outerBoundaryCoreSource_iff_concreteTopologyFacts :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (JordanTopologyFactsConcrete.TopologyFacts.{0} C) :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_concreteTopologyFacts
      C)

/-- The W28 source is exactly the remaining core-topology target. -/
theorem nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology :
    Nonempty (OuterBoundaryCoreSource C) <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_remainingCoreTopology
      C)

/-- The W28 source is exactly the noncrossing-to-topology frontier. -/
theorem nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier :
    Nonempty (OuterBoundaryCoreSource C) <->
      ConcreteNoncrossingTopologyFrontier C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_noncrossingFrontier
      C)

/-- The frontier is the automatic graph facts plus the W28 core source. -/
theorem noncrossingFrontier_iff_graphFacts_and_outerBoundaryCoreSource :
    ConcreteNoncrossingTopologyFrontier C <->
      OuterBoundaryExistenceConcrete.ConcreteGraphFacts C /\
        Nonempty (OuterBoundaryCoreSource C) := by
  constructor
  case mp =>
    intro h
    exact
      And.intro h.1
        ((nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).2 h)
  case mpr =>
    intro h
    exact
      (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).1 h.2

/-- Full planar-boundary data contains the W28 core source by forgetting
angle and subpolygon fields. -/
theorem nonempty_outerBoundaryCoreSource_of_planarBoundaryData
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (CanonicalGraph C)) :
    Nonempty (OuterBoundaryCoreSource C) :=
  Nonempty.intro (OuterBoundaryCoreSource.ofPlanarBoundaryData P)

/-- Concrete topology facts provide the W28 core source. -/
theorem nonempty_outerBoundaryCoreSource_of_concreteTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  Nonempty.intro (OuterBoundaryCoreSource.ofConcreteTopologyFacts T)

/-- Missing-topology facts provide the W28 core source. -/
theorem nonempty_outerBoundaryCoreSource_of_missingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  Nonempty.intro (OuterBoundaryCoreSource.ofMissingTopologyFacts T)

/-- Exact topology fields provide the W28 source, with graph facts still
coming from the canonical unit-distance theorem. -/
theorem nonempty_outerBoundaryCoreSource_of_exactTopologyFields
    (h : OuterBoundaryExistenceConcrete.ExactTopologyFields C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  (nonempty_outerBoundaryCoreSource_iff_exactTopologyFields C).2 h

/-- The concrete frontier provides the W28 source. -/
theorem nonempty_outerBoundaryCoreSource_of_noncrossingFrontier
    (h : ConcreteNoncrossingTopologyFrontier C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).2 h

def GlobalOuterBoundaryCoreSourceTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (OuterBoundaryCoreSource C)

/-- The global W28 source target is the same as the W26 selected-topology
extraction target. -/
theorem globalOuterBoundaryCoreSourceTarget_iff_actualSelectedTopology :
    GlobalOuterBoundaryCoreSourceTarget <->
      PlanarTopologyActualExtractionW26.GlobalActualSelectedTopologyExtractionTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C).2
      (h n C)

/-- The global W28 source target is the same as the W10/W26 outer-boundary
core construction target. -/
theorem globalOuterBoundaryCoreSourceTarget_iff_outerBoundaryCoreTarget :
    GlobalOuterBoundaryCoreSourceTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology C).2
      (h n C)

/-- The global W28 source target is also exactly the concrete noncrossing
frontier target; the graph half of that frontier is already automatic. -/
theorem globalOuterBoundaryCoreSourceTarget_iff_noncrossingFrontier :
    GlobalOuterBoundaryCoreSourceTarget <->
      forall (n : Nat) (C : _root_.UDConfig n),
        ConcreteNoncrossingTopologyFrontier C := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).2
      (h n C)

end

end OuterBoundaryCoreConstructionW28

namespace Verified

open Swanepoel.OuterBoundaryCoreConstructionW28

abbrev SwanepoelW28OuterBoundaryCoreSource
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource C

theorem swanepoelW28_outerBoundaryCoreSource_exactly_actualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW28OuterBoundaryCoreSource C) <->
      Nonempty
        (Swanepoel.ActualSelectedTopologyDataW27.ActualSelectedTopologyData
          C) :=
  Swanepoel.OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData
    C

theorem swanepoelW28_outerBoundaryCoreSource_exactly_concreteFrontier
    {n : Nat} (C : _root_.UDConfig n) :
      Nonempty (SwanepoelW28OuterBoundaryCoreSource C) <->
      Swanepoel.TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier
        C :=
  Swanepoel.OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier
    C

theorem swanepoelW28_globalSource_exactly_globalCoreTarget :
    Swanepoel.OuterBoundaryCoreConstructionW28.GlobalOuterBoundaryCoreSourceTarget <->
      Swanepoel.OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Swanepoel.OuterBoundaryCoreConstructionW28.globalOuterBoundaryCoreSourceTarget_iff_outerBoundaryCoreTarget

end Verified
end Swanepoel
end ErdosProblems1066
