import ErdosProblems1066.Swanepoel.PlanarTopologyActualExtractionW26

set_option autoImplicit false

/-!
# W27 actual selected-topology data adapters

The W26 package isolated the remaining topology object:
`ActualSelectedTopologyData`, a selected outer face together with the
enclosure predicates for that same face.  This file adds only local wrapper
adapters from the topology interfaces that already exist in the development.

No new face theory is introduced here.  The canonical noncrossing graph facts
remain theorem-proved from the unit-distance graph; the only constructive
content needed for an actual datum is still the selected-face/enclosure
payload.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ActualSelectedTopologyDataW27

open PlanarTopologyActualExtractionW26
open TopologyExtractionFromNoncrossing

noncomputable section

universe u

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  PlanarTopologyActualExtractionW26.CanonicalGraph C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  PlanarTopologyActualExtractionW26.ActualSelectedTopologyData C

namespace ActualSelectedTopologyData

variable {C : _root_.UDConfig n}

/-- Build the W26 actual datum from the concrete missing-topology wrapper. -/
def ofMissingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    ActualSelectedTopologyData C where
  selectedOuterFace :=
    { faceBoundary := T.faceBoundary
      outerFace := T.outerFace
      outerFace_isOuter := T.outerFace_isOuter }
  enclosure :=
    { outerEnclosure := T.outerEnclosure }

/-- Build the W26 actual datum from the concrete topology-facts wrapper. -/
def ofConcreteTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    ActualSelectedTopologyData C where
  selectedOuterFace :=
    { faceBoundary := T.faceBoundary
      outerFace := T.outerFace
      outerFace_isOuter := T.outerFace_isOuter }
  enclosure :=
    { outerEnclosure := T.outerEnclosure }

/-- Build the W26 actual datum from an already checked outer-boundary core. -/
def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    ActualSelectedTopologyData C where
  selectedOuterFace :=
    { faceBoundary := P.faceBoundary
      outerFace := P.outerFace
      outerFace_isOuter := P.outerFace_isOuter }
  enclosure :=
    { outerEnclosure := P.outerEnclosure }

/-- Build the W26 actual datum from full planar-boundary data by forgetting
angle and subpolygon fields. -/
def ofPlanarBoundaryData
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0} (CanonicalGraph C)) :
    ActualSelectedTopologyData C :=
  ofOuterBoundaryCore P.core

/-- The actual datum contains the checked outer-boundary core. -/
def toOuterBoundaryCore
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryCore.{0} (CanonicalGraph C) :=
  A.enclosure.toCore

@[simp]
theorem ofMissingTopologyFacts_toMissingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    (ofMissingTopologyFacts T).toMissingTopologyFacts = T := by
  cases T
  rfl

@[simp]
theorem ofConcreteTopologyFacts_toConcreteTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    (ofConcreteTopologyFacts T).toConcreteTopologyFacts = T := by
  cases T with
  | mk D E =>
    cases D
    cases E
    rfl

@[simp]
theorem ofOuterBoundaryCore_toOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (ofOuterBoundaryCore P).toOuterBoundaryCore = P := by
  cases P
  rfl

@[simp]
theorem toOuterBoundaryCore_ofPlanarBoundaryData
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0} (CanonicalGraph C)) :
    (ofPlanarBoundaryData P).toOuterBoundaryCore = P.core := by
  rfl

@[simp]
theorem toOuterBoundaryCore_faceBoundary
    (A : ActualSelectedTopologyData C) :
    A.toOuterBoundaryCore.faceBoundary = A.faceBoundary :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerFace
    (A : ActualSelectedTopologyData C) :
    A.toOuterBoundaryCore.outerFace = A.outerFace :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerEnclosure
    (A : ActualSelectedTopologyData C) :
    A.toOuterBoundaryCore.outerEnclosure = A.outerEnclosure :=
  rfl

end ActualSelectedTopologyData

variable (C : _root_.UDConfig n)

/-- The W26 actual datum is exactly the concrete missing-topology wrapper. -/
theorem nonempty_actualSelectedTopologyData_iff_missingTopologyFacts :
    Nonempty (ActualSelectedTopologyData C) <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.toMissingTopologyFacts⟩
  · rintro ⟨T⟩
    exact ⟨ActualSelectedTopologyData.ofMissingTopologyFacts T⟩

/-- The W26 actual datum is exactly the concrete topology-facts wrapper. -/
theorem nonempty_actualSelectedTopologyData_iff_concreteTopologyFacts :
    Nonempty (ActualSelectedTopologyData C) <->
      Nonempty (JordanTopologyFactsConcrete.TopologyFacts.{0} C) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.toConcreteTopologyFacts⟩
  · rintro ⟨T⟩
    exact ⟨ActualSelectedTopologyData.ofConcreteTopologyFacts T⟩

/-- The W26 actual datum is exactly an outer-boundary core for the canonical
unit-distance graph. -/
theorem nonempty_actualSelectedTopologyData_iff_outerBoundaryCore :
    Nonempty (ActualSelectedTopologyData C) <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.toOuterBoundaryCore⟩
  · rintro ⟨P⟩
    exact ⟨ActualSelectedTopologyData.ofOuterBoundaryCore P⟩

/-- The raw exact topology field list reduces directly to the W26 actual
selected-face/enclosure datum. -/
theorem nonempty_actualSelectedTopologyData_iff_exactTopologyFields :
    Nonempty (ActualSelectedTopologyData C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  PlanarTopologyActualExtractionW26.exactTopologyFields_iff_nonempty_actualSelectedTopologyData
    C |>.symm

/-- The core-topology target is no stronger and no weaker than producing the
actual selected topology datum. -/
theorem nonempty_actualSelectedTopologyData_iff_remainingCoreTopology :
    Nonempty (ActualSelectedTopologyData C) <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  remainingCoreTopologyRequirements_iff_nonempty_actualSelectedTopologyData C |>.symm

/-- The noncrossing frontier reduces to the actual topology datum because the
graph side is supplied by the canonical unit-distance graph theorem. -/
theorem nonempty_actualSelectedTopologyData_iff_noncrossingFrontier :
    Nonempty (ActualSelectedTopologyData C) <->
      ConcreteNoncrossingTopologyFrontier C :=
  concreteNoncrossingTopologyFrontier_iff_nonempty_actualSelectedTopologyData
    C |>.symm

/-- The graph facts are automatic; adding them to concrete topology facts does
not change the actual selected-topology target. -/
theorem nonempty_actualSelectedTopologyData_iff_graphFacts_and_topologyFacts :
    Nonempty (ActualSelectedTopologyData C) <->
      OuterBoundaryExistenceConcrete.ConcreteGraphFacts C /\
        Nonempty (JordanTopologyFactsConcrete.TopologyFacts.{0} C) := by
  constructor
  · intro h
    exact
      ⟨PlanarTopologyActualExtractionW26.concreteGraphFacts_available C,
        (nonempty_actualSelectedTopologyData_iff_concreteTopologyFacts C).1 h⟩
  · intro h
    exact (nonempty_actualSelectedTopologyData_iff_concreteTopologyFacts C).2 h.2

/-- A completed planar-boundary package sharply reduces to the W26 actual
topology datum by forgetting only angle and subpolygon data. -/
theorem nonempty_actualSelectedTopologyData_of_planarBoundaryData
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0} (CanonicalGraph C)) :
    Nonempty (ActualSelectedTopologyData C) :=
  ⟨ActualSelectedTopologyData.ofPlanarBoundaryData P⟩

/-- A checked outer-boundary core sharply reduces to the W26 actual topology
datum. -/
theorem nonempty_actualSelectedTopologyData_of_outerBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    Nonempty (ActualSelectedTopologyData C) :=
  ⟨ActualSelectedTopologyData.ofOuterBoundaryCore P⟩

/-- Concrete topology facts sharply reduce to the W26 actual topology datum. -/
theorem nonempty_actualSelectedTopologyData_of_concreteTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    Nonempty (ActualSelectedTopologyData C) :=
  ⟨ActualSelectedTopologyData.ofConcreteTopologyFacts T⟩

end

end ActualSelectedTopologyDataW27

namespace Verified

open Swanepoel.ActualSelectedTopologyDataW27

abbrev SwanepoelW27ActualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

theorem swanepoelW27_actualSelectedTopologyData_exactly_outerBoundaryCore
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW27ActualSelectedTopologyData C) <->
      Nonempty
        (Swanepoel.OuterBoundaryCore.{0}
          (Swanepoel.ActualSelectedTopologyDataW27.CanonicalGraph C)) :=
  Swanepoel.ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_outerBoundaryCore
    C

theorem swanepoelW27_actualSelectedTopologyData_exactly_concreteTopologyFacts
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW27ActualSelectedTopologyData C) <->
      Nonempty (Swanepoel.JordanTopologyFactsConcrete.TopologyFacts.{0} C) :=
  nonempty_actualSelectedTopologyData_iff_concreteTopologyFacts C

end Verified
end Swanepoel
end ErdosProblems1066
