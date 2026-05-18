import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstructionW28

set_option autoImplicit false

/-!
# W29 outer-boundary source fields

W28 identified the remaining outer-boundary source with an
`OuterBoundaryCore` for the canonical unit-distance graph.  This file advances
that statement by naming the concrete fields needed for one configuration:

* the graph-level canonical/noncrossing facts, already theorem-proved; and
* the dependent topology fields: face-boundary data, a selected outer face,
  and enclosure predicates for that same face.

No face or enclosure theorem is assumed here.  The residual blocker is exposed
as an exact equivalence with those selected-face/enclosure fields.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundarySourceConstructionW29

open OuterBoundaryCoreConstructionW28

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  OuterBoundaryCoreConstructionW28.CanonicalGraph C

abbrev CanonicalGraphFacts (C : _root_.UDConfig n) :=
  OuterBoundaryExistenceConcrete.ConcreteGraphFacts C

abbrev OuterBoundaryCoreSource (C : _root_.UDConfig n) :=
  OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  PlanarTopologyExtractionBridgeW25.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  PlanarTopologyExtractionBridgeW25.SelectedEnclosureData D

/-- The graph-level side is already constructed for every concrete
configuration. -/
theorem canonicalGraphFacts_available
    (C : _root_.UDConfig n) :
    CanonicalGraphFacts C :=
  OuterBoundaryCoreConstructionW28.concreteGraphFacts_available C

theorem canonicalGraph_edgeSet_eq_unitDistanceEdges
    (C : _root_.UDConfig n) :
    (CanonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C :=
  (canonicalGraphFacts_available C).edgeSet_eq_unitDistanceEdges

theorem canonicalGraph_pairwiseNoncrossing
    (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  (canonicalGraphFacts_available C).pairwiseNoncrossing

/-- The exact dependent topology field left after canonical noncrossing:
choose a face-boundary surface, an outer face in it, and enclosure predicates
for that same selected face. -/
def SelectedFaceEnclosureFields (C : _root_.UDConfig n) : Prop :=
  Exists fun H :
      FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
        (CanonicalGraph C) =>
    Exists fun F : H.Face =>
      H.IsOuterFace F /\
        Nonempty
          (OuterBoundaryInterface.OuterBoundaryEnclosure
            (CanonicalGraph C) H F)

/-- Concrete W29 source fields for one configuration.  The graph field is
automatic; the remaining fields are the selected outer face and enclosure. -/
structure OuterBoundarySourceFields (C : _root_.UDConfig n) where
  graphFacts : CanonicalGraphFacts C
  faceBoundary :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) faceBoundary outerFace

namespace OuterBoundarySourceFields

variable {C : _root_.UDConfig n}

def ofRawSelectedFaceAndEnclosure
    (H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C))
    (F : H.Face)
    (hF : H.IsOuterFace F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    OuterBoundarySourceFields C where
  graphFacts := canonicalGraphFacts_available C
  faceBoundary := H
  outerFace := F
  outerFace_isOuter := hF
  outerEnclosure := E

def selectedOuterFace
    (S : OuterBoundarySourceFields C) :
    SelectedOuterFaceData C where
  faceBoundary := S.faceBoundary
  outerFace := S.outerFace
  outerFace_isOuter := S.outerFace_isOuter

def selectedEnclosure
    (S : OuterBoundarySourceFields C) :
    SelectedEnclosureData S.selectedOuterFace where
  outerEnclosure := S.outerEnclosure

def toSelectedFaceEnclosureFields
    (S : OuterBoundarySourceFields C) :
    SelectedFaceEnclosureFields C :=
  Exists.intro S.faceBoundary
    (Exists.intro S.outerFace
      (And.intro S.outerFace_isOuter
        (Nonempty.intro S.outerEnclosure)))

def core
    (S : OuterBoundarySourceFields C) :
    OuterBoundaryCore.{0} (CanonicalGraph C) where
  faceBoundary := S.faceBoundary
  outerFace := S.outerFace
  outerFace_isOuter := S.outerFace_isOuter
  outerEnclosure := S.outerEnclosure

def toOuterBoundaryCoreSource
    (S : OuterBoundarySourceFields C) :
    OuterBoundaryCoreSource C :=
  OuterBoundaryCoreSource.ofOuterBoundaryCore S.core

def toActualSelectedTopologyData
    (S : OuterBoundarySourceFields C) :
    ActualSelectedTopologyData C :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
    S.core

def toBoundaryCycleCertificate
    (S : OuterBoundarySourceFields C) :
    OuterBoundaryCoreConstruction.BoundaryCycleCertificate
      (CanonicalGraph C) :=
  OuterBoundaryCoreConstruction.BoundaryCycleCertificate.ofCore S.core

def toSplitExactTopologyFields
    (S : OuterBoundarySourceFields C) :
    TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  Exists.intro S.selectedOuterFace (Nonempty.intro S.selectedEnclosure)

def ofSelectedOuterFaceAndEnclosure
    (D : SelectedOuterFaceData C)
    (E : SelectedEnclosureData D) :
    OuterBoundarySourceFields C :=
  ofRawSelectedFaceAndEnclosure D.faceBoundary D.outerFace
    D.outerFace_isOuter E.outerEnclosure

def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    OuterBoundarySourceFields C :=
  ofRawSelectedFaceAndEnclosure P.faceBoundary P.outerFace
    P.outerFace_isOuter P.outerEnclosure

def ofOuterBoundaryCoreSource
    (S : OuterBoundaryCoreSource C) :
    OuterBoundarySourceFields C :=
  ofOuterBoundaryCore S.core

def ofActualSelectedTopologyData
    (A : ActualSelectedTopologyData C) :
    OuterBoundarySourceFields C :=
  ofSelectedOuterFaceAndEnclosure A.selectedOuterFace A.enclosure

def ofSelectedFaceEnclosureFields
    (h : SelectedFaceEnclosureFields C) :
    Nonempty (OuterBoundarySourceFields C) := by
  cases h with
  | intro H hH =>
      cases hH with
      | intro F hFPair =>
          cases hFPair with
          | intro hF hE =>
              cases hE with
              | intro E =>
                  exact
                    Nonempty.intro
                      (ofRawSelectedFaceAndEnclosure H F hF E)

@[simp]
theorem selectedOuterFace_faceBoundary
    (S : OuterBoundarySourceFields C) :
    S.selectedOuterFace.faceBoundary = S.faceBoundary :=
  rfl

@[simp]
theorem selectedOuterFace_outerFace
    (S : OuterBoundarySourceFields C) :
    S.selectedOuterFace.outerFace = S.outerFace :=
  rfl

@[simp]
theorem selectedEnclosure_outerEnclosure
    (S : OuterBoundarySourceFields C) :
    S.selectedEnclosure.outerEnclosure = S.outerEnclosure :=
  rfl

@[simp]
theorem core_faceBoundary
    (S : OuterBoundarySourceFields C) :
    S.core.faceBoundary = S.faceBoundary :=
  rfl

@[simp]
theorem core_outerFace
    (S : OuterBoundarySourceFields C) :
    S.core.outerFace = S.outerFace :=
  rfl

@[simp]
theorem core_outerEnclosure
    (S : OuterBoundarySourceFields C) :
    S.core.outerEnclosure = S.outerEnclosure :=
  rfl

@[simp]
theorem toOuterBoundaryCoreSource_core
    (S : OuterBoundarySourceFields C) :
    S.toOuterBoundaryCoreSource.core = S.core :=
  rfl

@[simp]
theorem toActualSelectedTopologyData_toOuterBoundaryCore
    (S : OuterBoundarySourceFields C) :
    S.toActualSelectedTopologyData.toOuterBoundaryCore = S.core := by
  cases S
  rfl

@[simp]
theorem toBoundaryCycleCertificate_cycle
    (S : OuterBoundarySourceFields C) :
    S.toBoundaryCycleCertificate.cycle = S.core.outerCycle :=
  rfl

@[simp]
theorem ofSelectedOuterFaceAndEnclosure_core
    (D : SelectedOuterFaceData C)
    (E : SelectedEnclosureData D) :
    (ofSelectedOuterFaceAndEnclosure D E).core = E.toCore := by
  cases D
  cases E
  rfl

@[simp]
theorem ofOuterBoundaryCore_core
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (ofOuterBoundaryCore P).core = P := by
  cases P
  rfl

@[simp]
theorem ofOuterBoundaryCoreSource_core
    (S : OuterBoundaryCoreSource C) :
    (ofOuterBoundaryCoreSource S).core = S.core := by
  cases S
  rfl

@[simp]
theorem ofActualSelectedTopologyData_core
    (A : ActualSelectedTopologyData C) :
    (ofActualSelectedTopologyData A).core =
      A.toOuterBoundaryCore := by
  cases A
  rfl

theorem pairwiseNoncrossing
    (S : OuterBoundarySourceFields C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  S.graphFacts.pairwiseNoncrossing

theorem outerCycle_vertex_injective
    (S : OuterBoundarySourceFields C) :
    Function.Injective S.core.outerCycle.vertex :=
  S.core.outerCycle_vertex_injective

theorem all_vertices_insideOrOn
    (S : OuterBoundarySourceFields C) (v : Fin n) :
    S.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  S.outerEnclosure.all_vertices_insideOrOn v

theorem onBoundary_iff_outerCycle
    (S : OuterBoundarySourceFields C) (v : Fin n) :
    S.outerEnclosure.onBoundary v <->
      Exists fun k : Fin S.core.outerCycle.length =>
        S.core.outerCycle.vertex k = v := by
  exact S.core.onBoundary_iff_outer_cycle v

end OuterBoundarySourceFields

variable (C : _root_.UDConfig n)

/-- The W29 source fields are exactly W28's `OuterBoundaryCoreSource`. -/
theorem nonempty_outerBoundarySourceFields_iff_outerBoundaryCoreSource :
    Nonempty (OuterBoundarySourceFields C) <->
      Nonempty (OuterBoundaryCoreSource C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toOuterBoundaryCoreSource
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact
          Nonempty.intro
            (OuterBoundarySourceFields.ofOuterBoundaryCoreSource S)

/-- The W29 source fields are exactly a checked outer-boundary core. -/
theorem nonempty_outerBoundarySourceFields_iff_outerBoundaryCore :
    Nonempty (OuterBoundarySourceFields C) <->
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
        exact
          Nonempty.intro
            (OuterBoundarySourceFields.ofOuterBoundaryCore P)

/-- The W29 source fields are exactly the W27 actual selected-topology datum. -/
theorem nonempty_outerBoundarySourceFields_iff_actualSelectedTopologyData :
    Nonempty (OuterBoundarySourceFields C) <->
      Nonempty (ActualSelectedTopologyData C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toActualSelectedTopologyData
  case mpr =>
    intro h
    cases h with
    | intro A =>
        exact
          Nonempty.intro
            (OuterBoundarySourceFields.ofActualSelectedTopologyData A)

/-- The residual topology blocker is exactly the selected outer face together
with enclosure data for that same face. -/
theorem nonempty_outerBoundarySourceFields_iff_selectedFaceEnclosureFields :
    Nonempty (OuterBoundarySourceFields C) <->
      SelectedFaceEnclosureFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact S.toSelectedFaceEnclosureFields
  case mpr =>
    intro h
    exact OuterBoundarySourceFields.ofSelectedFaceEnclosureFields h

theorem selectedFaceEnclosureFields_iff_splitExactTopologyFields :
    SelectedFaceEnclosureFields C <->
      TopologyExtractionFromNoncrossing.SplitExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H hH =>
        cases hH with
        | intro F hFPair =>
            cases hFPair with
            | intro hF hE =>
                cases hE with
                | intro E =>
                    let D : SelectedOuterFaceData C :=
                      { faceBoundary := H
                        outerFace := F
                        outerFace_isOuter := hF }
                    exact
                      Exists.intro D
                        (Nonempty.intro { outerEnclosure := E })
  case mpr =>
    intro h
    cases h with
    | intro D hD =>
        cases hD with
        | intro E =>
            exact
              Exists.intro D.faceBoundary
                (Exists.intro D.outerFace
                  (And.intro D.outerFace_isOuter
                    (Nonempty.intro E.outerEnclosure)))

theorem selectedFaceEnclosureFields_iff_exactTopologyFields :
    SelectedFaceEnclosureFields C <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Iff.trans
    (selectedFaceEnclosureFields_iff_splitExactTopologyFields C)
    (TopologyExtractionFromNoncrossing.splitExactTopologyFields_iff_exactTopologyFields
      C)

theorem nonempty_outerBoundarySourceFields_iff_exactTopologyFields :
    Nonempty (OuterBoundarySourceFields C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Iff.trans
    (nonempty_outerBoundarySourceFields_iff_selectedFaceEnclosureFields C)
    (selectedFaceEnclosureFields_iff_exactTopologyFields C)

theorem nonempty_outerBoundarySourceFields_iff_remainingCoreTopology :
    Nonempty (OuterBoundarySourceFields C) <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  Iff.trans
    (nonempty_outerBoundarySourceFields_iff_outerBoundaryCoreSource C)
    (OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology
      C)

theorem nonempty_outerBoundarySourceFields_iff_noncrossingFrontier :
    Nonempty (OuterBoundarySourceFields C) <->
      TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier
        C :=
  Iff.trans
    (nonempty_outerBoundarySourceFields_iff_outerBoundaryCoreSource C)
    (OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier
      C)

def GlobalOuterBoundarySourceFieldsTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (OuterBoundarySourceFields C)

def GlobalSelectedFaceEnclosureFieldsTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    SelectedFaceEnclosureFields C

theorem globalOuterBoundarySourceFieldsTarget_iff_w28CoreSourceTarget :
    GlobalOuterBoundarySourceFieldsTarget <->
      OuterBoundaryCoreConstructionW28.GlobalOuterBoundaryCoreSourceTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_outerBoundarySourceFields_iff_outerBoundaryCoreSource C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_outerBoundarySourceFields_iff_outerBoundaryCoreSource C).2
      (h n C)

theorem globalOuterBoundarySourceFieldsTarget_iff_selectedFaceEnclosureFields :
    GlobalOuterBoundarySourceFieldsTarget <->
      GlobalSelectedFaceEnclosureFieldsTarget := by
  constructor
  case mp =>
    intro h n C
    exact
      (nonempty_outerBoundarySourceFields_iff_selectedFaceEnclosureFields C).1
        (h n C)
  case mpr =>
    intro h n C
    exact
      (nonempty_outerBoundarySourceFields_iff_selectedFaceEnclosureFields C).2
        (h n C)

end

end OuterBoundarySourceConstructionW29
end Swanepoel
end ErdosProblems1066
