import ErdosProblems1066.Swanepoel.OuterBoundarySourceConstructionW29

set_option autoImplicit false

/-!
# W30 selected-face enclosure source

W29 identified the remaining outer-boundary source as exactly the selected
outer face and enclosure data for the canonical unit-distance graph.  This file
keeps that target as the W30 focus:

* construct `SelectedFaceEnclosureFields` from raw face-boundary, outer-face,
  and enclosure witnesses, or from any existing topology package; and
* record the exact blocker equivalences after `PlanarInterface` and
  `FaceReduction`: graph noncrossing is automatic, while face-boundary data, a
  selected outer face, and enclosure predicates are still the precise missing
  topology payload.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SelectedFaceEnclosureSourceW30

open OuterBoundarySourceConstructionW29
open PlanarTopologyActualExtractionW26

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  OuterBoundarySourceConstructionW29.CanonicalGraph C

abbrev CanonicalGraphFacts (C : _root_.UDConfig n) :=
  OuterBoundarySourceConstructionW29.CanonicalGraphFacts C

abbrev SelectedFaceEnclosureFields (C : _root_.UDConfig n) :=
  OuterBoundarySourceConstructionW29.SelectedFaceEnclosureFields C

abbrev OuterBoundarySourceFields (C : _root_.UDConfig n) :=
  OuterBoundarySourceConstructionW29.OuterBoundarySourceFields C

abbrev OuterBoundaryCoreSource (C : _root_.UDConfig n) :=
  OuterBoundarySourceConstructionW29.OuterBoundaryCoreSource C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  OuterBoundarySourceConstructionW29.ActualSelectedTopologyData C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  OuterBoundarySourceConstructionW29.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  OuterBoundarySourceConstructionW29.SelectedEnclosureData D

/-- Once face-boundary data are fixed, the remaining local data are exactly a
selected outer face and an enclosure for that same face. -/
def SelectedFaceAndEnclosureFor
    {C : _root_.UDConfig n}
    (H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C)) : Prop :=
  Exists fun F : H.Face =>
    H.IsOuterFace F /\
      Nonempty
        (OuterBoundaryInterface.OuterBoundaryEnclosure
          (CanonicalGraph C) H F)

/-- A named form of the exact W30 blocker: face-boundary hypotheses, a selected
outer face, and enclosure predicates for the canonical graph. -/
def ExactSelectedFaceEnclosureBlocker
    (C : _root_.UDConfig n) : Prop :=
  Exists fun H :
      FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
        (CanonicalGraph C) =>
    SelectedFaceAndEnclosureFor H

theorem selectedFaceEnclosureFields_iff_exactBlocker
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      ExactSelectedFaceEnclosureBlocker C := by
  rfl

/-- Direct constructor from the three dependent pieces exposed by the blocker. -/
def ofRawSelectedFaceAndEnclosure
    {C : _root_.UDConfig n}
    (H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C))
    (F : H.Face)
    (hF : H.IsOuterFace F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    SelectedFaceEnclosureFields C :=
  Exists.intro H
    (Exists.intro F
      (And.intro hF (Nonempty.intro E)))

theorem ofSelectedFaceAndEnclosureFor
    {C : _root_.UDConfig n}
    (H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C))
    (h : SelectedFaceAndEnclosureFor H) :
    SelectedFaceEnclosureFields C :=
  Exists.intro H h

theorem selectedFaceAndEnclosureFor_iff_exists_outerFace
    {C : _root_.UDConfig n}
    (H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C)) :
    SelectedFaceAndEnclosureFor H <->
      Exists fun F : H.Face =>
        H.IsOuterFace F /\
          Nonempty
            (OuterBoundaryInterface.OuterBoundaryEnclosure
              (CanonicalGraph C) H F) := by
  rfl

/-- Existing split selected-face/enclosure data construct the W30 target. -/
def ofSelectedOuterFaceAndEnclosure
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceData C)
    (E : SelectedEnclosureData D) :
    SelectedFaceEnclosureFields C :=
  ofRawSelectedFaceAndEnclosure D.faceBoundary D.outerFace
    D.outerFace_isOuter E.outerEnclosure

theorem ofSelectedOuterFaceAndEnclosure_nonempty
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceData C)
    (hE : Nonempty (SelectedEnclosureData D)) :
    SelectedFaceEnclosureFields C := by
  cases hE with
  | intro E =>
      exact ofSelectedOuterFaceAndEnclosure D E

/-- A checked W29 source package contains exactly the selected-face/enclosure
fields. -/
def ofOuterBoundarySourceFields
    {C : _root_.UDConfig n}
    (S : OuterBoundarySourceFields C) :
    SelectedFaceEnclosureFields C :=
  S.toSelectedFaceEnclosureFields

/-- A checked W28 core source contains the selected-face/enclosure fields. -/
def ofOuterBoundaryCoreSource
    {C : _root_.UDConfig n}
    (S : OuterBoundaryCoreSource C) :
    SelectedFaceEnclosureFields C :=
  (OuterBoundarySourceFields.ofOuterBoundaryCoreSource S)
    |>.toSelectedFaceEnclosureFields

/-- A checked outer-boundary core contains the selected-face/enclosure fields. -/
def ofOuterBoundaryCore
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    SelectedFaceEnclosureFields C :=
  (OuterBoundarySourceFields.ofOuterBoundaryCore P)
    |>.toSelectedFaceEnclosureFields

/-- W27 actual selected topology data contain the W30 target. -/
def ofActualSelectedTopologyData
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    SelectedFaceEnclosureFields C :=
  (OuterBoundarySourceFields.ofActualSelectedTopologyData A)
    |>.toSelectedFaceEnclosureFields

/-- The raw exact topology fields are the same data as the W30 target. -/
theorem selectedFaceEnclosureFields_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  OuterBoundarySourceConstructionW29.selectedFaceEnclosureFields_iff_exactTopologyFields
    C

theorem ofExactTopologyFields
    {C : _root_.UDConfig n}
    (h : OuterBoundaryExistenceConcrete.ExactTopologyFields C) :
    SelectedFaceEnclosureFields C :=
  (selectedFaceEnclosureFields_iff_exactTopologyFields C).2 h

/-- Split selected-face/enclosure fields are definitionally the same blocker,
through the W25 frontier surface. -/
theorem selectedFaceEnclosureFields_iff_splitExactTopologyFields
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  OuterBoundarySourceConstructionW29.selectedFaceEnclosureFields_iff_splitExactTopologyFields
    C

theorem selectedFaceEnclosureFields_iff_selectedOuterFaceData_and_enclosure
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      Exists fun D : SelectedOuterFaceData C =>
        Nonempty (SelectedEnclosureData D) :=
  selectedFaceEnclosureFields_iff_splitExactTopologyFields C

theorem selectedFaceEnclosureFields_iff_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      Nonempty (ActualSelectedTopologyData C) :=
  Iff.trans
    (selectedFaceEnclosureFields_iff_splitExactTopologyFields C)
    (nonempty_actualSelectedTopologyData_iff_splitExactTopologyFields C).symm

theorem selectedFaceEnclosureFields_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) :=
  Iff.trans
    (selectedFaceEnclosureFields_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_outerBoundaryCore
      C)

/-- After `PlanarInterface` and `FaceReduction`, the remaining core topology
target is exactly the selected face and enclosure blocker. -/
theorem selectedFaceEnclosureFields_iff_remainingCoreTopology
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  Iff.trans
    (selectedFaceEnclosureFields_iff_exactTopologyFields C)
    (OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_exactTopologyFields
      C).symm

/-- The noncrossing frontier is blocked by exactly the W30 selected-face and
enclosure payload, because graph facts are already automatic. -/
theorem selectedFaceEnclosureFields_iff_noncrossingFrontier
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C :=
  Iff.trans
    (selectedFaceEnclosureFields_iff_exactTopologyFields C)
    (TopologyExtractionFromNoncrossing.concreteNoncrossingTopologyFrontier_iff_exactTopologyFields
      C).symm

/-- Graph-level facts are not part of the remaining blocker; they are available
for every canonical graph. -/
theorem canonicalGraphFacts_available
    (C : _root_.UDConfig n) :
    CanonicalGraphFacts C :=
  OuterBoundarySourceConstructionW29.canonicalGraphFacts_available C

theorem selectedFaceEnclosureFields_iff_graphFacts_and_exactBlocker
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      CanonicalGraphFacts C /\ ExactSelectedFaceEnclosureBlocker C := by
  constructor
  case mp =>
    intro h
    exact And.intro (canonicalGraphFacts_available C)
      ((selectedFaceEnclosureFields_iff_exactBlocker C).1 h)
  case mpr =>
    intro h
    exact (selectedFaceEnclosureFields_iff_exactBlocker C).2 h.2

theorem selectedFaceEnclosureFields_iff_graphFacts_and_exactTopologyFields
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      CanonicalGraphFacts C /\
        OuterBoundaryExistenceConcrete.ExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    exact And.intro (canonicalGraphFacts_available C)
      ((selectedFaceEnclosureFields_iff_exactTopologyFields C).1 h)
  case mpr =>
    intro h
    exact (selectedFaceEnclosureFields_iff_exactTopologyFields C).2 h.2

abbrev GlobalSelectedFaceEnclosureFieldsTarget : Prop :=
  OuterBoundarySourceConstructionW29.GlobalSelectedFaceEnclosureFieldsTarget

theorem globalSelectedFaceEnclosureFieldsTarget_iff_actualSelectedTopology :
    GlobalSelectedFaceEnclosureFieldsTarget <->
      PlanarTopologyActualExtractionW26.GlobalActualSelectedTopologyExtractionTarget := by
  constructor
  case mp =>
    intro h n C
    exact (selectedFaceEnclosureFields_iff_actualSelectedTopologyData C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (selectedFaceEnclosureFields_iff_actualSelectedTopologyData C).2
      (h n C)

theorem globalSelectedFaceEnclosureFieldsTarget_iff_outerBoundaryCoreTarget :
    GlobalSelectedFaceEnclosureFieldsTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Iff.trans
    globalSelectedFaceEnclosureFieldsTarget_iff_actualSelectedTopology
    globalActualSelectedTopologyExtractionTarget_iff_outerBoundaryCoreTarget

end

end SelectedFaceEnclosureSourceW30

namespace Verified

open Swanepoel.SelectedFaceEnclosureSourceW30

abbrev SwanepoelW30SelectedFaceEnclosureFields
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields C

theorem swanepoelW30_selectedFaceEnclosure_exactly_exactTopologyFields
    {n : Nat} (C : _root_.UDConfig n) :
    SwanepoelW30SelectedFaceEnclosureFields C <->
      Swanepoel.OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Swanepoel.SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactTopologyFields
    C

theorem swanepoelW30_selectedFaceEnclosure_exactly_actualSelectedTopology
    {n : Nat} (C : _root_.UDConfig n) :
    SwanepoelW30SelectedFaceEnclosureFields C <->
      Nonempty
        (Swanepoel.PlanarTopologyActualExtractionW26.ActualSelectedTopologyData
          C) :=
  selectedFaceEnclosureFields_iff_actualSelectedTopologyData C

abbrev SwanepoelW30GlobalSelectedFaceEnclosureFieldsTarget : Prop :=
  SelectedFaceEnclosureSourceW30.GlobalSelectedFaceEnclosureFieldsTarget

theorem swanepoelW30_globalSelectedFaceEnclosure_exactly_coreTarget :
    SwanepoelW30GlobalSelectedFaceEnclosureFieldsTarget <->
      Swanepoel.OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  globalSelectedFaceEnclosureFieldsTarget_iff_outerBoundaryCoreTarget

end Verified
end Swanepoel
end ErdosProblems1066
