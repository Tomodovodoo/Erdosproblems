import ErdosProblems1066.Swanepoel.SelectedFaceEnclosureSourceW30
import ErdosProblems1066.Swanepoel.BoundaryWitnessRemainingFieldsW26

/-!
# W31 enclosure and face-boundary source facade

This file keeps the W30 selected-face/enclosure target source-facing.  It
packages the actual fields still needed after `FaceReduction`: a
unit-distance face-boundary surface, a selected outer face, and enclosure
predicates for that same face.

The constructors below are all projections from existing topology, Jordan, and
boundary-family records.  Where the current development does not construct
faces/enclosures globally, the exact remaining blockers are re-exported as
equivalences to the W30 selected-face/enclosure target.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace EnclosureAndFaceBoundaryW31

universe u

variable {n : Nat}

noncomputable section

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.CanonicalGraph C

abbrev FaceBoundaryHypotheses (C : _root_.UDConfig n) :=
  FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (CanonicalGraph C)

abbrev SelectedFaceEnclosureFields (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields C

abbrev ExactSelectedFaceEnclosureBlocker (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureSourceW30.ExactSelectedFaceEnclosureBlocker C

abbrev SelectedFaceAndEnclosureFor
    {C : _root_.UDConfig n} (H : FaceBoundaryHypotheses C) : Prop :=
  SelectedFaceEnclosureSourceW30.SelectedFaceAndEnclosureFor H

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  SelectedFaceEnclosureSourceW30.SelectedEnclosureData D

abbrev OuterBoundarySourceFields (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.OuterBoundarySourceFields C

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  JordanBoundaryConcreteInhabitationW24.ConcreteTopologyFacts C

abbrev MinimalBoundaryTopologyWitness
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitness.{u}
    C hmin

abbrev SelectedFaceWitnessRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessRow.{u}
    C hmin

abbrev SelectedFaceRemainingComponentRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
    C hmin

abbrev SelectedFaceRemainingComponentFamily : Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentFamily.{u}

abbrev ConcreteTriangleRunSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryTriangleRunSourceFields.{u}
    C hmin

abbrev ConcreteExtractionSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryExtractionSourceFields.{u}
    C hmin

abbrev ConcreteTriangleRunSourceFamily : Type (u + 1) :=
  JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{u}

abbrev ConcreteExtractionSourceFamily : Type (u + 1) :=
  JordanBoundaryFamiliesConcreteW23.ConcreteExtractionSourceFamily.{u}

/-- The source-facing W31 package: the actual face-boundary hypotheses, the
selected outer face, and enclosure predicates. -/
structure FaceBoundaryEnclosureSource (C : _root_.UDConfig n) where
  faceBoundary : FaceBoundaryHypotheses C
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) faceBoundary outerFace

namespace FaceBoundaryEnclosureSource

variable {C : _root_.UDConfig n}

def selectedOuterFaceData (S : FaceBoundaryEnclosureSource C) :
    SelectedOuterFaceData C where
  faceBoundary := S.faceBoundary
  outerFace := S.outerFace
  outerFace_isOuter := S.outerFace_isOuter

def selectedEnclosureData (S : FaceBoundaryEnclosureSource C) :
    SelectedEnclosureData S.selectedOuterFaceData where
  outerEnclosure := S.outerEnclosure

def toSelectedFaceEnclosureFields
    (S : FaceBoundaryEnclosureSource C) :
    SelectedFaceEnclosureFields C :=
  SelectedFaceEnclosureSourceW30.ofRawSelectedFaceAndEnclosure
    S.faceBoundary S.outerFace S.outerFace_isOuter S.outerEnclosure

def toExactSelectedFaceEnclosureBlocker
    (S : FaceBoundaryEnclosureSource C) :
    ExactSelectedFaceEnclosureBlocker C :=
  (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactBlocker
    C).1 S.toSelectedFaceEnclosureFields

def toOuterBoundarySourceFields
    (S : FaceBoundaryEnclosureSource C) :
    OuterBoundarySourceFields C :=
  OuterBoundarySourceConstructionW29.OuterBoundarySourceFields.ofRawSelectedFaceAndEnclosure
    S.faceBoundary S.outerFace S.outerFace_isOuter S.outerEnclosure

def toOuterBoundaryCore
    (S : FaceBoundaryEnclosureSource C) :
    OuterBoundaryCore.{0} (CanonicalGraph C) :=
  S.toOuterBoundarySourceFields.core

def toConcreteTopologyFacts
    (S : FaceBoundaryEnclosureSource C) :
    ConcreteTopologyFacts C :=
  MinimalBoundaryTopologyWitnessInhabitationW25.topologyFactsOfSelectedFace
    S.selectedOuterFaceData S.selectedEnclosureData

def toSplitExactTopologyFields
    (S : FaceBoundaryEnclosureSource C) :
    TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  Exists.intro S.selectedOuterFaceData
    (Nonempty.intro S.selectedEnclosureData)

def planarFaceBoundary
    (S : FaceBoundaryEnclosureSource C) :
    PlanarInterface.FaceBoundaryHypotheses
      (CanonicalGraph C).toStraightLine :=
  S.faceBoundary.toFaceBoundaryHypotheses

theorem pairwiseNoncrossing
    (S : FaceBoundaryEnclosureSource C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  S.faceBoundary.toFaceBoundaryHypotheses.noncrossing

theorem all_vertices_insideOrOn
    (S : FaceBoundaryEnclosureSource C) (v : Fin n) :
    S.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  S.outerEnclosure.all_vertices_insideOrOn v

theorem onBoundary_iff_outerCycle
    (S : FaceBoundaryEnclosureSource C) (v : Fin n) :
    S.outerEnclosure.onBoundary v <->
      Exists fun k : Fin S.toOuterBoundaryCore.outerCycle.length =>
        S.toOuterBoundaryCore.outerCycle.vertex k = v :=
  S.toOuterBoundaryCore.onBoundary_iff_outer_cycle v

@[simp]
theorem selectedOuterFaceData_faceBoundary
    (S : FaceBoundaryEnclosureSource C) :
    S.selectedOuterFaceData.faceBoundary = S.faceBoundary :=
  rfl

@[simp]
theorem selectedOuterFaceData_outerFace
    (S : FaceBoundaryEnclosureSource C) :
    S.selectedOuterFaceData.outerFace = S.outerFace :=
  rfl

@[simp]
theorem selectedEnclosureData_outerEnclosure
    (S : FaceBoundaryEnclosureSource C) :
    S.selectedEnclosureData.outerEnclosure = S.outerEnclosure :=
  rfl

@[simp]
theorem toOuterBoundaryCore_faceBoundary
    (S : FaceBoundaryEnclosureSource C) :
    S.toOuterBoundaryCore.faceBoundary = S.faceBoundary :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerFace
    (S : FaceBoundaryEnclosureSource C) :
    S.toOuterBoundaryCore.outerFace = S.outerFace :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerEnclosure
    (S : FaceBoundaryEnclosureSource C) :
    S.toOuterBoundaryCore.outerEnclosure = S.outerEnclosure :=
  rfl

end FaceBoundaryEnclosureSource

def ofRawFaceBoundaryAndEnclosure
    {C : _root_.UDConfig n}
    (H : FaceBoundaryHypotheses C)
    (F : H.Face)
    (hF : H.IsOuterFace F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    FaceBoundaryEnclosureSource C where
  faceBoundary := H
  outerFace := F
  outerFace_isOuter := hF
  outerEnclosure := E

def ofSelectedOuterFaceAndEnclosure
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceData C)
    (E : SelectedEnclosureData D) :
    FaceBoundaryEnclosureSource C :=
  ofRawFaceBoundaryAndEnclosure D.faceBoundary D.outerFace
    D.outerFace_isOuter E.outerEnclosure

def ofOuterBoundaryCore
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    FaceBoundaryEnclosureSource C :=
  ofRawFaceBoundaryAndEnclosure P.faceBoundary P.outerFace
    P.outerFace_isOuter P.outerEnclosure

def ofOuterBoundarySourceFields
    {C : _root_.UDConfig n}
    (S : OuterBoundarySourceFields C) :
    FaceBoundaryEnclosureSource C :=
  ofRawFaceBoundaryAndEnclosure S.faceBoundary S.outerFace
    S.outerFace_isOuter S.outerEnclosure

def ofConcreteTopologyFacts
    {C : _root_.UDConfig n}
    (T : ConcreteTopologyFacts C) :
    FaceBoundaryEnclosureSource C :=
  ofRawFaceBoundaryAndEnclosure T.faceBoundary T.outerFace
    T.outerFace_isOuter T.outerEnclosure

def ofMinimalBoundaryTopologyWitness
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    FaceBoundaryEnclosureSource C :=
  ofConcreteTopologyFacts P.topology

def ofConcreteTriangleRunSourceFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : ConcreteTriangleRunSourceFields.{u} C hmin) :
    FaceBoundaryEnclosureSource C :=
  ofConcreteTopologyFacts P.topology

def ofConcreteExtractionSourceFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : ConcreteExtractionSourceFields.{u} C hmin) :
    FaceBoundaryEnclosureSource C :=
  ofConcreteTopologyFacts P.topology

def ofSelectedFaceWitnessRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    FaceBoundaryEnclosureSource C :=
  ofSelectedOuterFaceAndEnclosure R.selectedFace R.enclosure

def ofSelectedFaceRemainingComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : SelectedFaceRemainingComponentRow.{u} C hmin) :
    FaceBoundaryEnclosureSource C :=
  ofSelectedOuterFaceAndEnclosure R.selectedFace R.enclosure

def ofSelectedFaceRemainingComponentFamilyRow
    (F : SelectedFaceRemainingComponentFamily.{u})
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    FaceBoundaryEnclosureSource C :=
  ofSelectedFaceRemainingComponentRow (F.row C hmin)

def ofConcreteTriangleRunSourceFamilyRow
    (F : ConcreteTriangleRunSourceFamily.{u})
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    FaceBoundaryEnclosureSource C :=
  ofConcreteTriangleRunSourceFields (F.row C hmin)

def ofConcreteExtractionSourceFamilyRow
    (F : ConcreteExtractionSourceFamily.{u})
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    FaceBoundaryEnclosureSource C :=
  ofConcreteExtractionSourceFields (F.row C hmin)

theorem nonempty_source_iff_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      SelectedFaceEnclosureFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S => exact S.toSelectedFaceEnclosureFields
  case mpr =>
    intro h
    cases h with
    | intro H hH =>
      cases hH with
      | intro F hF =>
        cases hF with
        | intro hOuter hE =>
          cases hE with
          | intro E =>
            exact
              Nonempty.intro
                (ofRawFaceBoundaryAndEnclosure H F hOuter E)

theorem nonempty_source_iff_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      ExactSelectedFaceEnclosureBlocker C :=
  Iff.trans
    (nonempty_source_iff_selectedFaceEnclosureFields C)
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactBlocker
      C)

theorem exactBlocker_iff_faceBoundary_and_enclosure
    (C : _root_.UDConfig n) :
    ExactSelectedFaceEnclosureBlocker C <->
      Exists fun H : FaceBoundaryHypotheses C =>
        SelectedFaceAndEnclosureFor H := by
  rfl

theorem nonempty_source_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Iff.trans
    (nonempty_source_iff_selectedFaceEnclosureFields C)
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactTopologyFields
      C)

theorem nonempty_source_iff_splitExactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  Iff.trans
    (nonempty_source_iff_selectedFaceEnclosureFields C)
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_splitExactTopologyFields
      C)

theorem nonempty_source_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      Nonempty
        (OuterBoundaryCore.{0}
          (CanonicalGraph C)) :=
  Iff.trans
    (nonempty_source_iff_selectedFaceEnclosureFields C)
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_outerBoundaryCore
      C)

theorem nonempty_source_iff_remainingCoreTopology
    (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  Iff.trans
    (nonempty_source_iff_selectedFaceEnclosureFields C)
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_remainingCoreTopology
      C)

theorem nonempty_source_iff_noncrossingFrontier
    (C : _root_.UDConfig n) :
    Nonempty (FaceBoundaryEnclosureSource C) <->
      TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C :=
  Iff.trans
    (nonempty_source_iff_selectedFaceEnclosureFields C)
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_noncrossingFrontier
      C)

theorem source_missing_iff_no_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
    Not (Nonempty (FaceBoundaryEnclosureSource C)) <->
      Not (SelectedFaceEnclosureFields C) :=
  not_congr (nonempty_source_iff_selectedFaceEnclosureFields C)

theorem source_missing_iff_no_exactTopologyFields
    (C : _root_.UDConfig n) :
    Not (Nonempty (FaceBoundaryEnclosureSource C)) <->
      Not (OuterBoundaryExistenceConcrete.ExactTopologyFields C) :=
  not_congr (nonempty_source_iff_exactTopologyFields C)

theorem source_missing_iff_no_exactBlocker
    (C : _root_.UDConfig n) :
    Not (Nonempty (FaceBoundaryEnclosureSource C)) <->
      Not (ExactSelectedFaceEnclosureBlocker C) :=
  not_congr (nonempty_source_iff_exactBlocker C)

theorem canonicalGraph_pairwiseNoncrossing
    (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  SelectedFaceEnclosureSourceW30.canonicalGraphFacts_available
    C |>.pairwiseNoncrossing

def planarFaceBoundaryOfHypotheses
    {C : _root_.UDConfig n}
    (H : FaceBoundaryHypotheses C) :
    PlanarInterface.FaceBoundaryHypotheses
      (CanonicalGraph C).toStraightLine :=
  H.toFaceBoundaryHypotheses

theorem planarFaceBoundaryOfHypotheses_noncrossing
    {C : _root_.UDConfig n}
    (H : FaceBoundaryHypotheses C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  H.toFaceBoundaryHypotheses.noncrossing

def GlobalFaceBoundaryEnclosureSourceTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (FaceBoundaryEnclosureSource C)

theorem globalFaceBoundaryEnclosureSourceTarget_iff_w30SelectedTarget :
    GlobalFaceBoundaryEnclosureSourceTarget <->
      SelectedFaceEnclosureSourceW30.GlobalSelectedFaceEnclosureFieldsTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_source_iff_selectedFaceEnclosureFields C).1 (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_source_iff_selectedFaceEnclosureFields C).2 (h n C)

theorem globalFaceBoundaryEnclosureSourceTarget_iff_outerBoundaryCoreTarget :
    GlobalFaceBoundaryEnclosureSourceTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Iff.trans
    globalFaceBoundaryEnclosureSourceTarget_iff_w30SelectedTarget
    SelectedFaceEnclosureSourceW30.globalSelectedFaceEnclosureFieldsTarget_iff_outerBoundaryCoreTarget

end

end EnclosureAndFaceBoundaryW31

namespace Verified

universe u

abbrev SwanepoelW31FaceBoundaryEnclosureSource
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.EnclosureAndFaceBoundaryW31.FaceBoundaryEnclosureSource C

theorem swanepoelW31_source_exactly_w30SelectedFaceEnclosure
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW31FaceBoundaryEnclosureSource C) <->
      Swanepoel.SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields C :=
  Swanepoel.EnclosureAndFaceBoundaryW31.nonempty_source_iff_selectedFaceEnclosureFields
    C

theorem swanepoelW31_source_exactly_exactTopologyFields
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW31FaceBoundaryEnclosureSource C) <->
      Swanepoel.OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Swanepoel.EnclosureAndFaceBoundaryW31.nonempty_source_iff_exactTopologyFields
    C

theorem swanepoelW31_source_missing_exactly_no_exactBlocker
    {n : Nat} (C : _root_.UDConfig n) :
    Not (Nonempty (SwanepoelW31FaceBoundaryEnclosureSource C)) <->
      Not
        (Swanepoel.SelectedFaceEnclosureSourceW30.ExactSelectedFaceEnclosureBlocker
          C) :=
  Swanepoel.EnclosureAndFaceBoundaryW31.source_missing_iff_no_exactBlocker
    C

abbrev SwanepoelW31GlobalFaceBoundaryEnclosureSourceTarget : Prop :=
  Swanepoel.EnclosureAndFaceBoundaryW31.GlobalFaceBoundaryEnclosureSourceTarget

theorem swanepoelW31_globalSource_exactly_outerBoundaryCoreTarget :
    SwanepoelW31GlobalFaceBoundaryEnclosureSourceTarget <->
      Swanepoel.OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Swanepoel.EnclosureAndFaceBoundaryW31.globalFaceBoundaryEnclosureSourceTarget_iff_outerBoundaryCoreTarget

end Verified
end Swanepoel
end ErdosProblems1066
