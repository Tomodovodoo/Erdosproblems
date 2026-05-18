import ErdosProblems1066.Swanepoel.SelectedFaceEnclosureSourceW30

set_option autoImplicit false

/-!
# W31 selected outer-face construction source

W30 identifies the selected-face/enclosure payload as the remaining topology
source for the outer-boundary route.  This file separates the smaller selected
outer-face source from the enclosure data that still has to be built for that
same dependent face.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SelectedOuterFaceConstructionW31

open SelectedFaceEnclosureSourceW30
open OuterBoundarySourceConstructionW29
open OuterBoundaryCoreConstructionW28
open PlanarTopologyActualExtractionW26

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.CanonicalGraph C

abbrev CanonicalGraphFacts (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.CanonicalGraphFacts C

abbrev SelectedFaceEnclosureFields (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields C

abbrev OuterBoundarySourceFields (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.OuterBoundarySourceFields C

abbrev OuterBoundaryCoreSource (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.OuterBoundaryCoreSource C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.ActualSelectedTopologyData C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  SelectedFaceEnclosureSourceW30.SelectedEnclosureData D

/-- The smallest selected outer-face source package: a face-boundary surface,
a selected face on it, and the proof that this selected face is outer. -/
structure SelectedOuterFaceSource (C : _root_.UDConfig n) where
  faceBoundary :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace

namespace SelectedOuterFaceSource

variable {C : _root_.UDConfig n}

def ofRaw
    (H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
      (CanonicalGraph C))
    (F : H.Face)
    (hF : H.IsOuterFace F) :
    SelectedOuterFaceSource C where
  faceBoundary := H
  outerFace := F
  outerFace_isOuter := hF

def toSelectedOuterFaceData
    (S : SelectedOuterFaceSource C) :
    SelectedOuterFaceData C where
  faceBoundary := S.faceBoundary
  outerFace := S.outerFace
  outerFace_isOuter := S.outerFace_isOuter

def ofSelectedOuterFaceData
    (D : SelectedOuterFaceData C) :
    SelectedOuterFaceSource C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

def outerCycle
    (S : SelectedOuterFaceSource C) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
    S.faceBoundary S.outerFace

def outerSimplePolygon
    (S : SelectedOuterFaceSource C) :
    OuterBoundaryInterface.SimplePolygon
      (CanonicalGraph C) S.outerCycle :=
  OuterBoundaryReduction.BoundaryCycle.simplePolygonOfFaceBoundary
    S.faceBoundary S.outerFace

def ofOuterBoundarySourceFields
    (S : OuterBoundarySourceFields C) :
    SelectedOuterFaceSource C :=
  ofRaw S.faceBoundary S.outerFace S.outerFace_isOuter

def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    SelectedOuterFaceSource C :=
  ofRaw P.faceBoundary P.outerFace P.outerFace_isOuter

def ofOuterBoundaryCoreSource
    (S : OuterBoundaryCoreSource C) :
    SelectedOuterFaceSource C :=
  ofOuterBoundaryCore S.core

def ofActualSelectedTopologyData
    (A : ActualSelectedTopologyData C) :
    SelectedOuterFaceSource C :=
  ofSelectedOuterFaceData A.selectedOuterFace

def ofSelectedEnclosureData
    (D : SelectedOuterFaceData C)
    (_E : SelectedEnclosureData D) :
    SelectedOuterFaceSource C :=
  ofSelectedOuterFaceData D

@[simp]
theorem toSelectedOuterFaceData_faceBoundary
    (S : SelectedOuterFaceSource C) :
    S.toSelectedOuterFaceData.faceBoundary = S.faceBoundary :=
  rfl

@[simp]
theorem toSelectedOuterFaceData_outerFace
    (S : SelectedOuterFaceSource C) :
    S.toSelectedOuterFaceData.outerFace = S.outerFace :=
  rfl

theorem toSelectedOuterFaceData_outerFace_isOuter
    (S : SelectedOuterFaceSource C) :
    S.toSelectedOuterFaceData.faceBoundary.IsOuterFace
      S.toSelectedOuterFaceData.outerFace :=
  S.outerFace_isOuter

@[simp]
theorem ofSelectedOuterFaceData_toSelectedOuterFaceData
    (S : SelectedOuterFaceSource C) :
    ofSelectedOuterFaceData S.toSelectedOuterFaceData = S := by
  cases S
  rfl

@[simp]
theorem toSelectedOuterFaceData_ofSelectedOuterFaceData
    (D : SelectedOuterFaceData C) :
    (ofSelectedOuterFaceData D).toSelectedOuterFaceData = D := by
  cases D
  rfl

@[simp]
theorem outerCycle_eq
    (S : SelectedOuterFaceSource C) :
    S.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        S.faceBoundary S.outerFace :=
  rfl

@[simp]
theorem outerCycle_length
    (S : SelectedOuterFaceSource C) :
    S.outerCycle.length =
      S.faceBoundary.boundaryLength S.outerFace :=
  rfl

theorem outerCycle_vertex_injective
    (S : SelectedOuterFaceSource C) :
    Function.Injective S.outerCycle.vertex :=
  S.faceBoundary.boundarySimple S.outerFace

theorem outerCycle_adjacent_unitDistanceAdj
    (S : SelectedOuterFaceSource C) (k : Fin S.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (CanonicalGraph C).config
      (S.outerCycle.vertex k)
      (S.outerCycle.vertex
        (PlanarInterface.cyclicSucc S.outerCycle.length_pos k)) :=
  S.outerCycle.adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (S : SelectedOuterFaceSource C) (k : Fin S.outerCycle.length) :
    Geometry.Distance.eucDist (S.outerCycle.point k)
      (S.outerCycle.point
        (PlanarInterface.cyclicSucc S.outerCycle.length_pos k)) = 1 :=
  S.outerCycle.edge_geometry_dist_eq_one k

end SelectedOuterFaceSource

/-- The proposition-level selected outer-face source blocker. -/
def SelectedOuterFaceFields (C : _root_.UDConfig n) : Prop :=
  Exists fun H :
      FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
        (CanonicalGraph C) =>
    Exists fun F : H.Face =>
      H.IsOuterFace F

/-- Once a selected outer-face source is fixed, the remaining honest topology
payload is enclosure data for that same selected dependent face. -/
def SelectedOuterFaceEnclosureBlocker
    {C : _root_.UDConfig n} (S : SelectedOuterFaceSource C) : Prop :=
  Nonempty
    (OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) S.faceBoundary S.outerFace)

def ExactSelectedOuterFaceSourceBlocker
    (C : _root_.UDConfig n) : Prop :=
  SelectedOuterFaceFields C

def ExactSelectedOuterFaceToTopologyBlocker
    (C : _root_.UDConfig n) : Prop :=
  Exists fun S : SelectedOuterFaceSource C =>
    SelectedOuterFaceEnclosureBlocker S

theorem nonempty_selectedOuterFaceSource_iff_selectedOuterFaceFields
    (C : _root_.UDConfig n) :
    Nonempty (SelectedOuterFaceSource C) <->
      SelectedOuterFaceFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Exists.intro S.faceBoundary
          (Exists.intro S.outerFace S.outerFace_isOuter)
  case mpr =>
    intro h
    cases h with
    | intro H hH =>
        cases hH with
        | intro F hF =>
            exact Nonempty.intro (SelectedOuterFaceSource.ofRaw H F hF)

theorem nonempty_selectedOuterFaceSource_iff_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (SelectedOuterFaceSource C) <->
      ExactSelectedOuterFaceSourceBlocker C :=
  nonempty_selectedOuterFaceSource_iff_selectedOuterFaceFields C

theorem nonempty_selectedOuterFaceSource_iff_selectedOuterFaceData
    (C : _root_.UDConfig n) :
    Nonempty (SelectedOuterFaceSource C) <->
      Nonempty (SelectedOuterFaceData C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toSelectedOuterFaceData
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact
          Nonempty.intro
            (SelectedOuterFaceSource.ofSelectedOuterFaceData D)

theorem selectedOuterFaceFields_iff_selectedOuterFaceData
    (C : _root_.UDConfig n) :
    SelectedOuterFaceFields C <->
      Nonempty (SelectedOuterFaceData C) :=
  Iff.trans
    (nonempty_selectedOuterFaceSource_iff_selectedOuterFaceFields C).symm
    (nonempty_selectedOuterFaceSource_iff_selectedOuterFaceData C)

def selectedOuterFaceSourceOfSelectedFaceEnclosureFields
    {C : _root_.UDConfig n}
    (h : SelectedFaceEnclosureFields C) :
    Nonempty (SelectedOuterFaceSource C) := by
  cases h with
  | intro H hH =>
      cases hH with
      | intro F hFPair =>
          exact
            Nonempty.intro
              (SelectedOuterFaceSource.ofRaw H F hFPair.1)

def selectedOuterFaceSourceOfExactTopologyFields
    {C : _root_.UDConfig n}
    (h : OuterBoundaryExistenceConcrete.ExactTopologyFields C) :
    Nonempty (SelectedOuterFaceSource C) :=
  selectedOuterFaceSourceOfSelectedFaceEnclosureFields
    ((SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactTopologyFields
      C).2 h)

def selectedOuterFaceSourceOfSplitExactTopologyFields
    {C : _root_.UDConfig n}
    (h : TopologyExtractionFromNoncrossing.SplitExactTopologyFields C) :
    Nonempty (SelectedOuterFaceSource C) := by
  cases h with
  | intro D _hE =>
      exact
        Nonempty.intro
          (SelectedOuterFaceSource.ofSelectedOuterFaceData D)

def selectedOuterFaceSourceOfActualSelectedTopologyData
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    SelectedOuterFaceSource C :=
  SelectedOuterFaceSource.ofActualSelectedTopologyData A

def selectedOuterFaceSourceOfOuterBoundaryCore
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    SelectedOuterFaceSource C :=
  SelectedOuterFaceSource.ofOuterBoundaryCore P

def selectedOuterFaceSourceOfOuterBoundaryCoreSource
    {C : _root_.UDConfig n}
    (S : OuterBoundaryCoreSource C) :
    SelectedOuterFaceSource C :=
  SelectedOuterFaceSource.ofOuterBoundaryCoreSource S

def selectedOuterFaceSourceOfOuterBoundarySourceFields
    {C : _root_.UDConfig n}
    (S : OuterBoundarySourceFields C) :
    SelectedOuterFaceSource C :=
  SelectedOuterFaceSource.ofOuterBoundarySourceFields S

theorem selectedFaceEnclosureFields_iff_exists_source_enclosureBlocker
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      ExactSelectedOuterFaceToTopologyBlocker C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro H hH =>
        cases hH with
        | intro F hFPair =>
            cases hFPair with
            | intro hF hE =>
                exact
                  Exists.intro
                    (SelectedOuterFaceSource.ofRaw H F hF) hE
  case mpr =>
    intro h
    cases h with
    | intro S hE =>
        exact
          Exists.intro S.faceBoundary
            (Exists.intro S.outerFace
              (And.intro S.outerFace_isOuter hE))

theorem exactSelectedOuterFaceToTopologyBlocker_iff_actualSelectedTopology
    (C : _root_.UDConfig n) :
    ExactSelectedOuterFaceToTopologyBlocker C <->
      Nonempty (ActualSelectedTopologyData C) :=
  Iff.trans
    (selectedFaceEnclosureFields_iff_exists_source_enclosureBlocker C).symm
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_actualSelectedTopologyData
      C)

theorem exactSelectedOuterFaceToTopologyBlocker_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    ExactSelectedOuterFaceToTopologyBlocker C <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) :=
  Iff.trans
    (selectedFaceEnclosureFields_iff_exists_source_enclosureBlocker C).symm
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_outerBoundaryCore
      C)

theorem selectedFaceEnclosureFields_iff_selectedOuterFaceSource_and_enclosure
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C <->
      Exists fun S : SelectedOuterFaceSource C =>
        SelectedOuterFaceEnclosureBlocker S :=
  selectedFaceEnclosureFields_iff_exists_source_enclosureBlocker C

theorem selectedFaceEnclosureFields_implies_selectedOuterFaceFields
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureFields C ->
      SelectedOuterFaceFields C := by
  intro h
  exact
    (nonempty_selectedOuterFaceSource_iff_selectedOuterFaceFields C).1
      (selectedOuterFaceSourceOfSelectedFaceEnclosureFields h)

theorem selectedOuterFaceSource_iff_graphFacts_and_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (SelectedOuterFaceSource C) <->
      CanonicalGraphFacts C /\
        ExactSelectedOuterFaceSourceBlocker C := by
  constructor
  case mp =>
    intro h
    exact And.intro
      (SelectedFaceEnclosureSourceW30.canonicalGraphFacts_available C)
      ((nonempty_selectedOuterFaceSource_iff_exactBlocker C).1 h)
  case mpr =>
    intro h
    exact (nonempty_selectedOuterFaceSource_iff_exactBlocker C).2 h.2

abbrev GlobalSelectedOuterFaceSourceTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (SelectedOuterFaceSource C)

abbrev GlobalSelectedOuterFaceToTopologyBlockerTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    ExactSelectedOuterFaceToTopologyBlocker C

theorem globalSelectedFaceEnclosureFieldsTarget_iff_selectedOuterFaceToTopologyBlocker :
    SelectedFaceEnclosureSourceW30.GlobalSelectedFaceEnclosureFieldsTarget <->
      GlobalSelectedOuterFaceToTopologyBlockerTarget := by
  constructor
  case mp =>
    intro h n C
    exact
      (selectedFaceEnclosureFields_iff_exists_source_enclosureBlocker C).1
        (h n C)
  case mpr =>
    intro h n C
    exact
      (selectedFaceEnclosureFields_iff_exists_source_enclosureBlocker C).2
        (h n C)

theorem globalSelectedOuterFaceToTopologyBlocker_iff_outerBoundaryCoreTarget :
    GlobalSelectedOuterFaceToTopologyBlockerTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Iff.trans
    globalSelectedFaceEnclosureFieldsTarget_iff_selectedOuterFaceToTopologyBlocker.symm
    SelectedFaceEnclosureSourceW30.globalSelectedFaceEnclosureFieldsTarget_iff_outerBoundaryCoreTarget

theorem globalSelectedOuterFaceSource_of_selectedFaceEnclosureFields :
    SelectedFaceEnclosureSourceW30.GlobalSelectedFaceEnclosureFieldsTarget ->
      GlobalSelectedOuterFaceSourceTarget := by
  intro h n C
  exact selectedOuterFaceSourceOfSelectedFaceEnclosureFields (h n C)

end

end SelectedOuterFaceConstructionW31

namespace Verified

open Swanepoel.SelectedOuterFaceConstructionW31

abbrev SwanepoelW31SelectedOuterFaceSource
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.SelectedOuterFaceConstructionW31.SelectedOuterFaceSource C

theorem swanepoelW31_selectedOuterFaceSource_exactly_selectedOuterFaceFields
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW31SelectedOuterFaceSource C) <->
      Swanepoel.SelectedOuterFaceConstructionW31.SelectedOuterFaceFields C :=
  nonempty_selectedOuterFaceSource_iff_selectedOuterFaceFields C

theorem swanepoelW31_selectedOuterFace_to_topology_blocker_exactly_actualTopology
    {n : Nat} (C : _root_.UDConfig n) :
    Swanepoel.SelectedOuterFaceConstructionW31.ExactSelectedOuterFaceToTopologyBlocker
        C <->
      Nonempty
        (Swanepoel.PlanarTopologyActualExtractionW26.ActualSelectedTopologyData
          C) :=
  exactSelectedOuterFaceToTopologyBlocker_iff_actualSelectedTopology C

theorem swanepoelW31_globalSelectedOuterFaceToTopologyBlocker_exactly_coreTarget :
    Swanepoel.SelectedOuterFaceConstructionW31.GlobalSelectedOuterFaceToTopologyBlockerTarget <->
      Swanepoel.OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  globalSelectedOuterFaceToTopologyBlocker_iff_outerBoundaryCoreTarget

end Verified
end Swanepoel
end ErdosProblems1066
