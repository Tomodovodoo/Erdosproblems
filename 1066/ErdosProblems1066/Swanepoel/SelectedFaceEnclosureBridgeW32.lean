import ErdosProblems1066.Swanepoel.SelectedOuterFaceConstructionW31
import ErdosProblems1066.Swanepoel.EnclosureAndFaceBoundaryW31

set_option autoImplicit false

/-!
# W32 selected-face/enclosure bridge

This file combines the W31 selected outer-face source with the W31
face-boundary/enclosure source.  The route keeps the selected face explicit and
indexes the enclosure by that same dependent face, so every constructor consumes
the face data it uses.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SelectedFaceEnclosureBridgeW32

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.CanonicalGraph C

abbrev FaceBoundaryHypotheses (C : _root_.UDConfig n) :=
  FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (CanonicalGraph C)

abbrev SelectedOuterFaceSource (C : _root_.UDConfig n) :=
  SelectedOuterFaceConstructionW31.SelectedOuterFaceSource C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureSourceW30.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  SelectedFaceEnclosureSourceW30.SelectedEnclosureData D

abbrev SelectedOuterFaceEnclosureBlocker
    {C : _root_.UDConfig n} (S : SelectedOuterFaceSource C) : Prop :=
  SelectedOuterFaceConstructionW31.SelectedOuterFaceEnclosureBlocker S

abbrev FaceBoundaryEnclosureSource (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.FaceBoundaryEnclosureSource C

abbrev SelectedFaceEnclosureFields (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields C

abbrev ExactSelectedFaceEnclosureBlocker (C : _root_.UDConfig n) : Prop :=
  SelectedFaceEnclosureSourceW30.ExactSelectedFaceEnclosureBlocker C

abbrev ExactSelectedOuterFaceToTopologyBlocker
    (C : _root_.UDConfig n) : Prop :=
  SelectedOuterFaceConstructionW31.ExactSelectedOuterFaceToTopologyBlocker C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

/-- A W32 route consisting of a selected W31 outer face and an enclosure for
that exact dependent face. -/
structure SelectedFaceEnclosureRoute (C : _root_.UDConfig n) where
  selectedOuterFace : SelectedOuterFaceSource C
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C)
      selectedOuterFace.faceBoundary
      selectedOuterFace.outerFace

namespace SelectedFaceEnclosureRoute

variable {C : _root_.UDConfig n}

def ofRaw
    (H : FaceBoundaryHypotheses C)
    (F : H.Face)
    (hF : H.IsOuterFace F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    SelectedFaceEnclosureRoute C where
  selectedOuterFace :=
    SelectedOuterFaceConstructionW31.SelectedOuterFaceSource.ofRaw H F hF
  outerEnclosure := E

def ofSelectedOuterFaceSource
    (S : SelectedOuterFaceSource C)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) S.faceBoundary S.outerFace) :
    SelectedFaceEnclosureRoute C where
  selectedOuterFace := S
  outerEnclosure := E

/-- The enclosure predicates canonically determined by a selected boundary
face: every vertex is inside-or-on, and boundary vertices are exactly the
vertices appearing on the selected boundary cycle. -/
def boundarySetEnclosure
    (S : SelectedOuterFaceSource C) :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) S.faceBoundary S.outerFace where
  insideOrOn := fun _ => True
  onBoundary := fun v =>
    Exists fun k : Fin (S.faceBoundary.boundaryLength S.outerFace) =>
      S.faceBoundary.boundaryVertex S.outerFace k = v
  boundary_vertex_onBoundary := fun k => Exists.intro k rfl
  boundary_point_insideOrOn := fun _ => trivial
  all_vertices_insideOrOn := fun _ => trivial
  onBoundary_iff_outer_cycle := fun _ => Iff.rfl

/-- Build the selected face/enclosure route from selected face-boundary data
alone, using the boundary-set enclosure predicates. -/
def ofSelectedOuterFaceSourceBoundarySet
    (S : SelectedOuterFaceSource C) :
    SelectedFaceEnclosureRoute C :=
  ofSelectedOuterFaceSource S (boundarySetEnclosure S)

def ofFaceBoundaryEnclosureSource
    (S : FaceBoundaryEnclosureSource C) :
    SelectedFaceEnclosureRoute C :=
  ofRaw S.faceBoundary S.outerFace S.outerFace_isOuter S.outerEnclosure

def selectedOuterFaceData
    (R : SelectedFaceEnclosureRoute C) :
    SelectedOuterFaceData C :=
  R.selectedOuterFace.toSelectedOuterFaceData

def selectedEnclosureData
    (R : SelectedFaceEnclosureRoute C) :
    SelectedEnclosureData R.selectedOuterFaceData where
  outerEnclosure := R.outerEnclosure

def toSelectedFaceEnclosureFields
    (R : SelectedFaceEnclosureRoute C) :
    SelectedFaceEnclosureFields C :=
  SelectedFaceEnclosureSourceW30.ofSelectedOuterFaceAndEnclosure
    R.selectedOuterFaceData R.selectedEnclosureData

def toExactSelectedFaceEnclosureBlocker
    (R : SelectedFaceEnclosureRoute C) :
    ExactSelectedFaceEnclosureBlocker C :=
  (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactBlocker
    C).1 R.toSelectedFaceEnclosureFields

def toSelectedOuterFaceEnclosureBlocker
    (R : SelectedFaceEnclosureRoute C) :
    SelectedOuterFaceEnclosureBlocker R.selectedOuterFace :=
  Nonempty.intro R.outerEnclosure

def toExactSelectedOuterFaceToTopologyBlocker
    (R : SelectedFaceEnclosureRoute C) :
    ExactSelectedOuterFaceToTopologyBlocker C :=
  Exists.intro R.selectedOuterFace R.toSelectedOuterFaceEnclosureBlocker

theorem outerBoundaryEnclosureRow
    (R : SelectedFaceEnclosureRoute C) :
    Nonempty
      (OuterBoundaryInterface.OuterBoundaryEnclosure
        (CanonicalGraph C)
        R.selectedOuterFace.faceBoundary
        R.selectedOuterFace.outerFace) :=
  Nonempty.intro R.outerEnclosure

theorem toExactActualTopologyFields
    (R : SelectedFaceEnclosureRoute C)
    (hlen :
      3 <=
        R.selectedOuterFace.faceBoundary.boundaryLength
          R.selectedOuterFace.outerFace) :
    OuterBoundaryExistenceConcrete.ExactActualTopologyFields C :=
  OuterBoundaryExistenceConcrete.exactActualTopologyFields_of_faceBoundaryFields
    (C := C) (H := R.selectedOuterFace.faceBoundary)
    (F := R.selectedOuterFace.outerFace)
    R.selectedOuterFace.outerFace_isOuter hlen R.outerBoundaryEnclosureRow

def toFaceBoundaryEnclosureSource
    (R : SelectedFaceEnclosureRoute C) :
    FaceBoundaryEnclosureSource C :=
  EnclosureAndFaceBoundaryW31.ofRawFaceBoundaryAndEnclosure
    R.selectedOuterFace.faceBoundary
    R.selectedOuterFace.outerFace
    R.selectedOuterFace.outerFace_isOuter
    R.outerEnclosure

def toOuterBoundaryCore
    (R : SelectedFaceEnclosureRoute C) :
    OuterBoundaryCore.{0} (CanonicalGraph C) :=
  R.toFaceBoundaryEnclosureSource.toOuterBoundaryCore

def toActualSelectedTopologyData
    (R : SelectedFaceEnclosureRoute C) :
    ActualSelectedTopologyData C :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
    R.toOuterBoundaryCore

def planarFaceBoundary
    (R : SelectedFaceEnclosureRoute C) :
    PlanarInterface.FaceBoundaryHypotheses
      (CanonicalGraph C).toStraightLine :=
  R.selectedOuterFace.faceBoundary.toFaceBoundaryHypotheses

theorem pairwiseNoncrossing
    (R : SelectedFaceEnclosureRoute C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  R.planarFaceBoundary.noncrossing

theorem all_vertices_insideOrOn
    (R : SelectedFaceEnclosureRoute C) (v : Fin n) :
    R.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  R.outerEnclosure.all_vertices_insideOrOn v

theorem onBoundary_iff_outerCycle
    (R : SelectedFaceEnclosureRoute C) (v : Fin n) :
    R.outerEnclosure.onBoundary v <->
      Exists fun k : Fin R.toOuterBoundaryCore.outerCycle.length =>
        R.toOuterBoundaryCore.outerCycle.vertex k = v :=
  R.toFaceBoundaryEnclosureSource.onBoundary_iff_outerCycle v

@[simp]
theorem selectedOuterFaceData_faceBoundary
    (R : SelectedFaceEnclosureRoute C) :
    R.selectedOuterFaceData.faceBoundary =
      R.selectedOuterFace.faceBoundary :=
  rfl

@[simp]
theorem selectedOuterFaceData_outerFace
    (R : SelectedFaceEnclosureRoute C) :
    R.selectedOuterFaceData.outerFace =
      R.selectedOuterFace.outerFace :=
  rfl

@[simp]
theorem selectedEnclosureData_outerEnclosure
    (R : SelectedFaceEnclosureRoute C) :
    R.selectedEnclosureData.outerEnclosure = R.outerEnclosure :=
  rfl

@[simp]
theorem toFaceBoundaryEnclosureSource_faceBoundary
    (R : SelectedFaceEnclosureRoute C) :
    R.toFaceBoundaryEnclosureSource.faceBoundary =
      R.selectedOuterFace.faceBoundary :=
  rfl

@[simp]
theorem toFaceBoundaryEnclosureSource_outerFace
    (R : SelectedFaceEnclosureRoute C) :
    R.toFaceBoundaryEnclosureSource.outerFace =
      R.selectedOuterFace.outerFace :=
  rfl

@[simp]
theorem toFaceBoundaryEnclosureSource_outerEnclosure
    (R : SelectedFaceEnclosureRoute C) :
    R.toFaceBoundaryEnclosureSource.outerEnclosure = R.outerEnclosure :=
  rfl

@[simp]
theorem toFaceBoundaryEnclosureSource_ofFaceBoundaryEnclosureSource
    (S : FaceBoundaryEnclosureSource C) :
    (ofFaceBoundaryEnclosureSource S).toFaceBoundaryEnclosureSource = S := by
  cases S
  rfl

@[simp]
theorem ofFaceBoundaryEnclosureSource_toFaceBoundaryEnclosureSource
    (R : SelectedFaceEnclosureRoute C) :
    ofFaceBoundaryEnclosureSource R.toFaceBoundaryEnclosureSource = R := by
  cases R with
  | mk S E =>
      cases S
      rfl

def faceBoundaryEnclosureSourceEquiv
    (C : _root_.UDConfig n) :
    SelectedFaceEnclosureRoute C ≃ FaceBoundaryEnclosureSource C where
  toFun := fun R => R.toFaceBoundaryEnclosureSource
  invFun := fun S => ofFaceBoundaryEnclosureSource S
  left_inv := fun R =>
    ofFaceBoundaryEnclosureSource_toFaceBoundaryEnclosureSource R
  right_inv := fun S =>
    toFaceBoundaryEnclosureSource_ofFaceBoundaryEnclosureSource S

end SelectedFaceEnclosureRoute

def ofRawSelectedFaceAndEnclosure
    {C : _root_.UDConfig n}
    (H : FaceBoundaryHypotheses C)
    (F : H.Face)
    (hF : H.IsOuterFace F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    SelectedFaceEnclosureRoute C :=
  SelectedFaceEnclosureRoute.ofRaw H F hF E

theorem outerBoundaryEnclosureRow_ofRawSelectedFaceAndEnclosure
    {C : _root_.UDConfig n}
    {H : FaceBoundaryHypotheses C}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    Nonempty
      (OuterBoundaryInterface.OuterBoundaryEnclosure
        (CanonicalGraph C) H F) :=
  (ofRawSelectedFaceAndEnclosure H F hF E).outerBoundaryEnclosureRow

theorem exactActualTopologyFields_ofRawSelectedFaceAndEnclosure
    {C : _root_.UDConfig n}
    {H : FaceBoundaryHypotheses C}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hlen : 3 <= H.boundaryLength F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    OuterBoundaryExistenceConcrete.ExactActualTopologyFields C :=
  (ofRawSelectedFaceAndEnclosure H F hF E).toExactActualTopologyFields hlen

def ofSelectedOuterFaceSourceAndEnclosure
    {C : _root_.UDConfig n}
    (S : SelectedOuterFaceSource C)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) S.faceBoundary S.outerFace) :
    SelectedFaceEnclosureRoute C :=
  SelectedFaceEnclosureRoute.ofSelectedOuterFaceSource S E

def ofSelectedOuterFaceSourceBoundarySet
    {C : _root_.UDConfig n}
    (S : SelectedOuterFaceSource C) :
    SelectedFaceEnclosureRoute C :=
  SelectedFaceEnclosureRoute.ofSelectedOuterFaceSourceBoundarySet S

def ofFaceBoundaryEnclosureSource
    {C : _root_.UDConfig n}
    (S : FaceBoundaryEnclosureSource C) :
    SelectedFaceEnclosureRoute C :=
  SelectedFaceEnclosureRoute.ofFaceBoundaryEnclosureSource S

def ofOuterBoundaryCore
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    SelectedFaceEnclosureRoute C :=
  ofFaceBoundaryEnclosureSource
    (EnclosureAndFaceBoundaryW31.ofOuterBoundaryCore P)

def ofActualSelectedTopologyData
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    SelectedFaceEnclosureRoute C :=
  ofOuterBoundaryCore
    (ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
      A)

def actualSelectedTopologyDataOfRoute
    {C : _root_.UDConfig n}
    (R : SelectedFaceEnclosureRoute C) :
    ActualSelectedTopologyData C :=
  R.toActualSelectedTopologyData

theorem nonempty_actualSelectedTopologyData_of_route
    {C : _root_.UDConfig n}
    (h : Nonempty (SelectedFaceEnclosureRoute C)) :
    Nonempty (ActualSelectedTopologyData C) := by
  cases h with
  | intro R =>
      exact Nonempty.intro R.toActualSelectedTopologyData

def MinimalFailureSelectedFaceEnclosureRouteRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      SelectedFaceEnclosureRoute C

def MinimalFailureActualSelectedTopologyRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ActualSelectedTopologyData C

def actualSelectedTopologyRowsOfSelectedFaceEnclosureRouteRows
    (rows : MinimalFailureSelectedFaceEnclosureRouteRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => (rows C hmin).toActualSelectedTopologyData

def ofOuterBoundarySourceFields
    {C : _root_.UDConfig n}
    (S : SelectedFaceEnclosureSourceW30.OuterBoundarySourceFields C) :
    SelectedFaceEnclosureRoute C :=
  ofFaceBoundaryEnclosureSource
    (EnclosureAndFaceBoundaryW31.ofOuterBoundarySourceFields S)

theorem nonempty_route_iff_faceBoundaryEnclosureSource
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (FaceBoundaryEnclosureSource C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro R.toFaceBoundaryEnclosureSource
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro (ofFaceBoundaryEnclosureSource S)

theorem nonempty_route_iff_selectedOuterFaceSource_and_enclosure
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Exists fun S : SelectedOuterFaceSource C =>
        SelectedOuterFaceEnclosureBlocker S := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact
          Exists.intro R.selectedOuterFace
            R.toSelectedOuterFaceEnclosureBlocker
  case mpr =>
    intro h
    cases h with
    | intro S hS =>
        cases hS with
        | intro E =>
            exact
              Nonempty.intro
                (ofSelectedOuterFaceSourceAndEnclosure S E)

theorem selectedOuterFaceSource_implies_route
    {C : _root_.UDConfig n}
    (S : SelectedOuterFaceSource C) :
    Nonempty (SelectedFaceEnclosureRoute C) :=
  Nonempty.intro (ofSelectedOuterFaceSourceBoundarySet S)

theorem nonempty_route_iff_selectedOuterFaceSource
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (SelectedOuterFaceSource C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro R.selectedOuterFace
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact selectedOuterFaceSource_implies_route S

theorem nonempty_route_iff_selectedOuterFaceFields
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      SelectedOuterFaceConstructionW31.SelectedOuterFaceFields C :=
  Iff.trans
    (nonempty_route_iff_selectedOuterFaceSource C)
    (SelectedOuterFaceConstructionW31.nonempty_selectedOuterFaceSource_iff_selectedOuterFaceFields
      C)

theorem nonempty_route_iff_exactSelectedOuterFaceSourceBlocker
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      SelectedOuterFaceConstructionW31.ExactSelectedOuterFaceSourceBlocker C :=
  Iff.trans
    (nonempty_route_iff_selectedOuterFaceSource C)
    (SelectedOuterFaceConstructionW31.nonempty_selectedOuterFaceSource_iff_exactBlocker
      C)

theorem nonempty_route_iff_exactSelectedOuterFaceToTopologyBlocker
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      ExactSelectedOuterFaceToTopologyBlocker C :=
  nonempty_route_iff_selectedOuterFaceSource_and_enclosure C

theorem nonempty_route_iff_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      SelectedFaceEnclosureFields C :=
  Iff.trans
    (nonempty_route_iff_faceBoundaryEnclosureSource C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_selectedFaceEnclosureFields
      C)

theorem nonempty_route_iff_exactSelectedFaceEnclosureBlocker
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      ExactSelectedFaceEnclosureBlocker C :=
  Iff.trans
    (nonempty_route_iff_selectedFaceEnclosureFields C)
    (SelectedFaceEnclosureSourceW30.selectedFaceEnclosureFields_iff_exactBlocker
      C)

theorem nonempty_route_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) :=
  Iff.trans
    (nonempty_route_iff_faceBoundaryEnclosureSource C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_outerBoundaryCore C)

theorem nonempty_route_iff_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (ActualSelectedTopologyData C) :=
  Iff.trans
    (nonempty_route_iff_outerBoundaryCore C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_outerBoundaryCore
      C).symm

theorem route_missing_iff_no_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
    Not (Nonempty (SelectedFaceEnclosureRoute C)) <->
      Not (SelectedFaceEnclosureFields C) :=
  not_congr (nonempty_route_iff_selectedFaceEnclosureFields C)

theorem route_missing_iff_no_exactSelectedFaceEnclosureBlocker
    (C : _root_.UDConfig n) :
    Not (Nonempty (SelectedFaceEnclosureRoute C)) <->
      Not (ExactSelectedFaceEnclosureBlocker C) :=
  not_congr (nonempty_route_iff_exactSelectedFaceEnclosureBlocker C)

theorem route_missing_iff_no_outerBoundaryCore
    (C : _root_.UDConfig n) :
    Not (Nonempty (SelectedFaceEnclosureRoute C)) <->
      Not (Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C))) :=
  not_congr (nonempty_route_iff_outerBoundaryCore C)

theorem route_missing_iff_no_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    Not (Nonempty (SelectedFaceEnclosureRoute C)) <->
      Not (Nonempty (ActualSelectedTopologyData C)) :=
  not_congr (nonempty_route_iff_actualSelectedTopologyData C)

end

end SelectedFaceEnclosureBridgeW32

namespace Verified

open Swanepoel.SelectedFaceEnclosureBridgeW32

abbrev SwanepoelW32SelectedFaceEnclosureRoute
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.SelectedFaceEnclosureBridgeW32.SelectedFaceEnclosureRoute C

theorem swanepoelW32_route_exactly_w31FaceBoundaryEnclosureSource
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32SelectedFaceEnclosureRoute C) <->
      Nonempty
        (Swanepoel.EnclosureAndFaceBoundaryW31.FaceBoundaryEnclosureSource
          C) :=
  Swanepoel.SelectedFaceEnclosureBridgeW32.nonempty_route_iff_faceBoundaryEnclosureSource
    C

theorem swanepoelW32_route_exactly_w31SelectedOuterFaceWithEnclosure
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32SelectedFaceEnclosureRoute C) <->
      Swanepoel.SelectedOuterFaceConstructionW31.ExactSelectedOuterFaceToTopologyBlocker
        C :=
  nonempty_route_iff_exactSelectedOuterFaceToTopologyBlocker C

theorem swanepoelW32_route_exactly_w30SelectedFaceEnclosure
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32SelectedFaceEnclosureRoute C) <->
      Swanepoel.SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields
        C :=
  Swanepoel.SelectedFaceEnclosureBridgeW32.nonempty_route_iff_selectedFaceEnclosureFields
    C

theorem swanepoelW32_route_exactly_actualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32SelectedFaceEnclosureRoute C) <->
      Nonempty
        (Swanepoel.SelectedFaceEnclosureBridgeW32.ActualSelectedTopologyData
          C) :=
  Swanepoel.SelectedFaceEnclosureBridgeW32.nonempty_route_iff_actualSelectedTopologyData
    C

theorem swanepoelW32_route_missing_exactly_no_selectedFaceEnclosure
    {n : Nat} (C : _root_.UDConfig n) :
    Not (Nonempty (SwanepoelW32SelectedFaceEnclosureRoute C)) <->
      Not
        (Swanepoel.SelectedFaceEnclosureSourceW30.SelectedFaceEnclosureFields
          C) :=
  Swanepoel.SelectedFaceEnclosureBridgeW32.route_missing_iff_no_selectedFaceEnclosureFields
    C

end Verified
end Swanepoel
end ErdosProblems1066
