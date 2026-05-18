import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstructionW28
import ErdosProblems1066.Swanepoel.SelectedFaceWitnessConstructionW28

set_option autoImplicit false

/-!
# W29 extracted-boundary witness source

W28 supplies the checked outer-boundary core.  The W25/W28 extracted minimal
boundary witness also requires the remaining boundary-analysis gates:
classification, angle comparison, subpolygon data, long-arc data, and the
triangle run.

This file records that exact source surface and gives row/family constructors
to and from `ExtractedMinimalBoundaryTopologyWitnessFamily`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ExtractedBoundaryWitnessSourceW29

open BoundaryWitnessRemainingFieldsW26
open OuterBoundaryCoreConstructionW28
open PlanarTopologyExtractionBridgeW25
open SelectedFaceWitnessConstructionW28

universe u

noncomputable section

variable {n : Nat}

abbrev ExtractedWitnessRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  PlanarTopologyExtractionBridgeW25.ExtractedMinimalBoundaryTopologyWitness.{u}
    C hmin

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  PlanarTopologyExtractionBridgeW25.ExtractedMinimalBoundaryTopologyWitnessFamily.{u}

abbrev W28OuterBoundaryCoreSource (C : _root_.UDConfig n) :=
  OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  PlanarTopologyExtractionBridgeW25.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  PlanarTopologyExtractionBridgeW25.SelectedEnclosureData D

abbrev RemainingComponentFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.RemainingWitnessComponentFields.{u}
    C hmin D E

def coreSourceOfSelectedFaceAndEnclosure
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    W28OuterBoundaryCoreSource C :=
  OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource.ofSelectedOuterFaceAndEnclosure
    D E

@[simp]
theorem coreSourceOfSelectedFaceAndEnclosure_core
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    (coreSourceOfSelectedFaceAndEnclosure D E).core =
      PlanarTopologyExtractionBridgeW25.SelectedEnclosureData.toCore E :=
  rfl

structure ExtractedBoundaryWitnessSourceRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) where
  outerBoundary : W28OuterBoundaryCoreSource C
  selectedFace : SelectedOuterFaceData C
  enclosure : SelectedEnclosureData selectedFace
  outerBoundary_core :
    outerBoundary.core =
      PlanarTopologyExtractionBridgeW25.SelectedEnclosureData.toCore enclosure
  remaining : RemainingComponentFields.{u} C hmin selectedFace enclosure

namespace ExtractedBoundaryWitnessSourceRow

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def remainingWitnessFields
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    MinimalBoundaryTopologyWitnessInhabitationW25.RemainingWitnessFields.{u}
      C hmin S.selectedFace S.enclosure :=
  S.remaining.toRemainingWitnessFields

def toExtractedWitness
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    ExtractedWitnessRow.{u} C hmin where
  outerFaceData := S.selectedFace
  enclosureData := S.enclosure
  classification := S.remainingWitnessFields.classification
  geometricAngleSum := S.remainingWitnessFields.geometricAngleSum
  forced_le_geometric := S.remainingWitnessFields.forced_le_geometric
  geometric_le_polygon := S.remainingWitnessFields.geometric_le_polygon
  Subpolygon := S.remainingWitnessFields.Subpolygon
  subpolygonData := S.remainingWitnessFields.subpolygonData
  longArc := S.remainingWitnessFields.longArc
  triangleRun := S.remainingWitnessFields.triangleRun

def ofExtractedWitness
    (P : ExtractedWitnessRow.{u} C hmin) :
    ExtractedBoundaryWitnessSourceRow.{u} C hmin where
  outerBoundary :=
    coreSourceOfSelectedFaceAndEnclosure P.outerFaceData P.enclosureData
  selectedFace := P.outerFaceData
  enclosure := P.enclosureData
  outerBoundary_core := rfl
  remaining :=
    RemainingWitnessComponentFields.ofRemainingWitnessFields
      (SelectedFaceWitnessConstructionW28.remainingWitnessFieldsOfExtracted
        P)

@[simp]
theorem toExtractedWitness_outerFaceData
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    S.toExtractedWitness.outerFaceData = S.selectedFace :=
  rfl

@[simp]
theorem toExtractedWitness_enclosureData
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    S.toExtractedWitness.enclosureData = S.enclosure :=
  rfl

@[simp]
theorem toExtractedWitness_classification
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    S.toExtractedWitness.classification =
      S.remaining.classificationField.classification :=
  rfl

@[simp]
theorem toExtractedWitness_geometricAngleSum
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    S.toExtractedWitness.geometricAngleSum =
      S.remaining.angleField.geometricAngleSum :=
  rfl

@[simp]
theorem toExtractedWitness_Subpolygon
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    S.toExtractedWitness.Subpolygon =
      S.remaining.subpolygonField.Subpolygon :=
  rfl

@[simp]
theorem toExtractedWitness_longArc
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    S.toExtractedWitness.longArc =
      S.remaining.longArcField.longArc :=
  rfl

@[simp]
theorem toExtractedWitness_triangleRun
    (S : ExtractedBoundaryWitnessSourceRow.{u} C hmin) :
    S.toExtractedWitness.triangleRun =
      S.remaining.triangleRunField.triangleRun :=
  rfl

theorem nonempty_extractedWitness_iff_sourceRow :
    Nonempty (ExtractedWitnessRow.{u} C hmin) <->
      Nonempty (ExtractedBoundaryWitnessSourceRow.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (ofExtractedWitness P)
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toExtractedWitness

end ExtractedBoundaryWitnessSourceRow

structure ExtractedBoundaryWitnessSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ExtractedBoundaryWitnessSourceRow.{u} C hmin

namespace ExtractedBoundaryWitnessSourceFamily

def toExtractedWitnessFamily
    (F : ExtractedBoundaryWitnessSourceFamily.{u}) :
    ExtractedWitnessFamily.{u} where
  row := fun C hmin => (F.row C hmin).toExtractedWitness

def ofExtractedWitnessFamily
    (F : ExtractedWitnessFamily.{u}) :
    ExtractedBoundaryWitnessSourceFamily.{u} where
  row := fun C hmin =>
    ExtractedBoundaryWitnessSourceRow.ofExtractedWitness (F.row C hmin)

theorem nonempty_extractedWitnessFamily
    (F : ExtractedBoundaryWitnessSourceFamily.{u}) :
    Nonempty ExtractedWitnessFamily.{u} :=
  Nonempty.intro F.toExtractedWitnessFamily

theorem nonempty_w28OuterBoundaryCoreSource
    (F : ExtractedBoundaryWitnessSourceFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (W28OuterBoundaryCoreSource C) :=
  Nonempty.intro (F.row C hmin).outerBoundary

end ExtractedBoundaryWitnessSourceFamily

theorem sourceFamily_nonempty_of_extractedWitnessFamily
    (h : Nonempty ExtractedWitnessFamily.{u}) :
    Nonempty ExtractedBoundaryWitnessSourceFamily.{u} := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (ExtractedBoundaryWitnessSourceFamily.ofExtractedWitnessFamily F)

theorem extractedWitnessFamily_nonempty_of_sourceFamily
    (h : Nonempty ExtractedBoundaryWitnessSourceFamily.{u}) :
    Nonempty ExtractedWitnessFamily.{u} := by
  cases h with
  | intro F =>
      exact F.nonempty_extractedWitnessFamily

theorem extractedWitnessFamily_nonempty_iff_sourceFamily :
    Nonempty ExtractedWitnessFamily.{u} <->
      Nonempty ExtractedBoundaryWitnessSourceFamily.{u} := by
  constructor
  case mp =>
    exact sourceFamily_nonempty_of_extractedWitnessFamily
  case mpr =>
    exact extractedWitnessFamily_nonempty_of_sourceFamily

theorem selectedFaceWitnessFamily_nonempty_of_sourceFamily
    (h : Nonempty ExtractedBoundaryWitnessSourceFamily.{u}) :
    Nonempty SelectedFaceWitnessFamily.{u} :=
  SelectedFaceWitnessConstructionW28.selectedFaceWitnessFamily_nonempty_of_extracted
    (extractedWitnessFamily_nonempty_of_sourceFamily h)

theorem boundaryRemainingComponentFamily_nonempty_of_sourceFamily
    (h : Nonempty ExtractedBoundaryWitnessSourceFamily.{u}) :
    Nonempty BoundaryRemainingComponentFamily.{u} :=
  SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamily_nonempty_of_extracted
    (extractedWitnessFamily_nonempty_of_sourceFamily h)

end

end ExtractedBoundaryWitnessSourceW29
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW29ExtractedBoundaryWitnessSourceFamily : Type (u + 1) :=
  Swanepoel.ExtractedBoundaryWitnessSourceW29.ExtractedBoundaryWitnessSourceFamily.{u}

abbrev SwanepoelW29ExtractedMinimalBoundaryTopologyWitnessFamily :
    Type (u + 1) :=
  Swanepoel.ExtractedBoundaryWitnessSourceW29.ExtractedWitnessFamily.{u}

theorem swanepoelW29_extractedWitnessFamily_exactly_sourceFamily :
    Nonempty SwanepoelW29ExtractedMinimalBoundaryTopologyWitnessFamily.{u} <->
      Nonempty SwanepoelW29ExtractedBoundaryWitnessSourceFamily.{u} :=
  Swanepoel.ExtractedBoundaryWitnessSourceW29.extractedWitnessFamily_nonempty_iff_sourceFamily

theorem swanepoelW29_selectedFaceWitnessFamily_nonempty_of_sourceFamily
    (h : Nonempty SwanepoelW29ExtractedBoundaryWitnessSourceFamily.{u}) :
    Nonempty
      Swanepoel.SelectedFaceWitnessConstructionW28.SelectedFaceWitnessFamily.{u} :=
  Swanepoel.ExtractedBoundaryWitnessSourceW29.selectedFaceWitnessFamily_nonempty_of_sourceFamily
    h

end Verified
end ErdosProblems1066
