import ErdosProblems1066.Swanepoel.BoundaryRemainingComponentsConcreteW27
import ErdosProblems1066.Swanepoel.PlanarTopologyExtractionBridgeW25

set_option autoImplicit false

/-!
# W28 selected-face witness construction

`PlanarTopologyExtractionBridgeW25` packages the boundary data as an extracted
minimal-boundary witness row.  This file identifies that row with the W25
selected-face witness row and then feeds the result into the W27 remaining
component package.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SelectedFaceWitnessConstructionW28

open BoundaryRemainingComponentsConcreteW27
open MinimalBoundaryTopologyWitnessInhabitationW25
open PlanarTopologyExtractionBridgeW25

universe u

noncomputable section

variable {n : Nat}
variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

abbrev ExtractedWitnessRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  PlanarTopologyExtractionBridgeW25.ExtractedMinimalBoundaryTopologyWitness.{u}
    C hmin

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  PlanarTopologyExtractionBridgeW25.ExtractedMinimalBoundaryTopologyWitnessFamily.{u}

abbrev SelectedFaceWitnessRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessRow.{u}
    C hmin

abbrev SelectedFaceWitnessFamily : Type (u + 1) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessFamily.{u}

abbrev BoundaryRemainingComponentFamily : Type (u + 1) :=
  BoundaryRemainingComponentsConcreteW27.BoundaryRemainingComponentFamily.{u}

def remainingWitnessFieldsOfExtracted
    (P : ExtractedWitnessRow.{u} C hmin) :
    RemainingWitnessFields.{u} C hmin P.outerFaceData P.enclosureData where
  classification := P.classification.toConcreteClassification
  geometricAngleSum := P.geometricAngleSum
  forced_le_geometric := P.forced_le_geometric
  geometric_le_polygon := P.geometric_le_polygon
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def selectedFaceWitnessRowOfExtracted
    (P : ExtractedWitnessRow.{u} C hmin) :
    SelectedFaceWitnessRow.{u} C hmin where
  selectedFace := P.outerFaceData
  enclosure := P.enclosureData
  remaining := remainingWitnessFieldsOfExtracted P

def extractedOfSelectedFaceWitnessRow
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    ExtractedWitnessRow.{u} C hmin where
  outerFaceData := R.selectedFace
  enclosureData := R.enclosure
  classification := R.remaining.classification
  geometricAngleSum := R.remaining.geometricAngleSum
  forced_le_geometric := R.remaining.forced_le_geometric
  geometric_le_polygon := R.remaining.geometric_le_polygon
  Subpolygon := R.remaining.Subpolygon
  subpolygonData := R.remaining.subpolygonData
  longArc := R.remaining.longArc
  triangleRun := R.remaining.triangleRun

@[simp]
theorem selectedFaceWitnessRowOfExtracted_selectedFace
    (P : ExtractedWitnessRow.{u} C hmin) :
    (selectedFaceWitnessRowOfExtracted P).selectedFace = P.outerFaceData :=
  rfl

@[simp]
theorem selectedFaceWitnessRowOfExtracted_enclosure
    (P : ExtractedWitnessRow.{u} C hmin) :
    (selectedFaceWitnessRowOfExtracted P).enclosure = P.enclosureData :=
  rfl

@[simp]
theorem selectedFaceWitnessRowOfExtracted_remaining
    (P : ExtractedWitnessRow.{u} C hmin) :
    (selectedFaceWitnessRowOfExtracted P).remaining =
      remainingWitnessFieldsOfExtracted P :=
  rfl

@[simp]
theorem extractedOfSelectedFaceWitnessRow_outerFaceData
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    (extractedOfSelectedFaceWitnessRow R).outerFaceData = R.selectedFace :=
  rfl

@[simp]
theorem extractedOfSelectedFaceWitnessRow_enclosureData
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    (extractedOfSelectedFaceWitnessRow R).enclosureData = R.enclosure :=
  rfl

def selectedFaceWitnessRowEquivExtracted :
    Equiv (ExtractedWitnessRow.{u} C hmin)
      (SelectedFaceWitnessRow.{u} C hmin) where
  toFun := selectedFaceWitnessRowOfExtracted
  invFun := extractedOfSelectedFaceWitnessRow
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro R
    cases R with
    | mk selectedFace enclosure remaining =>
        cases remaining
        rfl

theorem nonempty_selectedFaceWitnessRow_iff_extracted
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (SelectedFaceWitnessRow.{u} C hmin) <->
      Nonempty (ExtractedWitnessRow.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (extractedOfSelectedFaceWitnessRow R)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (selectedFaceWitnessRowOfExtracted P)

def selectedFaceWitnessFamilyOfExtracted
    (F : ExtractedWitnessFamily.{u}) :
    SelectedFaceWitnessFamily.{u} where
  row := fun C hmin => selectedFaceWitnessRowOfExtracted (F.row C hmin)

def extractedFamilyOfSelectedFaceWitnessFamily
    (F : SelectedFaceWitnessFamily.{u}) :
    ExtractedWitnessFamily.{u} where
  row := fun C hmin => extractedOfSelectedFaceWitnessRow (F.row C hmin)

def selectedFaceWitnessFamilyEquivExtracted :
    Equiv ExtractedWitnessFamily.{u} SelectedFaceWitnessFamily.{u} where
  toFun := selectedFaceWitnessFamilyOfExtracted
  invFun := extractedFamilyOfSelectedFaceWitnessFamily
  left_inv := by
    intro F
    cases F
    rfl
  right_inv := by
    intro F
    cases F
    rfl

theorem selectedFaceWitnessFamily_nonempty_of_extracted
    (h : Nonempty ExtractedWitnessFamily.{u}) :
    Nonempty SelectedFaceWitnessFamily.{u} := by
  cases h with
  | intro F =>
      exact Nonempty.intro (selectedFaceWitnessFamilyOfExtracted F)

theorem extracted_nonempty_of_selectedFaceWitnessFamily
    (h : Nonempty SelectedFaceWitnessFamily.{u}) :
    Nonempty ExtractedWitnessFamily.{u} := by
  cases h with
  | intro F =>
      exact Nonempty.intro (extractedFamilyOfSelectedFaceWitnessFamily F)

theorem selectedFaceWitnessFamily_nonempty_iff_extracted :
    Nonempty SelectedFaceWitnessFamily.{u} <->
      Nonempty ExtractedWitnessFamily.{u} := by
  constructor
  case mp =>
    exact extracted_nonempty_of_selectedFaceWitnessFamily
  case mpr =>
    exact selectedFaceWitnessFamily_nonempty_of_extracted

def boundaryRemainingComponentFamilyOfExtracted
    (F : ExtractedWitnessFamily.{u}) :
    BoundaryRemainingComponentFamily.{u} :=
  BoundaryRemainingComponentsConcreteW27.boundaryRemainingComponentFamilyOfSelectedFaceWitnessFamily
    (selectedFaceWitnessFamilyOfExtracted F)

theorem boundaryRemainingComponentFamily_nonempty_of_extracted
    (h : Nonempty ExtractedWitnessFamily.{u}) :
    Nonempty BoundaryRemainingComponentFamily.{u} := by
  cases h with
  | intro F =>
      exact Nonempty.intro (boundaryRemainingComponentFamilyOfExtracted F)

theorem extracted_nonempty_of_boundaryRemainingComponentFamily
    (h : Nonempty BoundaryRemainingComponentFamily.{u}) :
    Nonempty ExtractedWitnessFamily.{u} :=
  extracted_nonempty_of_selectedFaceWitnessFamily
    (BoundaryRemainingComponentsConcreteW27.selectedFaceWitnessFamily_nonempty_of_boundaryRemainingComponentFamily
      h)

theorem boundaryRemainingComponentFamily_nonempty_iff_extracted :
    Nonempty BoundaryRemainingComponentFamily.{u} <->
      Nonempty ExtractedWitnessFamily.{u} := by
  constructor
  case mp =>
    exact extracted_nonempty_of_boundaryRemainingComponentFamily
  case mpr =>
    exact boundaryRemainingComponentFamily_nonempty_of_extracted

end

end SelectedFaceWitnessConstructionW28
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW28ExtractedWitnessFamily : Type (u + 1) :=
  Swanepoel.SelectedFaceWitnessConstructionW28.ExtractedWitnessFamily.{u}

abbrev SwanepoelW28SelectedFaceWitnessFamily : Type (u + 1) :=
  Swanepoel.SelectedFaceWitnessConstructionW28.SelectedFaceWitnessFamily.{u}

abbrev SwanepoelW28BoundaryRemainingComponentFamily : Type (u + 1) :=
  Swanepoel.SelectedFaceWitnessConstructionW28.BoundaryRemainingComponentFamily.{u}

theorem swanepoelW28_selectedFaceWitnessFamily_nonempty_iff_extracted :
    Nonempty SwanepoelW28SelectedFaceWitnessFamily.{u} <->
      Nonempty SwanepoelW28ExtractedWitnessFamily.{u} :=
  Swanepoel.SelectedFaceWitnessConstructionW28.selectedFaceWitnessFamily_nonempty_iff_extracted

theorem swanepoelW28_boundaryRemainingComponentFamily_nonempty_iff_extracted :
    Nonempty SwanepoelW28BoundaryRemainingComponentFamily.{u} <->
      Nonempty SwanepoelW28ExtractedWitnessFamily.{u} :=
  Swanepoel.SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamily_nonempty_iff_extracted

theorem swanepoelW28_boundaryRemainingComponentFamily_nonempty_of_extracted
    (h : Nonempty SwanepoelW28ExtractedWitnessFamily.{u}) :
    Nonempty SwanepoelW28BoundaryRemainingComponentFamily.{u} :=
  Swanepoel.SelectedFaceWitnessConstructionW28.boundaryRemainingComponentFamily_nonempty_of_extracted
    h

end Verified
end ErdosProblems1066
