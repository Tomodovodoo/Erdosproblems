import ErdosProblems1066.Swanepoel.BoundaryWitnessRemainingFieldsW26

set_option autoImplicit false

/-!
# W27 concrete boundary remaining-component bridge

This worker closes the purely structural direction left after W26: a W25
selected-face witness family already contains the five remaining boundary
components over the selected topology.  We expose the five component gates by
name and reassemble them into the W26 component-family surface.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryRemainingComponentsConcreteW27

open BoundaryWitnessRemainingFieldsW26

universe u

noncomputable section

variable {n : Nat}
variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}

abbrev W25RemainingWitnessFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :=
  BoundaryWitnessRemainingFieldsW26.W25RemainingWitnessFields.{u} C hmin D E

abbrev W25SelectedFaceWitnessRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessRow.{u}
    C hmin

abbrev W25SelectedFaceWitnessFamily : Type (u + 1) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessFamily.{u}

abbrev BoundaryRemainingComponentFamily : Type (u + 1) :=
  SelectedFaceRemainingComponentFamily.{u}

/-! ## The five named gates extracted from a W25 remaining row -/

def classificationGateOfRemainingWitnessFields
    (R : W25RemainingWitnessFields C hmin D E) :
    BoundaryClassificationField.{u} C D E where
  classification := R.classification

def angleComparisonGateOfRemainingWitnessFields
    (R : W25RemainingWitnessFields C hmin D E) :
    OuterBoundaryAngleComparisonField.{u}
      (classificationGateOfRemainingWitnessFields R) where
  geometricAngleSum := R.geometricAngleSum
  forced_le_geometric := R.forced_le_geometric
  geometric_le_polygon := R.geometric_le_polygon

def subpolygonGateOfRemainingWitnessFields
    (R : W25RemainingWitnessFields C hmin D E) :
    SubpolygonDataField.{u} C where
  Subpolygon := R.Subpolygon
  subpolygonData := R.subpolygonData

def longArcGateOfRemainingWitnessFields
    (R : W25RemainingWitnessFields C hmin D E) :
    LongArcField.{u}
      (angleComparisonGateOfRemainingWitnessFields R)
      (subpolygonGateOfRemainingWitnessFields R) where
  longArc := R.longArc

def triangleRunGateOfRemainingWitnessFields
    (R : W25RemainingWitnessFields C hmin D E) :
    TriangleRunField.{u}
      (angleComparisonGateOfRemainingWitnessFields R)
      (subpolygonGateOfRemainingWitnessFields R) where
  triangleRun := R.triangleRun

/-! ## Reassembly into the W26 component rows and family -/

def componentFieldsOfRemainingWitnessFields
    (R : W25RemainingWitnessFields C hmin D E) :
    RemainingWitnessComponentFields.{u} C hmin D E where
  classificationField := classificationGateOfRemainingWitnessFields R
  angleField := angleComparisonGateOfRemainingWitnessFields R
  subpolygonField := subpolygonGateOfRemainingWitnessFields R
  longArcField := longArcGateOfRemainingWitnessFields R
  triangleRunField := triangleRunGateOfRemainingWitnessFields R

@[simp]
theorem componentFieldsOfRemainingWitnessFields_toRemainingWitnessFields
    (R : W25RemainingWitnessFields C hmin D E) :
    (componentFieldsOfRemainingWitnessFields R).toRemainingWitnessFields = R := by
  cases R
  rfl

def selectedFaceRemainingComponentRowOfSelectedFaceWitnessRow
    (R : W25SelectedFaceWitnessRow C hmin) :
    SelectedFaceRemainingComponentRow.{u} C hmin where
  selectedFace := R.selectedFace
  enclosure := R.enclosure
  remaining := componentFieldsOfRemainingWitnessFields R.remaining

@[simp]
theorem selectedFaceRemainingComponentRow_toSelectedFaceWitnessRow
    (R : W25SelectedFaceWitnessRow C hmin) :
    (selectedFaceRemainingComponentRowOfSelectedFaceWitnessRow R).toSelectedFaceWitnessRow =
      R := by
  cases R with
  | mk selectedFace enclosure remaining =>
      cases remaining
      rfl

def boundaryRemainingComponentFamilyOfSelectedFaceWitnessFamily
    (F : W25SelectedFaceWitnessFamily.{u}) :
    BoundaryRemainingComponentFamily.{u} where
  row := fun C hmin =>
    selectedFaceRemainingComponentRowOfSelectedFaceWitnessRow (F.row C hmin)

theorem boundaryRemainingComponentFamily_nonempty_of_selectedFaceWitnessFamily
    (h : Nonempty W25SelectedFaceWitnessFamily.{u}) :
    Nonempty BoundaryRemainingComponentFamily.{u} := by
  cases h with
  | intro F =>
      exact Nonempty.intro
        (boundaryRemainingComponentFamilyOfSelectedFaceWitnessFamily F)

theorem selectedFaceWitnessFamily_nonempty_of_boundaryRemainingComponentFamily
    (h : Nonempty BoundaryRemainingComponentFamily.{u}) :
    Nonempty W25SelectedFaceWitnessFamily.{u} :=
  BoundaryWitnessRemainingFieldsW26.selectedFaceWitnessFamily_nonempty_of_componentFamily
    h

theorem boundaryRemainingComponentFamily_nonempty_iff_selectedFaceWitnessFamily :
    Nonempty BoundaryRemainingComponentFamily.{u} <->
      Nonempty W25SelectedFaceWitnessFamily.{u} := by
  constructor
  case mp =>
    exact selectedFaceWitnessFamily_nonempty_of_boundaryRemainingComponentFamily
  case mpr =>
    exact boundaryRemainingComponentFamily_nonempty_of_selectedFaceWitnessFamily

end

end BoundaryRemainingComponentsConcreteW27
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW27BoundaryRemainingComponentFamily : Type (u + 1) :=
  Swanepoel.BoundaryRemainingComponentsConcreteW27.BoundaryRemainingComponentFamily.{u}

abbrev SwanepoelW27SelectedFaceWitnessFamily : Type (u + 1) :=
  Swanepoel.BoundaryRemainingComponentsConcreteW27.W25SelectedFaceWitnessFamily.{u}

theorem swanepoelW27_boundaryRemainingComponentFamily_nonempty_iff_selectedFaceWitnessFamily :
    Nonempty SwanepoelW27BoundaryRemainingComponentFamily.{u} <->
      Nonempty SwanepoelW27SelectedFaceWitnessFamily.{u} :=
  Swanepoel.BoundaryRemainingComponentsConcreteW27.boundaryRemainingComponentFamily_nonempty_iff_selectedFaceWitnessFamily

theorem swanepoelW27_boundaryRemainingComponentFamily_nonempty_of_selectedFaceWitnessFamily
    (h : Nonempty SwanepoelW27SelectedFaceWitnessFamily.{u}) :
    Nonempty SwanepoelW27BoundaryRemainingComponentFamily.{u} :=
  Swanepoel.BoundaryRemainingComponentsConcreteW27.boundaryRemainingComponentFamily_nonempty_of_selectedFaceWitnessFamily
    h

end Verified
end ErdosProblems1066
