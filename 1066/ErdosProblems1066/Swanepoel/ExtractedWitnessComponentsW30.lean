import ErdosProblems1066.Swanepoel.ExtractedBoundaryWitnessSourceW29

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W30 extracted witness components

W29 packages the extracted boundary witness as selected outer-face/enclosure
data plus the W26 remaining component fields.  This file keeps the W30 source
surface focused on those remaining fields:

* boundary-walk classification;
* outer-boundary angle comparison;
* subpolygon cycle/count/angle data;
* long-arc data over the resulting planar boundary; and
* the triangle run over the same planar boundary.

No new geometry is assumed here.  The file only names constructors and exact
nonempty/missing-blocker equivalences for the component payloads.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ExtractedWitnessComponentsW30

open BoundaryWitnessRemainingFieldsW26
open ExtractedBoundaryWitnessSourceW29

universe u

noncomputable section

variable {n : Nat}

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  ExtractedBoundaryWitnessSourceW29.SelectedOuterFaceData C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  ExtractedBoundaryWitnessSourceW29.SelectedEnclosureData D

abbrev ExtractedWitnessRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedWitnessRow.{u} C hmin

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedWitnessFamily.{u}

abbrev BoundaryWitnessSourceRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedBoundaryWitnessSourceRow.{u}
    C hmin

abbrev BoundaryWitnessSourceFamily : Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.ExtractedBoundaryWitnessSourceFamily.{u}

abbrev RemainingComponentFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    Type (u + 1) :=
  ExtractedBoundaryWitnessSourceW29.RemainingComponentFields.{u}
    C hmin D E

abbrev BoundaryClassificationComponent
    (C : _root_.UDConfig n)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.BoundaryClassificationField.{u} C D E

abbrev AngleComparisonComponent
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    (classification : BoundaryClassificationComponent.{u} C D E) :
    Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.OuterBoundaryAngleComparisonField.{u}
    classification

abbrev SubpolygonComponent
    (C : _root_.UDConfig n) : Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.SubpolygonDataField.{u} C

abbrev LongArcComponent
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    {classification : BoundaryClassificationComponent.{u} C D E}
    (angle : AngleComparisonComponent.{u} classification)
    (subpolygon : SubpolygonComponent.{u} C) : Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.LongArcField.{u} angle subpolygon

abbrev TriangleRunComponent
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    {classification : BoundaryClassificationComponent.{u} C D E}
    (angle : AngleComparisonComponent.{u} classification)
    (subpolygon : SubpolygonComponent.{u} C) : Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.TriangleRunField.{u} angle subpolygon

/-! ## Fixed selected-face component payload -/

/-- The W30 spelling of the five W26 remaining component gates over a fixed
selected face and enclosure. -/
structure ExtractedRemainingComponentFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    Type (u + 1) where
  classification : BoundaryClassificationComponent.{u} C D E
  angleComparison : AngleComparisonComponent.{u} classification
  subpolygon : SubpolygonComponent.{u} C
  longArc : LongArcComponent.{u} angleComparison subpolygon
  triangleRun : TriangleRunComponent.{u} angleComparison subpolygon

namespace ExtractedRemainingComponentFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}

def toRemainingComponentFields
    (P : ExtractedRemainingComponentFields.{u} C hmin D E) :
    RemainingComponentFields.{u} C hmin D E where
  classificationField := P.classification
  angleField := P.angleComparison
  subpolygonField := P.subpolygon
  longArcField := P.longArc
  triangleRunField := P.triangleRun

def ofRemainingComponentFields
    (P : RemainingComponentFields.{u} C hmin D E) :
    ExtractedRemainingComponentFields.{u} C hmin D E where
  classification := P.classificationField
  angleComparison := P.angleField
  subpolygon := P.subpolygonField
  longArc := P.longArcField
  triangleRun := P.triangleRunField

@[simp]
theorem toRemainingComponentFields_classification
    (P : ExtractedRemainingComponentFields.{u} C hmin D E) :
    P.toRemainingComponentFields.classificationField =
      P.classification :=
  rfl

@[simp]
theorem toRemainingComponentFields_angle
    (P : ExtractedRemainingComponentFields.{u} C hmin D E) :
    P.toRemainingComponentFields.angleField =
      P.angleComparison :=
  rfl

@[simp]
theorem toRemainingComponentFields_subpolygon
    (P : ExtractedRemainingComponentFields.{u} C hmin D E) :
    P.toRemainingComponentFields.subpolygonField =
      P.subpolygon :=
  rfl

@[simp]
theorem toRemainingComponentFields_longArc
    (P : ExtractedRemainingComponentFields.{u} C hmin D E) :
    P.toRemainingComponentFields.longArcField =
      P.longArc :=
  rfl

@[simp]
theorem toRemainingComponentFields_triangleRun
    (P : ExtractedRemainingComponentFields.{u} C hmin D E) :
    P.toRemainingComponentFields.triangleRunField =
      P.triangleRun :=
  rfl

def remainingComponentFieldsEquiv :
    Equiv
      (ExtractedRemainingComponentFields.{u} C hmin D E)
      (RemainingComponentFields.{u} C hmin D E) where
  toFun := toRemainingComponentFields
  invFun := ofRemainingComponentFields
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro P
    cases P
    rfl

theorem nonempty_remainingComponentFields_iff :
    Nonempty (RemainingComponentFields.{u} C hmin D E) <->
      Nonempty (ExtractedRemainingComponentFields.{u} C hmin D E) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (ofRemainingComponentFields P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toRemainingComponentFields

theorem not_remainingComponentFields_iff :
    Not (Nonempty (RemainingComponentFields.{u} C hmin D E)) <->
      Not (Nonempty (ExtractedRemainingComponentFields.{u} C hmin D E)) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (nonempty_remainingComponentFields_iff.2 h)
  case mpr =>
    intro hbad h
    exact hbad (nonempty_remainingComponentFields_iff.1 h)

end ExtractedRemainingComponentFields

/-- The exact dependent payload left after selected face/enclosure data are
fixed.  The long-arc and triangle-run fields are tied to the same angle and
subpolygon components. -/
def ExactRemainingComponentPayload
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceData C) (E : SelectedEnclosureData D) :
    Prop :=
  Exists fun classification : BoundaryClassificationComponent.{u} C D E =>
    Exists fun angle : AngleComparisonComponent.{u} classification =>
      Exists fun subpolygon : SubpolygonComponent.{u} C =>
        Nonempty (LongArcComponent.{u} angle subpolygon) /\
          Nonempty (TriangleRunComponent.{u} angle subpolygon)

def exactPayloadOfComponents
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D}
    (classification : BoundaryClassificationComponent.{u} C D E)
    (angle : AngleComparisonComponent.{u} classification)
    (subpolygon : SubpolygonComponent.{u} C)
    (longArc : LongArcComponent.{u} angle subpolygon)
    (triangleRun : TriangleRunComponent.{u} angle subpolygon) :
    ExactRemainingComponentPayload.{u} C hmin D E :=
  Exists.intro classification
    (Exists.intro angle
      (Exists.intro subpolygon
        (And.intro (Nonempty.intro longArc)
          (Nonempty.intro triangleRun))))

theorem exactPayload_iff_componentFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D} :
    ExactRemainingComponentPayload.{u} C hmin D E <->
      Nonempty (ExtractedRemainingComponentFields.{u} C hmin D E) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro classification h1 =>
        cases h1 with
        | intro angle h2 =>
            cases h2 with
            | intro subpolygon h3 =>
                cases h3 with
                | intro hLong hTriangle =>
                    cases hLong with
                    | intro longArc =>
                        cases hTriangle with
                        | intro triangleRun =>
                            exact
                              Nonempty.intro
                                { classification := classification
                                  angleComparison := angle
                                  subpolygon := subpolygon
                                  longArc := longArc
                                  triangleRun := triangleRun }
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          exactPayloadOfComponents
            P.classification P.angleComparison P.subpolygon
            P.longArc P.triangleRun

theorem nonempty_remainingComponentFields_iff_exactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D} :
    Nonempty (RemainingComponentFields.{u} C hmin D E) <->
      ExactRemainingComponentPayload.{u} C hmin D E :=
  (ExtractedRemainingComponentFields.nonempty_remainingComponentFields_iff
    (C := C) (hmin := hmin) (D := D) (E := E)).trans
    exactPayload_iff_componentFields.symm

theorem not_remainingComponentFields_iff_not_exactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {D : SelectedOuterFaceData C} {E : SelectedEnclosureData D} :
    Not (Nonempty (RemainingComponentFields.{u} C hmin D E)) <->
      Not (ExactRemainingComponentPayload.{u} C hmin D E) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (nonempty_remainingComponentFields_iff_exactPayload.2 h)
  case mpr =>
    intro hbad h
    exact hbad (nonempty_remainingComponentFields_iff_exactPayload.1 h)

/-! ## Row-level extracted witness components -/

structure ExtractedWitnessComponentRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) where
  selectedFace : SelectedOuterFaceData C
  enclosure : SelectedEnclosureData selectedFace
  components :
    ExtractedRemainingComponentFields.{u} C hmin selectedFace enclosure

namespace ExtractedWitnessComponentRow

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def remainingComponentFields
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    RemainingComponentFields.{u} C hmin P.selectedFace P.enclosure :=
  P.components.toRemainingComponentFields

def toBoundaryWitnessSourceRow
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    BoundaryWitnessSourceRow.{u} C hmin where
  outerBoundary :=
    ExtractedBoundaryWitnessSourceW29.coreSourceOfSelectedFaceAndEnclosure
      P.selectedFace P.enclosure
  selectedFace := P.selectedFace
  enclosure := P.enclosure
  outerBoundary_core := rfl
  remaining := P.remainingComponentFields

def toExtractedWitness
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    ExtractedWitnessRow.{u} C hmin :=
  P.toBoundaryWitnessSourceRow.toExtractedWitness

def ofBoundaryWitnessSourceRow
    (P : BoundaryWitnessSourceRow.{u} C hmin) :
    ExtractedWitnessComponentRow.{u} C hmin where
  selectedFace := P.selectedFace
  enclosure := P.enclosure
  components :=
    ExtractedRemainingComponentFields.ofRemainingComponentFields
      P.remaining

def ofExtractedWitness
    (P : ExtractedWitnessRow.{u} C hmin) :
    ExtractedWitnessComponentRow.{u} C hmin :=
  ofBoundaryWitnessSourceRow
    (ExtractedBoundaryWitnessSourceRow.ofExtractedWitness P)

@[simp]
theorem toBoundaryWitnessSourceRow_selectedFace
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toBoundaryWitnessSourceRow.selectedFace = P.selectedFace :=
  rfl

@[simp]
theorem toBoundaryWitnessSourceRow_enclosure
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toBoundaryWitnessSourceRow.enclosure = P.enclosure :=
  rfl

@[simp]
theorem toBoundaryWitnessSourceRow_remaining
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toBoundaryWitnessSourceRow.remaining =
      P.remainingComponentFields :=
  rfl

@[simp]
theorem toExtractedWitness_classification
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toExtractedWitness.classification =
      P.components.classification.classification :=
  rfl

@[simp]
theorem toExtractedWitness_geometricAngleSum
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toExtractedWitness.geometricAngleSum =
      P.components.angleComparison.geometricAngleSum :=
  rfl

@[simp]
theorem toExtractedWitness_Subpolygon
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toExtractedWitness.Subpolygon =
      P.components.subpolygon.Subpolygon :=
  rfl

@[simp]
theorem toExtractedWitness_longArc
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toExtractedWitness.longArc =
      P.components.longArc.longArc :=
  rfl

@[simp]
theorem toExtractedWitness_triangleRun
    (P : ExtractedWitnessComponentRow.{u} C hmin) :
    P.toExtractedWitness.triangleRun =
      P.components.triangleRun.triangleRun :=
  rfl

theorem nonempty_sourceRow_iff_componentRow :
    Nonempty (BoundaryWitnessSourceRow.{u} C hmin) <->
      Nonempty (ExtractedWitnessComponentRow.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (ofBoundaryWitnessSourceRow P)
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toBoundaryWitnessSourceRow

theorem nonempty_extractedWitness_iff_componentRow :
    Nonempty (ExtractedWitnessRow.{u} C hmin) <->
      Nonempty (ExtractedWitnessComponentRow.{u} C hmin) :=
  (ExtractedBoundaryWitnessSourceRow.nonempty_extractedWitness_iff_sourceRow
    (C := C) (hmin := hmin)).trans
    nonempty_sourceRow_iff_componentRow

end ExtractedWitnessComponentRow

/-- Row-level exact component payload: selected face, enclosure, then the five
dependent remaining components over that fixed topology. -/
def ExactExtractedWitnessComponentPayload
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Prop :=
  Exists fun D : SelectedOuterFaceData C =>
    Exists fun E : SelectedEnclosureData D =>
      ExactRemainingComponentPayload.{u} C hmin D E

theorem exactExtractedWitnessPayload_iff_componentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    ExactExtractedWitnessComponentPayload.{u} C hmin <->
      Nonempty (ExtractedWitnessComponentRow.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D hD =>
        cases hD with
        | intro E hPayload =>
            have hComponents :
                Nonempty
                  (ExtractedRemainingComponentFields.{u} C hmin D E) :=
              (exactPayload_iff_componentFields
                (C := C) (hmin := hmin) (D := D) (E := E)).1
                hPayload
            cases hComponents with
            | intro components =>
                exact
                  Nonempty.intro
                    { selectedFace := D
                      enclosure := E
                      components := components }
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.selectedFace
            (Exists.intro P.enclosure
              ((exactPayload_iff_componentFields
                (C := C) (hmin := hmin)
                (D := P.selectedFace) (E := P.enclosure)).2
                (Nonempty.intro P.components)))

theorem nonempty_extractedWitness_iff_exactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty (ExtractedWitnessRow.{u} C hmin) <->
      ExactExtractedWitnessComponentPayload.{u} C hmin :=
  (ExtractedWitnessComponentRow.nonempty_extractedWitness_iff_componentRow
    (C := C) (hmin := hmin)).trans
    exactExtractedWitnessPayload_iff_componentRow.symm

theorem not_extractedWitness_iff_not_exactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Not (Nonempty (ExtractedWitnessRow.{u} C hmin)) <->
      Not (ExactExtractedWitnessComponentPayload.{u} C hmin) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (nonempty_extractedWitness_iff_exactPayload.2 h)
  case mpr =>
    intro hbad h
    exact hbad (nonempty_extractedWitness_iff_exactPayload.1 h)

/-! ## Family-level extracted witness components -/

structure ExtractedWitnessComponentFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ExtractedWitnessComponentRow.{u} C hmin

namespace ExtractedWitnessComponentFamily

def toBoundaryWitnessSourceFamily
    (F : ExtractedWitnessComponentFamily.{u}) :
    BoundaryWitnessSourceFamily.{u} where
  row := fun C hmin =>
    (F.row C hmin).toBoundaryWitnessSourceRow

def toExtractedWitnessFamily
    (F : ExtractedWitnessComponentFamily.{u}) :
    ExtractedWitnessFamily.{u} :=
  F.toBoundaryWitnessSourceFamily.toExtractedWitnessFamily

def ofBoundaryWitnessSourceFamily
    (F : BoundaryWitnessSourceFamily.{u}) :
    ExtractedWitnessComponentFamily.{u} where
  row := fun C hmin =>
    ExtractedWitnessComponentRow.ofBoundaryWitnessSourceRow
      (F.row C hmin)

def ofExtractedWitnessFamily
    (F : ExtractedWitnessFamily.{u}) :
    ExtractedWitnessComponentFamily.{u} :=
  ofBoundaryWitnessSourceFamily
    (ExtractedBoundaryWitnessSourceFamily.ofExtractedWitnessFamily F)

theorem nonempty_boundaryWitnessSourceFamily
    (F : ExtractedWitnessComponentFamily.{u}) :
    Nonempty BoundaryWitnessSourceFamily.{u} :=
  Nonempty.intro F.toBoundaryWitnessSourceFamily

theorem nonempty_extractedWitnessFamily
    (F : ExtractedWitnessComponentFamily.{u}) :
    Nonempty ExtractedWitnessFamily.{u} :=
  Nonempty.intro F.toExtractedWitnessFamily

end ExtractedWitnessComponentFamily

theorem sourceFamily_nonempty_iff_componentFamily :
    Nonempty BoundaryWitnessSourceFamily.{u} <->
      Nonempty ExtractedWitnessComponentFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F =>
        exact
          Nonempty.intro
            (ExtractedWitnessComponentFamily.ofBoundaryWitnessSourceFamily F)
  case mpr =>
    intro h
    cases h with
    | intro F =>
        exact F.nonempty_boundaryWitnessSourceFamily

theorem extractedWitnessFamily_nonempty_iff_componentFamily :
    Nonempty ExtractedWitnessFamily.{u} <->
      Nonempty ExtractedWitnessComponentFamily.{u} :=
  ExtractedBoundaryWitnessSourceW29.extractedWitnessFamily_nonempty_iff_sourceFamily.trans
    sourceFamily_nonempty_iff_componentFamily

theorem not_sourceFamily_iff_not_componentFamily :
    Not (Nonempty BoundaryWitnessSourceFamily.{u}) <->
      Not (Nonempty ExtractedWitnessComponentFamily.{u}) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (sourceFamily_nonempty_iff_componentFamily.2 h)
  case mpr =>
    intro hbad h
    exact hbad (sourceFamily_nonempty_iff_componentFamily.1 h)

theorem not_extractedWitnessFamily_iff_not_componentFamily :
    Not (Nonempty ExtractedWitnessFamily.{u}) <->
      Not (Nonempty ExtractedWitnessComponentFamily.{u}) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (extractedWitnessFamily_nonempty_iff_componentFamily.2 h)
  case mpr =>
    intro hbad h
    exact hbad (extractedWitnessFamily_nonempty_iff_componentFamily.1 h)

end

end ExtractedWitnessComponentsW30
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW30ExtractedWitnessComponentFamily : Type (u + 1) :=
  Swanepoel.ExtractedWitnessComponentsW30.ExtractedWitnessComponentFamily.{u}

abbrev SwanepoelW30ExtractedWitnessFamily : Type (u + 1) :=
  Swanepoel.ExtractedWitnessComponentsW30.ExtractedWitnessFamily.{u}

abbrev SwanepoelW30BoundaryWitnessSourceFamily : Type (u + 1) :=
  Swanepoel.ExtractedWitnessComponentsW30.BoundaryWitnessSourceFamily.{u}

theorem swanepoelW30_extractedWitnessFamily_exactly_componentFamily :
    Nonempty SwanepoelW30ExtractedWitnessFamily.{u} <->
      Nonempty SwanepoelW30ExtractedWitnessComponentFamily.{u} :=
  Swanepoel.ExtractedWitnessComponentsW30.extractedWitnessFamily_nonempty_iff_componentFamily

theorem swanepoelW30_sourceFamily_exactly_componentFamily :
    Nonempty SwanepoelW30BoundaryWitnessSourceFamily.{u} <->
      Nonempty SwanepoelW30ExtractedWitnessComponentFamily.{u} :=
  Swanepoel.ExtractedWitnessComponentsW30.sourceFamily_nonempty_iff_componentFamily

theorem swanepoelW30_missing_extractedWitnessFamily_exactly_missing_componentFamily :
    Not (Nonempty SwanepoelW30ExtractedWitnessFamily.{u}) <->
      Not (Nonempty SwanepoelW30ExtractedWitnessComponentFamily.{u}) :=
  Swanepoel.ExtractedWitnessComponentsW30.not_extractedWitnessFamily_iff_not_componentFamily

end Verified
end ErdosProblems1066
