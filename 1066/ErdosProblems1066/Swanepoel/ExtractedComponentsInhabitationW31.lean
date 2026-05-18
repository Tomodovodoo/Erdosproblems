import ErdosProblems1066.Swanepoel.ExtractedWitnessComponentsW30
import ErdosProblems1066.Swanepoel.BoundaryRemainingComponentsConcreteW27
import ErdosProblems1066.Swanepoel.ConcreteW23ComponentsInhabitationW26

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W31 extracted component inhabitation

W30 isolates the extracted remaining boundary components.  W27 already has the
same component data over the concrete selected-face row.  This file gives the
direct constructors between those two surfaces and records the exact remaining
blockers: an extracted component family is present exactly when the concrete
selected-face remaining component family is present; the older W23 concrete
package is still blocked exactly by the no-cut/tail data exposed in W25/W26.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ExtractedComponentsInhabitationW31

universe u

noncomputable section

variable {n : Nat}

abbrev ExtractedWitnessComponentFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedWitnessComponentFamily.{u}

abbrev ExtractedWitnessFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedWitnessFamily.{u}

abbrev BoundaryWitnessSourceFamily : Type (u + 1) :=
  ExtractedWitnessComponentsW30.BoundaryWitnessSourceFamily.{u}

abbrev BoundaryRemainingComponentFamily : Type (u + 1) :=
  BoundaryRemainingComponentsConcreteW27.BoundaryRemainingComponentFamily.{u}

abbrev SelectedFaceWitnessFamily : Type (u + 1) :=
  BoundaryRemainingComponentsConcreteW27.W25SelectedFaceWitnessFamily.{u}

abbrev ConcreteW23Components : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteW23Components

abbrev ConcreteNoCutTheorem : Prop :=
  ConcreteW23ComponentsInhabitationW26.ConcreteNoCutTheorem

abbrev ConcreteW23ComponentsExceptNoCut
    (noCut : ConcreteNoCutTheorem) : Type 1 :=
  ConcreteW23ComponentsInhabitationW26.ConcreteW23ComponentsExceptNoCut
    noCut

abbrev MinimalCutVertexBlockerExists : Prop :=
  ConcreteW23ComponentsInhabitationW26.MinimalCutVertexBlockerExists

abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  ConcreteW23ComponentsInhabitationW26.MinimalFailureCutVertexContradictionFamily

/-! ## Fixed-row constructors -/

def extractedRemainingComponentFieldsOfConcrete
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {D : ExtractedWitnessComponentsW30.SelectedOuterFaceData C}
    {E : ExtractedWitnessComponentsW30.SelectedEnclosureData D}
    (P :
      BoundaryWitnessRemainingFieldsW26.RemainingWitnessComponentFields.{u}
        C hmin D E) :
    ExtractedWitnessComponentsW30.ExtractedRemainingComponentFields.{u}
      C hmin D E :=
  ExtractedWitnessComponentsW30.ExtractedRemainingComponentFields.ofRemainingComponentFields
    P

def concreteRemainingComponentFieldsOfExtracted
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {D : ExtractedWitnessComponentsW30.SelectedOuterFaceData C}
    {E : ExtractedWitnessComponentsW30.SelectedEnclosureData D}
    (P :
      ExtractedWitnessComponentsW30.ExtractedRemainingComponentFields.{u}
        C hmin D E) :
    BoundaryWitnessRemainingFieldsW26.RemainingWitnessComponentFields.{u}
      C hmin D E :=
  P.toRemainingComponentFields

def extractedWitnessComponentRowOfConcrete
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
      C hmin) :
    ExtractedWitnessComponentsW30.ExtractedWitnessComponentRow.{u} C hmin where
  selectedFace := R.selectedFace
  enclosure := R.enclosure
  components := extractedRemainingComponentFieldsOfConcrete R.remaining

def concreteComponentRowOfExtractedWitnessComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : ExtractedWitnessComponentsW30.ExtractedWitnessComponentRow.{u}
      C hmin) :
    BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
      C hmin where
  selectedFace := R.selectedFace
  enclosure := R.enclosure
  remaining := concreteRemainingComponentFieldsOfExtracted R.components

@[simp]
theorem extractedWitnessComponentRowOfConcrete_selectedFace
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
      C hmin) :
    (extractedWitnessComponentRowOfConcrete R).selectedFace =
      R.selectedFace :=
  rfl

@[simp]
theorem extractedWitnessComponentRowOfConcrete_enclosure
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
      C hmin) :
    (extractedWitnessComponentRowOfConcrete R).enclosure =
      R.enclosure :=
  rfl

@[simp]
theorem concreteComponentRowOfExtracted_selectedFace
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : ExtractedWitnessComponentsW30.ExtractedWitnessComponentRow.{u}
      C hmin) :
    (concreteComponentRowOfExtractedWitnessComponentRow R).selectedFace =
      R.selectedFace :=
  rfl

@[simp]
theorem concreteComponentRowOfExtracted_enclosure
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : ExtractedWitnessComponentsW30.ExtractedWitnessComponentRow.{u}
      C hmin) :
    (concreteComponentRowOfExtractedWitnessComponentRow R).enclosure =
      R.enclosure :=
  rfl

theorem nonempty_concreteComponentRow_iff_extractedComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
          C hmin) <->
      Nonempty
        (ExtractedWitnessComponentsW30.ExtractedWitnessComponentRow.{u}
          C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro (extractedWitnessComponentRowOfConcrete R)
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact Nonempty.intro
          (concreteComponentRowOfExtractedWitnessComponentRow R)

/-! ## Family constructors -/

def extractedWitnessComponentFamilyOfBoundaryRemainingComponentFamily
    (F : BoundaryRemainingComponentFamily.{u}) :
    ExtractedWitnessComponentFamily.{u} where
  row := fun C hmin =>
    extractedWitnessComponentRowOfConcrete (F.row C hmin)

def boundaryRemainingComponentFamilyOfExtractedWitnessComponentFamily
    (F : ExtractedWitnessComponentFamily.{u}) :
    BoundaryRemainingComponentFamily.{u} where
  row := fun C hmin =>
    concreteComponentRowOfExtractedWitnessComponentRow (F.row C hmin)

def extractedWitnessComponentFamilyOfSelectedFaceWitnessFamily
    (F : SelectedFaceWitnessFamily.{u}) :
    ExtractedWitnessComponentFamily.{u} :=
  extractedWitnessComponentFamilyOfBoundaryRemainingComponentFamily
    (BoundaryRemainingComponentsConcreteW27.boundaryRemainingComponentFamilyOfSelectedFaceWitnessFamily
      F)

theorem extractedWitnessComponentFamily_nonempty_of_boundaryRemainingComponentFamily
    (h : Nonempty BoundaryRemainingComponentFamily.{u}) :
    Nonempty ExtractedWitnessComponentFamily.{u} := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (extractedWitnessComponentFamilyOfBoundaryRemainingComponentFamily F)

theorem boundaryRemainingComponentFamily_nonempty_of_extractedWitnessComponentFamily
    (h : Nonempty ExtractedWitnessComponentFamily.{u}) :
    Nonempty BoundaryRemainingComponentFamily.{u} := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (boundaryRemainingComponentFamilyOfExtractedWitnessComponentFamily F)

theorem extractedWitnessComponentFamily_nonempty_iff_boundaryRemainingComponentFamily :
    Nonempty ExtractedWitnessComponentFamily.{u} <->
      Nonempty BoundaryRemainingComponentFamily.{u} := by
  constructor
  case mp =>
    exact boundaryRemainingComponentFamily_nonempty_of_extractedWitnessComponentFamily
  case mpr =>
    exact extractedWitnessComponentFamily_nonempty_of_boundaryRemainingComponentFamily

theorem extractedWitnessComponentFamily_nonempty_of_selectedFaceWitnessFamily
    (h : Nonempty SelectedFaceWitnessFamily.{u}) :
    Nonempty ExtractedWitnessComponentFamily.{u} := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (extractedWitnessComponentFamilyOfSelectedFaceWitnessFamily F)

theorem selectedFaceWitnessFamily_nonempty_of_extractedWitnessComponentFamily
    (h : Nonempty ExtractedWitnessComponentFamily.{u}) :
    Nonempty SelectedFaceWitnessFamily.{u} :=
  BoundaryRemainingComponentsConcreteW27.selectedFaceWitnessFamily_nonempty_of_boundaryRemainingComponentFamily
    (boundaryRemainingComponentFamily_nonempty_of_extractedWitnessComponentFamily h)

theorem extractedWitnessComponentFamily_nonempty_iff_selectedFaceWitnessFamily :
    Nonempty ExtractedWitnessComponentFamily.{u} <->
      Nonempty SelectedFaceWitnessFamily.{u} := by
  constructor
  case mp =>
    exact selectedFaceWitnessFamily_nonempty_of_extractedWitnessComponentFamily
  case mpr =>
    exact extractedWitnessComponentFamily_nonempty_of_selectedFaceWitnessFamily

theorem extractedWitnessFamily_nonempty_iff_boundaryRemainingComponentFamily :
    Nonempty ExtractedWitnessFamily.{u} <->
      Nonempty BoundaryRemainingComponentFamily.{u} :=
  ExtractedWitnessComponentsW30.extractedWitnessFamily_nonempty_iff_componentFamily.trans
    extractedWitnessComponentFamily_nonempty_iff_boundaryRemainingComponentFamily

theorem boundaryWitnessSourceFamily_nonempty_iff_boundaryRemainingComponentFamily :
    Nonempty BoundaryWitnessSourceFamily.{u} <->
      Nonempty BoundaryRemainingComponentFamily.{u} :=
  ExtractedWitnessComponentsW30.sourceFamily_nonempty_iff_componentFamily.trans
    extractedWitnessComponentFamily_nonempty_iff_boundaryRemainingComponentFamily

/-! ## Exact blockers retained -/

theorem not_extractedWitnessComponentFamily_iff_not_boundaryRemainingComponentFamily :
    Not (Nonempty ExtractedWitnessComponentFamily.{u}) <->
      Not (Nonempty BoundaryRemainingComponentFamily.{u}) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad
      (extractedWitnessComponentFamily_nonempty_iff_boundaryRemainingComponentFamily.2
        h)
  case mpr =>
    intro hbad h
    exact hbad
      (extractedWitnessComponentFamily_nonempty_iff_boundaryRemainingComponentFamily.1
        h)

theorem not_extractedWitnessComponentFamily_iff_not_selectedFaceWitnessFamily :
    Not (Nonempty ExtractedWitnessComponentFamily.{u}) <->
      Not (Nonempty SelectedFaceWitnessFamily.{u}) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad
      (extractedWitnessComponentFamily_nonempty_iff_selectedFaceWitnessFamily.2
        h)
  case mpr =>
    intro hbad h
    exact hbad
      (extractedWitnessComponentFamily_nonempty_iff_selectedFaceWitnessFamily.1
        h)

theorem not_extractedWitnessFamily_iff_not_boundaryRemainingComponentFamily :
    Not (Nonempty ExtractedWitnessFamily.{u}) <->
      Not (Nonempty BoundaryRemainingComponentFamily.{u}) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad
      (extractedWitnessFamily_nonempty_iff_boundaryRemainingComponentFamily.2
        h)
  case mpr =>
    intro hbad h
    exact hbad
      (extractedWitnessFamily_nonempty_iff_boundaryRemainingComponentFamily.1
        h)

theorem concreteW23Components_nonempty_iff_noCut_tail :
    Nonempty ConcreteW23Components <->
      exists noCut : ConcreteNoCutTheorem,
        Nonempty (ConcreteW23ComponentsExceptNoCut noCut) :=
  ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_noCut_tail

theorem concreteW23Components_nonempty_iff_notBlocker_tail :
    Nonempty ConcreteW23Components <->
      exists h : Not MinimalCutVertexBlockerExists,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
              h)) :=
  ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_notBlocker_tail

theorem concreteW23Components_nonempty_iff_cutVertexContradiction_tail :
    Nonempty ConcreteW23Components <->
      exists H : MinimalFailureCutVertexContradictionFamily,
        Nonempty
          (ConcreteW23ComponentsExceptNoCut
            (ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
              H)) :=
  ConcreteW23ComponentsInhabitationW26.concreteW23Components_nonempty_iff_cutVertexContradiction_tail

theorem not_concreteW23Components_iff_not_noCut_tail :
    Not (Nonempty ConcreteW23Components) <->
      Not
        (exists noCut : ConcreteNoCutTheorem,
          Nonempty (ConcreteW23ComponentsExceptNoCut noCut)) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (concreteW23Components_nonempty_iff_noCut_tail.2 h)
  case mpr =>
    intro hbad h
    exact hbad (concreteW23Components_nonempty_iff_noCut_tail.1 h)

theorem not_concreteW23Components_iff_not_notBlocker_tail :
    Not (Nonempty ConcreteW23Components) <->
      Not
        (exists h : Not MinimalCutVertexBlockerExists,
          Nonempty
            (ConcreteW23ComponentsExceptNoCut
              (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
                h))) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad (concreteW23Components_nonempty_iff_notBlocker_tail.2 h)
  case mpr =>
    intro hbad h
    exact hbad (concreteW23Components_nonempty_iff_notBlocker_tail.1 h)

theorem not_concreteW23Components_iff_not_cutVertexContradiction_tail :
    Not (Nonempty ConcreteW23Components) <->
      Not
        (exists H : MinimalFailureCutVertexContradictionFamily,
          Nonempty
            (ConcreteW23ComponentsExceptNoCut
              (ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
                H))) := by
  constructor
  case mp =>
    intro hbad h
    exact hbad
      (concreteW23Components_nonempty_iff_cutVertexContradiction_tail.2 h)
  case mpr =>
    intro hbad h
    exact hbad
      (concreteW23Components_nonempty_iff_cutVertexContradiction_tail.1 h)

end

end ExtractedComponentsInhabitationW31
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW31ExtractedWitnessComponentFamily : Type (u + 1) :=
  Swanepoel.ExtractedComponentsInhabitationW31.ExtractedWitnessComponentFamily.{u}

abbrev SwanepoelW31BoundaryRemainingComponentFamily : Type (u + 1) :=
  Swanepoel.ExtractedComponentsInhabitationW31.BoundaryRemainingComponentFamily.{u}

abbrev SwanepoelW31SelectedFaceWitnessFamily : Type (u + 1) :=
  Swanepoel.ExtractedComponentsInhabitationW31.SelectedFaceWitnessFamily.{u}

abbrev SwanepoelW31ConcreteW23Components : Type 1 :=
  Swanepoel.ExtractedComponentsInhabitationW31.ConcreteW23Components

theorem swanepoelW31_extractedComponentFamily_exactly_boundaryRemainingComponentFamily :
    Nonempty SwanepoelW31ExtractedWitnessComponentFamily.{u} <->
      Nonempty SwanepoelW31BoundaryRemainingComponentFamily.{u} :=
  Swanepoel.ExtractedComponentsInhabitationW31.extractedWitnessComponentFamily_nonempty_iff_boundaryRemainingComponentFamily

theorem swanepoelW31_extractedComponentFamily_exactly_selectedFaceWitnessFamily :
    Nonempty SwanepoelW31ExtractedWitnessComponentFamily.{u} <->
      Nonempty SwanepoelW31SelectedFaceWitnessFamily.{u} :=
  Swanepoel.ExtractedComponentsInhabitationW31.extractedWitnessComponentFamily_nonempty_iff_selectedFaceWitnessFamily

theorem swanepoelW31_missing_extractedComponentFamily_exactly_missing_boundaryRemainingComponentFamily :
    Not (Nonempty SwanepoelW31ExtractedWitnessComponentFamily.{u}) <->
      Not (Nonempty SwanepoelW31BoundaryRemainingComponentFamily.{u}) :=
  Swanepoel.ExtractedComponentsInhabitationW31.not_extractedWitnessComponentFamily_iff_not_boundaryRemainingComponentFamily

theorem swanepoelW31_concreteW23Components_exactly_noCut_tail :
    Nonempty SwanepoelW31ConcreteW23Components <->
      exists noCut :
        Swanepoel.ExtractedComponentsInhabitationW31.ConcreteNoCutTheorem,
        Nonempty
          (Swanepoel.ExtractedComponentsInhabitationW31.ConcreteW23ComponentsExceptNoCut
            noCut) :=
  Swanepoel.ExtractedComponentsInhabitationW31.concreteW23Components_nonempty_iff_noCut_tail

end Verified
end ErdosProblems1066
