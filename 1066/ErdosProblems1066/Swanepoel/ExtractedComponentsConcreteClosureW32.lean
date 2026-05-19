import ErdosProblems1066.Swanepoel.ExtractedComponentsInhabitationW31
import ErdosProblems1066.Swanepoel.EnclosureAndFaceBoundaryW31
import ErdosProblems1066.Swanepoel.ActualSelectedTopologyDataW27
import ErdosProblems1066.Swanepoel.MinimalFailureSelectedTopologySourceW32
import ErdosProblems1066.Swanepoel.MinimalConnectednessClosure
import ErdosProblems1066.Swanepoel.MinimalFailureDegreeRange

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# W32 concrete extracted-component closure

W31 identified the extracted-component family with the selected-face remaining
component blocker.  This file refines that surface into concrete closure
packages: for each minimal cleared failure, the data are an actual
face-boundary/enclosure source plus the five extracted component gates over
that selected face.

The W23 no-cut/tail boundary is kept as a separate package.  It is not used to
manufacture extracted components; it records the exact W31 blocker for the
older concrete W23 component surface.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ExtractedComponentsConcreteClosureW32

universe u

noncomputable section

variable {n : Nat}

abbrev W31ExtractedWitnessComponentFamily : Type (u + 1) :=
  ExtractedComponentsInhabitationW31.ExtractedWitnessComponentFamily.{u}

abbrev W31ExtractedWitnessFamily : Type (u + 1) :=
  ExtractedComponentsInhabitationW31.ExtractedWitnessFamily.{u}

abbrev W31BoundaryWitnessSourceFamily : Type (u + 1) :=
  ExtractedComponentsInhabitationW31.BoundaryWitnessSourceFamily.{u}

abbrev W31BoundaryRemainingComponentFamily : Type (u + 1) :=
  ExtractedComponentsInhabitationW31.BoundaryRemainingComponentFamily.{u}

abbrev W31SelectedFaceWitnessFamily : Type (u + 1) :=
  ExtractedComponentsInhabitationW31.SelectedFaceWitnessFamily.{u}

abbrev W31ConcreteW23Components : Type 1 :=
  ExtractedComponentsInhabitationW31.ConcreteW23Components

abbrev W31ConcreteNoCutTheorem : Prop :=
  ExtractedComponentsInhabitationW31.ConcreteNoCutTheorem

abbrev W31ConcreteW23ComponentsExceptNoCut
    (noCut : W31ConcreteNoCutTheorem) : Type 1 :=
  ExtractedComponentsInhabitationW31.ConcreteW23ComponentsExceptNoCut
    noCut

abbrev W31MinimalCutVertexBlockerExists : Prop :=
  ExtractedComponentsInhabitationW31.MinimalCutVertexBlockerExists

abbrev W31MinimalFailureCutVertexContradictionFamily : Prop :=
  ExtractedComponentsInhabitationW31.MinimalFailureCutVertexContradictionFamily

abbrev FaceBoundaryEnclosureSource (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.FaceBoundaryEnclosureSource C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  JordanTopologyFactsConcrete.TopologyFacts.{0} C

abbrev MissingTopologyFacts (C : _root_.UDConfig n) :=
  JordanBoundaryConcrete.MissingTopologyFacts.{0} C

abbrev TopologyBoundary (C : _root_.UDConfig n) :=
  OuterBoundaryCore.{0} (ActualSelectedTopologyDataW27.CanonicalGraph C)

abbrev ExtractedWitnessComponentRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedWitnessComponentRow.{u} C hmin

abbrev BoundaryRemainingComponentRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  BoundaryWitnessRemainingFieldsW26.SelectedFaceRemainingComponentRow.{u}
    C hmin

abbrev ExtractedRemainingComponentFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : ExtractedWitnessComponentsW30.SelectedOuterFaceData C)
    (E : ExtractedWitnessComponentsW30.SelectedEnclosureData D) :
    Type (u + 1) :=
  ExtractedWitnessComponentsW30.ExtractedRemainingComponentFields.{u}
    C hmin D E

abbrev ExactExtractedWitnessComponentPayload
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  ExtractedWitnessComponentsW30.ExactExtractedWitnessComponentPayload.{u}
    C hmin

def faceBoundaryEnclosureSourceOfActualSelectedTopologyData
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    FaceBoundaryEnclosureSource C :=
  EnclosureAndFaceBoundaryW31.ofSelectedOuterFaceAndEnclosure
    A.selectedOuterFace A.enclosure

def actualSelectedTopologyDataOfFaceBoundaryEnclosureSource
    {C : _root_.UDConfig n}
    (S : FaceBoundaryEnclosureSource C) :
    ActualSelectedTopologyData C where
  selectedOuterFace := S.selectedOuterFaceData
  enclosure := S.selectedEnclosureData

@[simp]
theorem faceBoundaryEnclosureSourceOfActualSelectedTopologyData_selectedOuterFaceData
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    (faceBoundaryEnclosureSourceOfActualSelectedTopologyData A).selectedOuterFaceData =
      A.selectedOuterFace := by
  cases A with
  | mk selectedOuterFace enclosure =>
      cases selectedOuterFace
      cases enclosure
      rfl

@[simp]
theorem faceBoundaryEnclosureSourceOfActualSelectedTopologyData_selectedEnclosureData
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    (faceBoundaryEnclosureSourceOfActualSelectedTopologyData A).selectedEnclosureData =
      A.enclosure := by
  cases A with
  | mk selectedOuterFace enclosure =>
      cases selectedOuterFace
      cases enclosure
      rfl

@[simp]
theorem actualSelectedTopologyDataOfFaceBoundaryEnclosureSource_selectedOuterFace
    {C : _root_.UDConfig n}
    (S : FaceBoundaryEnclosureSource C) :
    (actualSelectedTopologyDataOfFaceBoundaryEnclosureSource S).selectedOuterFace =
      S.selectedOuterFaceData :=
  rfl

@[simp]
theorem actualSelectedTopologyDataOfFaceBoundaryEnclosureSource_enclosure
    {C : _root_.UDConfig n}
    (S : FaceBoundaryEnclosureSource C) :
    (actualSelectedTopologyDataOfFaceBoundaryEnclosureSource S).enclosure =
      S.selectedEnclosureData :=
  rfl

@[simp]
theorem faceBoundaryEnclosureSourceOfActualSelectedTopologyData_of_source
    {C : _root_.UDConfig n}
    (S : FaceBoundaryEnclosureSource C) :
    faceBoundaryEnclosureSourceOfActualSelectedTopologyData
      (actualSelectedTopologyDataOfFaceBoundaryEnclosureSource S) = S := by
  cases S
  rfl

@[simp]
theorem actualSelectedTopologyDataOfFaceBoundaryEnclosureSource_of_actual
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    actualSelectedTopologyDataOfFaceBoundaryEnclosureSource
      (faceBoundaryEnclosureSourceOfActualSelectedTopologyData A) = A := by
  cases A with
  | mk selectedOuterFace enclosure =>
      cases selectedOuterFace
      cases enclosure
      rfl

def actualSelectedTopologyDataEquivFaceBoundaryEnclosureSource
    (C : _root_.UDConfig n) :
    ActualSelectedTopologyData C ≃ FaceBoundaryEnclosureSource C where
  toFun := faceBoundaryEnclosureSourceOfActualSelectedTopologyData
  invFun := actualSelectedTopologyDataOfFaceBoundaryEnclosureSource
  left_inv := fun A =>
    actualSelectedTopologyDataOfFaceBoundaryEnclosureSource_of_actual A
  right_inv := fun S =>
    faceBoundaryEnclosureSourceOfActualSelectedTopologyData_of_source S

/-! ## Fixed minimal-failure package -/

/-- Concrete extracted-component closure data for one fixed minimal cleared
failure.  The selected face and enclosure are carried by an actual
face-boundary source; the remaining fields are the five W30 component gates
over that same face. -/
structure FixedFaceBoundaryExtractedComponentPackage
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) where
  source : FaceBoundaryEnclosureSource C
  components :
    ExtractedRemainingComponentFields.{u} C hmin
      source.selectedOuterFaceData source.selectedEnclosureData

namespace FixedFaceBoundaryExtractedComponentPackage

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def toExtractedWitnessComponentRow
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    ExtractedWitnessComponentRow.{u} C hmin where
  selectedFace := P.source.selectedOuterFaceData
  enclosure := P.source.selectedEnclosureData
  components := P.components

def toBoundaryRemainingComponentRow
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    BoundaryRemainingComponentRow.{u} C hmin :=
  ExtractedComponentsInhabitationW31.concreteComponentRowOfExtractedWitnessComponentRow
    P.toExtractedWitnessComponentRow

def toExactExtractedWitnessComponentPayload
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    ExactExtractedWitnessComponentPayload.{u} C hmin :=
  Exists.intro P.source.selectedOuterFaceData
    (Exists.intro P.source.selectedEnclosureData
      ((ExtractedWitnessComponentsW30.exactPayload_iff_componentFields
        (C := C) (hmin := hmin)
        (D := P.source.selectedOuterFaceData)
        (E := P.source.selectedEnclosureData)).2
        (Nonempty.intro P.components)))

def ofExtractedWitnessComponentRow
    (R : ExtractedWitnessComponentRow.{u} C hmin) :
    FixedFaceBoundaryExtractedComponentPackage.{u} C hmin where
  source :=
    EnclosureAndFaceBoundaryW31.ofSelectedOuterFaceAndEnclosure
      R.selectedFace R.enclosure
  components := R.components

def ofBoundaryRemainingComponentRow
    (R : BoundaryRemainingComponentRow.{u} C hmin) :
    FixedFaceBoundaryExtractedComponentPackage.{u} C hmin where
  source :=
    EnclosureAndFaceBoundaryW31.ofSelectedFaceRemainingComponentRow R
  components :=
    ExtractedComponentsInhabitationW31.extractedRemainingComponentFieldsOfConcrete
      R.remaining

@[simp]
theorem toExtractedWitnessComponentRow_selectedFace
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    P.toExtractedWitnessComponentRow.selectedFace =
      P.source.selectedOuterFaceData :=
  rfl

@[simp]
theorem toExtractedWitnessComponentRow_enclosure
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    P.toExtractedWitnessComponentRow.enclosure =
      P.source.selectedEnclosureData :=
  rfl

@[simp]
theorem toExtractedWitnessComponentRow_components
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    P.toExtractedWitnessComponentRow.components = P.components :=
  rfl

@[simp]
theorem toBoundaryRemainingComponentRow_selectedFace
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    P.toBoundaryRemainingComponentRow.selectedFace =
      P.source.selectedOuterFaceData :=
  rfl

@[simp]
theorem toBoundaryRemainingComponentRow_enclosure
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    P.toBoundaryRemainingComponentRow.enclosure =
      P.source.selectedEnclosureData :=
  rfl

@[simp]
theorem ofExtractedWitnessComponentRow_toExtractedWitnessComponentRow
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    ofExtractedWitnessComponentRow P.toExtractedWitnessComponentRow = P := by
  cases P with
  | mk source components =>
      cases source
      cases components
      rfl

@[simp]
theorem toExtractedWitnessComponentRow_ofExtractedWitnessComponentRow
    (R : ExtractedWitnessComponentRow.{u} C hmin) :
    (ofExtractedWitnessComponentRow R).toExtractedWitnessComponentRow = R := by
  cases R
  rfl

@[simp]
theorem ofBoundaryRemainingComponentRow_toBoundaryRemainingComponentRow
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    ofBoundaryRemainingComponentRow P.toBoundaryRemainingComponentRow = P := by
  cases P with
  | mk source components =>
      cases source
      cases components
      rfl

@[simp]
theorem toBoundaryRemainingComponentRow_ofBoundaryRemainingComponentRow
    (R : BoundaryRemainingComponentRow.{u} C hmin) :
    (ofBoundaryRemainingComponentRow R).toBoundaryRemainingComponentRow = R := by
  cases R with
  | mk selectedFace enclosure remaining =>
      cases remaining
      rfl

def extractedWitnessComponentRowEquiv :
    Equiv
      (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin)
      (ExtractedWitnessComponentRow.{u} C hmin) where
  toFun := toExtractedWitnessComponentRow
  invFun := ofExtractedWitnessComponentRow
  left_inv := ofExtractedWitnessComponentRow_toExtractedWitnessComponentRow
  right_inv := toExtractedWitnessComponentRow_ofExtractedWitnessComponentRow

def boundaryRemainingComponentRowEquiv :
    Equiv
      (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin)
      (BoundaryRemainingComponentRow.{u} C hmin) where
  toFun := toBoundaryRemainingComponentRow
  invFun := ofBoundaryRemainingComponentRow
  left_inv := ofBoundaryRemainingComponentRow_toBoundaryRemainingComponentRow
  right_inv := toBoundaryRemainingComponentRow_ofBoundaryRemainingComponentRow

end FixedFaceBoundaryExtractedComponentPackage

/-! ## Fixed package from actual selected-topology data -/

/-- Concrete extracted components over an actual selected topology datum for
one fixed minimal cleared failure.  This is the source-facing version of
`FixedFaceBoundaryExtractedComponentPackage`: it carries the selected
outer-face/enclosure datum directly and the five extracted component gates over
that same dependent datum. -/
structure FixedActualTopologyExtractedComponentPackage
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) where
  topology : ActualSelectedTopologyData C
  components :
    ExtractedRemainingComponentFields.{u} C hmin
      topology.selectedOuterFace topology.enclosure

namespace FixedActualTopologyExtractedComponentPackage

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def toFixedFaceBoundaryExtractedComponentPackage
    (P : FixedActualTopologyExtractedComponentPackage.{u} C hmin) :
    FixedFaceBoundaryExtractedComponentPackage.{u} C hmin where
  source := faceBoundaryEnclosureSourceOfActualSelectedTopologyData P.topology
  components := by
    simpa using P.components

def ofFixedFaceBoundaryExtractedComponentPackage
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    FixedActualTopologyExtractedComponentPackage.{u} C hmin where
  topology := actualSelectedTopologyDataOfFaceBoundaryEnclosureSource P.source
  components := by
    simpa using P.components

def toExtractedWitnessComponentRow
    (P : FixedActualTopologyExtractedComponentPackage.{u} C hmin) :
    ExtractedWitnessComponentRow.{u} C hmin :=
  P.toFixedFaceBoundaryExtractedComponentPackage.toExtractedWitnessComponentRow

def toBoundaryRemainingComponentRow
    (P : FixedActualTopologyExtractedComponentPackage.{u} C hmin) :
    BoundaryRemainingComponentRow.{u} C hmin :=
  P.toFixedFaceBoundaryExtractedComponentPackage.toBoundaryRemainingComponentRow

def toExactExtractedWitnessComponentPayload
    (P : FixedActualTopologyExtractedComponentPackage.{u} C hmin) :
    ExactExtractedWitnessComponentPayload.{u} C hmin :=
  P.toFixedFaceBoundaryExtractedComponentPackage.toExactExtractedWitnessComponentPayload

@[simp]
theorem toFixedFaceBoundaryExtractedComponentPackage_source
    (P : FixedActualTopologyExtractedComponentPackage.{u} C hmin) :
    P.toFixedFaceBoundaryExtractedComponentPackage.source =
      faceBoundaryEnclosureSourceOfActualSelectedTopologyData P.topology :=
  rfl

@[simp]
theorem ofFixedFaceBoundaryExtractedComponentPackage_toFixed
    (P : FixedActualTopologyExtractedComponentPackage.{u} C hmin) :
    ofFixedFaceBoundaryExtractedComponentPackage
      P.toFixedFaceBoundaryExtractedComponentPackage = P := by
  cases P with
  | mk topology components =>
      cases topology with
      | mk selectedOuterFace enclosure =>
          cases selectedOuterFace
          cases enclosure
          cases components
          rfl

@[simp]
theorem toFixed_ofFixedFaceBoundaryExtractedComponentPackage
    (P : FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) :
    (ofFixedFaceBoundaryExtractedComponentPackage P).toFixedFaceBoundaryExtractedComponentPackage =
      P := by
  cases P with
  | mk source components =>
      cases source
      cases components
      rfl

def fixedFaceBoundaryExtractedComponentPackageEquiv :
    Equiv
      (FixedActualTopologyExtractedComponentPackage.{u} C hmin)
      (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) where
  toFun := toFixedFaceBoundaryExtractedComponentPackage
  invFun := ofFixedFaceBoundaryExtractedComponentPackage
  left_inv := ofFixedFaceBoundaryExtractedComponentPackage_toFixed
  right_inv := toFixed_ofFixedFaceBoundaryExtractedComponentPackage

end FixedActualTopologyExtractedComponentPackage

theorem nonempty_fixedActualTopologyPackage_iff_fixedPackage
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (FixedActualTopologyExtractedComponentPackage.{u} C hmin) <->
      Nonempty
        (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            P.toFixedFaceBoundaryExtractedComponentPackage
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact
          open FixedActualTopologyExtractedComponentPackage in
          Nonempty.intro
            (ofFixedFaceBoundaryExtractedComponentPackage P)

theorem nonempty_fixedPackage_iff_extractedComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) <->
      Nonempty (ExtractedWitnessComponentRow.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toExtractedWitnessComponentRow
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact
          Nonempty.intro
            (FixedFaceBoundaryExtractedComponentPackage.ofExtractedWitnessComponentRow
              R)

theorem nonempty_fixedPackage_iff_boundaryRemainingComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) <->
      Nonempty (BoundaryRemainingComponentRow.{u} C hmin) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro P.toBoundaryRemainingComponentRow
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact
          Nonempty.intro
            (FixedFaceBoundaryExtractedComponentPackage.ofBoundaryRemainingComponentRow
              R)

theorem nonempty_fixedPackage_iff_exactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin) <->
      ExactExtractedWitnessComponentPayload.{u} C hmin :=
  (nonempty_fixedPackage_iff_extractedComponentRow
    (C := C) (hmin := hmin)).trans
    (ExtractedWitnessComponentsW30.exactExtractedWitnessPayload_iff_componentRow
      (C := C) (hmin := hmin)).symm

theorem nonempty_fixedActualTopologyPackage_iff_boundaryRemainingComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (FixedActualTopologyExtractedComponentPackage.{u} C hmin) <->
      Nonempty (BoundaryRemainingComponentRow.{u} C hmin) :=
  (nonempty_fixedActualTopologyPackage_iff_fixedPackage
    (C := C) (hmin := hmin)).trans
    (nonempty_fixedPackage_iff_boundaryRemainingComponentRow
      (C := C) (hmin := hmin))

theorem nonempty_fixedActualTopologyPackage_iff_exactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Nonempty
        (FixedActualTopologyExtractedComponentPackage.{u} C hmin) <->
      ExactExtractedWitnessComponentPayload.{u} C hmin :=
  (nonempty_fixedActualTopologyPackage_iff_fixedPackage
    (C := C) (hmin := hmin)).trans
    (nonempty_fixedPackage_iff_exactPayload
      (C := C) (hmin := hmin))

theorem not_fixedPackage_iff_not_boundaryRemainingComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    Not
        (Nonempty
          (FixedFaceBoundaryExtractedComponentPackage.{u} C hmin)) <->
      Not (Nonempty (BoundaryRemainingComponentRow.{u} C hmin)) :=
  not_congr
    (nonempty_fixedPackage_iff_boundaryRemainingComponentRow
      (C := C) (hmin := hmin))

/-! ## Fixed package over a supplied actual selected topology -/

abbrev ActualSelectedRemainingComponentFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (topology : ActualSelectedTopologyData C) :
    Type (u + 1) :=
  ExtractedRemainingComponentFields.{u} C hmin
    topology.selectedOuterFace topology.enclosure

abbrev ActualSelectedRemainingComponentSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (topology : ActualSelectedTopologyData C) :
    Type (u + 1) :=
  ExtractedWitnessComponentsW30.RemainingComponentFields.{u} C hmin
    topology.selectedOuterFace topology.enclosure

abbrev ActualSelectedRemainingWitnessFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (topology : ActualSelectedTopologyData C) :
    Type (u + 1) :=
  MinimalBoundaryTopologyWitnessInhabitationW25.RemainingWitnessFields.{u}
    C hmin topology.selectedOuterFace topology.enclosure

abbrev ActualSelectedExactRemainingComponentPayload
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (topology : ActualSelectedTopologyData C) : Prop :=
  ExtractedWitnessComponentsW30.ExactRemainingComponentPayload.{u}
    C hmin topology.selectedOuterFace topology.enclosure

def actualSelectedRemainingComponentFieldsEquivSourceFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C) :
    ActualSelectedRemainingComponentFields.{u} C hmin topology ≃
      ActualSelectedRemainingComponentSourceFields.{u} C hmin topology :=
  ExtractedWitnessComponentsW30.ExtractedRemainingComponentFields.remainingComponentFieldsEquiv
    (C := C) (hmin := hmin)
    (D := topology.selectedOuterFace)
    (E := topology.enclosure)

def actualSelectedRemainingSourceFieldsEquivWitnessFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C) :
    ActualSelectedRemainingComponentSourceFields.{u} C hmin topology ≃
      ActualSelectedRemainingWitnessFields.{u} C hmin topology :=
  BoundaryWitnessRemainingFieldsW26.RemainingWitnessComponentFields.remainingWitnessFieldsEquiv
    (C := C) (hmin := hmin)
    (D := topology.selectedOuterFace)
    (E := topology.enclosure)

def actualSelectedRemainingComponentFieldsEquivWitnessFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C) :
    ActualSelectedRemainingComponentFields.{u} C hmin topology ≃
      ActualSelectedRemainingWitnessFields.{u} C hmin topology :=
  (actualSelectedRemainingComponentFieldsEquivSourceFields
    (C := C) (hmin := hmin) topology).trans
    (actualSelectedRemainingSourceFieldsEquivWitnessFields
      (C := C) (hmin := hmin) topology)

def actualSelectedRemainingComponentFieldsOfSourceFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {topology : ActualSelectedTopologyData C}
    (R : ActualSelectedRemainingComponentSourceFields.{u} C hmin topology) :
    ActualSelectedRemainingComponentFields.{u} C hmin topology :=
  (actualSelectedRemainingComponentFieldsEquivSourceFields
    (C := C) (hmin := hmin) topology).symm R

def actualSelectedRemainingComponentFieldsOfWitnessFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {topology : ActualSelectedTopologyData C}
    (R : ActualSelectedRemainingWitnessFields.{u} C hmin topology) :
    ActualSelectedRemainingComponentFields.{u} C hmin topology :=
  (actualSelectedRemainingComponentFieldsEquivWitnessFields
    (C := C) (hmin := hmin) topology).symm R

def actualSelectedRemainingComponentFieldsOfExactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    {topology : ActualSelectedTopologyData C}
    (h : ActualSelectedExactRemainingComponentPayload.{u} C hmin topology) :
    ActualSelectedRemainingComponentFields.{u} C hmin topology :=
  Classical.choice
    ((ExtractedWitnessComponentsW30.exactPayload_iff_componentFields
      (C := C) (hmin := hmin)
      (D := topology.selectedOuterFace)
      (E := topology.enclosure)
      ).1 h)

def fixedActualTopologyPackageOfActualSelectedRemainingComponentFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C)
    (components :
      ActualSelectedRemainingComponentFields.{u} C hmin topology) :
    FixedActualTopologyExtractedComponentPackage.{u} C hmin where
  topology := topology
  components := components

def fixedActualTopologyPackageOfActualSelectedWitnessFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C)
    (R : ActualSelectedRemainingWitnessFields.{u} C hmin topology) :
    FixedActualTopologyExtractedComponentPackage.{u} C hmin :=
  fixedActualTopologyPackageOfActualSelectedRemainingComponentFields
    topology
    (actualSelectedRemainingComponentFieldsOfWitnessFields R)

@[simp]
theorem fixedActualTopologyPackageOfActualSelectedRemainingComponentFields_topology
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C)
    (components :
      ActualSelectedRemainingComponentFields.{u} C hmin topology) :
    (fixedActualTopologyPackageOfActualSelectedRemainingComponentFields
      topology components).topology = topology :=
  rfl

@[simp]
theorem fixedActualTopologyPackageOfActualSelectedRemainingComponentFields_components
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C)
    (components :
      ActualSelectedRemainingComponentFields.{u} C hmin topology) :
    (fixedActualTopologyPackageOfActualSelectedRemainingComponentFields
      topology components).components = components :=
  rfl

theorem nonempty_actualSelectedRemainingComponentFields_iff_sourceFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C) :
    Nonempty (ActualSelectedRemainingComponentFields.{u} C hmin topology) <->
      Nonempty
        (ActualSelectedRemainingComponentSourceFields.{u} C hmin topology) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            ((actualSelectedRemainingComponentFieldsEquivSourceFields
              (C := C) (hmin := hmin) topology) P)
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact
          Nonempty.intro
            ((actualSelectedRemainingComponentFieldsEquivSourceFields
              (C := C) (hmin := hmin) topology).symm R)

theorem nonempty_actualSelectedRemainingComponentFields_iff_witnessFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C) :
    Nonempty (ActualSelectedRemainingComponentFields.{u} C hmin topology) <->
      Nonempty
        (ActualSelectedRemainingWitnessFields.{u} C hmin topology) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            ((actualSelectedRemainingComponentFieldsEquivWitnessFields
              (C := C) (hmin := hmin) topology) P)
  case mpr =>
    intro h
    cases h with
    | intro R =>
        exact
          Nonempty.intro
            (actualSelectedRemainingComponentFieldsOfWitnessFields R)

theorem nonempty_actualSelectedRemainingComponentFields_iff_exactPayload
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (topology : ActualSelectedTopologyData C) :
    Nonempty (ActualSelectedRemainingComponentFields.{u} C hmin topology) <->
      ActualSelectedExactRemainingComponentPayload.{u} C hmin topology :=
  (ExtractedWitnessComponentsW30.exactPayload_iff_componentFields
    (C := C) (hmin := hmin)
    (D := topology.selectedOuterFace)
    (E := topology.enclosure)
    ).symm

/-! ## Honest minimal-failure selected topology rows -/

abbrev MinimalFailureActualSelectedTopologyRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      ActualSelectedTopologyData C

abbrev MinimalFailureConcreteTopologyFactsRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      ConcreteTopologyFacts C

abbrev MinimalFailureMissingTopologyFactsRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      MissingTopologyFacts C

abbrev MinimalFailureTopologyBoundaryRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      TopologyBoundary C

abbrev MinimalFailureActualSelectedTopologyDataTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty (ActualSelectedTopologyData C)

abbrev MinimalFailureSelectedTopologySourceTarget : Prop :=
  MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget

def minimalFailureActualSelectedTopologyDataTargetOfRows
    (topology : MinimalFailureActualSelectedTopologyRows) :
    MinimalFailureActualSelectedTopologyDataTarget :=
  fun C hmin => Nonempty.intro (topology C hmin)

def actualTopologyRowsOfConcreteTopologyFactsRows
    (topology : MinimalFailureConcreteTopologyFactsRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin =>
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofConcreteTopologyFacts
      (topology C hmin)

def actualTopologyRowsOfMissingTopologyFactsRows
    (topology : MinimalFailureMissingTopologyFactsRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin =>
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofMissingTopologyFacts
      (topology C hmin)

def actualTopologyRowsOfTopologyBoundaryRows
    (topology : MinimalFailureTopologyBoundaryRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin =>
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
      (topology C hmin)

theorem nonempty_actualTopologyRows_of_concreteTopologyFactsRows
    (topology : MinimalFailureConcreteTopologyFactsRows) :
    Nonempty MinimalFailureActualSelectedTopologyRows :=
  Nonempty.intro
    (actualTopologyRowsOfConcreteTopologyFactsRows topology)

theorem nonempty_actualTopologyRows_of_missingTopologyFactsRows
    (topology : MinimalFailureMissingTopologyFactsRows) :
    Nonempty MinimalFailureActualSelectedTopologyRows :=
  Nonempty.intro
    (actualTopologyRowsOfMissingTopologyFactsRows topology)

theorem nonempty_actualTopologyRows_of_topologyBoundaryRows
    (topology : MinimalFailureTopologyBoundaryRows) :
    Nonempty MinimalFailureActualSelectedTopologyRows :=
  Nonempty.intro
    (actualTopologyRowsOfTopologyBoundaryRows topology)

theorem minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (topology : MinimalFailureActualSelectedTopologyRows) :
    MinimalFailureSelectedTopologySourceTarget :=
  open MinimalFailureSelectedTopologySourceW32 in
  minimalFailureSelectedTopologySourceTarget_iff_actualSelectedTopologyDataTarget.2
    (minimalFailureActualSelectedTopologyDataTargetOfRows topology)

theorem minimalFailureSelectedTopologySourceTarget_of_concreteTopologyFactsRows
    (topology : MinimalFailureConcreteTopologyFactsRows) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (actualTopologyRowsOfConcreteTopologyFactsRows topology)

theorem minimalFailureSelectedTopologySourceTarget_of_missingTopologyFactsRows
    (topology : MinimalFailureMissingTopologyFactsRows) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (actualTopologyRowsOfMissingTopologyFactsRows topology)

theorem minimalFailureSelectedTopologySourceTarget_of_topologyBoundaryRows
    (topology : MinimalFailureTopologyBoundaryRows) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (actualTopologyRowsOfTopologyBoundaryRows topology)

def actualTopologyRowsOfMinimalFailureSelectedTopologySourceTarget
    (h : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureActualSelectedTopologyRows := by
  intro n C hmin
  exact
    open MinimalFailureSelectedTopologySourceW32 in
    Classical.choice
      ((minimalFailureSelectedTopologySource_iff_actualSelectedTopologyData
          hmin).1
        (h C hmin))

theorem minimalFailureSelectedTopologySourceTarget_iff_nonempty_actualTopologyRows :
    MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureActualSelectedTopologyRows := by
  constructor
  case mp =>
    intro h
    exact
      Nonempty.intro
        (actualTopologyRowsOfMinimalFailureSelectedTopologySourceTarget h)
  case mpr =>
    intro h
    cases h with
    | intro topology =>
        exact
          minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
            topology

def minimalFailureActualSelectedTopologyRowsOfTarget
    (target : MinimalFailureActualSelectedTopologyDataTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => Classical.choice (target C hmin)

def actualTopologyRowsOfMinimalFailureSelectedFaceRouteTarget
    (h :
      MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedFaceRouteTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  open MinimalFailureSelectedTopologySourceW32 in
  actualTopologyRowsOfMinimalFailureSelectedTopologySourceTarget
    (minimalFailureSelectedTopologySourceTarget_iff_routeTarget.2 h)

def actualTopologyRowsOfMinimalFailureConcreteTopologyFactsTarget
    (h :
      MinimalFailureSelectedTopologySourceW32.MinimalFailureConcreteTopologyFactsTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  open MinimalFailureSelectedTopologySourceW32 in
  actualTopologyRowsOfMinimalFailureSelectedTopologySourceTarget
    (minimalFailureSelectedTopologySourceTarget_iff_concreteTopologyFactsTarget.2
      h)

def actualTopologyRowsOfMinimalFailureRemainingCoreTopologyTarget
    (h :
      MinimalFailureSelectedTopologySourceW32.MinimalFailureRemainingCoreTopologyTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  open MinimalFailureSelectedTopologySourceW32 in
  actualTopologyRowsOfMinimalFailureSelectedTopologySourceTarget
    (minimalFailureSelectedTopologySourceTarget_iff_remainingCoreTopologyTarget.2
      h)

def actualTopologyRowsOfSelectedFaceEnclosureRouteRows
    (rows :
      SelectedFaceEnclosureBridgeW32.MinimalFailureSelectedFaceEnclosureRouteRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => (rows C hmin).toActualSelectedTopologyData

def actualTopologyRowsOfJordanSourceRows
    (rows : FaceBoundaryTopologySourceW32.MinimalFailureJordanSourceRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => (rows C hmin).actualSelectedTopologyData

theorem minimalFailureSelectedTopologySourceTarget_of_selectedFaceEnclosureRouteRows
    (rows :
      SelectedFaceEnclosureBridgeW32.MinimalFailureSelectedFaceEnclosureRouteRows) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (actualTopologyRowsOfSelectedFaceEnclosureRouteRows rows)

theorem minimalFailureSelectedTopologySourceTarget_of_jordanSourceRows
    (rows : FaceBoundaryTopologySourceW32.MinimalFailureJordanSourceRows) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (actualTopologyRowsOfJordanSourceRows rows)

structure ActualTopologyRemainingComponentRows
    (topology : MinimalFailureActualSelectedTopologyRows) :
    Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ActualSelectedRemainingComponentFields.{u} C hmin
          (topology C hmin)

def actualTopologyRemainingComponentRowsOfActualSelectedWitnessRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          ActualSelectedRemainingWitnessFields.{u} C hmin
            (topology C hmin)) :
    ActualTopologyRemainingComponentRows.{u} topology where
  row := fun {n} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) =>
    actualSelectedRemainingComponentFieldsOfWitnessFields
      (C := C) (hmin := hmin) (topology := topology C hmin)
      (rows C hmin)

theorem actualTopologyRemainingComponentRows_nonempty_of_actualSelectedWitnessRows
    {topology : MinimalFailureActualSelectedTopologyRows}
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          ActualSelectedRemainingWitnessFields.{u} C hmin
            (topology C hmin)) :
    Nonempty (ActualTopologyRemainingComponentRows.{u} topology) :=
  Nonempty.intro
    (actualTopologyRemainingComponentRowsOfActualSelectedWitnessRows
      (topology := topology)
      rows)

abbrev HonestActualTopologyExtractedComponentFamily : Type (u + 1) :=
  Sigma ActualTopologyRemainingComponentRows.{u}

namespace HonestActualTopologyExtractedComponentFamily

def topologyTarget
    (P : HonestActualTopologyExtractedComponentFamily.{u}) :
    MinimalFailureActualSelectedTopologyDataTarget :=
  minimalFailureActualSelectedTopologyDataTargetOfRows P.1

def fixedPackage
    (P : HonestActualTopologyExtractedComponentFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    FixedActualTopologyExtractedComponentPackage.{u} C hmin :=
  fixedActualTopologyPackageOfActualSelectedRemainingComponentFields
    (P.1 C hmin) (P.2.row C hmin)

end HonestActualTopologyExtractedComponentFamily

/-! ## Uniform extracted-component closure package -/

/-- Uniform concrete closure data for the extracted component family. -/
structure ConcreteExtractedComponentClosurePackage : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        FixedFaceBoundaryExtractedComponentPackage.{u} C hmin

namespace ConcreteExtractedComponentClosurePackage

def toExtractedWitnessComponentFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    W31ExtractedWitnessComponentFamily.{u} where
  row := fun C hmin =>
    (P.row C hmin).toExtractedWitnessComponentRow

def toBoundaryRemainingComponentFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    W31BoundaryRemainingComponentFamily.{u} where
  row := fun C hmin =>
    (P.row C hmin).toBoundaryRemainingComponentRow

def toExtractedWitnessFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    W31ExtractedWitnessFamily.{u} :=
  P.toExtractedWitnessComponentFamily.toExtractedWitnessFamily

def toBoundaryWitnessSourceFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    W31BoundaryWitnessSourceFamily.{u} :=
  P.toExtractedWitnessComponentFamily.toBoundaryWitnessSourceFamily

def toSelectedFaceWitnessFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    W31SelectedFaceWitnessFamily.{u} :=
  P.toBoundaryRemainingComponentFamily.toSelectedFaceWitnessFamily

def ofExtractedWitnessComponentFamily
    (F : W31ExtractedWitnessComponentFamily.{u}) :
    ConcreteExtractedComponentClosurePackage.{u} where
  row := fun C hmin =>
    FixedFaceBoundaryExtractedComponentPackage.ofExtractedWitnessComponentRow
      (F.row C hmin)

def ofBoundaryRemainingComponentFamily
    (F : W31BoundaryRemainingComponentFamily.{u}) :
    ConcreteExtractedComponentClosurePackage.{u} where
  row := fun C hmin =>
    FixedFaceBoundaryExtractedComponentPackage.ofBoundaryRemainingComponentRow
      (F.row C hmin)

def ofSelectedFaceWitnessFamily
    (F : W31SelectedFaceWitnessFamily.{u}) :
    ConcreteExtractedComponentClosurePackage.{u} :=
  open BoundaryRemainingComponentsConcreteW27 in
  ofBoundaryRemainingComponentFamily
    (boundaryRemainingComponentFamilyOfSelectedFaceWitnessFamily F)

theorem nonempty_extractedWitnessComponentFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    Nonempty W31ExtractedWitnessComponentFamily.{u} :=
  Nonempty.intro P.toExtractedWitnessComponentFamily

theorem nonempty_boundaryRemainingComponentFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    Nonempty W31BoundaryRemainingComponentFamily.{u} :=
  Nonempty.intro P.toBoundaryRemainingComponentFamily

theorem nonempty_selectedFaceWitnessFamily
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    Nonempty W31SelectedFaceWitnessFamily.{u} :=
  Nonempty.intro P.toSelectedFaceWitnessFamily

end ConcreteExtractedComponentClosurePackage

theorem concreteClosurePackage_nonempty_of_extractedWitnessComponentFamily
    (h : Nonempty W31ExtractedWitnessComponentFamily.{u}) :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (ConcreteExtractedComponentClosurePackage.ofExtractedWitnessComponentFamily
            F)

theorem extractedWitnessComponentFamily_nonempty_of_concreteClosurePackage
    (h : Nonempty ConcreteExtractedComponentClosurePackage.{u}) :
    Nonempty W31ExtractedWitnessComponentFamily.{u} := by
  cases h with
  | intro P =>
      exact P.nonempty_extractedWitnessComponentFamily

theorem concreteClosurePackage_nonempty_iff_extractedWitnessComponentFamily :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} <->
      Nonempty W31ExtractedWitnessComponentFamily.{u} := by
  constructor
  case mp =>
    exact extractedWitnessComponentFamily_nonempty_of_concreteClosurePackage
  case mpr =>
    exact concreteClosurePackage_nonempty_of_extractedWitnessComponentFamily

theorem concreteClosurePackage_nonempty_of_boundaryRemainingComponentFamily
    (h : Nonempty W31BoundaryRemainingComponentFamily.{u}) :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (ConcreteExtractedComponentClosurePackage.ofBoundaryRemainingComponentFamily
            F)

theorem boundaryRemainingComponentFamily_nonempty_of_concreteClosurePackage
    (h : Nonempty ConcreteExtractedComponentClosurePackage.{u}) :
    Nonempty W31BoundaryRemainingComponentFamily.{u} := by
  cases h with
  | intro P =>
      exact P.nonempty_boundaryRemainingComponentFamily

theorem concreteClosurePackage_nonempty_iff_boundaryRemainingComponentFamily :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} <->
      Nonempty W31BoundaryRemainingComponentFamily.{u} := by
  constructor
  case mp =>
    exact boundaryRemainingComponentFamily_nonempty_of_concreteClosurePackage
  case mpr =>
    exact concreteClosurePackage_nonempty_of_boundaryRemainingComponentFamily

theorem concreteClosurePackage_nonempty_iff_selectedFaceWitnessFamily :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} <->
      Nonempty W31SelectedFaceWitnessFamily.{u} :=
  open ExtractedComponentsInhabitationW31 in
  concreteClosurePackage_nonempty_iff_extractedWitnessComponentFamily.trans
    extractedWitnessComponentFamily_nonempty_iff_selectedFaceWitnessFamily

theorem concreteClosurePackage_nonempty_iff_extractedWitnessFamily :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} <->
      Nonempty W31ExtractedWitnessFamily.{u} :=
  open ExtractedComponentsInhabitationW31 in
  concreteClosurePackage_nonempty_iff_boundaryRemainingComponentFamily.trans
    extractedWitnessFamily_nonempty_iff_boundaryRemainingComponentFamily.symm

theorem concreteClosurePackage_nonempty_iff_boundaryWitnessSourceFamily :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} <->
      Nonempty W31BoundaryWitnessSourceFamily.{u} :=
  open ExtractedComponentsInhabitationW31 in
  concreteClosurePackage_nonempty_iff_boundaryRemainingComponentFamily.trans
    boundaryWitnessSourceFamily_nonempty_iff_boundaryRemainingComponentFamily.symm

theorem not_concreteClosurePackage_iff_not_boundaryRemainingComponentFamily :
    Not (Nonempty ConcreteExtractedComponentClosurePackage.{u}) <->
      Not (Nonempty W31BoundaryRemainingComponentFamily.{u}) :=
  not_congr concreteClosurePackage_nonempty_iff_boundaryRemainingComponentFamily

theorem not_concreteClosurePackage_iff_not_selectedFaceWitnessFamily :
    Not (Nonempty ConcreteExtractedComponentClosurePackage.{u}) <->
      Not (Nonempty W31SelectedFaceWitnessFamily.{u}) :=
  not_congr concreteClosurePackage_nonempty_iff_selectedFaceWitnessFamily

theorem not_concreteClosurePackage_iff_not_extractedWitnessComponentFamily :
    Not (Nonempty ConcreteExtractedComponentClosurePackage.{u}) <->
      Not (Nonempty W31ExtractedWitnessComponentFamily.{u}) :=
  not_congr concreteClosurePackage_nonempty_iff_extractedWitnessComponentFamily

/-! ## Uniform closure from actual selected-topology rows -/

/-- Uniform source-facing extracted-component closure data.  Each minimal
cleared failure carries an actual selected topology datum and the five
extracted component gates over that same datum. -/
structure ActualTopologyExtractedComponentClosurePackage : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        FixedActualTopologyExtractedComponentPackage.{u} C hmin

namespace ActualTopologyExtractedComponentClosurePackage

def toConcreteExtractedComponentClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    ConcreteExtractedComponentClosurePackage.{u} where
  row := fun C hmin =>
    (P.row C hmin).toFixedFaceBoundaryExtractedComponentPackage

def toExtractedWitnessComponentFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    W31ExtractedWitnessComponentFamily.{u} :=
  P.toConcreteExtractedComponentClosurePackage.toExtractedWitnessComponentFamily

def ofConcreteExtractedComponentClosurePackage
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    ActualTopologyExtractedComponentClosurePackage.{u} where
  row := fun C hmin =>
    FixedActualTopologyExtractedComponentPackage.ofFixedFaceBoundaryExtractedComponentPackage
      (P.row C hmin)

def toExtractedWitnessFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    W31ExtractedWitnessFamily.{u} :=
  P.toExtractedWitnessComponentFamily.toExtractedWitnessFamily

def toBoundaryWitnessSourceFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    W31BoundaryWitnessSourceFamily.{u} :=
  P.toExtractedWitnessComponentFamily.toBoundaryWitnessSourceFamily

def toBoundaryRemainingComponentFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    W31BoundaryRemainingComponentFamily.{u} :=
  P.toConcreteExtractedComponentClosurePackage.toBoundaryRemainingComponentFamily

def toSelectedFaceWitnessFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    W31SelectedFaceWitnessFamily.{u} :=
  P.toConcreteExtractedComponentClosurePackage.toSelectedFaceWitnessFamily

theorem nonempty_extractedWitnessComponentFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty W31ExtractedWitnessComponentFamily.{u} :=
  Nonempty.intro P.toExtractedWitnessComponentFamily

theorem nonempty_extractedWitnessFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty W31ExtractedWitnessFamily.{u} :=
  Nonempty.intro P.toExtractedWitnessFamily

theorem nonempty_boundaryWitnessSourceFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty W31BoundaryWitnessSourceFamily.{u} :=
  Nonempty.intro P.toBoundaryWitnessSourceFamily

theorem nonempty_boundaryRemainingComponentFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty W31BoundaryRemainingComponentFamily.{u} :=
  Nonempty.intro P.toBoundaryRemainingComponentFamily

theorem nonempty_selectedFaceWitnessFamily
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty W31SelectedFaceWitnessFamily.{u} :=
  Nonempty.intro P.toSelectedFaceWitnessFamily

@[simp]
theorem ofConcrete_toConcrete
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    ofConcreteExtractedComponentClosurePackage
      P.toConcreteExtractedComponentClosurePackage = P := by
  cases P
  rfl

@[simp]
theorem toConcrete_ofConcrete
    (P : ConcreteExtractedComponentClosurePackage.{u}) :
    (ofConcreteExtractedComponentClosurePackage P).toConcreteExtractedComponentClosurePackage =
      P := by
  cases P
  rfl

def concreteExtractedComponentClosurePackageEquiv :
    Equiv
      ActualTopologyExtractedComponentClosurePackage.{u}
      ConcreteExtractedComponentClosurePackage.{u} where
  toFun := toConcreteExtractedComponentClosurePackage
  invFun := ofConcreteExtractedComponentClosurePackage
  left_inv := ofConcrete_toConcrete
  right_inv := toConcrete_ofConcrete

end ActualTopologyExtractedComponentClosurePackage

namespace HonestActualTopologyExtractedComponentFamily

def toActualTopologyExtractedComponentClosurePackage
    (P : HonestActualTopologyExtractedComponentFamily.{u}) :
    ActualTopologyExtractedComponentClosurePackage.{u} where
  row := fun C hmin => P.fixedPackage C hmin

def ofActualTopologyExtractedComponentClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    HonestActualTopologyExtractedComponentFamily.{u} :=
  Sigma.mk
    (fun C hmin => (P.row C hmin).topology)
    { row := fun C hmin => (P.row C hmin).components }

end HonestActualTopologyExtractedComponentFamily

theorem concreteClosurePackage_nonempty_of_actualTopologyClosurePackage
    (h : Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty ConcreteExtractedComponentClosurePackage.{u} := by
  cases h with
  | intro P =>
      exact Nonempty.intro P.toConcreteExtractedComponentClosurePackage

theorem actualTopologyClosurePackage_nonempty_of_concreteClosurePackage
    (h : Nonempty ConcreteExtractedComponentClosurePackage.{u}) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} := by
  cases h with
  | intro P =>
      exact
        Nonempty.intro
          (ActualTopologyExtractedComponentClosurePackage.ofConcreteExtractedComponentClosurePackage
            P)

theorem actualTopologyClosurePackage_nonempty_iff_concreteClosurePackage :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty ConcreteExtractedComponentClosurePackage.{u} := by
  constructor
  case mp =>
    exact concreteClosurePackage_nonempty_of_actualTopologyClosurePackage
  case mpr =>
    exact actualTopologyClosurePackage_nonempty_of_concreteClosurePackage

theorem actualTopologyClosurePackage_nonempty_of_honestActualTopologyComponentFamily
    (h : Nonempty HonestActualTopologyExtractedComponentFamily.{u}) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} := by
  cases h with
  | intro P =>
      exact
        Nonempty.intro
          P.toActualTopologyExtractedComponentClosurePackage

theorem honestActualTopologyComponentFamily_nonempty_of_actualTopologyClosurePackage
    (h : Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty HonestActualTopologyExtractedComponentFamily.{u} := by
  cases h with
  | intro P =>
      exact
        Nonempty.intro
          (open HonestActualTopologyExtractedComponentFamily in
            ofActualTopologyExtractedComponentClosurePackage P)

theorem honestActualTopologyComponentFamily_nonempty_iff_actualTopologyClosurePackage :
    Nonempty HonestActualTopologyExtractedComponentFamily.{u} <->
      Nonempty ActualTopologyExtractedComponentClosurePackage.{u} := by
  constructor
  case mp =>
    exact actualTopologyClosurePackage_nonempty_of_honestActualTopologyComponentFamily
  case mpr =>
    exact honestActualTopologyComponentFamily_nonempty_of_actualTopologyClosurePackage

theorem actualTopologyClosurePackage_nonempty_iff_exists_actualTopologyRows_components :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Exists fun topology : MinimalFailureActualSelectedTopologyRows =>
        Nonempty (ActualTopologyRemainingComponentRows.{u} topology) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact
          Exists.intro
            (fun C hmin => (P.row C hmin).topology)
            (Nonempty.intro
              { row := fun C hmin => (P.row C hmin).components })
  case mpr =>
    intro h
    cases h with
    | intro topology hcomponents =>
        cases hcomponents with
        | intro components =>
            exact
              actualTopologyClosurePackage_nonempty_of_honestActualTopologyComponentFamily
                (Nonempty.intro
                  (Sigma.mk topology components))

def actualTopologyClosurePackageOfActualTopologyRows
    (topology : MinimalFailureActualSelectedTopologyRows)
    (components : ActualTopologyRemainingComponentRows.{u} topology) :
    ActualTopologyExtractedComponentClosurePackage.{u} where
  row := fun C hmin =>
    fixedActualTopologyPackageOfActualSelectedRemainingComponentFields
      (topology C hmin) (components.row C hmin)

def actualTopologyRowsOfActualTopologyClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => (P.row C hmin).topology

def actualTopologyRemainingComponentRowsOfActualTopologyClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    ActualTopologyRemainingComponentRows.{u}
      (actualTopologyRowsOfActualTopologyClosurePackage P) where
  row := fun C hmin => (P.row C hmin).components

def honestActualTopologyExtractedComponentFamilyOfActualTopologyClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    HonestActualTopologyExtractedComponentFamily.{u} :=
  Sigma.mk
    (actualTopologyRowsOfActualTopologyClosurePackage P)
    (actualTopologyRemainingComponentRowsOfActualTopologyClosurePackage P)

theorem minimalFailureActualSelectedTopologyDataTarget_of_actualTopologyClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    MinimalFailureActualSelectedTopologyDataTarget :=
  minimalFailureActualSelectedTopologyDataTargetOfRows
    (actualTopologyRowsOfActualTopologyClosurePackage P)

theorem minimalFailureSelectedTopologySourceTarget_of_actualTopologyClosurePackage
    (P : ActualTopologyExtractedComponentClosurePackage.{u}) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_of_actualTopologyRows
    (actualTopologyRowsOfActualTopologyClosurePackage P)

theorem minimalFailureSelectedTopologySourceTarget_of_nonempty_actualTopologyClosurePackage
    (h : Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) :
    MinimalFailureSelectedTopologySourceTarget := by
  cases h with
  | intro P =>
      exact minimalFailureSelectedTopologySourceTarget_of_actualTopologyClosurePackage P

theorem actualTopologyClosurePackage_nonempty_of_extractedWitnessComponentFamily
    (h : Nonempty W31ExtractedWitnessComponentFamily.{u}) :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackage_nonempty_of_concreteClosurePackage
    (concreteClosurePackage_nonempty_of_extractedWitnessComponentFamily h)

theorem extractedWitnessComponentFamily_nonempty_of_actualTopologyClosurePackage
    (h : Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty W31ExtractedWitnessComponentFamily.{u} := by
  cases h with
  | intro P =>
      exact P.nonempty_extractedWitnessComponentFamily

theorem actualTopologyClosurePackage_nonempty_iff_extractedWitnessComponentFamily :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty W31ExtractedWitnessComponentFamily.{u} := by
  constructor
  case mp =>
    exact extractedWitnessComponentFamily_nonempty_of_actualTopologyClosurePackage
  case mpr =>
    exact actualTopologyClosurePackage_nonempty_of_extractedWitnessComponentFamily

theorem honestActualTopologyComponentFamily_nonempty_iff_extractedWitnessComponentFamily :
    Nonempty HonestActualTopologyExtractedComponentFamily.{u} <->
      Nonempty W31ExtractedWitnessComponentFamily.{u} :=
  honestActualTopologyComponentFamily_nonempty_iff_actualTopologyClosurePackage.trans
    actualTopologyClosurePackage_nonempty_iff_extractedWitnessComponentFamily

theorem actualTopologyClosurePackage_nonempty_iff_extractedWitnessFamily :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty W31ExtractedWitnessFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_concreteClosurePackage.trans
    concreteClosurePackage_nonempty_iff_extractedWitnessFamily

theorem actualTopologyClosurePackage_nonempty_iff_boundaryWitnessSourceFamily :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty W31BoundaryWitnessSourceFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_concreteClosurePackage.trans
    concreteClosurePackage_nonempty_iff_boundaryWitnessSourceFamily

theorem actualTopologyClosurePackage_nonempty_iff_boundaryRemainingComponentFamily :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty W31BoundaryRemainingComponentFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_concreteClosurePackage.trans
    concreteClosurePackage_nonempty_iff_boundaryRemainingComponentFamily

theorem actualTopologyClosurePackage_nonempty_iff_selectedFaceWitnessFamily :
    Nonempty ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty W31SelectedFaceWitnessFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_concreteClosurePackage.trans
    concreteClosurePackage_nonempty_iff_selectedFaceWitnessFamily

theorem not_actualTopologyClosurePackage_iff_not_boundaryRemainingComponentFamily :
    Not (Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) <->
      Not (Nonempty W31BoundaryRemainingComponentFamily.{u}) :=
  not_congr actualTopologyClosurePackage_nonempty_iff_boundaryRemainingComponentFamily

theorem not_actualTopologyClosurePackage_iff_not_selectedFaceWitnessFamily :
    Not (Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) <->
      Not (Nonempty W31SelectedFaceWitnessFamily.{u}) :=
  not_congr actualTopologyClosurePackage_nonempty_iff_selectedFaceWitnessFamily

theorem not_actualTopologyClosurePackage_iff_not_extractedWitnessComponentFamily :
    Not (Nonempty ActualTopologyExtractedComponentClosurePackage.{u}) <->
      Not (Nonempty W31ExtractedWitnessComponentFamily.{u}) :=
  not_congr actualTopologyClosurePackage_nonempty_iff_extractedWitnessComponentFamily

theorem not_honestActualTopologyComponentFamily_iff_not_extractedWitnessComponentFamily :
    Not (Nonempty HonestActualTopologyExtractedComponentFamily.{u}) <->
      Not (Nonempty W31ExtractedWitnessComponentFamily.{u}) :=
  not_congr honestActualTopologyComponentFamily_nonempty_iff_extractedWitnessComponentFamily

/-! ## W23 no-cut and tail packages -/

structure ConcreteW23NoCutTailPackage : Type 1 where
  noCut : W31ConcreteNoCutTheorem
  tail : W31ConcreteW23ComponentsExceptNoCut noCut

namespace ConcreteW23NoCutTailPackage

def toConcreteW23Components
    (P : ConcreteW23NoCutTailPackage) :
    W31ConcreteW23Components :=
  ConcreteW23ComponentsInhabitationW26.concreteW23ComponentsOfNoCutTail
    (noCut := P.noCut)
    P.tail

end ConcreteW23NoCutTailPackage

def concreteW23NoCutTailPackageOfNoCutTail
    (noCut : W31ConcreteNoCutTheorem)
    (tail : W31ConcreteW23ComponentsExceptNoCut noCut) :
    ConcreteW23NoCutTailPackage where
  noCut := noCut
  tail := tail

theorem concreteW23NoCutTailPackage_nonempty_iff_noCut_tail :
    Nonempty ConcreteW23NoCutTailPackage <->
      exists noCut : W31ConcreteNoCutTheorem,
        Nonempty (W31ConcreteW23ComponentsExceptNoCut noCut) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.noCut (Nonempty.intro P.tail)
  case mpr =>
    intro h
    cases h with
    | intro noCut htail =>
        cases htail with
        | intro tail =>
            exact
              Nonempty.intro
                (concreteW23NoCutTailPackageOfNoCutTail noCut tail)

theorem concreteW23NoCutTailPackage_nonempty_iff_concreteW23Components :
    Nonempty ConcreteW23NoCutTailPackage <->
      Nonempty W31ConcreteW23Components :=
  concreteW23NoCutTailPackage_nonempty_iff_noCut_tail.trans
    ExtractedComponentsInhabitationW31.concreteW23Components_nonempty_iff_noCut_tail.symm

theorem not_concreteW23NoCutTailPackage_iff_not_concreteW23Components :
    Not (Nonempty ConcreteW23NoCutTailPackage) <->
      Not (Nonempty W31ConcreteW23Components) :=
  not_congr concreteW23NoCutTailPackage_nonempty_iff_concreteW23Components

structure ConcreteW23NotBlockerTailPackage : Type 1 where
  notBlocker : Not W31MinimalCutVertexBlockerExists
  tail :
    W31ConcreteW23ComponentsExceptNoCut
      (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
        notBlocker)

namespace ConcreteW23NotBlockerTailPackage

def toNoCutTailPackage
    (P : ConcreteW23NotBlockerTailPackage) :
    ConcreteW23NoCutTailPackage where
  noCut :=
    ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
      P.notBlocker
  tail := P.tail

def toConcreteW23Components
    (P : ConcreteW23NotBlockerTailPackage) :
    W31ConcreteW23Components :=
  P.toNoCutTailPackage.toConcreteW23Components

end ConcreteW23NotBlockerTailPackage

def concreteW23NotBlockerTailPackageOfTail
    (h : Not W31MinimalCutVertexBlockerExists)
    (tail :
      W31ConcreteW23ComponentsExceptNoCut
        (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
          h)) :
    ConcreteW23NotBlockerTailPackage where
  notBlocker := h
  tail := tail

theorem concreteW23NotBlockerTailPackage_nonempty_iff_notBlocker_tail :
    Nonempty ConcreteW23NotBlockerTailPackage <->
      exists h : Not W31MinimalCutVertexBlockerExists,
        Nonempty
          (W31ConcreteW23ComponentsExceptNoCut
            (ConcreteW23ComponentsInhabitationW26.noCutComponentOfNotCutVertexBlocker
              h)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.notBlocker (Nonempty.intro P.tail)
  case mpr =>
    intro h
    cases h with
    | intro hnot htail =>
        cases htail with
        | intro tail =>
            exact
              Nonempty.intro
                (concreteW23NotBlockerTailPackageOfTail hnot tail)

theorem concreteW23NotBlockerTailPackage_nonempty_iff_concreteW23Components :
    Nonempty ConcreteW23NotBlockerTailPackage <->
      Nonempty W31ConcreteW23Components :=
  concreteW23NotBlockerTailPackage_nonempty_iff_notBlocker_tail.trans
    ExtractedComponentsInhabitationW31.concreteW23Components_nonempty_iff_notBlocker_tail.symm

structure ConcreteW23CutVertexContradictionTailPackage : Type 1 where
  contradiction : W31MinimalFailureCutVertexContradictionFamily
  tail :
    W31ConcreteW23ComponentsExceptNoCut
      (ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
        contradiction)

namespace ConcreteW23CutVertexContradictionTailPackage

def toNoCutTailPackage
    (P : ConcreteW23CutVertexContradictionTailPackage) :
    ConcreteW23NoCutTailPackage where
  noCut :=
    ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
      P.contradiction
  tail := P.tail

def toConcreteW23Components
    (P : ConcreteW23CutVertexContradictionTailPackage) :
    W31ConcreteW23Components :=
  P.toNoCutTailPackage.toConcreteW23Components

end ConcreteW23CutVertexContradictionTailPackage

def concreteW23CutVertexContradictionTailPackageOfTail
    (H : W31MinimalFailureCutVertexContradictionFamily)
    (tail :
      W31ConcreteW23ComponentsExceptNoCut
        (ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
          H)) :
    ConcreteW23CutVertexContradictionTailPackage where
  contradiction := H
  tail := tail

theorem concreteW23CutVertexContradictionTailPackage_nonempty_iff_cutVertexContradiction_tail :
    Nonempty ConcreteW23CutVertexContradictionTailPackage <->
      exists H : W31MinimalFailureCutVertexContradictionFamily,
        Nonempty
          (W31ConcreteW23ComponentsExceptNoCut
            (ConcreteW23ComponentsInhabitationW26.noCutComponentOfCutVertexContradictionFamily
              H)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.contradiction (Nonempty.intro P.tail)
  case mpr =>
    intro h
    cases h with
    | intro H htail =>
        cases htail with
        | intro tail =>
            exact
              Nonempty.intro
                (concreteW23CutVertexContradictionTailPackageOfTail H tail)

theorem concreteW23CutVertexContradictionTailPackage_nonempty_iff_concreteW23Components :
    Nonempty ConcreteW23CutVertexContradictionTailPackage <->
      Nonempty W31ConcreteW23Components :=
  open ExtractedComponentsInhabitationW31 in
  concreteW23CutVertexContradictionTailPackage_nonempty_iff_cutVertexContradiction_tail.trans
    concreteW23Components_nonempty_iff_cutVertexContradiction_tail.symm

end

end ExtractedComponentsConcreteClosureW32
end Swanepoel

namespace Verified

open Swanepoel.ExtractedComponentsConcreteClosureW32

universe u

abbrev SwanepoelW32ConcreteExtractedComponentClosurePackage :
    Type (u + 1) :=
  ConcreteExtractedComponentClosurePackage.{u}

abbrev SwanepoelW32ActualTopologyExtractedComponentClosurePackage :
    Type (u + 1) :=
  ActualTopologyExtractedComponentClosurePackage.{u}

abbrev SwanepoelW32ConcreteW23NoCutTailPackage : Type 1 :=
  ConcreteW23NoCutTailPackage

theorem swanepoelW32_actualTopologyClosure_exactly_concreteClosure :
    Nonempty SwanepoelW32ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty SwanepoelW32ConcreteExtractedComponentClosurePackage.{u} :=
  actualTopologyClosurePackage_nonempty_iff_concreteClosurePackage

theorem swanepoelW32_actualTopologyClosure_exactly_w31ExtractedWitnessComponentFamily :
    Nonempty SwanepoelW32ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty W31ExtractedWitnessComponentFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_extractedWitnessComponentFamily

theorem swanepoelW32_concreteClosure_of_actualSelectedTopologyClosure
    (h : Nonempty SwanepoelW32ActualTopologyExtractedComponentClosurePackage.{u}) :
    Nonempty SwanepoelW32ConcreteExtractedComponentClosurePackage.{u} :=
  concreteClosurePackage_nonempty_of_actualTopologyClosurePackage h

theorem swanepoelW32_concreteClosure_exactly_w31BoundaryRemainingComponentFamily :
    Nonempty SwanepoelW32ConcreteExtractedComponentClosurePackage.{u} <->
      Nonempty
        W31BoundaryRemainingComponentFamily.{u} :=
  concreteClosurePackage_nonempty_iff_boundaryRemainingComponentFamily

theorem swanepoelW32_concreteClosure_exactly_w31SelectedFaceWitnessFamily :
    Nonempty SwanepoelW32ConcreteExtractedComponentClosurePackage.{u} <->
      Nonempty
        W31SelectedFaceWitnessFamily.{u} :=
  concreteClosurePackage_nonempty_iff_selectedFaceWitnessFamily

theorem swanepoelW32_actualTopologyClosure_exactly_w31BoundaryRemainingComponentFamily :
    Nonempty SwanepoelW32ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty
        W31BoundaryRemainingComponentFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_boundaryRemainingComponentFamily

theorem swanepoelW32_actualTopologyClosure_exactly_w31SelectedFaceWitnessFamily :
    Nonempty SwanepoelW32ActualTopologyExtractedComponentClosurePackage.{u} <->
      Nonempty
        W31SelectedFaceWitnessFamily.{u} :=
  actualTopologyClosurePackage_nonempty_iff_selectedFaceWitnessFamily

theorem swanepoelW32_missing_concreteClosure_exactly_missing_w31BoundaryRemainingComponentFamily :
    Not (Nonempty SwanepoelW32ConcreteExtractedComponentClosurePackage.{u}) <->
      Not
        (Nonempty
          W31BoundaryRemainingComponentFamily.{u}) :=
  not_concreteClosurePackage_iff_not_boundaryRemainingComponentFamily

theorem swanepoelW32_w23NoCutTailPackage_exactly_w31ConcreteW23Components :
    Nonempty SwanepoelW32ConcreteW23NoCutTailPackage <->
      Nonempty
        W31ConcreteW23Components :=
  concreteW23NoCutTailPackage_nonempty_iff_concreteW23Components

end Verified
end ErdosProblems1066
