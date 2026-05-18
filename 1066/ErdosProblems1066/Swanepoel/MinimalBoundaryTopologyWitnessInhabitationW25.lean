import ErdosProblems1066.Swanepoel.JordanBoundaryConcreteInhabitationW24
import ErdosProblems1066.Swanepoel.TopologyExtractionFromNoncrossing

set_option autoImplicit false

/-!
# W25 selected-face bridge to the W24 minimal boundary-topology witness

`TopologyExtractionFromNoncrossing` proves the graph/noncrossing side and
splits the remaining topology into a selected outer face and enclosure data.
This file records the exact bridge from those selected-face/enclosure packages
to the W24 `MinimalBoundaryTopologyWitness`.

The selected face and enclosure construct the concrete topology field.  The
fields still needed for the full W24 witness are named in
`RemainingWitnessFields`: boundary-walk classification, angle comparisons,
subpolygon data, long-arc data, and the selected triangular boundary run.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalBoundaryTopologyWitnessInhabitationW25

open BoundaryArcFiniteWalkConstructionW16
open TopologyExtractionFromNoncrossing

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryConcreteInhabitationW24.CanonicalGraph C

abbrev W24TopologyFacts (C : _root_.UDConfig n) :=
  JordanBoundaryConcreteInhabitationW24.ConcreteTopologyFacts C

abbrev W24BoundaryClassification
    (C : _root_.UDConfig n) (T : W24TopologyFacts C) :=
  JordanBoundaryConcreteInhabitationW24.ConcreteBoundaryWalkClassification C T

abbrev W24Witness
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitness.{u}
    C hmin

abbrev W24WitnessFamily : Type (u + 1) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u}

/-! ## Selected face plus enclosure gives the W24 topology field -/

def topologyFactsOfSelectedFace
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    W24TopologyFacts C where
  outerFaceData :=
    { faceBoundary := D.faceBoundary
      outerFace := D.outerFace
      outerFace_isOuter := D.outerFace_isOuter }
  enclosureData :=
    { outerEnclosure := E.outerEnclosure }

@[simp]
theorem topologyFactsOfSelectedFace_faceBoundary
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    (topologyFactsOfSelectedFace D E).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem topologyFactsOfSelectedFace_outerFace
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    (topologyFactsOfSelectedFace D E).outerFace = D.outerFace :=
  rfl

theorem topologyFactsOfSelectedFace_outerFace_isOuter
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    (topologyFactsOfSelectedFace D E).faceBoundary.IsOuterFace
      (topologyFactsOfSelectedFace D E).outerFace :=
  D.outerFace_isOuter

@[simp]
theorem topologyFactsOfSelectedFace_outerEnclosure
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    (topologyFactsOfSelectedFace D E).outerEnclosure =
      E.outerEnclosure :=
  rfl

@[simp]
theorem topologyFactsOfSelectedFace_toCore_faceBoundary
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    (topologyFactsOfSelectedFace D E).toCore.faceBoundary =
      D.faceBoundary :=
  rfl

theorem splitExactTopologyFields_of_selectedFace
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    SplitExactTopologyFields C :=
  Exists.intro D (Nonempty.intro E)

theorem exactTopologyFields_of_selectedFace
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  exactTopologyFields_of_split E

theorem concreteNoncrossingTopologyFrontier_of_selectedFace
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    ConcreteNoncrossingTopologyFrontier C :=
  concreteNoncrossingTopologyFrontier_of_exactTopologyFields
    (exactTopologyFields_of_selectedFace D E)

theorem topologyFacts_nonempty_of_selectedFace
    {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) :
    Nonempty (W24TopologyFacts C) :=
  Nonempty.intro (topologyFactsOfSelectedFace D E)

/-! ## The exact remaining W24 witness fields over that topology -/

structure RemainingWitnessFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (D : SelectedOuterFaceFields C)
    (E : EnclosureFields D) : Type (u + 1) where
  classification :
    W24BoundaryClassification C (topologyFactsOfSelectedFace D E)
  geometricAngleSum : Real
  forced_le_geometric :
    classification.counts.forcedBoundaryAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= classification.counts.polygonAngleSum
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      ((topologyFactsOfSelectedFace D E).toPlanarBoundaryData
        (classification.toOuterBoundaryWalkBookkeeping
          |>.toBoundaryBookkeepingAngleBounds geometricAngleSum
            forced_le_geometric geometric_le_polygon)
        Subpolygon subpolygonData)
  triangleRun :
    BoundaryArcTriangleRun
      ((topologyFactsOfSelectedFace D E).toPlanarBoundaryData
        (classification.toOuterBoundaryWalkBookkeeping
          |>.toBoundaryBookkeepingAngleBounds geometricAngleSum
            forced_le_geometric geometric_le_polygon)
        Subpolygon subpolygonData)

namespace RemainingWitnessFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
variable {D : SelectedOuterFaceFields C}
variable {E : EnclosureFields D}

def outerAngleBounds
    (R : RemainingWitnessFields.{u} C hmin D E) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  R.classification.toOuterBoundaryWalkBookkeeping
    |>.toBoundaryBookkeepingAngleBounds R.geometricAngleSum
      R.forced_le_geometric R.geometric_le_polygon

def planarBoundary
    (R : RemainingWitnessFields.{u} C hmin D E) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  (topologyFactsOfSelectedFace D E).toPlanarBoundaryData
    R.outerAngleBounds R.Subpolygon R.subpolygonData

@[simp]
theorem outerAngleBounds_counts
    (R : RemainingWitnessFields.{u} C hmin D E) :
    R.outerAngleBounds.counts = R.classification.counts :=
  rfl

@[simp]
theorem planarBoundary_core
    (R : RemainingWitnessFields.{u} C hmin D E) :
    R.planarBoundary.core = (topologyFactsOfSelectedFace D E).toCore :=
  rfl

def toW24Witness
    (R : RemainingWitnessFields.{u} C hmin D E) :
    W24Witness.{u} C hmin where
  topology := topologyFactsOfSelectedFace D E
  classification := R.classification
  geometricAngleSum := R.geometricAngleSum
  forced_le_geometric := R.forced_le_geometric
  geometric_le_polygon := R.geometric_le_polygon
  Subpolygon := R.Subpolygon
  subpolygonData := R.subpolygonData
  longArc := R.longArc
  triangleRun := R.triangleRun

@[simp]
theorem toW24Witness_topology
    (R : RemainingWitnessFields.{u} C hmin D E) :
    R.toW24Witness.topology = topologyFactsOfSelectedFace D E :=
  rfl

@[simp]
theorem toW24Witness_classification
    (R : RemainingWitnessFields.{u} C hmin D E) :
    R.toW24Witness.classification = R.classification :=
  rfl

@[simp]
theorem toW24Witness_outerAngleBounds
    (R : RemainingWitnessFields.{u} C hmin D E) :
    R.toW24Witness.outerAngleBounds = R.outerAngleBounds :=
  rfl

@[simp]
theorem toW24Witness_planarBoundary
    (R : RemainingWitnessFields.{u} C hmin D E) :
    R.toW24Witness.planarBoundary = R.planarBoundary :=
  rfl

end RemainingWitnessFields

/-! ## Row and family bridges -/

structure SelectedFaceWitnessRow
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Type (u + 1) where
  selectedFace : SelectedOuterFaceFields C
  enclosure : EnclosureFields selectedFace
  remaining :
    RemainingWitnessFields.{u} C hmin selectedFace enclosure

namespace SelectedFaceWitnessRow

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def topology
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    W24TopologyFacts C :=
  topologyFactsOfSelectedFace R.selectedFace R.enclosure

def toW24Witness
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    W24Witness.{u} C hmin :=
  R.remaining.toW24Witness

@[simp]
theorem toW24Witness_topology
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    R.toW24Witness.topology = R.topology :=
  rfl

theorem nonempty_w24Witness
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    Nonempty (W24Witness.{u} C hmin) :=
  Nonempty.intro R.toW24Witness

end SelectedFaceWitnessRow

theorem w24Witness_nonempty_of_selectedFace_remaining
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R : SelectedFaceWitnessRow.{u} C hmin) :
    Nonempty (W24Witness.{u} C hmin) :=
  R.nonempty_w24Witness

structure SelectedFaceWitnessFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        SelectedFaceWitnessRow.{u} C hmin

namespace SelectedFaceWitnessFamily

def toW24WitnessFamily
    (F : SelectedFaceWitnessFamily.{u}) :
    W24WitnessFamily.{u} where
  row := fun C hmin => (F.row C hmin).toW24Witness

theorem nonempty_w24WitnessFamily
    (F : SelectedFaceWitnessFamily.{u}) :
    Nonempty W24WitnessFamily.{u} :=
  Nonempty.intro F.toW24WitnessFamily

theorem nonempty_concreteTriangleRunSourceFamily
    (F : SelectedFaceWitnessFamily.{u}) :
    Nonempty
      JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{u} :=
  F.toW24WitnessFamily.nonempty_concreteTriangleRunSourceFamily

theorem nonempty_concreteExtractionSourceFamily
    (F : SelectedFaceWitnessFamily.{u}) :
    Nonempty
      JordanBoundaryFamiliesConcreteW23.ConcreteExtractionSourceFamily.{u} :=
  F.toW24WitnessFamily.nonempty_concreteExtractionSourceFamily

theorem nonempty_actualInputsFamily
    (F : SelectedFaceWitnessFamily.{u}) :
    Nonempty JordanBoundaryFamiliesConcreteW23.ActualInputsFamily.{u} :=
  F.toW24WitnessFamily.nonempty_actualInputsFamily

end SelectedFaceWitnessFamily

theorem w24WitnessFamily_nonempty_of_selectedFaceWitnessFamily
    (h : Nonempty SelectedFaceWitnessFamily.{u}) :
    Nonempty W24WitnessFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_w24WitnessFamily

/-!
The fields still not produced by selected-face/enclosure topology alone are
exactly the fields of `RemainingWitnessFields`:

* `classification`
* `geometricAngleSum`
* `forced_le_geometric`
* `geometric_le_polygon`
* `Subpolygon`
* `subpolygonData`
* `longArc`
* `triangleRun`
-/

end

end MinimalBoundaryTopologyWitnessInhabitationW25
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW25SelectedFaceWitnessFamily : Type (u + 1) :=
  Swanepoel.MinimalBoundaryTopologyWitnessInhabitationW25.SelectedFaceWitnessFamily.{u}

abbrev SwanepoelW25MinimalBoundaryTopologyWitnessFamily : Type (u + 1) :=
  Swanepoel.MinimalBoundaryTopologyWitnessInhabitationW25.W24WitnessFamily.{u}

theorem swanepoelW25_minimalBoundaryTopologyWitnessFamily_nonempty
    (h : Nonempty SwanepoelW25SelectedFaceWitnessFamily.{u}) :
    Nonempty SwanepoelW25MinimalBoundaryTopologyWitnessFamily.{u} :=
  Swanepoel.MinimalBoundaryTopologyWitnessInhabitationW25.w24WitnessFamily_nonempty_of_selectedFaceWitnessFamily
    h

end Verified
end ErdosProblems1066
