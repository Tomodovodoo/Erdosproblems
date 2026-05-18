import ErdosProblems1066.Swanepoel.JordanBoundaryConcreteInhabitationW24

set_option autoImplicit false

/-!
# W25 planar topology extraction bridge

This file connects the split topology data exposed by
`TopologyExtractionFromNoncrossing` to the W24 concrete boundary-topology
witness surface.  It contains only constructors and projections: selected
outer-face data plus enclosure data are repackaged as concrete topology facts,
then used as the topology input for boundary-walk classification and W24 source
package rows.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarTopologyExtractionBridgeW25

open BoundaryArcFiniteWalkConstructionW16
open BoundaryWalkClassificationConcrete
open JordanBoundaryConcreteInhabitationW24
open TopologyExtractionFromNoncrossing

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  TopologyExtractionFromNoncrossing.canonicalGraph C

abbrev SelectedOuterFaceData (C : _root_.UDConfig n) :=
  TopologyExtractionFromNoncrossing.SelectedOuterFaceFields C

abbrev SelectedEnclosureData
    {C : _root_.UDConfig n} (D : SelectedOuterFaceData C) :=
  TopologyExtractionFromNoncrossing.EnclosureFields D

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  JordanBoundaryConcreteInhabitationW24.ConcreteTopologyFacts C

abbrev ConcreteBoundaryWalkClassification
    (C : _root_.UDConfig n) (T : ConcreteTopologyFacts C) :=
  JordanBoundaryConcreteInhabitationW24.ConcreteBoundaryWalkClassification C T

/-! ## Outer-face and enclosure projection -/

namespace SelectedOuterFaceData

variable {C : _root_.UDConfig n}

def toJordanOuterFaceData (D : SelectedOuterFaceData C) :
    JordanTopologyFactsConcrete.OuterFaceData (CanonicalGraph C) where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

def toExtractionOuterFaceData (D : SelectedOuterFaceData C) :
    JordanBoundaryExtraction.OuterFaceData (CanonicalGraph C) where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

def planarFaceBoundary (D : SelectedOuterFaceData C) :
    PlanarInterface.FaceBoundaryHypotheses (CanonicalGraph C).toStraightLine :=
  D.faceBoundary.toFaceBoundaryHypotheses

def outerCycle (D : SelectedOuterFaceData C) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
    D.faceBoundary D.outerFace

def outerSimplePolygon (D : SelectedOuterFaceData C) :
    OuterBoundaryInterface.SimplePolygon (CanonicalGraph C) D.outerCycle :=
  OuterBoundaryReduction.BoundaryCycle.simplePolygonOfFaceBoundary
    D.faceBoundary D.outerFace

@[simp]
theorem toJordanOuterFaceData_faceBoundary
    (D : SelectedOuterFaceData C) :
    D.toJordanOuterFaceData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toJordanOuterFaceData_outerFace
    (D : SelectedOuterFaceData C) :
    D.toJordanOuterFaceData.outerFace = D.outerFace :=
  rfl

theorem toJordanOuterFaceData_outerFace_isOuter
    (D : SelectedOuterFaceData C) :
    D.toJordanOuterFaceData.faceBoundary.IsOuterFace
      D.toJordanOuterFaceData.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toExtractionOuterFaceData_faceBoundary
    (D : SelectedOuterFaceData C) :
    D.toExtractionOuterFaceData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem planarFaceBoundary_eq
    (D : SelectedOuterFaceData C) :
    D.planarFaceBoundary = D.faceBoundary.toFaceBoundaryHypotheses :=
  rfl

@[simp]
theorem outerCycle_eq
    (D : SelectedOuterFaceData C) :
    D.outerCycle =
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
        D.faceBoundary D.outerFace :=
  rfl

@[simp]
theorem outerCycle_length
    (D : SelectedOuterFaceData C) :
    D.outerCycle.length = D.faceBoundary.boundaryLength D.outerFace :=
  rfl

theorem outerCycle_vertex_injective
    (D : SelectedOuterFaceData C) :
    Function.Injective D.outerCycle.vertex :=
  D.faceBoundary.boundarySimple D.outerFace

theorem outerCycle_adjacent_unitDistanceAdj
    (D : SelectedOuterFaceData C) (k : Fin D.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (CanonicalGraph C).config
      (D.outerCycle.vertex k)
      (D.outerCycle.vertex
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) :=
  D.outerCycle.adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (D : SelectedOuterFaceData C) (k : Fin D.outerCycle.length) :
    Geometry.Distance.eucDist (D.outerCycle.point k)
      (D.outerCycle.point
        (PlanarInterface.cyclicSucc D.outerCycle.length_pos k)) = 1 :=
  D.outerCycle.edge_geometry_dist_eq_one k

theorem isOuterFace (D : SelectedOuterFaceData C) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.outerFace_isOuter

end SelectedOuterFaceData

namespace SelectedEnclosureData

variable {C : _root_.UDConfig n}
variable {D : SelectedOuterFaceData C}

def toJordanEnclosureData (E : SelectedEnclosureData D) :
    JordanTopologyFactsConcrete.EnclosureData D.toJordanOuterFaceData where
  outerEnclosure := E.outerEnclosure

def toExtractionEnclosureData (E : SelectedEnclosureData D) :
    JordanBoundaryExtraction.EnclosureData D.toExtractionOuterFaceData where
  outerEnclosure := E.outerEnclosure

def toMissingTopologyFacts (E : SelectedEnclosureData D) :
    JordanBoundaryConcrete.MissingTopologyFacts C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := E.outerEnclosure

def toExtractionData (E : SelectedEnclosureData D) :
    JordanBoundaryExtraction.Data (CanonicalGraph C) :=
  E.toMissingTopologyFacts.toExtractionData

def toCore (E : SelectedEnclosureData D) :
    OuterBoundaryCore (CanonicalGraph C) :=
  E.toMissingTopologyFacts.toCore

def toConcreteTopologyFacts (E : SelectedEnclosureData D) :
    ConcreteTopologyFacts C :=
  JordanTopologyFactsConcrete.TopologyFacts.ofMissingTopologyFacts
    E.toMissingTopologyFacts

@[simp]
theorem toJordanEnclosureData_outerEnclosure
    (E : SelectedEnclosureData D) :
    E.toJordanEnclosureData.outerEnclosure = E.outerEnclosure :=
  rfl

@[simp]
theorem toMissingTopologyFacts_faceBoundary
    (E : SelectedEnclosureData D) :
    E.toMissingTopologyFacts.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toMissingTopologyFacts_outerFace
    (E : SelectedEnclosureData D) :
    E.toMissingTopologyFacts.outerFace = D.outerFace :=
  rfl

@[simp]
theorem toMissingTopologyFacts_outerEnclosure
    (E : SelectedEnclosureData D) :
    E.toMissingTopologyFacts.outerEnclosure = E.outerEnclosure :=
  rfl

@[simp]
theorem toCore_faceBoundary
    (E : SelectedEnclosureData D) :
    E.toCore.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace
    (E : SelectedEnclosureData D) :
    E.toCore.outerFace = D.outerFace :=
  rfl

theorem toCore_outerFace_isOuter
    (E : SelectedEnclosureData D) :
    E.toCore.faceBoundary.IsOuterFace E.toCore.outerFace :=
  D.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure
    (E : SelectedEnclosureData D) :
    E.toCore.outerEnclosure = E.outerEnclosure :=
  rfl

@[simp]
theorem toConcreteTopologyFacts_toCore
    (E : SelectedEnclosureData D) :
    E.toConcreteTopologyFacts.toCore = E.toCore :=
  rfl

theorem outerCycle_vertex_onBoundary
    (E : SelectedEnclosureData D) (k : Fin D.outerCycle.length) :
    E.outerEnclosure.onBoundary (D.outerCycle.vertex k) :=
  E.outerEnclosure.boundary_vertex_onBoundary k

theorem outerCycle_point_insideOrOn
    (E : SelectedEnclosureData D) (k : Fin D.outerCycle.length) :
    E.outerEnclosure.insideOrOn (D.outerCycle.point k) :=
  E.outerEnclosure.boundary_point_insideOrOn k

theorem all_vertices_insideOrOn
    (E : SelectedEnclosureData D) (v : Fin n) :
    E.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  E.outerEnclosure.all_vertices_insideOrOn v

theorem onBoundary_iff_outerCycle
    (E : SelectedEnclosureData D) (v : Fin n) :
    E.outerEnclosure.onBoundary v <->
      Exists fun k : Fin D.outerCycle.length => D.outerCycle.vertex k = v :=
  E.outerEnclosure.onBoundary_iff_outer_cycle v

end SelectedEnclosureData

/-! ## Boundary-walk classification over the extracted topology -/

abbrev ExtractedBoundaryWalkClassification
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceData C} (E : SelectedEnclosureData D) :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs E.toCore

namespace ExtractedBoundaryWalkClassification

variable {C : _root_.UDConfig n}
variable {D : SelectedOuterFaceData C}
variable {E : SelectedEnclosureData D}

def toConcreteClassification
    (K : ExtractedBoundaryWalkClassification E) :
    ConcreteBoundaryWalkClassification C E.toConcreteTopologyFacts := by
  exact K

def boundaryBookkeeping
    (K : ExtractedBoundaryWalkClassification E) :
    BoundaryClassification.BoundaryBookkeeping.{0} :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.boundaryBookkeeping
    K

def counts
    (K : ExtractedBoundaryWalkClassification E) :
    BoundaryCounting.BoundaryCounts :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.counts K

def outerAngleBounds
    (K : ExtractedBoundaryWalkClassification E)
    (geometricAngleSum : Real)
    (forced_le_geometric : K.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon : geometricAngleSum <= K.counts.polygonAngleSum) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  K.toOuterBoundaryWalkBookkeeping
    |>.toBoundaryBookkeepingAngleBounds geometricAngleSum
      forced_le_geometric geometric_le_polygon

@[simp]
theorem toConcreteClassification_counts
    (K : ExtractedBoundaryWalkClassification E) :
    K.toConcreteClassification.counts = K.counts :=
  rfl

@[simp]
theorem toConcreteClassification_boundaryBookkeeping
    (K : ExtractedBoundaryWalkClassification E) :
    K.toConcreteClassification.boundaryBookkeeping =
      K.boundaryBookkeeping :=
  rfl

@[simp]
theorem outerAngleBounds_counts
    (K : ExtractedBoundaryWalkClassification E)
    (geometricAngleSum : Real)
    (forced_le_geometric : K.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon : geometricAngleSum <= K.counts.polygonAngleSum) :
    (K.outerAngleBounds geometricAngleSum
      forced_le_geometric geometric_le_polygon).counts = K.counts :=
  rfl

end ExtractedBoundaryWalkClassification

/-! ## W24 witness row sourced from split topology extraction data -/

structure ExtractedMinimalBoundaryTopologyWitness
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  outerFaceData : SelectedOuterFaceData C
  enclosureData : SelectedEnclosureData outerFaceData
  classification : ExtractedBoundaryWalkClassification enclosureData
  geometricAngleSum : Real
  forced_le_geometric :
    classification.counts.forcedBoundaryAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= classification.counts.polygonAngleSum
  Subpolygon : Type u
  subpolygonData :
    Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData
      (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (enclosureData.toConcreteTopologyFacts.toPlanarBoundaryData
        (classification.toOuterBoundaryWalkBookkeeping
          |>.toBoundaryBookkeepingAngleBounds geometricAngleSum
            forced_le_geometric geometric_le_polygon)
        Subpolygon subpolygonData)
  triangleRun :
    BoundaryArcTriangleRun
      (enclosureData.toConcreteTopologyFacts.toPlanarBoundaryData
        (classification.toOuterBoundaryWalkBookkeeping
          |>.toBoundaryBookkeepingAngleBounds geometricAngleSum
            forced_le_geometric geometric_le_polygon)
        Subpolygon subpolygonData)

namespace ExtractedMinimalBoundaryTopologyWitness

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def topology
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    ConcreteTopologyFacts C :=
  P.enclosureData.toConcreteTopologyFacts

def core
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    OuterBoundaryCore (CanonicalGraph C) :=
  P.enclosureData.toCore

def outerCycle
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  P.outerFaceData.outerCycle

def concreteClassification
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    ConcreteBoundaryWalkClassification C P.topology :=
  P.classification.toConcreteClassification

def outerAngleBounds
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  P.classification.toOuterBoundaryWalkBookkeeping
    |>.toBoundaryBookkeepingAngleBounds P.geometricAngleSum
      P.forced_le_geometric P.geometric_le_polygon

def planarBoundary
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def toW24Witness
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitness.{u}
      C hmin where
  topology := P.topology
  classification := P.concreteClassification
  geometricAngleSum := P.geometricAngleSum
  forced_le_geometric := P.forced_le_geometric
  geometric_le_polygon := P.geometric_le_polygon
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

@[simp]
theorem topology_toCore
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.topology.toCore = P.core :=
  rfl

@[simp]
theorem concreteClassification_counts
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.concreteClassification.counts = P.classification.counts :=
  rfl

@[simp]
theorem outerAngleBounds_counts
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.outerAngleBounds.counts = P.classification.counts :=
  rfl

@[simp]
theorem planarBoundary_core
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.planarBoundary.core = P.core :=
  rfl

@[simp]
theorem toW24Witness_topology
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toW24Witness.topology = P.topology :=
  rfl

@[simp]
theorem toW24Witness_classification
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toW24Witness.classification = P.concreteClassification :=
  rfl

@[simp]
theorem toW24Witness_planarBoundary
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toW24Witness.planarBoundary = P.planarBoundary :=
  rfl

def toBoundaryWalkBudgetSourceFields
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundarySourceInhabitationW22.ConcreteBoundaryWalkBudgetSourceFields.{u}
      C hmin :=
  P.toW24Witness.toBoundaryWalkBudgetSourceFields

def toConcreteTriangleRunSourceFields
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryTriangleRunSourceFields.{u}
      C hmin :=
  P.toW24Witness.toConcreteTriangleRunSourceFields

def toConcreteExtractionSourceFields
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryExtractionSourceFields.{u}
      C hmin :=
  P.toW24Witness.toConcreteExtractionSourceFields

def toW19TopologyArcSourceFields
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundaryConcreteInhabitationW24.W19TopologyArcSourceFields.{u}
      C hmin :=
  P.toW24Witness.toW19TopologyArcSourceFields

def toW21NamedRowDependency
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundaryConcreteInhabitationW24.W21NamedRowDependency.{u}
      C hmin :=
  P.toW24Witness.toW21NamedRowDependency

def toActualTopologyArcInputs
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    TopologyArcClosureW19.ActualTopologyArcInputs.{u} C :=
  P.toW24Witness.toActualTopologyArcInputs

@[simp]
theorem toW19TopologyArcSourceFields_planarBoundary
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toW19TopologyArcSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toActualTopologyArcInputs_boundaryArc
    (P : ExtractedMinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

end ExtractedMinimalBoundaryTopologyWitness

/-! ## Family-level source inputs -/

structure ExtractedMinimalBoundaryTopologyWitnessFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ExtractedMinimalBoundaryTopologyWitness.{u} C hmin

namespace ExtractedMinimalBoundaryTopologyWitnessFamily

def toW24WitnessFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u} where
  row := fun C hmin => (F.row C hmin).toW24Witness

def toBoundaryWalkBudgetSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    JordanBoundaryFamiliesConcreteW23.BoundaryWalkBudgetSourceFamily.{u} :=
  F.toW24WitnessFamily.toBoundaryWalkBudgetSourceFamily

def toConcreteTriangleRunSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{u} :=
  F.toW24WitnessFamily.toConcreteTriangleRunSourceFamily

def toConcreteExtractionSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    JordanBoundaryFamiliesConcreteW23.ConcreteExtractionSourceFamily.{u} :=
  F.toW24WitnessFamily.toConcreteExtractionSourceFamily

def toW19TopologyArcSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u} :=
  F.toW24WitnessFamily.toW19TopologyArcSourceFamily

def toW21NamedDependency
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    JordanBoundaryConcreteInhabitationW24.W21NamedDependency.{u} :=
  F.toW24WitnessFamily.toW21NamedDependency

def toActualInputsFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    JordanBoundaryFamiliesConcreteW23.ActualInputsFamily.{u} :=
  F.toW24WitnessFamily.toActualInputsFamily

theorem nonempty_w24WitnessFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro F.toW24WitnessFamily

theorem nonempty_boundaryWalkBudgetSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty JordanBoundaryFamiliesConcreteW23.BoundaryWalkBudgetSourceFamily.{u} :=
  Nonempty.intro F.toBoundaryWalkBudgetSourceFamily

theorem nonempty_concreteTriangleRunSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{u} :=
  Nonempty.intro F.toConcreteTriangleRunSourceFamily

theorem nonempty_concreteExtractionSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty JordanBoundaryFamiliesConcreteW23.ConcreteExtractionSourceFamily.{u} :=
  Nonempty.intro F.toConcreteExtractionSourceFamily

theorem nonempty_w19TopologyArcSourceFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u} :=
  Nonempty.intro F.toW19TopologyArcSourceFamily

theorem nonempty_w21NamedDependency
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty JordanBoundaryConcreteInhabitationW24.W21NamedDependency.{u} :=
  Nonempty.intro F.toW21NamedDependency

theorem nonempty_actualInputsFamily
    (F : ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty JordanBoundaryFamiliesConcreteW23.ActualInputsFamily.{u} :=
  Nonempty.intro F.toActualInputsFamily

end ExtractedMinimalBoundaryTopologyWitnessFamily

theorem w24WitnessFamily_nonempty_of_extracted
    (h : Nonempty ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty
      JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_w24WitnessFamily

theorem w19TopologyArcSourceFamily_nonempty_of_extracted
    (h : Nonempty ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_w19TopologyArcSourceFamily

theorem actualInputsFamily_nonempty_of_extracted
    (h : Nonempty ExtractedMinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty JordanBoundaryFamiliesConcreteW23.ActualInputsFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_actualInputsFamily

end

end PlanarTopologyExtractionBridgeW25
end Swanepoel
end ErdosProblems1066
