import ErdosProblems1066.Swanepoel.BoundaryTopologySourceW21
import ErdosProblems1066.Swanepoel.BoundaryWalkFinitePartitions
import ErdosProblems1066.Swanepoel.TopologyExtractionFromNoncrossing

set_option autoImplicit false

/-!
# W22 Jordan-boundary source inhabitation

This file keeps the W21 Jordan-boundary source families honest while routing
them through the concrete Jordan/topology and boundary-walk surfaces.  The
remaining non-topological row data are still explicit: angle bounds,
subpolygon data, long-arc data, and either a W16 triangular boundary run or a
W16 theorem producing one.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanBoundarySourceInhabitationW22

open BoundaryArcFiniteWalkConstructionW16
open BoundaryTopologySourceW21

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanTopologyFactsConcrete.canonicalGraph C

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  JordanTopologyFactsConcrete.TopologyFacts.{0} C

abbrev TriangleRunSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryTriangleRunSourceFields.{u}
    C hmin

abbrev ExtractionSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryExtractionSourceFields.{u}
    C hmin

abbrev TriangleRunSourceFamily : Type (u + 1) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryTriangleRunSourceFamily.{u}

abbrev ExtractionSourceFamily : Type (u + 1) :=
  BoundaryTopologySourceW21.MinimalFailureJordanBoundaryExtractionSourceFamily.{u}

/-! ## Concrete topology frontier adapters -/

theorem splitExactTopologyFields_iff_concreteTopologyFacts
    (C : _root_.UDConfig n) :
    TopologyExtractionFromNoncrossing.SplitExactTopologyFields C <->
      Nonempty (ConcreteTopologyFacts C) :=
  Iff.trans
    (TopologyExtractionFromNoncrossing.splitExactTopologyFields_iff_exactTopologyFields
      C)
    (Iff.trans
      (OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_exactTopologyFields
        C).symm
      (OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_topologyFacts
        C))

theorem concreteTopologyFacts_of_frontier
    {C : _root_.UDConfig n}
    (h :
      TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C) :
    Nonempty (ConcreteTopologyFacts C) :=
  (splitExactTopologyFields_iff_concreteTopologyFacts C).1 h.2

theorem concreteTopologyFacts_of_outerBoundaryCore
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    Nonempty (ConcreteTopologyFacts C) :=
  Nonempty.intro (JordanTopologyFactsConcrete.TopologyFacts.ofCore P)

/-! ## Pointwise source rows without duplicating the Jordan extraction data -/

structure ConcreteJordanBoundaryTriangleRunSourceFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  topology : ConcreteTopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
  triangleRun :
    BoundaryArcTriangleRun
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace ConcreteJordanBoundaryTriangleRunSourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def planarBoundary
    (P : ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def toW21SourceFields
    (P : ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    TriangleRunSourceFields.{u} C hmin where
  jordan := P.topology.toExtractionData
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := by
    change
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
            P.topology.toExtractionData).toPlanarBoundaryData
          P.outerAngleBounds P.Subpolygon P.subpolygonData)
    rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]
    exact P.longArc
  triangleRun := by
    change
      BoundaryArcTriangleRun
        ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
            P.topology.toExtractionData).toPlanarBoundaryData
          P.outerAngleBounds P.Subpolygon P.subpolygonData)
    rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]
    exact P.triangleRun

def ofW21SourceFields
    (P : TriangleRunSourceFields.{u} C hmin) :
    ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

@[simp]
theorem toW21SourceFields_planarBoundary
    (P : ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    P.toW21SourceFields.planarBoundary = P.planarBoundary := by
  change
    ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
        P.topology.toExtractionData).toPlanarBoundaryData
      P.outerAngleBounds P.Subpolygon P.subpolygonData) =
        P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
          P.subpolygonData
  rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]

theorem nonempty_w21SourceFields
    (P : ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    Nonempty (TriangleRunSourceFields.{u} C hmin) :=
  Nonempty.intro P.toW21SourceFields

end ConcreteJordanBoundaryTriangleRunSourceFields

structure ConcreteJordanBoundaryExtractionSourceFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  topology : ConcreteTopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)
  arcExtraction :
    TopologyToBoundaryArcW14.BoundaryArcExtractionFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace ConcreteJordanBoundaryExtractionSourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def planarBoundary
    (P : ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def triangleRun
    (P : ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin) :
    BoundaryArcTriangleRun P.planarBoundary :=
  TriangleRunSelectorW17.BoundaryArcSelector.triangleRunOfExtractionFields
    P.arcExtraction

def toW21SourceFields
    (P : ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin) :
    ExtractionSourceFields.{u} C hmin where
  jordan := P.topology.toExtractionData
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := by
    change
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
            P.topology.toExtractionData).toPlanarBoundaryData
          P.outerAngleBounds P.Subpolygon P.subpolygonData)
    rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]
    exact P.longArc
  arcExtraction := by
    change
      TopologyToBoundaryArcW14.BoundaryArcExtractionFields
        ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
            P.topology.toExtractionData).toPlanarBoundaryData
          P.outerAngleBounds P.Subpolygon P.subpolygonData)
    rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]
    exact P.arcExtraction

def toTriangleRunSourceFields
    (P : ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin) :
    ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def ofW21SourceFields
    (P : ExtractionSourceFields.{u} C hmin) :
    ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  arcExtraction := P.arcExtraction

@[simp]
theorem toW21SourceFields_planarBoundary
    (P : ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin) :
    P.toW21SourceFields.planarBoundary = P.planarBoundary := by
  change
    ((JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData
        P.topology.toExtractionData).toPlanarBoundaryData
      P.outerAngleBounds P.Subpolygon P.subpolygonData) =
        P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
          P.subpolygonData
  rw [JordanTopologyFactsConcrete.TopologyFacts.ofExtractionData_toExtractionData]

@[simp]
theorem triangleRun_pIndex
    (P : ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin)
    (i : M8LabelsFromBoundaryInterface.M8BoundaryIndex) :
    P.triangleRun.pIndex i = P.arcExtraction.boundaryArc.pIndex i :=
  rfl

theorem nonempty_w21SourceFields
    (P : ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin) :
    Nonempty (ExtractionSourceFields.{u} C hmin) :=
  Nonempty.intro P.toW21SourceFields

end ConcreteJordanBoundaryExtractionSourceFields

namespace ConcreteJordanBoundaryTriangleRunSourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def toExtractionSourceFields
    (P : ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin) :
    ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  arcExtraction := P.triangleRun.toFiniteWalkData.toBoundaryArcExtractionFields

end ConcreteJordanBoundaryTriangleRunSourceFields

/-! ## Family conversions -/

structure ConcreteJordanBoundaryTriangleRunSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin

namespace ConcreteJordanBoundaryTriangleRunSourceFamily

def toW21SourceFamily
    (F : ConcreteJordanBoundaryTriangleRunSourceFamily.{u}) :
    TriangleRunSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toW21SourceFields

theorem nonempty_w21SourceFamily
    (F : ConcreteJordanBoundaryTriangleRunSourceFamily.{u}) :
    Nonempty TriangleRunSourceFamily.{u} :=
  Nonempty.intro F.toW21SourceFamily

end ConcreteJordanBoundaryTriangleRunSourceFamily

structure ConcreteJordanBoundaryExtractionSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin

namespace ConcreteJordanBoundaryExtractionSourceFamily

def toW21SourceFamily
    (F : ConcreteJordanBoundaryExtractionSourceFamily.{u}) :
    ExtractionSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toW21SourceFields

def toTriangleRunSourceFamily
    (F : ConcreteJordanBoundaryExtractionSourceFamily.{u}) :
    ConcreteJordanBoundaryTriangleRunSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toTriangleRunSourceFields

theorem nonempty_w21SourceFamily
    (F : ConcreteJordanBoundaryExtractionSourceFamily.{u}) :
    Nonempty ExtractionSourceFamily.{u} :=
  Nonempty.intro F.toW21SourceFamily

end ConcreteJordanBoundaryExtractionSourceFamily

namespace ConcreteJordanBoundaryTriangleRunSourceFamily

def toExtractionSourceFamily
    (F : ConcreteJordanBoundaryTriangleRunSourceFamily.{u}) :
    ConcreteJordanBoundaryExtractionSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toExtractionSourceFields

end ConcreteJordanBoundaryTriangleRunSourceFamily

def concreteTriangleRunSourceFamilyOfW21
    (F : TriangleRunSourceFamily.{u}) :
    ConcreteJordanBoundaryTriangleRunSourceFamily.{u} where
  row := fun C hmin =>
    ConcreteJordanBoundaryTriangleRunSourceFields.ofW21SourceFields
      (F.row C hmin)

def concreteExtractionSourceFamilyOfW21
    (F : ExtractionSourceFamily.{u}) :
    ConcreteJordanBoundaryExtractionSourceFamily.{u} where
  row := fun C hmin =>
    ConcreteJordanBoundaryExtractionSourceFields.ofW21SourceFields
      (F.row C hmin)

theorem triangleRunSourceFamily_nonempty_iff_concrete :
    Nonempty TriangleRunSourceFamily.{u} <->
      Nonempty ConcreteJordanBoundaryTriangleRunSourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F => exact Nonempty.intro (concreteTriangleRunSourceFamilyOfW21 F)
  case mpr =>
    intro h
    cases h with
    | intro F => exact F.nonempty_w21SourceFamily

theorem extractionSourceFamily_nonempty_iff_concrete :
    Nonempty ExtractionSourceFamily.{u} <->
      Nonempty ConcreteJordanBoundaryExtractionSourceFamily.{u} := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro F => exact Nonempty.intro (concreteExtractionSourceFamilyOfW21 F)
  case mpr =>
    intro h
    cases h with
    | intro F => exact F.nonempty_w21SourceFamily

/-! ## Reduction to concrete budget rows plus the W16 triangle-run theorem -/

structure ConcreteJordanBoundaryBudgetSourceFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  topology : ConcreteTopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields
      (topology.toPlanarBoundaryData outerAngleBounds Subpolygon
        subpolygonData)

namespace ConcreteJordanBoundaryBudgetSourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def planarBoundary
    (P : ConcreteJordanBoundaryBudgetSourceFields.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

def toTriangleRunSourceFields
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (P : ConcreteJordanBoundaryBudgetSourceFields.{u} C hmin) :
    ConcreteJordanBoundaryTriangleRunSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun :=
    Classical.choice
      (Hrun C P.topology P.outerAngleBounds P.Subpolygon
        P.subpolygonData P.longArc)

def toExtractionSourceFields
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (P : ConcreteJordanBoundaryBudgetSourceFields.{u} C hmin) :
    ConcreteJordanBoundaryExtractionSourceFields.{u} C hmin :=
  (P.toTriangleRunSourceFields Hrun).toExtractionSourceFields

end ConcreteJordanBoundaryBudgetSourceFields

structure ConcreteJordanBoundaryBudgetSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ConcreteJordanBoundaryBudgetSourceFields.{u} C hmin

namespace ConcreteJordanBoundaryBudgetSourceFamily

def toTriangleRunSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteJordanBoundaryBudgetSourceFamily.{u}) :
    ConcreteJordanBoundaryTriangleRunSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toTriangleRunSourceFields Hrun

def toExtractionSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteJordanBoundaryBudgetSourceFamily.{u}) :
    ConcreteJordanBoundaryExtractionSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toExtractionSourceFields Hrun

theorem nonempty_triangleRunSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteJordanBoundaryBudgetSourceFamily.{u}) :
    Nonempty TriangleRunSourceFamily.{u} :=
  (F.toTriangleRunSourceFamily Hrun).nonempty_w21SourceFamily

theorem nonempty_extractionSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteJordanBoundaryBudgetSourceFamily.{u}) :
    Nonempty ExtractionSourceFamily.{u} :=
  (F.toExtractionSourceFamily Hrun).nonempty_w21SourceFamily

end ConcreteJordanBoundaryBudgetSourceFamily

/-! ## Boundary-walk angle rows feeding the budget surface -/

structure ConcreteBoundaryWalkBudgetSourceFields
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  topology : ConcreteTopologyFacts C
  classification :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toCore
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
      (topology.toPlanarBoundaryData
        (classification.toOuterBoundaryWalkBookkeeping
          |>.toBoundaryBookkeepingAngleBounds geometricAngleSum
            forced_le_geometric geometric_le_polygon)
        Subpolygon subpolygonData)

namespace ConcreteBoundaryWalkBudgetSourceFields

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def outerAngleBounds
    (P : ConcreteBoundaryWalkBudgetSourceFields.{u} C hmin) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  P.classification.toOuterBoundaryWalkBookkeeping
    |>.toBoundaryBookkeepingAngleBounds P.geometricAngleSum
      P.forced_le_geometric P.geometric_le_polygon

def toBudgetSourceFields
    (P : ConcreteBoundaryWalkBudgetSourceFields.{u} C hmin) :
    ConcreteJordanBoundaryBudgetSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc

@[simp]
theorem outerAngleBounds_counts
    (P : ConcreteBoundaryWalkBudgetSourceFields.{u} C hmin) :
    P.outerAngleBounds.counts = P.classification.counts :=
  rfl

end ConcreteBoundaryWalkBudgetSourceFields

structure ConcreteBoundaryWalkBudgetSourceFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        ConcreteBoundaryWalkBudgetSourceFields.{u} C hmin

namespace ConcreteBoundaryWalkBudgetSourceFamily

def toBudgetSourceFamily
    (F : ConcreteBoundaryWalkBudgetSourceFamily.{u}) :
    ConcreteJordanBoundaryBudgetSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toBudgetSourceFields

theorem nonempty_triangleRunSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteBoundaryWalkBudgetSourceFamily.{u}) :
    Nonempty TriangleRunSourceFamily.{u} :=
  F.toBudgetSourceFamily.nonempty_triangleRunSourceFamily Hrun

theorem nonempty_extractionSourceFamily
    (Hrun : BoundaryArcTriangleRunTheorem.{u})
    (F : ConcreteBoundaryWalkBudgetSourceFamily.{u}) :
    Nonempty ExtractionSourceFamily.{u} :=
  F.toBudgetSourceFamily.nonempty_extractionSourceFamily Hrun

end ConcreteBoundaryWalkBudgetSourceFamily

end

end JordanBoundarySourceInhabitationW22
end Swanepoel
end ErdosProblems1066
