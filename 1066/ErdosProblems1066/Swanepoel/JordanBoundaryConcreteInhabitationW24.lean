import ErdosProblems1066.Swanepoel.JordanBoundaryFamiliesConcreteW23
import ErdosProblems1066.Swanepoel.BoundaryWalkFinitePartitions
import ErdosProblems1066.Swanepoel.TopologySourceInhabitationW21
import ErdosProblems1066.Swanepoel.TopologyArcClosureW19
import ErdosProblems1066.Swanepoel.TriangleRunSelectorW17

set_option autoImplicit false

/-!
# W24 concrete Jordan-boundary witness bridge

This module isolates the concrete boundary-topology witness still needed to
inhabit the Jordan/boundary source families without postulating a global
triangle-run theorem.

The witness is deliberately exact: concrete Jordan topology, concrete
boundary-walk classification and angle comparisons, subpolygon data, long-arc
data, and the thirteen-edge triangular boundary run over the same planar
boundary.  From that data we build the W21/W23 topology families, the actual
topology-arc input family, and the boundary counting/bookkeeping inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace JordanBoundaryConcreteInhabitationW24

open BoundaryArcFiniteWalkConstructionW16
open BoundaryWalkClassificationConcrete
open JordanBoundaryFamiliesConcreteW23

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryFamiliesConcreteW23.CanonicalGraph C

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  JordanBoundaryFamiliesConcreteW23.ConcreteTopologyFacts C

abbrev ConcreteBoundaryWalkClassification
    (C : _root_.UDConfig n) (T : ConcreteTopologyFacts C) :=
  JordanBoundaryFamiliesConcreteW23.ConcreteBoundaryWalkClassification C T

abbrev W21NamedRowDependency
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  TopologySourceInhabitationW21.NamedTopologyArcRowDependency.{u} C hmin

abbrev W21NamedDependency : Type (u + 1) :=
  TopologySourceInhabitationW21.NamedTopologyArcDependency.{u}

abbrev W21ActualInputsFamily : Type (u + 1) :=
  TopologySourceInhabitationW21.ActualInputsFamily.{u}

abbrev W19TopologyArcSourceFields
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Type (u + 1) :=
  TopologyArcClosureW19.MinimalFailureTopologyArcSourceFields.{u} C hmin

/-! ## Pointwise minimal witness -/

/--
The exact concrete row still needed to inhabit the Jordan-boundary triangle-run
and extraction families.

All fields are concrete project surfaces.  In particular, noncrossing is
already provided by `FaceReduction` for the canonical graph; this witness only
supplies the remaining boundary topology/counting/long-arc/run data.
-/
structure MinimalBoundaryTopologyWitness
    (C : _root_.UDConfig n)
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C) where
  topology : ConcreteTopologyFacts C
  classification : ConcreteBoundaryWalkClassification C topology
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
  triangleRun :
    BoundaryArcTriangleRun
      (topology.toPlanarBoundaryData
        (classification.toOuterBoundaryWalkBookkeeping
          |>.toBoundaryBookkeepingAngleBounds geometricAngleSum
            forced_le_geometric geometric_le_polygon)
        Subpolygon subpolygonData)

namespace MinimalBoundaryTopologyWitness

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def canonicalGraphPairwiseNoncrossing
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  P.topology.pairwiseNoncrossing

def outerAngleBounds
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  P.classification.toOuterBoundaryWalkBookkeeping
    |>.toBoundaryBookkeepingAngleBounds P.geometricAngleSum
      P.forced_le_geometric P.geometric_le_polygon

def planarBoundary
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

@[simp]
theorem outerAngleBounds_counts
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.outerAngleBounds.counts = P.classification.counts :=
  rfl

@[simp]
theorem planarBoundary_core
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.planarBoundary.core = P.topology.toCore :=
  rfl

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.planarBoundary.outerBoundaryCounts = P.classification.counts :=
  rfl

def toBoundaryWalkBudgetSourceFields
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundarySourceInhabitationW22.ConcreteBoundaryWalkBudgetSourceFields.{u}
      C hmin where
  topology := P.topology
  classification := P.classification
  geometricAngleSum := P.geometricAngleSum
  forced_le_geometric := P.forced_le_geometric
  geometric_le_polygon := P.geometric_le_polygon
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc

def toBudgetSourceFields
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryBudgetSourceFields.{u}
      C hmin :=
  P.toBoundaryWalkBudgetSourceFields.toBudgetSourceFields

def toConcreteTriangleRunSourceFields
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryTriangleRunSourceFields.{u}
      C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toConcreteExtractionSourceFields
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    JordanBoundarySourceInhabitationW22.ConcreteJordanBoundaryExtractionSourceFields.{u}
      C hmin :=
  P.toConcreteTriangleRunSourceFields.toExtractionSourceFields

def toW19TopologyArcSourceFields
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    W19TopologyArcSourceFields.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toW21NamedRowDependency
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    W21NamedRowDependency.{u} C hmin where
  topology := P.topology
  outerAngleBounds := P.outerAngleBounds
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := P.longArc
  triangleRun := P.triangleRun

def toActualTopologyArcInputs
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    TopologyArcClosureW19.ActualTopologyArcInputs.{u} C :=
  P.toW19TopologyArcSourceFields.toActualTopologyArcInputs

def finiteWalk
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkData
      P.toActualTopologyArcInputs.planarBoundary :=
  P.triangleRun.toFiniteWalkData

@[simp]
theorem toBoundaryWalkBudgetSourceFields_outerAngleBounds
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toBoundaryWalkBudgetSourceFields.outerAngleBounds =
      P.outerAngleBounds :=
  rfl

@[simp]
theorem toConcreteTriangleRunSourceFields_planarBoundary
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toConcreteTriangleRunSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toConcreteExtractionSourceFields_planarBoundary
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toConcreteExtractionSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toW19TopologyArcSourceFields_planarBoundary
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toW19TopologyArcSourceFields.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem toActualTopologyArcInputs_boundaryArc
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.toActualTopologyArcInputs.boundaryArc =
      P.triangleRun.toFiniteWalkData.toBoundaryArcCertificate :=
  rfl

/-! ## Boundary counting and bookkeeping projections -/

def boundaryBookkeeping
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    BoundaryClassification.BoundaryBookkeeping.{0} :=
  P.classification.boundaryBookkeeping

def boundaryCounts
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    BoundaryCounting.BoundaryCounts :=
  P.classification.counts

def countsRealization
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    BoundaryClassification.BoundaryCountsRealization.{0} :=
  P.classification.countsRealization

def countsRealizationLift
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    BoundaryClassification.BoundaryCountsRealization.{u} :=
  P.classification.countsRealizationLift

@[simp]
theorem countsRealization_toBoundaryCounts
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.countsRealization.toBoundaryCounts = P.boundaryCounts :=
  rfl

@[simp]
theorem countsRealizationLift_toBoundaryCounts
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.countsRealizationLift.toBoundaryCounts = P.boundaryCounts :=
  rfl

theorem edgeCount_partition
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryBookkeeping.triangleEdgeCount + P.boundaryCounts.b =
      P.topology.toCore.outerCycle.length :=
  P.classification.boundaryBookkeeping_triangleEdgeCount_add_counts_b

theorem degreeCount_partition
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryCounts.d3 + P.boundaryCounts.d4 +
        P.boundaryCounts.d5 + P.boundaryCounts.d6 =
      P.topology.toCore.outerCycle.length :=
  P.classification.counts_degree_sum_eq_length

@[simp]
theorem boundaryCounts_d3
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryCounts.d3 =
      Fintype.card P.classification.degree3Indices := by
  exact P.classification.counts_d3

@[simp]
theorem boundaryCounts_d4
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryCounts.d4 =
      Fintype.card P.classification.degree4Indices := by
  exact P.classification.counts_d4

@[simp]
theorem boundaryCounts_d5
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryCounts.d5 =
      Fintype.card P.classification.degree5Indices := by
  exact P.classification.counts_d5

@[simp]
theorem boundaryCounts_d6
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryCounts.d6 =
      Fintype.card P.classification.degree6Indices := by
  exact P.classification.counts_d6

@[simp]
theorem boundaryCounts_b
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryCounts.b =
      Fintype.card P.classification.nontriangleEdgeIndices := by
  exact P.classification.counts_b

@[simp]
theorem boundaryCounts_B
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    P.boundaryCounts.B =
      Fintype.card P.classification.longArcIndices := by
  exact P.classification.counts_B

end MinimalBoundaryTopologyWitness

/-! ## Family bridge -/

structure MinimalBoundaryTopologyWitnessFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        MinimalBoundaryTopologyWitness.{u} C hmin

namespace MinimalBoundaryTopologyWitnessFamily

def toBoundaryWalkBudgetSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    BoundaryWalkBudgetSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toBoundaryWalkBudgetSourceFields

def toConcreteTriangleRunSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ConcreteTriangleRunSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toConcreteTriangleRunSourceFields

def toConcreteExtractionSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ConcreteExtractionSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toConcreteExtractionSourceFields

def toW19TopologyArcSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u} where
  row := fun C hmin => (F.row C hmin).toW19TopologyArcSourceFields

def toW21TriangleRunSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    W21TriangleRunSourceFamily.{u} :=
  w21TriangleRunSourceFamilyOfConcrete F.toConcreteTriangleRunSourceFamily

def toW21ExtractionSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    W21ExtractionSourceFamily.{u} :=
  w21ExtractionSourceFamilyOfConcrete F.toConcreteExtractionSourceFamily

def toW21NamedDependency
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    W21NamedDependency.{u} where
  row := fun C hmin => (F.row C hmin).toW21NamedRowDependency

def toActualInputsFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    ActualInputsFamily.{u} :=
  actualInputsFamilyOfConcreteTriangleRunSourceFamily
    F.toConcreteTriangleRunSourceFamily

def toW21ActualInputsFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    W21ActualInputsFamily.{u} :=
  F.toW21NamedDependency.toActualInputsFamily

@[simp]
theorem toConcreteExtractionSourceFamily_eq
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    F.toConcreteExtractionSourceFamily =
      concreteExtractionSourceFamilyOfConcreteTriangleRunSourceFamily
        F.toConcreteTriangleRunSourceFamily := by
  cases F
  rfl

@[simp]
theorem toActualInputsFamily_eq_w21
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    F.toActualInputsFamily = F.toW21ActualInputsFamily := by
  cases F
  rfl

theorem nonempty_boundaryWalkBudgetSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty BoundaryWalkBudgetSourceFamily.{u} :=
  Nonempty.intro F.toBoundaryWalkBudgetSourceFamily

theorem nonempty_concreteTriangleRunSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ConcreteTriangleRunSourceFamily.{u} :=
  Nonempty.intro F.toConcreteTriangleRunSourceFamily

theorem nonempty_concreteExtractionSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ConcreteExtractionSourceFamily.{u} :=
  Nonempty.intro F.toConcreteExtractionSourceFamily

theorem nonempty_w21TriangleRunSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21TriangleRunSourceFamily.{u} :=
  Nonempty.intro F.toW21TriangleRunSourceFamily

theorem nonempty_w21ExtractionSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21ExtractionSourceFamily.{u} :=
  Nonempty.intro F.toW21ExtractionSourceFamily

theorem nonempty_w21NamedDependency
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21NamedDependency.{u} :=
  Nonempty.intro F.toW21NamedDependency

theorem nonempty_actualInputsFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ActualInputsFamily.{u} :=
  Nonempty.intro F.toActualInputsFamily

theorem nonempty_w21ActualInputsFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21ActualInputsFamily.{u} :=
  Nonempty.intro F.toW21ActualInputsFamily

theorem nonempty_w19TopologyArcSourceFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty TopologyArcClosureW19.MinimalFailureTopologyArcSourceFamily.{u} :=
  Nonempty.intro F.toW19TopologyArcSourceFamily

end MinimalBoundaryTopologyWitnessFamily

/-! ## Nonempty bridge facade -/

theorem concreteTriangleRunSourceFamily_nonempty_of_minimalBoundaryTopologyWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ConcreteTriangleRunSourceFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_concreteTriangleRunSourceFamily

theorem concreteExtractionSourceFamily_nonempty_of_minimalBoundaryTopologyWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ConcreteExtractionSourceFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_concreteExtractionSourceFamily

theorem namedDependency_nonempty_of_minimalBoundaryTopologyWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty NamedDependency.{u} := by
  cases h with
  | intro F =>
      exact
        Nonempty.intro
          (namedDependencyOfConcreteTriangleRunSourceFamily
            F.toConcreteTriangleRunSourceFamily)

theorem actualInputsFamily_nonempty_of_minimalBoundaryTopologyWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty ActualInputsFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_actualInputsFamily

theorem w21NamedDependency_nonempty_of_minimalBoundaryTopologyWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21NamedDependency.{u} := by
  cases h with
  | intro F => exact F.nonempty_w21NamedDependency

theorem w21ActualInputsFamily_nonempty_of_minimalBoundaryTopologyWitness
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty W21ActualInputsFamily.{u} := by
  cases h with
  | intro F => exact F.nonempty_w21ActualInputsFamily

end

end JordanBoundaryConcreteInhabitationW24
end Swanepoel

namespace Verified

universe u

abbrev SwanepoelW24MinimalBoundaryTopologyWitnessFamily : Type (u + 1) :=
  Swanepoel.JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u}

theorem swanepoelW24_concreteTriangleRunSourceFamily_nonempty
    (h : Nonempty SwanepoelW24MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty
      Swanepoel.JordanBoundaryFamiliesConcreteW23.ConcreteTriangleRunSourceFamily.{u} :=
  Swanepoel.JordanBoundaryConcreteInhabitationW24.concreteTriangleRunSourceFamily_nonempty_of_minimalBoundaryTopologyWitness
    h

theorem swanepoelW24_concreteExtractionSourceFamily_nonempty
    (h : Nonempty SwanepoelW24MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty
      Swanepoel.JordanBoundaryFamiliesConcreteW23.ConcreteExtractionSourceFamily.{u} :=
  Swanepoel.JordanBoundaryConcreteInhabitationW24.concreteExtractionSourceFamily_nonempty_of_minimalBoundaryTopologyWitness
    h

theorem swanepoelW24_actualInputsFamily_nonempty
    (h : Nonempty SwanepoelW24MinimalBoundaryTopologyWitnessFamily.{u}) :
    Nonempty
      Swanepoel.JordanBoundaryFamiliesConcreteW23.ActualInputsFamily.{u} :=
  Swanepoel.JordanBoundaryConcreteInhabitationW24.actualInputsFamily_nonempty_of_minimalBoundaryTopologyWitness
    h

end Verified
end ErdosProblems1066
