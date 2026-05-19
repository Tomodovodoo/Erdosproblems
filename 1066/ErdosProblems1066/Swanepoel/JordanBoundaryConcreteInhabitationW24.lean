import ErdosProblems1066.Swanepoel.JordanBoundaryFamiliesConcreteW23
import ErdosProblems1066.Swanepoel.BoundaryWalkFinitePartitions
import ErdosProblems1066.Swanepoel.BoundaryPartitionInstantiation
import ErdosProblems1066.Swanepoel.Lemma6Lemma7AssemblyW13
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

/-! ## Skeleton rows and the exact remaining field -/

/--
The part of a minimal-boundary topology witness supplied by the selected
topology, boundary classification, angle comparison, and subpolygon rows.

This deliberately stops before the two dependent boundary-arc fields.  It is
the shape produced by the current S2/S3 selected-topology, classification,
angle, and subpolygon sources.
-/
structure MinimalBoundaryTopologySkeleton
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

namespace MinimalBoundaryTopologySkeleton

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

def outerAngleBounds
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  P.classification.toOuterBoundaryWalkBookkeeping
    |>.toBoundaryBookkeepingAngleBounds P.geometricAngleSum
      P.forced_le_geometric P.geometric_le_polygon

def planarBoundary
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topology.toPlanarBoundaryData P.outerAngleBounds P.Subpolygon
    P.subpolygonData

@[simp]
theorem outerAngleBounds_counts
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin) :
    P.outerAngleBounds.counts = P.classification.counts :=
  rfl

@[simp]
theorem planarBoundary_core
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin) :
    P.planarBoundary.core = P.topology.toCore :=
  rfl

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin) :
    P.planarBoundary.outerBoundaryCounts = P.classification.counts :=
  rfl

/--
The exact field still missing from the skeleton: concrete long-arc existence
data and a thirteen-edge triangle run over the same assembled planar boundary.
-/
structure MissingLongArcTriangleRunField
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin) : Type (u + 1) where
  longArc :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      P.planarBoundary
  triangleRun :
    BoundaryArcTriangleRun.{u} P.planarBoundary

namespace MissingLongArcTriangleRunField

variable {P : MinimalBoundaryTopologySkeleton.{u} C hmin}

/-- The nonconcave long arc selected by the long-arc half of the missing field. -/
noncomputable def selectedLongArc
    (M : P.MissingLongArcTriangleRunField) : M.longArc.LongArc :=
  M.longArc.selectedLongArc

/-- The long-arc half of the missing field has positive cardinality. -/
theorem longArcCount_pos
    (M : P.MissingLongArcTriangleRunField) :
    0 < M.longArc.longArcCount :=
  M.longArc.longArcCount_pos

/-- The long-arc type carried by the missing field is inhabited. -/
theorem longArc_nonempty
    (M : P.MissingLongArcTriangleRunField) :
    Nonempty M.longArc.LongArc :=
  M.longArc.longArc_nonempty

/-- The selected arc from the missing field is nonconcave. -/
theorem selectedLongArc_not_concave
    (M : P.MissingLongArcTriangleRunField) :
    Not (M.longArc.concave M.selectedLongArc) :=
  M.longArc.selectedLongArc_not_concave

/-- The selected arc from the missing field has total turn below `pi / 3`. -/
theorem selectedLongArc_totalTurn_lt_pi_div_three
    (M : P.MissingLongArcTriangleRunField) :
    Lemma10Inequalities.totalTurn
        (M.longArc.rawTurn M.selectedLongArc) <
      Real.pi / 3 :=
  M.longArc.selectedLongArc_totalTurn_lt_pi_div_three

/-- Pointwise nonnegativity for the selected raw turn in the missing field. -/
theorem selectedLongArc_rawTurn_nonnegative_on_arc
    (M : P.MissingLongArcTriangleRunField) :
    forall k : Nat,
      Membership.mem Lemma10Inequalities.turnIndexSet k ->
        0 <= M.longArc.rawTurn M.selectedLongArc k :=
  M.longArc.selectedLongArc_rawTurn_nonnegative_on_arc

/-- Existence form of the missing field's selected nonconcave long arc. -/
theorem exists_nonconcave_longArc_with_turn_bounds
    (M : P.MissingLongArcTriangleRunField) :
    Exists fun a : M.longArc.LongArc =>
      And (Not (M.longArc.concave a))
        (And
          (Lemma10Inequalities.totalTurn (M.longArc.rawTurn a) <
            Real.pi / 3)
          (forall k : Nat,
            Membership.mem Lemma10Inequalities.turnIndexSet k ->
              0 <= M.longArc.rawTurn a k)) :=
  M.longArc.exists_nonconcave_longArc_with_turn_bounds

/-- Boundary-budget data selected by the missing field's long-arc half. -/
noncomputable def nonconcaveArcBoundaryBudgetData
    (M : P.MissingLongArcTriangleRunField) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (CanonicalGraph C) :=
  M.longArc.toNonconcaveArcBoundaryBudgetData

@[simp]
theorem nonconcaveArcBoundaryBudgetData_planarBoundary
    (M : P.MissingLongArcTriangleRunField) :
    M.nonconcaveArcBoundaryBudgetData.planarBoundary = P.planarBoundary :=
  rfl

@[simp]
theorem nonconcaveArcBoundaryBudgetData_rawTurn
    (M : P.MissingLongArcTriangleRunField) :
    M.nonconcaveArcBoundaryBudgetData.rawTurn =
      M.longArc.rawTurn M.selectedLongArc :=
  rfl

/-- Construction-level M8 turn bounds produced by the missing field's long arc. -/
def m8TurnBounds
    (M : P.MissingLongArcTriangleRunField) :
    M8ConstructionInterface.M8TurnBounds :=
  M.longArc.toM8TurnBounds

/-- The missing field's M8 turn function is pointwise nonnegative. -/
theorem m8TurnBounds_turn_nonnegative
    (M : P.MissingLongArcTriangleRunField) (k : Nat) :
    0 <= M.m8TurnBounds.turn k :=
  M.longArc.toM8TurnBounds_turn_nonnegative k

/-- The missing field's M8 total turn is below `pi / 3`. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three
    (M : P.MissingLongArcTriangleRunField) :
    Lemma10Inequalities.totalTurn M.m8TurnBounds.turn < Real.pi / 3 :=
  M.longArc.toM8TurnBounds_totalTurn_lt_pi_div_three

/-- The missing field's explicit thirteen-turn M8 sum is below `pi / 3`. -/
theorem m8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three
    (M : P.MissingLongArcTriangleRunField) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
        M.m8TurnBounds.turn < Real.pi / 3 :=
  M.longArc.toM8TurnBounds_m8ThirteenTurnSum_lt_pi_div_three

end MissingLongArcTriangleRunField

def missingFieldOfLongArcTriangleRun
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin)
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
        P.planarBoundary)
    (triangleRun : BoundaryArcTriangleRun.{u} P.planarBoundary) :
    P.MissingLongArcTriangleRunField where
  longArc := longArc
  triangleRun := triangleRun

def toWitness
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin)
    (M : P.MissingLongArcTriangleRunField) :
    MinimalBoundaryTopologyWitness.{u} C hmin where
  topology := P.topology
  classification := P.classification
  geometricAngleSum := P.geometricAngleSum
  forced_le_geometric := P.forced_le_geometric
  geometric_le_polygon := P.geometric_le_polygon
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData
  longArc := M.longArc
  triangleRun := M.triangleRun

def ofWitness
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    MinimalBoundaryTopologySkeleton.{u} C hmin where
  topology := P.topology
  classification := P.classification
  geometricAngleSum := P.geometricAngleSum
  forced_le_geometric := P.forced_le_geometric
  geometric_le_polygon := P.geometric_le_polygon
  Subpolygon := P.Subpolygon
  subpolygonData := P.subpolygonData

def missingFieldOfWitness
    (P : MinimalBoundaryTopologyWitness.{u} C hmin) :
    (ofWitness P).MissingLongArcTriangleRunField :=
  { longArc := P.longArc
    triangleRun := P.triangleRun }

@[simp]
theorem toWitness_topology
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin)
    (M : P.MissingLongArcTriangleRunField) :
    (P.toWitness M).topology = P.topology :=
  rfl

@[simp]
theorem toWitness_classification
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin)
    (M : P.MissingLongArcTriangleRunField) :
    (P.toWitness M).classification = P.classification :=
  rfl

@[simp]
theorem toWitness_longArc
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin)
    (M : P.MissingLongArcTriangleRunField) :
    (P.toWitness M).longArc = M.longArc :=
  rfl

@[simp]
theorem toWitness_triangleRun
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin)
    (M : P.MissingLongArcTriangleRunField) :
    (P.toWitness M).triangleRun = M.triangleRun :=
  rfl

end MinimalBoundaryTopologySkeleton

/-! ## Family bridge -/

structure MinimalBoundaryTopologyWitnessFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        MinimalBoundaryTopologyWitness.{u} C hmin

namespace MinimalBoundaryTopologyWitnessFamily

structure SkeletonFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        MinimalBoundaryTopologySkeleton.{u} C hmin

def skeleton
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    SkeletonFamily.{u} where
  row := fun C hmin =>
    MinimalBoundaryTopologySkeleton.ofWitness (F.row C hmin)

def MissingLongArcTriangleRunField
    (S : SkeletonFamily.{u}) : Type (u + 1) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      (S.row C hmin).MissingLongArcTriangleRunField

def LongArcFieldFamily
    (S : SkeletonFamily.{u}) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
        (S.row C hmin).planarBoundary

/--
Honest row source for the long-arc half of the skeleton missing field.

For each skeleton boundary this asks only for the exact count inequality
`d_3 <= N + A` consumed by `BoundaryLongArcExistenceFields`, plus the raw-turn
interpretation used to decide concavity.  It deliberately stops before any
triangle-run input.
-/
structure LongArcRawTurnRows
    (S : SkeletonFamily.{u}) : Type (u + 1) where
  degreeThree_le_negativeCount_add_longArcCount :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (S.row C hmin).classification.counts.d3 <=
          (S.row C hmin).classification.counts.negativeCount +
            @Fintype.card (S.row C hmin).classification.longArcIndices
              inferInstance
  rawTurn :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        (S.row C hmin).classification.longArcIndices -> Nat -> Real
  rawTurn_nonnegative_on_arc :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (a : (S.row C hmin).classification.longArcIndices)
      (k : Nat),
        Membership.mem Lemma10Inequalities.turnIndexSet k ->
          0 <= rawTurn C hmin a k

/-- Assemble skeleton raw-turn rows from W13's classified raw-turn rows and
the already-proved count coverage for the same classified boundary. -/
def longArcRawTurnRowsOfBoundaryLongArcRawTurnRows
    (S : SkeletonFamily.{u})
    (degreeThree_le_negativeCount_add_longArcCount :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.counts.d3 <=
            (S.row C hmin).classification.counts.negativeCount +
              @Fintype.card (S.row C hmin).classification.longArcIndices
                inferInstance)
    (rawRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows
            (S.row C hmin).classification) :
    LongArcRawTurnRows.{u} S where
  degreeThree_le_negativeCount_add_longArcCount :=
    degreeThree_le_negativeCount_add_longArcCount
  rawTurn := fun C hmin => (rawRows C hmin).rawTurn
  rawTurn_nonnegative_on_arc := by
    intro n C hmin a k hk
    exact (rawRows C hmin).rawTurn_nonnegative_on_arc a k hk

/-- W13 gap-negative coverage, specialized to the skeleton's concrete
`longArcIndices`, gives the exact raw-row count inequality. -/
theorem degreeThree_le_negativeCount_add_longArcIndexCount_of_gapNegativeCoverageData
    (S : SkeletonFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (coverage :
      Lemma6Lemma7AssemblyW13.GapNegativeCoverageData
        (S.row C hmin).planarBoundary
        (@Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance)) :
    (S.row C hmin).classification.counts.d3 <=
      (S.row C hmin).classification.counts.negativeCount +
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance := by
  change
    (S.row C hmin).planarBoundary.outerBoundaryCounts.d3 <=
      (S.row C hmin).planarBoundary.outerBoundaryCounts.negativeCount +
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance
  exact coverage.degreeThree_le_negativeCount_add_longArcCount

/-- W13 boundary-walk coverage output gives the raw-row count inequality once
its exposed long-arc count is identified with the skeleton's concrete
`longArcIndices`. -/
theorem degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryWalkGapNegativeCoverageOutput
    (S : SkeletonFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (coverage :
      Lemma6Lemma7AssemblyW13.BoundaryWalkGapNegativeCoverageOutput
        (S.row C hmin).planarBoundary)
    (longArcCount_eq :
      coverage.longArcCount =
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance) :
    (S.row C hmin).classification.counts.d3 <=
      (S.row C hmin).classification.counts.negativeCount +
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance := by
  have hcoverage := coverage.degreeThree_le_negativeCount_add_longArcCount
  rw [longArcCount_eq] at hcoverage
  change
    (S.row C hmin).planarBoundary.outerBoundaryCounts.d3 <=
      (S.row C hmin).planarBoundary.outerBoundaryCounts.negativeCount +
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance
  exact hcoverage

/-- Build the skeleton raw-turn rows from W13 coverage data plus the raw-turn
nonnegativity rows.  Concavity remains the definitional raw total-turn
threshold in the downstream constructor. -/
def longArcRawTurnRowsOfGapNegativeCoverageDataAndRawTurns
    (S : SkeletonFamily.{u})
    (coverage :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.GapNegativeCoverageData
            (S.row C hmin).planarBoundary
            (@Fintype.card (S.row C hmin).classification.longArcIndices
              inferInstance))
    (rawTurn :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
        (a : (S.row C hmin).classification.longArcIndices)
        (k : Nat),
          Membership.mem Lemma10Inequalities.turnIndexSet k ->
            0 <= rawTurn C hmin a k) :
    LongArcRawTurnRows.{u} S where
  degreeThree_le_negativeCount_add_longArcCount := by
    intro n C hmin
    exact
      degreeThree_le_negativeCount_add_longArcIndexCount_of_gapNegativeCoverageData
        S C hmin (coverage C hmin)
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc

/-- Build the skeleton raw-turn rows from W13 boundary-walk coverage outputs
plus the raw-turn nonnegativity rows. -/
def longArcRawTurnRowsOfBoundaryWalkGapNegativeCoverageOutputsAndRawTurns
    (S : SkeletonFamily.{u})
    (coverage :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryWalkGapNegativeCoverageOutput
            (S.row C hmin).planarBoundary)
    (longArcCount_eq :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (coverage C hmin).longArcCount =
            @Fintype.card (S.row C hmin).classification.longArcIndices
              inferInstance)
    (rawTurn :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (S.row C hmin).classification.longArcIndices -> Nat -> Real)
    (rawTurn_nonnegative_on_arc :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
        (a : (S.row C hmin).classification.longArcIndices)
        (k : Nat),
          Membership.mem Lemma10Inequalities.turnIndexSet k ->
            0 <= rawTurn C hmin a k) :
    LongArcRawTurnRows.{u} S where
  degreeThree_le_negativeCount_add_longArcCount := by
    intro n C hmin
    exact
      degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryWalkGapNegativeCoverageOutput
        S C hmin (coverage C hmin) (longArcCount_eq C hmin)
  rawTurn := rawTurn
  rawTurn_nonnegative_on_arc := rawTurn_nonnegative_on_arc

/-- Build the concrete carrier/raw-turn source rows for one skeleton boundary
from the finite classified long-arc carrier. -/
def boundaryLongArcCarrierRawTurnRowsOfLongArcRawTurnRows
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    LongArcExistenceConcrete.BoundaryLongArcCarrierRawTurnRows.{u}
      (S.row C hmin).planarBoundary :=
  LongArcExistenceConcrete.BoundaryLongArcCarrierRawTurnRows.ofFiniteCarrierRawTurns
    (D := (S.row C hmin).planarBoundary)
    (S.row C hmin).classification.longArcIndices
    (by
      change
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance =
            (S.row C hmin).classification.counts.B
      exact (S.row C hmin).classification.counts_B.symm)
    (by
      change
        (S.row C hmin).classification.counts.d3 <=
          (S.row C hmin).classification.counts.negativeCount +
            @Fintype.card (S.row C hmin).classification.longArcIndices
              inferInstance
      exact R.degreeThree_le_negativeCount_add_longArcCount C hmin)
    (R.rawTurn C hmin)
    (R.rawTurn_nonnegative_on_arc C hmin)

@[simp]
theorem boundaryLongArcCarrierRawTurnRowsOfLongArcRawTurnRows_rawTurn
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (boundaryLongArcCarrierRawTurnRowsOfLongArcRawTurnRows
      S R C hmin).rawTurn = R.rawTurn C hmin :=
  rfl

/-- Project W13 long-arc source packages to the skeleton raw-turn rows.

The package supplies the genuine raw-turn function and the Lemma 6/Lemma 7
coverage inequality.  The explicit equivalence identifies the package's
long-arc carrier with the skeleton's concrete classified `longArcIndices`; the
raw turns are transported along that equivalence. -/
def longArcRawTurnRowsOfBoundaryLongArcGapNegativePackages
    (S : SkeletonFamily.{u})
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices) :
    LongArcRawTurnRows.{u} S where
  degreeThree_le_negativeCount_add_longArcCount := by
    intro n C hmin
    let Q := package C hmin
    have hcoverage :
        (S.row C hmin).classification.counts.d3 <=
          (S.row C hmin).classification.counts.negativeCount +
            Q.source.longArcCount := by
      change
        (S.row C hmin).planarBoundary.outerBoundaryCounts.d3 <=
          (S.row C hmin).planarBoundary.outerBoundaryCounts.negativeCount +
            Q.source.longArcCount
      exact Q.degreeThree_le_negativeCount_add_longArcCount
    have hcard :
        Q.source.longArcCount =
          @Fintype.card (S.row C hmin).classification.longArcIndices
            inferInstance := by
      change
        @Fintype.card Q.source.LongArc Q.source.longArcFintype =
          @Fintype.card (S.row C hmin).classification.longArcIndices
            inferInstance
      exact
        @Fintype.card_congr Q.source.LongArc
          (S.row C hmin).classification.longArcIndices
          Q.source.longArcFintype inferInstance (longArcEquiv C hmin)
    rw [hcard] at hcoverage
    exact hcoverage
  rawTurn := fun C hmin a k =>
    (package C hmin).source.rawTurn ((longArcEquiv C hmin).symm a) k
  rawTurn_nonnegative_on_arc := by
    intro n C hmin a k hk
    exact
      (package C hmin).source.rawTurn_nonnegative_on_arc
        ((longArcEquiv C hmin).symm a) k hk

/-- W13 bundled gap-negative rows give the skeleton's exact count gap directly
from their coverage field and concrete long-arc count identity. -/
theorem degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (S.row C hmin).classification.counts.d3 <=
      (S.row C hmin).classification.counts.negativeCount +
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance := by
  have hcoverage :=
    (rows C hmin).coverage.degreeThree_le_negativeCount_add_longArcCount
  rw [(rows C hmin).longArcCount_eq] at hcoverage
  change
    (S.row C hmin).planarBoundary.outerBoundaryCounts.d3 <=
      (S.row C hmin).planarBoundary.outerBoundaryCounts.negativeCount +
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance
  exact hcoverage

/-- W13 boundary long-arc packages give the skeleton's exact count gap after
identifying their long-arc carrier with the classified boundary long arcs. -/
theorem degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryLongArcGapNegativePackage
    (S : SkeletonFamily.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (package :
      Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
        (S.row C hmin).planarBoundary)
    (longArcEquiv :
      Equiv package.source.LongArc
        (S.row C hmin).classification.longArcIndices) :
    (S.row C hmin).classification.counts.d3 <=
      (S.row C hmin).classification.counts.negativeCount +
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance := by
  have hcoverage :
      (S.row C hmin).classification.counts.d3 <=
        (S.row C hmin).classification.counts.negativeCount +
          package.source.longArcCount := by
    change
      (S.row C hmin).planarBoundary.outerBoundaryCounts.d3 <=
        (S.row C hmin).planarBoundary.outerBoundaryCounts.negativeCount +
          package.source.longArcCount
    exact package.degreeThree_le_negativeCount_add_longArcCount
  have hcard :
      package.source.longArcCount =
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance := by
    change
      @Fintype.card package.source.LongArc package.source.longArcFintype =
        @Fintype.card (S.row C hmin).classification.longArcIndices
          inferInstance
    exact
      @Fintype.card_congr package.source.LongArc
        (S.row C hmin).classification.longArcIndices
        package.source.longArcFintype inferInstance longArcEquiv
  rw [hcard] at hcoverage
  exact hcoverage

/--
Combine real boundary-turn raw rows with W13 count-gap packages.

This is the W24-side integration point for the W11 turn-angle route: W11 can
forget its actual angle certificates to `LongArcRawTurnRows`, while this
constructor replaces the count gap by the W13 package count gap and keeps the
W11-projected raw turns.
-/
def longArcRawTurnRowsOfTurnRowsAndBoundaryLongArcGapNegativePackages
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices) :
    LongArcRawTurnRows.{u} S where
  degreeThree_le_negativeCount_add_longArcCount := by
    intro n C hmin
    exact
      degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryLongArcGapNegativePackage
        S C hmin (package C hmin) (longArcEquiv C hmin)
  rawTurn := turnRows.rawTurn
  rawTurn_nonnegative_on_arc := turnRows.rawTurn_nonnegative_on_arc

/-- Convert the honest raw-turn rows into the classified-boundary long-arc
fields used by the W10 boundary angle/turn package. -/
def longArcExistenceFieldsOfLongArcRawTurnRows
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      (S.row C hmin).classification
      (S.row C hmin).geometricAngleSum
      (S.row C hmin).forced_le_geometric
      (S.row C hmin).geometric_le_polygon
      (S.row C hmin).Subpolygon
      (S.row C hmin).subpolygonData :=
  BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields.ofCoverageAndRawTurns
    (D := (S.row C hmin).classification)
    (geometricAngleSum := (S.row C hmin).geometricAngleSum)
    (forced_le_geometric := (S.row C hmin).forced_le_geometric)
    (geometric_le_polygon := (S.row C hmin).geometric_le_polygon)
    (Subpolygon := (S.row C hmin).Subpolygon)
    (subpolygonData := (S.row C hmin).subpolygonData)
    (R.degreeThree_le_negativeCount_add_longArcCount C hmin)
    (R.rawTurn C hmin)
    (R.rawTurn_nonnegative_on_arc C hmin)

/-- Convert the honest count/raw-turn rows into the pointwise long-arc
existence field over the skeleton's planar boundary. -/
def longArcFieldOfLongArcRawTurnRows
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      (S.row C hmin).planarBoundary :=
  (boundaryLongArcCarrierRawTurnRowsOfLongArcRawTurnRows S R C hmin)
    |>.toBoundaryLongArcExistenceFields

@[simp]
theorem longArcFieldOfLongArcRawTurnRows_rawTurn
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (longArcFieldOfLongArcRawTurnRows S R C hmin).rawTurn =
      R.rawTurn C hmin :=
  rfl

/-- The raw-turn rows give pointwise nonnegativity in the resulting
`BoundaryLongArcExistenceFields`. -/
theorem longArcFieldOfLongArcRawTurnRows_rawTurn_nonnegative_on_arc
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices)
    (k : Nat)
    (hk : Membership.mem Lemma10Inequalities.turnIndexSet k) :
    0 <=
      (longArcFieldOfLongArcRawTurnRows S R C hmin).rawTurn a k :=
  (longArcFieldOfLongArcRawTurnRows S R C hmin).rawTurn_nonnegative_on_arc
    a k hk

/-- In the raw-row constructor, concavity is the raw `pi / 3` total-turn
threshold. -/
theorem longArcFieldOfLongArcRawTurnRows_concave_iff_totalTurn_ge_pi_div_three
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices) :
    (longArcFieldOfLongArcRawTurnRows S R C hmin).concave a <->
      Real.pi / 3 <=
        Lemma10Inequalities.totalTurn
          ((longArcFieldOfLongArcRawTurnRows S R C hmin).rawTurn a) :=
  (longArcFieldOfLongArcRawTurnRows S R C hmin).concave_iff a

/-- Nonconcavity in the raw-row constructor is strict failure of the raw
`pi / 3` total-turn threshold. -/
theorem longArcFieldOfLongArcRawTurnRows_not_concave_iff_totalTurn_lt_pi_div_three
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (a : (S.row C hmin).classification.longArcIndices) :
    Not ((longArcFieldOfLongArcRawTurnRows S R C hmin).concave a) <->
      Lemma10Inequalities.totalTurn
          ((longArcFieldOfLongArcRawTurnRows S R C hmin).rawTurn a) <
        Real.pi / 3 :=
  (longArcFieldOfLongArcRawTurnRows S R C hmin).not_concave_iff_totalTurn_lt_pi_div_three
    a

/-- The exact long-arc field family required by the non-circular W24/W33
missing-field route, produced without supplying any triangle-run data. -/
def longArcFieldFamilyOfLongArcRawTurnRows
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S) :
    LongArcFieldFamily S :=
  fun C hmin => longArcFieldOfLongArcRawTurnRows S R C hmin

theorem longArcFieldFamily_nonempty_of_longArcRawTurnRows
    (S : SkeletonFamily.{u})
    (R : LongArcRawTurnRows.{u} S) :
    Nonempty (LongArcFieldFamily S) :=
  Nonempty.intro (longArcFieldFamilyOfLongArcRawTurnRows S R)

/-- W13 boundary long-arc gap-negative packages, after identifying their
long-arc carrier with the skeleton's concrete classified long-arc indices,
produce the exact skeleton-level long-arc field family. -/
def longArcFieldFamilyOfBoundaryLongArcGapNegativePackages
    (S : SkeletonFamily.{u})
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices) :
    LongArcFieldFamily S :=
  longArcFieldFamilyOfLongArcRawTurnRows S
    (longArcRawTurnRowsOfBoundaryLongArcGapNegativePackages
      S package longArcEquiv)

/-- W11-projected turn rows plus W13 boundary long-arc packages produce the
exact skeleton-level long-arc field family. -/
def longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativePackages
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices) :
    LongArcFieldFamily S :=
  longArcFieldFamilyOfLongArcRawTurnRows S
    (longArcRawTurnRowsOfTurnRowsAndBoundaryLongArcGapNegativePackages
      S turnRows package longArcEquiv)

/-- Convert W13's cycle-safe bundled rows to the exact package family consumed
by the W24 long-arc bridge. -/
noncomputable def boundaryLongArcGapNegativePackageFamilyOfRows
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
          (S.row C hmin).planarBoundary := by
  intro n C hmin
  change
    Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
      ((S.row C hmin).classification.toPlanarBoundaryData
        (S.row C hmin).geometricAngleSum
        (S.row C hmin).forced_le_geometric
        (S.row C hmin).geometric_le_polygon
        (S.row C hmin).Subpolygon
        (S.row C hmin).subpolygonData)
  exact
    (rows C hmin).toBoundaryLongArcGapNegativePackage

/-- The W13 row package uses the skeleton's classified long-arc carrier, so
the package carrier is definitionally equivalent to `longArcIndices`. -/
noncomputable def boundaryLongArcGapNegativeRowsLongArcEquiv
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Equiv
          ((boundaryLongArcGapNegativePackageFamilyOfRows S rows
            C hmin).source.LongArc)
          (S.row C hmin).classification.longArcIndices := by
  intro n C hmin
  change
    Equiv (S.row C hmin).classification.longArcIndices
      (S.row C hmin).classification.longArcIndices
  exact Equiv.refl _

/-- W13's bundled gap-negative rows already contain the real raw-turn rows on
the skeleton's classified long-arc carrier.  This projection is the
import-cycle-free W24 handoff; it does not choose any new long arcs. -/
noncomputable def longArcRawTurnRowsOfBoundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    LongArcRawTurnRows.{u} S :=
  longArcRawTurnRowsOfBoundaryLongArcRawTurnRows S
    (degreeThree_le_negativeCount_add_longArcIndexCount_of_boundaryLongArcGapNegativeRows
      S rows)
    (fun C hmin => (rows C hmin).rawRows)

/-- W13 bundled gap-negative rows produce concrete finite carrier/raw-turn
rows for a single skeleton boundary, using their own raw-turn rows and
coverage count identity. -/
noncomputable def boundaryLongArcCarrierRawTurnRowsOfBoundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    LongArcExistenceConcrete.BoundaryLongArcCarrierRawTurnRows.{u}
      (S.row C hmin).planarBoundary :=
  (rows C hmin).toBoundaryLongArcCarrierRawTurnRows

/-- Pointwise long-arc fields from W13 bundled gap-negative rows, routed
through the concrete finite carrier/raw-turn constructor. -/
noncomputable def longArcFieldOfBoundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      (S.row C hmin).planarBoundary :=
  (boundaryLongArcCarrierRawTurnRowsOfBoundaryLongArcGapNegativeRows
    S rows C hmin).toBoundaryLongArcExistenceFields

/-- W13 bundled gap-negative rows produce the exact skeleton-level long-arc
field family directly, using their own raw-turn rows. -/
noncomputable def longArcFieldFamilyOfBoundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    LongArcFieldFamily S :=
  fun C hmin => longArcFieldOfBoundaryLongArcGapNegativeRows S rows C hmin

/-- W11-style turn rows plus W13 bundled gap-negative rows produce the exact
skeleton-level long-arc field family. -/
noncomputable def longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    LongArcFieldFamily S :=
  longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativePackages
    S turnRows
    (boundaryLongArcGapNegativePackageFamilyOfRows S rows)
    (boundaryLongArcGapNegativeRowsLongArcEquiv S rows)

theorem longArcFieldFamily_nonempty_of_boundaryLongArcGapNegativePackages
    (S : SkeletonFamily.{u})
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices) :
    Nonempty (LongArcFieldFamily S) :=
  Nonempty.intro
    (longArcFieldFamilyOfBoundaryLongArcGapNegativePackages
      S package longArcEquiv)

theorem longArcFieldFamily_nonempty_of_turnRows_boundaryLongArcGapNegativePackages
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices) :
    Nonempty (LongArcFieldFamily S) :=
  Nonempty.intro
    (longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativePackages
      S turnRows package longArcEquiv)

theorem longArcFieldFamily_nonempty_of_turnRows_boundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    Nonempty (LongArcFieldFamily S) :=
  Nonempty.intro
    (longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativeRows
      S turnRows rows)

theorem longArcFieldFamily_nonempty_of_boundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    Nonempty (LongArcFieldFamily S) :=
  Nonempty.intro
    (longArcFieldFamilyOfBoundaryLongArcGapNegativeRows S rows)

/-- Build W13 bundled gap-negative rows on the skeleton boundary from actual
no-boundary-gap rows and the real classified raw-turn rows. -/
noncomputable def boundaryLongArcGapNegativeRowsOfNoBoundaryGapTriangleDegree34Rows
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (P : MinimalBoundaryTopologySkeleton.{u} C hmin)
    (hno :
      forall k : Fin P.topology.toCore.outerCycle.length,
        Not
          (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            P.classification k))
    (rawRows :
      Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows
        P.classification) :
    Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
      P.classification P.geometricAngleSum P.forced_le_geometric
      P.geometric_le_polygon P.Subpolygon P.subpolygonData :=
  Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows.ofLemma6Obstruction
    (D0 := P.classification)
    (angleSum := P.geometricAngleSum)
    (forced_le := P.forced_le_geometric)
    (angle_le_polygon := P.geometric_le_polygon)
    (Subpolygon0 := P.Subpolygon)
    (subpolygonRows := P.subpolygonData)
    (Lemma6NegativeAfterGapW12.BoundaryWalkLemma6Obstruction.ofNegativeAfterFact
      (Lemma6Lemma7AssemblyW13.ClassifiedBoundary.boundaryWalkLemma6E14NegativeAfterFact_of_no_boundaryGapTriangleDegree34Rows
        P.classification hno))
    rawRows

/-- Actual no-boundary-gap rows for a skeleton family, with the concrete
no-gap row and the raw turn rows needed by the long-arc field. -/
structure BoundaryLongArcNoBoundaryGapTriangleDegree34Rows
    (S : SkeletonFamily.{u}) : Type (u + 1) where
  no_boundaryGapTriangleDegree34Rows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
      (k : Fin (S.row C hmin).topology.toCore.outerCycle.length),
        Not
          (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            (S.row C hmin).classification k)
  rawRows :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows
          (S.row C hmin).classification

namespace BoundaryLongArcNoBoundaryGapTriangleDegree34Rows

variable {S : SkeletonFamily.{u}}

/-- Project actual no-boundary-gap rows to W13's bundled gap-negative rows. -/
noncomputable def toBoundaryLongArcGapNegativeRows
    (R : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S) :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
        Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
          (S.row C hmin).classification
          (S.row C hmin).geometricAngleSum
          (S.row C hmin).forced_le_geometric
          (S.row C hmin).geometric_le_polygon
          (S.row C hmin).Subpolygon
          (S.row C hmin).subpolygonData := by
  intro n C hmin
  exact
    boundaryLongArcGapNegativeRowsOfNoBoundaryGapTriangleDegree34Rows
      (S.row C hmin)
      (R.no_boundaryGapTriangleDegree34Rows C hmin)
      (R.rawRows C hmin)

/-- Actual no-boundary-gap rows already contain the W13 raw-turn rows, so they
produce the W24 long-arc field family without package/equivalence plumbing. -/
noncomputable def toLongArcFieldFamily
    (R : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S) :
    LongArcFieldFamily S :=
  longArcFieldFamilyOfBoundaryLongArcGapNegativeRows S
    R.toBoundaryLongArcGapNegativeRows

/-- Nonempty form of the long-arc-field projection from actual no-gap rows. -/
theorem longArcFieldFamily_nonempty
    (R : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S) :
    Nonempty (LongArcFieldFamily S) :=
  Nonempty.intro R.toLongArcFieldFamily

end BoundaryLongArcNoBoundaryGapTriangleDegree34Rows

def TriangleRunFieldFamily
    (S : SkeletonFamily.{u}) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      BoundaryArcTriangleRun.{u} (S.row C hmin).planarBoundary

def BoundaryArcExtractionFieldFamily
    (S : SkeletonFamily.{u}) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      TopologyToBoundaryArcW14.BoundaryArcExtractionFields.{u}
        (S.row C hmin).planarBoundary

def BoundaryArcFiniteWalkDataFamily
    (S : SkeletonFamily.{u}) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkData.{u}
        (S.row C hmin).planarBoundary

def FinitePQSpineCyclicSuccessorRowsFamily
    (S : SkeletonFamily.{u}) :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty
        { K :
            BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
              (S.row C hmin).planarBoundary //
          BoundaryArcExtractionProofW15.BoundaryArcFiniteWalkData.M8FinitePQSpineCyclicSuccessorRows
            K }

/--
Uniform finite-`p/q` successor-row source for the missing-field route.

This is the W16 source theorem surface, deliberately keyed only to a W14
topology/angle/subpolygon/long-arc row.  It is the non-circular supplier for
the W24/W33 missing field; generated-order rows over a later
actual-component closure must not be used to build the missing field that
creates that closure.
-/
abbrev FinitePQSpineCyclicSuccessorRowsTheorem : Prop :=
  BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem.{u}

def triangleRunFieldFamilyOfExtractionFields
    (S : SkeletonFamily.{u})
    (A : BoundaryArcExtractionFieldFamily S) :
    TriangleRunFieldFamily S :=
  fun C hmin =>
    TriangleRunSelectorW17.BoundaryArcSelector.triangleRunOfExtractionFields
      (A C hmin)

def triangleRunFieldFamilyOfFiniteWalkData
    (S : SkeletonFamily.{u})
    (W : BoundaryArcFiniteWalkDataFamily S) :
    TriangleRunFieldFamily S :=
  fun C hmin =>
    TriangleRunSelectorW17.BoundaryArcSelector.triangleRunOfFiniteWalkData
      (W C hmin)

def triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRows
    (S : SkeletonFamily.{u})
    (H : FinitePQSpineCyclicSuccessorRowsFamily S) :
    TriangleRunFieldFamily S :=
  fun C hmin =>
    let Srow := Classical.choice (H C hmin)
    BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.ofFinitePQSpineCertificateRows
      Srow.1 Srow.2

def triangleRunFieldFamilyOfTriangleRunTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (Hrun : BoundaryArcTriangleRunTheorem.{u}) :
    TriangleRunFieldFamily S :=
  fun C hmin =>
    let P := S.row C hmin
    Classical.choice
      (Hrun C P.topology P.outerAngleBounds P.Subpolygon P.subpolygonData
        (longArc C hmin))

def triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    TriangleRunFieldFamily S :=
  fun C hmin =>
    let P := S.row C hmin
    let Srow :=
      Classical.choice
        (H C P.topology P.outerAngleBounds P.Subpolygon P.subpolygonData
          (longArc C hmin))
    BoundaryArcFiniteWalkConstructionW16.BoundaryArcTriangleRun.ofFinitePQSpineCertificateRows
      Srow.1 Srow.2

/--
Pointwise S2/S3 skeleton triangle-run target from finite `p/q`
cyclic-successor rows.

This theorem stops before the S4 missing-field record: it supplies only the
`BoundaryArcTriangleRun` over the skeleton's assembled planar boundary.
-/
theorem triangleRunTarget_of_skeleton_finitePQSpineCyclicSuccessorRows
    (S : SkeletonFamily.{u})
    (H : FinitePQSpineCyclicSuccessorRowsFamily S)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BoundaryArcTriangleRun.{u} (S.row C hmin).planarBoundary) :=
  Nonempty.intro
    ((triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRows S H)
      C hmin)

/--
The non-circular W16 finite-`p/q` successor-row theorem supplies a pointwise
`BoundaryArcTriangleRun` over any S2/S3 skeleton row once the long-arc family is
available.
-/
theorem triangleRunTarget_of_skeleton_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u})
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (BoundaryArcTriangleRun.{u} (S.row C hmin).planarBoundary) :=
  Nonempty.intro
    ((triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRowsTheorem
      S longArc H) C hmin)

theorem triangleRunFieldFamily_nonempty_of_finitePQSpineCyclicSuccessorRows
    (S : SkeletonFamily.{u})
    (H : FinitePQSpineCyclicSuccessorRowsFamily S) :
    Nonempty (TriangleRunFieldFamily S) :=
  Nonempty.intro
    (triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRows S H)

theorem triangleRunFieldFamily_nonempty_of_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (TriangleRunFieldFamily S) :=
  Nonempty.intro
    (triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRowsTheorem
      S longArc H)

def missingField
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MissingLongArcTriangleRunField F.skeleton :=
  fun C hmin =>
    MinimalBoundaryTopologySkeleton.missingFieldOfWitness (F.row C hmin)

def missingFieldOfLongArcTriangleRun
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (triangleRun : TriangleRunFieldFamily S) :
    MissingLongArcTriangleRunField S :=
  fun C hmin =>
    MinimalBoundaryTopologySkeleton.missingFieldOfLongArcTriangleRun
      (S.row C hmin) (longArc C hmin) (triangleRun C hmin)

def missingFieldOfLongArcFinitePQSpineCyclicSuccessorRows
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsFamily S) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcTriangleRun S longArc
    (triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRows S H)

def missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcTriangleRun S longArc
    (triangleRunFieldFamilyOfFinitePQSpineCyclicSuccessorRowsTheorem
      S longArc H)

/-- W13 long-arc gap-negative packages plus the W16 finite-`p/q` theorem
produce the exact missing long-arc/triangle-run field for a skeleton family. -/
def missingFieldOfBoundaryLongArcGapNegativePackagesFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem S
    (longArcFieldFamilyOfBoundaryLongArcGapNegativePackages
      S package longArcEquiv)
    H

/-- W11-projected turn rows plus W13 packages and the W16 finite-`p/q`
theorem produce the skeleton missing field directly. -/
def missingFieldOfTurnRowsBoundaryLongArcGapNegativePackagesFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem S
    (longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativePackages
      S turnRows package longArcEquiv)
    H

/-- W11-style turn rows plus W13 bundled gap-negative rows and the W16
finite-`p/q` theorem produce the skeleton missing field directly. -/
noncomputable def missingFieldOfTurnRowsBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem S
    (longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativeRows
      S turnRows rows)
    H

/-- Explicit triangle-run rows plus W13 bundled gap-negative rows produce the
exact W24 missing field.  The long arcs come from the W13 row package and the
triangle runs are supplied by the caller. -/
noncomputable def missingFieldOfTriangleRunBoundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (triangleRun : TriangleRunFieldFamily S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcTriangleRun S
    (longArcFieldFamilyOfBoundaryLongArcGapNegativeRows S rows)
    triangleRun

/-- W13 bundled gap-negative rows plus the non-circular W16 finite-`p/q`
theorem produce the exact missing long-arc/triangle-run field. -/
noncomputable def missingFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem S
    (longArcFieldFamilyOfBoundaryLongArcGapNegativeRows S rows)
    H

/-- Actual no-boundary-gap rows plus the W16 finite-`p/q` theorem produce the
exact missing long-arc/triangle-run field, using W13's bundled row projection
rather than an intermediate package/equivalence route. -/
noncomputable def missingFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MissingLongArcTriangleRunField S :=
  missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem S
    rows.toLongArcFieldFamily H

theorem missingField_nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRows
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsFamily S) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfLongArcFinitePQSpineCyclicSuccessorRows S longArc H)

theorem missingField_nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      S longArc H)

theorem missingField_nonempty_of_boundaryLongArcGapNegativePackages_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfBoundaryLongArcGapNegativePackagesFinitePQSpineCyclicSuccessorRowsTheorem
      S package longArcEquiv H)

theorem missingField_nonempty_of_turnRows_boundaryLongArcGapNegativePackages_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (package :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.BoundaryLongArcGapNegativePackage
            (S.row C hmin).planarBoundary)
    (longArcEquiv :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Equiv (package C hmin).source.LongArc
            (S.row C hmin).classification.longArcIndices)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfTurnRowsBoundaryLongArcGapNegativePackagesFinitePQSpineCyclicSuccessorRowsTheorem
      S turnRows package longArcEquiv H)

theorem missingField_nonempty_of_turnRows_boundaryLongArcGapNegativeRows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (turnRows : LongArcRawTurnRows.{u} S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfTurnRowsBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
      S turnRows rows H)

theorem missingField_nonempty_of_triangleRun_boundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (triangleRun : TriangleRunFieldFamily S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfTriangleRunBoundaryLongArcGapNegativeRows
      S triangleRun rows)

theorem missingField_nonempty_of_boundaryLongArcGapNegativeRows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
      S rows H)

/-- Nonempty missing-field form of the actual no-boundary-gap/W16 composition. -/
theorem missingField_nonempty_of_noBoundaryGapTriangleDegree34Rows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  Nonempty.intro
    (missingFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
      S rows H)

/-- Explicit M8 triangle-run indices plus the actual W13/no-gap long-arc rows
produce the exact W24 missing field. -/
theorem missingField_nonempty_of_noBoundaryGapTriangleDegree34Rows_explicitM8TriangleRunIndicesTheorem
    (S : SkeletonFamily.{u})
    (rows : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S)
    (H : TriangleRunSelectorW17.ExplicitM8TriangleRunIndicesTheorem.{u}) :
    Nonempty (MissingLongArcTriangleRunField S) :=
  missingField_nonempty_of_noBoundaryGapTriangleDegree34Rows_finitePQSpineCyclicSuccessorRowsTheorem
    S rows
    (TriangleRunSelectorW17.finitePQSpineCyclicSuccessorRowsTheorem_of_explicitM8TriangleRunIndicesTheorem
      H)

def ofSkeletonAndMissingField
    (S : SkeletonFamily.{u})
    (M : MissingLongArcTriangleRunField S) :
    MinimalBoundaryTopologyWitnessFamily.{u} where
  row := fun C hmin =>
    (S.row C hmin).toWitness (M C hmin)

def ofSkeletonAndLongArcTriangleRun
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (triangleRun : TriangleRunFieldFamily S) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  ofSkeletonAndMissingField S
    (missingFieldOfLongArcTriangleRun S longArc triangleRun)

def ofSkeletonLongArcAndFinitePQSpineCyclicSuccessorRows
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsFamily S) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  ofSkeletonAndMissingField S
    (missingFieldOfLongArcFinitePQSpineCyclicSuccessorRows S longArc H)

def ofSkeletonLongArcAndFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  ofSkeletonAndMissingField S
    (missingFieldOfLongArcFinitePQSpineCyclicSuccessorRowsTheorem
      S longArc H)

noncomputable def ofSkeletonTriangleRunAndBoundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (triangleRun : TriangleRunFieldFamily S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  ofSkeletonAndMissingField S
    (missingFieldOfTriangleRunBoundaryLongArcGapNegativeRows
      S triangleRun rows)

noncomputable def ofSkeletonBoundaryLongArcGapNegativeRowsAndFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  ofSkeletonAndMissingField S
    (missingFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem
      S rows H)

/-- Witness-family constructor from actual no-boundary-gap rows and the W16
finite-`p/q` theorem. -/
noncomputable def ofSkeletonNoBoundaryGapTriangleDegree34RowsAndFinitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    MinimalBoundaryTopologyWitnessFamily.{u} :=
  ofSkeletonAndMissingField S
    (missingFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem
      S rows H)

theorem nonempty_of_skeleton_and_missingField
    (S : SkeletonFamily.{u})
    (M : MissingLongArcTriangleRunField S) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro (ofSkeletonAndMissingField S M)

theorem nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRows
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsFamily S) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro
    (ofSkeletonLongArcAndFinitePQSpineCyclicSuccessorRows S longArc H)

theorem nonempty_of_skeleton_longArc_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (longArc : LongArcFieldFamily S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro
    (ofSkeletonLongArcAndFinitePQSpineCyclicSuccessorRowsTheorem
      S longArc H)

theorem nonempty_of_skeleton_triangleRun_boundaryLongArcGapNegativeRows
    (S : SkeletonFamily.{u})
    (triangleRun : TriangleRunFieldFamily S)
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro
    (ofSkeletonTriangleRunAndBoundaryLongArcGapNegativeRows
      S triangleRun rows)

theorem nonempty_of_skeleton_boundaryLongArcGapNegativeRows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcGapNegativeRows
            (S.row C hmin).classification
            (S.row C hmin).geometricAngleSum
            (S.row C hmin).forced_le_geometric
            (S.row C hmin).geometric_le_polygon
            (S.row C hmin).Subpolygon
            (S.row C hmin).subpolygonData)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro
    (ofSkeletonBoundaryLongArcGapNegativeRowsAndFinitePQSpineCyclicSuccessorRowsTheorem
      S rows H)

/-- Nonempty witness-family form of the actual no-boundary-gap/W16
composition. -/
theorem nonempty_of_skeleton_noBoundaryGapTriangleDegree34Rows_finitePQSpineCyclicSuccessorRowsTheorem
    (S : SkeletonFamily.{u})
    (rows : BoundaryLongArcNoBoundaryGapTriangleDegree34Rows.{u} S)
    (H : FinitePQSpineCyclicSuccessorRowsTheorem.{u}) :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} :=
  Nonempty.intro
    (ofSkeletonNoBoundaryGapTriangleDegree34RowsAndFinitePQSpineCyclicSuccessorRowsTheorem
      S rows H)

theorem exists_skeleton_missingField_of_nonempty
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    Exists fun S : SkeletonFamily.{u} =>
      Nonempty (MissingLongArcTriangleRunField S) := by
  cases h with
  | intro F =>
      exact Exists.intro F.skeleton (Nonempty.intro F.missingField)

theorem nonempty_iff_exists_skeleton_missingField :
    Nonempty MinimalBoundaryTopologyWitnessFamily.{u} <->
      Exists fun S : SkeletonFamily.{u} =>
        Nonempty (MissingLongArcTriangleRunField S) := by
  constructor
  case mp =>
    exact exists_skeleton_missingField_of_nonempty
  case mpr =>
    intro h
    cases h with
    | intro S hM =>
        cases hM with
        | intro M =>
            exact nonempty_of_skeleton_and_missingField S M

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
