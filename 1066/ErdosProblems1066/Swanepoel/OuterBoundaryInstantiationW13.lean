import ErdosProblems1066.Swanepoel.BoundaryClassificationW12
import ErdosProblems1066.Swanepoel.OuterBoundaryAngleW12
import ErdosProblems1066.Swanepoel.BoundaryCounting
import ErdosProblems1066.Swanepoel.PlanarInterface

set_option autoImplicit false

/-!
# Outer-boundary instantiation, W13

This file provides checked bridges from supplied outer-boundary data to the
angle and counting conclusions used downstream.  The first record exposes the
small geometric comparison fields needed by the counting layer.  The second
record packages the classified outer boundary together with the concrete local
angle witnesses already used in W12, then projects to the smaller record.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryInstantiationW13

open BoundaryCounting
open BoundaryClassification
open BoundaryWalkClassificationConcrete

universe u

noncomputable section

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

structure ExplicitOuterBoundaryAngleFields
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  core : OuterBoundaryCore G
  countsRealization : BoundaryCountsRealization.{u}
  geometricAngleSum : Real
  forced_le_geometric :
    countsRealization.toBoundaryCounts.forcedBoundaryAngleSum <=
      geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <=
      countsRealization.toBoundaryCounts.polygonAngleSum

namespace ExplicitOuterBoundaryAngleFields

variable (D : ExplicitOuterBoundaryAngleFields.{u} G)

def counts : BoundaryCounts :=
  D.countsRealization.toBoundaryCounts

def bookkeeping : BoundaryBookkeeping.{u} :=
  D.countsRealization.bookkeeping

def planarFaceBoundary :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  D.core.toFaceBoundaryHypotheses

def pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  OuterBoundaryCore.pairwiseNoncrossing (D.core)

def angleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} where
  countsRealization := D.countsRealization
  geometricAngleSum := D.geometricAngleSum
  forced_le_geometric := D.forced_le_geometric
  geometric_le_polygon := D.geometric_le_polygon

@[simp]
theorem angleBounds_counts :
    D.angleBounds.counts = D.counts :=
  rfl

@[simp]
theorem angleBounds_bookkeeping :
    D.angleBounds.countsRealization.bookkeeping = D.bookkeeping :=
  rfl

def outerBoundaryAngleData :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G where
  core := D.core
  angleBounds := D.angleBounds

@[simp]
theorem outerBoundaryAngleData_core :
    D.outerBoundaryAngleData.core = D.core :=
  rfl

@[simp]
theorem outerBoundaryAngleData_counts :
    D.outerBoundaryAngleData.counts = D.counts :=
  rfl

def canonicalBoundaryCountHypotheses :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  D.angleBounds.toCanonicalBoundaryCountHypotheses D.core

@[simp]
theorem canonicalBoundaryCountHypotheses_faceBoundary :
    D.canonicalBoundaryCountHypotheses.faceBoundary =
      D.core.faceBoundary :=
  rfl

@[simp]
theorem canonicalBoundaryCountHypotheses_counts :
    D.canonicalBoundaryCountHypotheses.counts = D.counts :=
  rfl

theorem angleLowerBound :
    D.counts.AngleLowerBound :=
  D.angleBounds.angleLowerBound

theorem projected_angleLowerBound :
    D.bookkeeping.toBoundaryCounts.AngleLowerBound :=
  D.angleBounds.projected_angleLowerBound

theorem boundaryAngleCountInequality :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  D.angleBounds.boundaryAngleCountInequality

theorem boundaryAngleCountInequality_viaCore :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  D.angleBounds.boundaryAngleCountInequality_viaOuterBoundaryCore D.core

theorem boundaryNegativeCountInequality :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  D.angleBounds.boundaryNegativeCountInequality

theorem boundaryAngleCount_bookkeeping :
    D.bookkeeping.d5 + 2 * D.bookkeeping.d6 + D.bookkeeping.b +
        D.bookkeeping.longArcCount + 6 <= D.bookkeeping.d3 := by
  simpa [bookkeeping, BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounts.boundary_angle_count_inequality
      D.bookkeeping.toBoundaryCounts D.projected_angleLowerBound

theorem boundaryNegativeCount_bookkeeping :
    D.bookkeeping.negativeElementCount +
        D.bookkeeping.longArcCount + 6 <= D.bookkeeping.d3 := by
  simpa [bookkeeping, BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounts.boundary_negative_count_inequality
      D.bookkeeping.toBoundaryCounts D.projected_angleLowerBound

end ExplicitOuterBoundaryAngleFields

structure ActualOuterBoundaryAngleData
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  core : OuterBoundaryCore G
  classification : OuterBoundaryClassificationInputs core
  angleWitness : OuterBoundaryAngleW12.UnitSeparatedAngleFamilies classification

namespace ActualOuterBoundaryAngleData

variable (D : ActualOuterBoundaryAngleData G)

def counts : BoundaryCounts :=
  D.classification.counts

def countsRealization : BoundaryCountsRealization.{0} :=
  BoundaryClassificationW12.ClassifiedBoundary.countsRealization
    D.classification

def bookkeeping : BoundaryBookkeeping.{0} :=
  BoundaryClassificationW12.ClassifiedBoundary.boundaryBookkeeping
    D.classification

def concreteBookkeeping : BoundaryBookkeeping.{0} :=
  BoundaryClassificationW12.ClassifiedBoundary.concreteBoundaryBookkeeping
    D.classification

def planarFaceBoundary :
    PlanarInterface.FaceBoundaryHypotheses G.toStraightLine :=
  D.core.toFaceBoundaryHypotheses

def pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  OuterBoundaryCore.pairwiseNoncrossing (D.core)

def toExplicitAngleFields :
    ExplicitOuterBoundaryAngleFields.{0} G where
  core := D.core
  countsRealization := D.countsRealization
  geometricAngleSum := D.angleWitness.geometricAngleSum
  forced_le_geometric := D.angleWitness.forced_le_geometricAngleSum
  geometric_le_polygon := D.angleWitness.geometric_le_polygon

@[simp]
theorem toExplicitAngleFields_core :
    D.toExplicitAngleFields.core = D.core :=
  rfl

@[simp]
theorem toExplicitAngleFields_counts :
    D.toExplicitAngleFields.counts = D.counts :=
  rfl

@[simp]
theorem toExplicitAngleFields_bookkeeping :
    D.toExplicitAngleFields.bookkeeping = D.bookkeeping :=
  rfl

def angleRealization :
    BoundaryAngleRealization.OuterBoundaryAngleRealization :=
  OuterBoundaryAngleW12.outerBoundaryAngleRealization D.angleWitness

@[simp]
theorem angleRealization_counts :
    D.angleRealization.counts = D.counts :=
  rfl

def angleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{0} :=
  OuterBoundaryAngleW12.boundaryBookkeepingAngleBounds D.angleWitness

@[simp]
theorem angleBounds_counts :
    D.angleBounds.counts = D.counts :=
  rfl

def bookkeepingAngleRealization :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleRealization.{0} :=
  OuterBoundaryAngleW12.boundaryBookkeepingAngleRealization D.angleWitness

@[simp]
theorem bookkeepingAngleRealization_counts :
    D.bookkeepingAngleRealization.counts = D.counts :=
  rfl

def outerBoundaryAngleData :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{0} G :=
  OuterBoundaryAngleW12.outerBoundaryAngleData D.angleWitness

@[simp]
theorem outerBoundaryAngleData_core :
    D.outerBoundaryAngleData.core = D.core :=
  rfl

@[simp]
theorem outerBoundaryAngleData_counts :
    D.outerBoundaryAngleData.counts = D.counts :=
  rfl

def outerBoundaryRealizedAngleData :
    OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{0} G :=
  OuterBoundaryAngleW12.outerBoundaryRealizedAngleData D.angleWitness

@[simp]
theorem outerBoundaryRealizedAngleData_core :
    D.outerBoundaryRealizedAngleData.core = D.core :=
  rfl

@[simp]
theorem outerBoundaryRealizedAngleData_counts :
    D.outerBoundaryRealizedAngleData.counts = D.counts :=
  rfl

def canonicalBoundaryCountHypotheses :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  (D.toExplicitAngleFields :
    ExplicitOuterBoundaryAngleFields.{0} G).canonicalBoundaryCountHypotheses

@[simp]
theorem canonicalBoundaryCountHypotheses_faceBoundary :
    D.canonicalBoundaryCountHypotheses.faceBoundary =
      D.core.faceBoundary :=
  rfl

@[simp]
theorem canonicalBoundaryCountHypotheses_counts :
    D.canonicalBoundaryCountHypotheses.counts = D.counts :=
  rfl

theorem angleLowerBound :
    D.counts.AngleLowerBound :=
  OuterBoundaryAngleW12.angleLowerBound D.angleWitness

theorem angleLowerBound_viaExplicitFields :
    D.toExplicitAngleFields.counts.AngleLowerBound :=
  D.toExplicitAngleFields.angleLowerBound

theorem boundaryAngleCountInequality :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  OuterBoundaryAngleW12.boundaryAngleCountInequality D.angleWitness

theorem boundaryAngleCountInequality_viaExplicitFields :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 := by
  simpa using
    (D.toExplicitAngleFields :
      ExplicitOuterBoundaryAngleFields.{0} G).boundaryAngleCountInequality

theorem boundaryAngleCountInequality_viaOuterBoundaryAngleData :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
    D.counts.B + 6 <= D.counts.d3 := by
  simpa using
    (D.outerBoundaryAngleData :
      OuterBoundaryAngleClosure.OuterBoundaryAngleData.{0}
        G).boundaryAngleCountInequality

theorem boundaryAngleCountInequality_viaRealizedAngleData :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
    D.counts.B + 6 <= D.counts.d3 := by
  simpa using
    (D.outerBoundaryRealizedAngleData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{0}
        G).boundaryAngleCountInequality

theorem boundaryNegativeCountInequality :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  OuterBoundaryAngleW12.boundaryNegativeCountInequality D.angleWitness

theorem boundaryNegativeCountInequality_viaExplicitFields :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 := by
  simpa using
    (D.toExplicitAngleFields :
      ExplicitOuterBoundaryAngleFields.{0} G).boundaryNegativeCountInequality

theorem boundaryNegativeCountInequality_viaOuterBoundaryAngleData :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 := by
  simpa using
    (D.outerBoundaryAngleData :
      OuterBoundaryAngleClosure.OuterBoundaryAngleData.{0}
        G).boundaryNegativeCountInequality

theorem boundaryNegativeCountInequality_viaRealizedAngleData :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 := by
  simpa using
    (D.outerBoundaryRealizedAngleData :
      OuterBoundaryAngleClosure.OuterBoundaryRealizedAngleData.{0}
        G).boundaryNegativeCountInequality

theorem boundaryAngleCount_bookkeeping :
    D.bookkeeping.d5 + 2 * D.bookkeeping.d6 + D.bookkeeping.b +
        D.bookkeeping.longArcCount + 6 <= D.bookkeeping.d3 := by
  simpa using
    (D.toExplicitAngleFields :
      ExplicitOuterBoundaryAngleFields.{0} G).boundaryAngleCount_bookkeeping

theorem boundaryNegativeCount_bookkeeping :
    D.bookkeeping.negativeElementCount +
        D.bookkeeping.longArcCount + 6 <= D.bookkeeping.d3 := by
  simpa using
    (D.toExplicitAngleFields :
      ExplicitOuterBoundaryAngleFields.{0} G).boundaryNegativeCount_bookkeeping

end ActualOuterBoundaryAngleData

end

end OuterBoundaryInstantiationW13
end Swanepoel
end ErdosProblems1066
