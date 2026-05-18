import ErdosProblems1066.Swanepoel.BoundaryWalkFinitePartitions
import ErdosProblems1066.Swanepoel.BoundaryCountingInstantiationW10
import ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement

set_option autoImplicit false

/-!
# W12 boundary classification/count extraction

This file is a small facade over the existing boundary package.  It extracts
the concrete `BoundaryCountsRealization` data already carried by the planar
boundary and concrete boundary-walk layers, and records the count/cardinality
projections in the form consumed by `BoundaryCounting`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryClassificationW12

open BoundaryClassification
open BoundaryCounting
open BoundaryWalkClassificationConcrete

universe u

noncomputable section

variable {n : Nat}

/-! ## Generic planar-boundary extraction -/

namespace PlanarBoundaryData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The boundary-count realization carried by an assembled planar-boundary
package. -/
def countsRealization
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    BoundaryCountsRealization.{u} :=
  D.outerAngleBounds.countsRealization

/-- The finite boundary bookkeeping carried by an assembled planar-boundary
package. -/
def boundaryBookkeeping
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    BoundaryBookkeeping.{u} :=
  (countsRealization D).bookkeeping

@[simp]
theorem countsRealization_toBoundaryCounts
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (countsRealization D).toBoundaryCounts = D.outerBoundaryCounts :=
  rfl

@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (boundaryBookkeeping D).toBoundaryCounts = D.outerBoundaryCounts :=
  (countsRealization D).realizes

/-- The checked angle lower bound pulled back to the extracted bookkeeping. -/
theorem boundaryBookkeeping_angleLowerBound
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    ((boundaryBookkeeping D).toBoundaryCounts).AngleLowerBound :=
  D.outerAngleBounds.projected_angleLowerBound

@[simp]
theorem outerBoundaryCounts_d3
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.d3 = (boundaryBookkeeping D).d3 := by
  rw [<- boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d4
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.d4 = (boundaryBookkeeping D).d4 := by
  rw [<- boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d5
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.d5 = (boundaryBookkeeping D).d5 := by
  rw [<- boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d6
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.d6 = (boundaryBookkeeping D).d6 := by
  rw [<- boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_b
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.b = (boundaryBookkeeping D).b := by
  rw [<- boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_B
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.B = (boundaryBookkeeping D).longArcCount := by
  rw [<- boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_negativeCount
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    D.outerBoundaryCounts.negativeCount =
      (boundaryBookkeeping D).negativeElementCount := by
  rw [<- boundaryBookkeeping_toBoundaryCounts D]
  rfl

/-- E12 stated directly in the extracted finite-bookkeeping fields. -/
theorem boundaryAngleCount_bookkeeping
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (boundaryBookkeeping D).d5 + 2 * (boundaryBookkeeping D).d6 +
        (boundaryBookkeeping D).b +
          (boundaryBookkeeping D).longArcCount + 6 <=
      (boundaryBookkeeping D).d3 := by
  simpa [BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounts.boundary_angle_count_inequality
      ((boundaryBookkeeping D).toBoundaryCounts)
      (boundaryBookkeeping_angleLowerBound D)

/-- Negative-element E12 stated directly in the extracted bookkeeping fields. -/
theorem boundaryNegativeCount_bookkeeping
    (D : PlanarBoundaryClosure.PlanarBoundaryData.{u} G) :
    (boundaryBookkeeping D).negativeElementCount +
        (boundaryBookkeeping D).longArcCount + 6 <=
      (boundaryBookkeeping D).d3 := by
  simpa [BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounts.boundary_negative_count_inequality
      ((boundaryBookkeeping D).toBoundaryCounts)
      (boundaryBookkeeping_angleLowerBound D)

end PlanarBoundaryData

/-! ## Concrete classified boundary extraction -/

namespace ClassifiedBoundary

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

/-- The universe-polymorphic boundary-count realization computed from the
concrete classified outer-boundary walk. -/
def countsRealization
    (D : OuterBoundaryClassificationInputs P) :
    BoundaryCountsRealization.{u} :=
  D.countsRealizationLift

/-- The lifted finite bookkeeping computed from the concrete classified
outer-boundary walk. -/
def boundaryBookkeeping
    (D : OuterBoundaryClassificationInputs P) :
    BoundaryBookkeeping.{u} :=
  (countsRealization D).bookkeeping

/-- The concrete Type-0 bookkeeping, with representatives literally the
selected boundary-index subtypes from the classified walk. -/
def concreteBoundaryBookkeeping
    (D : OuterBoundaryClassificationInputs P) :
    BoundaryBookkeeping.{0} :=
  D.boundaryBookkeeping

@[simp]
theorem countsRealization_toBoundaryCounts
    (D : OuterBoundaryClassificationInputs P) :
    (countsRealization D).toBoundaryCounts = D.counts :=
  rfl

@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).toBoundaryCounts = D.counts :=
  (countsRealization D).realizes

@[simp]
theorem concreteBoundaryBookkeeping_toBoundaryCounts
    (D : OuterBoundaryClassificationInputs P) :
    (concreteBoundaryBookkeeping D).toBoundaryCounts = D.counts :=
  rfl

@[simp]
theorem boundaryBookkeeping_d3
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).d3 = Fintype.card D.degree3Indices := by
  calc
    (boundaryBookkeeping D).d3 = D.counts.d3 := by
      exact congrArg BoundaryCounts.d3 (boundaryBookkeeping_toBoundaryCounts D)
    _ = Fintype.card D.degree3Indices := by
      exact D.counts_d3

@[simp]
theorem boundaryBookkeeping_d4
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).d4 = Fintype.card D.degree4Indices := by
  calc
    (boundaryBookkeeping D).d4 = D.counts.d4 := by
      exact congrArg BoundaryCounts.d4 (boundaryBookkeeping_toBoundaryCounts D)
    _ = Fintype.card D.degree4Indices := by
      exact D.counts_d4

@[simp]
theorem boundaryBookkeeping_d5
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).d5 = Fintype.card D.degree5Indices := by
  calc
    (boundaryBookkeeping D).d5 = D.counts.d5 := by
      exact congrArg BoundaryCounts.d5 (boundaryBookkeeping_toBoundaryCounts D)
    _ = Fintype.card D.degree5Indices := by
      exact D.counts_d5

@[simp]
theorem boundaryBookkeeping_d6
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).d6 = Fintype.card D.degree6Indices := by
  calc
    (boundaryBookkeeping D).d6 = D.counts.d6 := by
      exact congrArg BoundaryCounts.d6 (boundaryBookkeeping_toBoundaryCounts D)
    _ = Fintype.card D.degree6Indices := by
      exact D.counts_d6

@[simp]
theorem boundaryBookkeeping_b
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).b =
      Fintype.card D.nontriangleEdgeIndices := by
  calc
    (boundaryBookkeeping D).b = D.counts.b := by
      exact congrArg BoundaryCounts.b (boundaryBookkeeping_toBoundaryCounts D)
    _ = Fintype.card D.nontriangleEdgeIndices := by
      exact D.counts_b

@[simp]
theorem boundaryBookkeeping_B
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).longArcCount =
      Fintype.card D.longArcIndices := by
  calc
    (boundaryBookkeeping D).longArcCount = D.counts.B := by
      exact congrArg BoundaryCounts.B (boundaryBookkeeping_toBoundaryCounts D)
    _ = Fintype.card D.longArcIndices := by
      exact D.counts_B

@[simp]
theorem concreteBoundaryBookkeeping_triangleEdgeCount
    (D : OuterBoundaryClassificationInputs P) :
    (concreteBoundaryBookkeeping D).triangleEdgeCount =
      Fintype.card D.triangleEdgeIndices := by
  change D.boundaryBookkeeping.triangleEdgeCount =
    Fintype.card D.triangleEdgeIndices
  exact D.boundaryBookkeeping_triangleEdgeCount

@[simp]
theorem boundaryBookkeeping_negativeElementCount
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).negativeElementCount =
      Fintype.card D.nontriangleEdgeIndices +
        Fintype.card D.degree5Indices +
        Fintype.card D.degree6Indices := by
  rw [BoundaryBookkeeping.negativeElementCount,
    boundaryBookkeeping_b D, boundaryBookkeeping_d5 D,
    boundaryBookkeeping_d6 D]

/-- The extracted concrete degree counts partition the selected boundary
cycle. -/
theorem degreeCounts_add_eq_boundaryLength
    (D : OuterBoundaryClassificationInputs P) :
    (boundaryBookkeeping D).d3 + (boundaryBookkeeping D).d4 +
        (boundaryBookkeeping D).d5 + (boundaryBookkeeping D).d6 =
      P.outerCycle.length := by
  simpa using D.counts_degree_sum_eq_length

/-- The extracted triangle/nontriangle edge counts partition the selected
boundary cycle edges. -/
theorem concreteTriangleEdgeCount_add_b_eq_boundaryLength
    (D : OuterBoundaryClassificationInputs P) :
    (concreteBoundaryBookkeeping D).triangleEdgeCount +
        (concreteBoundaryBookkeeping D).b =
      P.outerCycle.length := by
  calc
    (concreteBoundaryBookkeeping D).triangleEdgeCount +
        (concreteBoundaryBookkeeping D).b =
      (concreteBoundaryBookkeeping D).triangleEdgeCount + D.counts.b := by
        have hb : (concreteBoundaryBookkeeping D).b = D.counts.b := by
          change ((concreteBoundaryBookkeeping D).toBoundaryCounts).b =
            D.counts.b
          exact congrArg BoundaryCounts.b
            (concreteBoundaryBookkeeping_toBoundaryCounts D)
        rw [hb]
    _ = P.outerCycle.length := by
      simpa [concreteBoundaryBookkeeping] using
        D.boundaryBookkeeping_triangleEdgeCount_add_counts_b

/-- E12 for the concrete classified counts, from any supplied angle lower
bound on those counts. -/
theorem boundaryAngleCount_of_angleLowerBound
    (D : OuterBoundaryClassificationInputs P)
    (hangle : D.counts.AngleLowerBound) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality D.counts hangle

/-- Negative-element E12 for the concrete classified counts, from any supplied
angle lower bound on those counts. -/
theorem boundaryNegativeCount_of_angleLowerBound
    (D : OuterBoundaryClassificationInputs P)
    (hangle : D.counts.AngleLowerBound) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality D.counts hangle

end ClassifiedBoundary

/-! ## Extraction from concrete local angle witnesses -/

namespace UnitSeparatedAngleFamilies

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}
variable {D : OuterBoundaryClassificationInputs P}

/-- The boundary angle-bound package obtained from the concrete
subtype-indexed local angle witnesses. -/
def toBoundaryBookkeepingAngleBounds
    (W : BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} where
  countsRealization := ClassifiedBoundary.countsRealization D
  geometricAngleSum := W.geometricAngleSum
  forced_le_geometric := by
    simpa using W.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa using W.geometric_le_polygon

@[simp]
theorem toBoundaryBookkeepingAngleBounds_counts
    (W : BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    (toBoundaryBookkeepingAngleBounds W).counts = D.counts :=
  rfl

@[simp]
theorem toBoundaryBookkeepingAngleBounds_bookkeeping
    (W : BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    (toBoundaryBookkeepingAngleBounds W).countsRealization.bookkeeping =
      ClassifiedBoundary.boundaryBookkeeping D :=
  rfl

/-- The concrete local angle witnesses give the counting-layer lower bound. -/
theorem angleLowerBound
    (W : BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    D.counts.AngleLowerBound :=
  W.angleLowerBound

/-- E12 after extracting the concrete count realization and local angle
witnesses. -/
theorem boundaryAngleCount
    (W : BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  ClassifiedBoundary.boundaryAngleCount_of_angleLowerBound D W.angleLowerBound

/-- Negative-element E12 after extracting the concrete count realization and
local angle witnesses. -/
theorem boundaryNegativeCount
    (W : BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies D) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  ClassifiedBoundary.boundaryNegativeCount_of_angleLowerBound D W.angleLowerBound

end UnitSeparatedAngleFamilies

/-! ## M8 route extraction -/

namespace M8BoundaryRouteData

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

/-- The boundary-count realization carried by the planar-boundary package
inside the M8 route. -/
def countsRealization
    (D : BoundaryFaceCountingToM8.M8BoundaryRouteData.{u} C hmin) :
    BoundaryCountsRealization.{u} :=
  D.planarBoundary.outerAngleBounds.countsRealization

/-- The finite boundary bookkeeping carried by the M8 route. -/
def boundaryBookkeeping
    (D : BoundaryFaceCountingToM8.M8BoundaryRouteData.{u} C hmin) :
    BoundaryBookkeeping.{u} :=
  (countsRealization D).bookkeeping

@[simp]
theorem countsRealization_toBoundaryCounts
    (D : BoundaryFaceCountingToM8.M8BoundaryRouteData.{u} C hmin) :
    (countsRealization D).toBoundaryCounts =
      D.faceCounting.concrete.boundaryCounts :=
  rfl

@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : BoundaryFaceCountingToM8.M8BoundaryRouteData.{u} C hmin) :
    (boundaryBookkeeping D).toBoundaryCounts =
      D.faceCounting.concrete.boundaryCounts :=
  (countsRealization D).realizes

theorem boundaryAngleCount_bookkeeping
    (D : BoundaryFaceCountingToM8.M8BoundaryRouteData.{u} C hmin) :
    (boundaryBookkeeping D).d5 + 2 * (boundaryBookkeeping D).d6 +
        (boundaryBookkeeping D).b +
          (boundaryBookkeeping D).longArcCount + 6 <=
      (boundaryBookkeeping D).d3 := by
  simpa [BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounts.boundary_angle_count_inequality
      ((boundaryBookkeeping D).toBoundaryCounts)
      (by
        simpa [boundaryBookkeeping_toBoundaryCounts D] using
          D.faceCounting.concrete.boundaryAngleLowerBound)

theorem boundaryNegativeCount_bookkeeping
    (D : BoundaryFaceCountingToM8.M8BoundaryRouteData.{u} C hmin) :
    (boundaryBookkeeping D).negativeElementCount +
        (boundaryBookkeeping D).longArcCount + 6 <=
      (boundaryBookkeeping D).d3 := by
  simpa [BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounts.boundary_negative_count_inequality
      ((boundaryBookkeeping D).toBoundaryCounts)
      (by
        simpa [boundaryBookkeeping_toBoundaryCounts D] using
          D.faceCounting.concrete.boundaryAngleLowerBound)

end M8BoundaryRouteData

namespace M8RefinedBoundaryRouteData

variable {C : _root_.UDConfig n}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

/-- The refined M8 route exposes the same boundary-count realization as its
refined planar face data. -/
def countsRealization
    (D :
      PlanarBoundaryFaceDataRefinement.M8RefinedBoundaryRouteData.{u}
        C hmin) :
    BoundaryCountsRealization.{u} :=
  D.boundaryCountsRealization

/-- The refined M8 route exposes the same finite boundary bookkeeping as its
refined planar face data. -/
def boundaryBookkeeping
    (D :
      PlanarBoundaryFaceDataRefinement.M8RefinedBoundaryRouteData.{u}
        C hmin) :
    BoundaryBookkeeping.{u} :=
  D.boundaryBookkeeping

@[simp]
theorem countsRealization_toBoundaryCounts
    (D :
      PlanarBoundaryFaceDataRefinement.M8RefinedBoundaryRouteData.{u}
        C hmin) :
    (countsRealization D).toBoundaryCounts =
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts := by
  simpa [countsRealization] using
    D.faceData.boundaryCountsRealization_toBoundaryCounts

@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D :
      PlanarBoundaryFaceDataRefinement.M8RefinedBoundaryRouteData.{u}
        C hmin) :
    (boundaryBookkeeping D).toBoundaryCounts =
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts := by
  simp [boundaryBookkeeping]

/-- E12 on the refined M8 route, stated in the extracted bookkeeping fields. -/
theorem boundaryAngleCount_bookkeeping
    (D :
      PlanarBoundaryFaceDataRefinement.M8RefinedBoundaryRouteData.{u}
        C hmin) :
    (boundaryBookkeeping D).d5 + 2 * (boundaryBookkeeping D).d6 +
        (boundaryBookkeeping D).b +
          (boundaryBookkeeping D).longArcCount + 6 <=
      (boundaryBookkeeping D).d3 := by
  simpa [boundaryBookkeeping] using D.boundaryAngleCount_bookkeeping

/-- Negative-element E12 on the refined M8 route, stated in the extracted
bookkeeping fields. -/
theorem boundaryNegativeCount_bookkeeping
    (D :
      PlanarBoundaryFaceDataRefinement.M8RefinedBoundaryRouteData.{u}
        C hmin) :
    (boundaryBookkeeping D).negativeElementCount +
        (boundaryBookkeeping D).longArcCount + 6 <=
      (boundaryBookkeeping D).d3 := by
  simpa [boundaryBookkeeping] using D.boundaryNegativeCount_bookkeeping

end M8RefinedBoundaryRouteData

end

end BoundaryClassificationW12
end Swanepoel
end ErdosProblems1066
