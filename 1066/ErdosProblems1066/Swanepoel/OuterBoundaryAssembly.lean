import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.BoundaryClassification
import ErdosProblems1066.Swanepoel.BoundaryAngleInterface
import ErdosProblems1066.Swanepoel.BoundaryCounting
import ErdosProblems1066.Swanepoel.FaceCountingBridge

/-!
# Outer-boundary assembly

This module is a conditional adapter.  It combines an honest outer-boundary
core with finite boundary bookkeeping and an explicit geometric angle package,
then exposes the face-boundary and count hypotheses already consumed by the
Swanepoel reduction interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryAssembly

open BoundaryCounting

universe u

variable {n : Nat}

/-- Boundary bookkeeping together with an angle package for the same realized
outer-boundary counts. -/
structure BoundaryBookkeepingAngleRealization where
  countsRealization : BoundaryClassification.BoundaryCountsRealization.{u}
  anglePackage : BoundaryAngleInterface.BoundaryAngleLowerBoundPackage
  angle_counts_eq_realized :
    anglePackage.counts = countsRealization.toBoundaryCounts

namespace BoundaryBookkeepingAngleRealization

/-- The boundary counts produced by the finite bookkeeping realization. -/
def counts (A : BoundaryBookkeepingAngleRealization.{u}) : BoundaryCounts :=
  A.countsRealization.toBoundaryCounts

/-- Constructor from separately supplied bookkeeping and angle data. -/
def of
    (R : BoundaryClassification.BoundaryCountsRealization.{u})
    (P : BoundaryAngleInterface.BoundaryAngleLowerBoundPackage)
    (hcounts : P.counts = R.toBoundaryCounts) :
    BoundaryBookkeepingAngleRealization.{u} where
  countsRealization := R
  anglePackage := P
  angle_counts_eq_realized := hcounts

/-- The angle package targets the bookkeeping-realized counts. -/
theorem anglePackage_counts_eq
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.anglePackage.counts = A.counts :=
  A.angle_counts_eq_realized

/-- The angle lower bound transported to the bookkeeping-realized counts. -/
def angleLowerBound
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.AngleLowerBound :=
  Eq.mp (congrArg BoundaryCounts.AngleLowerBound
      A.angle_counts_eq_realized)
    A.anglePackage.angleLowerBound

/-- The assembled bookkeeping and angle data imply the outer-boundary count. -/
theorem boundaryAngleCountInequality
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality
    A.counts A.angleLowerBound

/-- The same assembled data imply the negative-element count form. -/
theorem boundaryNegativeCountInequality
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.negativeCount + A.counts.B + 6 <= A.counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality
    A.counts A.angleLowerBound

end BoundaryBookkeepingAngleRealization

/-- The face-boundary and count hypotheses expected by downstream reductions. -/
structure FaceBoundaryCountHypotheses
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : PlanarInterface.FaceBoundaryHypotheses G.toStraightLine
  canonicalBoundaryCounts :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G

namespace FaceBoundaryCountHypotheses

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- The unit-distance face-boundary data retained by the count package. -/
def unitDistanceFaceBoundary
    (H : FaceBoundaryCountHypotheses G) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses G :=
  H.canonicalBoundaryCounts.faceBoundary

/-- The realized outer-boundary counts retained by the count package. -/
def counts (H : FaceBoundaryCountHypotheses G) : BoundaryCounts :=
  H.canonicalBoundaryCounts.counts

/-- The angle lower bound retained by the count package. -/
def angleLowerBound
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.AngleLowerBound :=
  H.canonicalBoundaryCounts.angleLowerBound

/-- The canonical graph supplies the noncrossing hypothesis. -/
theorem noncrossing
    (H : FaceBoundaryCountHypotheses G) :
    PlanarInterface.PairwiseNoncrossing G.config G.edgeSet :=
  H.canonicalBoundaryCounts.noncrossing

/-- The packaged hypotheses imply the outer-boundary count. -/
theorem boundaryAngleCountInequality
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.d5 + 2 * H.counts.d6 + H.counts.b + H.counts.B + 6 <=
      H.counts.d3 :=
  H.canonicalBoundaryCounts.boundaryAngleCountInequality

/-- The packaged hypotheses imply the negative-element count form. -/
theorem boundaryNegativeCountInequality
    (H : FaceBoundaryCountHypotheses G) :
    H.counts.negativeCount + H.counts.B + 6 <= H.counts.d3 :=
  H.canonicalBoundaryCounts.boundaryNegativeCountInequality

end FaceBoundaryCountHypotheses

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-- Assemble the canonical count hypotheses from an outer-boundary core,
realized boundary bookkeeping, and a matching angle package. -/
def canonicalBoundaryCountHypothesesOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  P.toCanonicalBoundaryCountHypotheses
    A.counts A.angleLowerBound

/-- Assemble the face-boundary and count hypotheses used downstream. -/
def faceBoundaryCountHypothesesOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    FaceBoundaryCountHypotheses G where
  faceBoundary := P.toFaceBoundaryHypotheses
  canonicalBoundaryCounts :=
    canonicalBoundaryCountHypothesesOfCore P A

/-- Conditional assembly theorem: honest core data plus matching bookkeeping
and angle data produce the downstream face-boundary/count hypotheses. -/
theorem existsFaceBoundaryCountHypothesesOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    Exists fun H : FaceBoundaryCountHypotheses G =>
      H.faceBoundary = P.toFaceBoundaryHypotheses /\
        H.canonicalBoundaryCounts =
          canonicalBoundaryCountHypothesesOfCore P A :=
  Exists.intro (faceBoundaryCountHypothesesOfCore P A)
    (And.intro rfl rfl)

/-- The assembled core/bookkeeping/angle data imply the E12 count needed by
outer-boundary reductions. -/
theorem boundaryAngleCountInequalityOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.d5 + 2 * A.counts.d6 + A.counts.b + A.counts.B + 6 <=
      A.counts.d3 :=
  (canonicalBoundaryCountHypothesesOfCore P A).boundaryAngleCountInequality

/-- The assembled core/bookkeeping/angle data imply the negative-element form
needed by downstream counting reductions. -/
theorem boundaryNegativeCountInequalityOfCore
    (P : OuterBoundaryCore G)
    (A : BoundaryBookkeepingAngleRealization.{u}) :
    A.counts.negativeCount + A.counts.B + 6 <= A.counts.d3 :=
  (canonicalBoundaryCountHypothesesOfCore P A).boundaryNegativeCountInequality

end OuterBoundaryAssembly
end Swanepoel
end ErdosProblems1066
