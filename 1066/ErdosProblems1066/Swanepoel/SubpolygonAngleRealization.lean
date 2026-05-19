import ErdosProblems1066.Swanepoel.SubpolygonCore
import ErdosProblems1066.Swanepoel.BoundaryAngleInterface
import ErdosProblems1066.Swanepoel.AngleGeometry

/-!
# Concrete subpolygon angle realization

This module combines the concrete subpolygon data from `SubpolygonCore` with
the geometric angle-sum comparisons used by `BoundaryAngleInterface`.

It does not build the geometric angle sum or prove the comparisons.  Callers
must supply those real inequalities, and this file only routes them to the
checked E13 counting conclusions.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonAngleRealization

open BoundaryAngleInterface
open BoundaryCounting
open FaceReduction
open SubpolygonCore

universe u

noncomputable section

variable {n : Nat}

/-! ## Angle data over concrete subpolygon counts -/

/--
Angle-sum data for the degree counts computed from an induced subpolygon
boundary.

The two inequalities are the exact real comparisons needed to turn the
computed degree counts into a `SubpolygonDegreeCounts.AngleLowerBound`.
-/
structure ConcreteAngleBounds
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : BoundaryCycle G) (S : InducedVertexSet G C) where
  geometricAngleSum : Real
  forced_le_geometric :
    S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= S.degreeCounts.polygonAngleSum

namespace ConcreteAngleBounds

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {S : InducedVertexSet G C}

/-- The computed degree counts carried by the induced subpolygon data. -/
def counts (_A : ConcreteAngleBounds G C S) : SubpolygonDegreeCounts :=
  S.degreeCounts

/-- Convert the concrete computed counts and angle comparisons to the
boundary-angle interface package. -/
def toSubpolygonAngleLowerBoundPackage
    (A : ConcreteAngleBounds G C S) :
    SubpolygonAngleLowerBoundPackage where
  counts := A.counts
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts] using A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts] using A.geometric_le_polygon

/-- The counting-layer angle lower bound for the computed counts. -/
theorem angleLowerBound
    (A : ConcreteAngleBounds G C S) :
    S.degreeCounts.AngleLowerBound := by
  simpa [toSubpolygonAngleLowerBoundPackage, counts] using
    A.toSubpolygonAngleLowerBoundPackage.angleLowerBound

/-- Convert the angle data to the core degree-count package. -/
def toDegreeCountData
    (A : ConcreteAngleBounds G C S) :
    DegreeCountData G C S where
  angleLowerBound := A.angleLowerBound

/-- E13 with high-degree slack for the concrete induced subpolygon counts. -/
theorem lowDegreeWithHighDegreeSlack
    (A : ConcreteAngleBounds G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa [toSubpolygonAngleLowerBoundPackage, counts] using
    A.toSubpolygonAngleLowerBoundPackage.lowDegreeWithHighDegreeSlack

/-- The same slack conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeWithHighDegreeSlack_viaSubpolygonCore
    (A : ConcreteAngleBounds G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  A.toDegreeCountData.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for the concrete counts. -/
theorem lowDegreeInequality
    (A : ConcreteAngleBounds G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa [toSubpolygonAngleLowerBoundPackage, counts] using
    A.toSubpolygonAngleLowerBoundPackage.lowDegreeInequality

/-- The same low-degree conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeInequality_viaSubpolygonCore
    (A : ConcreteAngleBounds G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  A.toDegreeCountData.lowDegreeInequality

end ConcreteAngleBounds

/-! ## Native triangulation rows for subpolygon angle sums -/

/-- Previous corner in a three-corner triangle, used to state actual
Euclidean triangle angles without importing the outer-boundary triangulation
module and creating an import cycle. -/
def triangleCornerPrev (c : Fin 3) : Fin 3 :=
  { val := (c.val + 2) % 3, isLt := Nat.mod_lt _ (by decide) }

/-- Next corner in a three-corner triangle, used to state actual Euclidean
triangle angles. -/
def triangleCornerNext (c : Fin 3) : Fin 3 :=
  { val := (c.val + 1) % 3, isLt := Nat.mod_lt _ (by decide) }

/-- The actual interior angle at a corner of a concrete triangle. -/
def triangleCornerAngle
    (trianglePoint : Fin 3 -> PlanarInterface.Point) (c : Fin 3) : Real :=
  AngleGeometry.angleAt
    (trianglePoint (triangleCornerPrev c))
    (trianglePoint c)
    (trianglePoint (triangleCornerNext c))

/-- The actual predecessor/current/successor angle at one subpolygon boundary
index, for an explicitly supplied predecessor map. -/
def boundaryInteriorAngleAt
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G)
    (previousIndex : Fin C.length -> Fin C.length)
    (k : Fin C.length) : Real :=
  AngleGeometry.angleAt
    (C.point (previousIndex k))
    (C.point k)
    (C.point (PlanarInterface.cyclicSucc C.length_pos k))

/-- The actual predecessor/current/successor angle sum along a subpolygon
boundary, for an explicitly supplied predecessor map. -/
def boundaryInteriorAngleSum
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G)
    (previousIndex : Fin C.length -> Fin C.length) : Real :=
  Finset.sum (Finset.univ : Finset (Fin C.length))
    (fun k => boundaryInteriorAngleAt C previousIndex k)

/--
Native subpolygon triangulation rows.

This is the exact local analogue of
`PlanarBoundaryFaceDataRefinement.SimplePolygonInteriorAngleTriangulationRows`,
kept here without importing that downstream module.  The rows require real
triangle corner points, each triangle's actual angle sum, and an equality
between the subpolygon boundary angle sum and the sum of those triangle
angles.  The count compatibility field is the remaining data that connects
the boundary cycle length to the computed E13 degree-count vertex total.
-/
structure ConcreteSubpolygonInteriorAngleTriangulationRows
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : BoundaryCycle G) (S : InducedVertexSet G C) : Type (u + 1) where
  previousIndex : Fin C.length -> Fin C.length
  previousIndex_succ :
    forall k : Fin C.length,
      PlanarInterface.cyclicSucc C.length_pos (previousIndex k) = k
  boundaryVertexCount_eq_degreeVertexCount :
    C.length = S.degreeCounts.vertexCount
  boundaryLength_ge_three : 3 <= C.length
  Triangle : Type u
  triangleFintype : Fintype Triangle
  triangleCount_eq_boundaryLength_sub_two :
    @Fintype.card Triangle triangleFintype = C.length - 2
  trianglePoint : Triangle -> Fin 3 -> PlanarInterface.Point
  triangleAngleSum_eq_pi :
    forall T : Triangle,
      Finset.sum (Finset.univ : Finset (Fin 3))
          (fun c => triangleCornerAngle (trianglePoint T) c) =
        Real.pi
  boundaryInteriorAngleSum_eq_triangleAngleSum :
    boundaryInteriorAngleSum C previousIndex =
      letI := triangleFintype
      Finset.sum (Finset.univ : Finset Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => triangleCornerAngle (trianglePoint T) c))

namespace ConcreteSubpolygonInteriorAngleTriangulationRows

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {S : InducedVertexSet G C}

/-- A genuine triangulation with `boundary length - 2` triangles gives the
polygon-angle side of the computed E13 subpolygon count, once the boundary
length is identified with the degree-count vertex total. -/
theorem triangleAngleSum_eq_subpolygonPolygonAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S) :
    letI := R.triangleFintype
    Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => triangleCornerAngle (R.trianglePoint T) c)) =
      S.degreeCounts.polygonAngleSum := by
  classical
  letI := R.triangleFintype
  have htwoC : 2 <= C.length :=
    Nat.le_trans (by norm_num) R.boundaryLength_ge_three
  have htwoCounts : 2 <= S.degreeCounts.vertexCount := by
    rw [<- R.boundaryVertexCount_eq_degreeVertexCount]
    exact htwoC
  calc
    Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => triangleCornerAngle (R.trianglePoint T) c)) =
        Finset.sum (Finset.univ : Finset R.Triangle) (fun _ => Real.pi) := by
          exact Finset.sum_congr rfl
            (fun T _ => R.triangleAngleSum_eq_pi T)
    _ = (Fintype.card R.Triangle : Real) * Real.pi := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ((C.length - 2 : Nat) : Real) * Real.pi := by
          rw [R.triangleCount_eq_boundaryLength_sub_two]
    _ = ((S.degreeCounts.vertexCount - 2 : Nat) : Real) * Real.pi := by
          rw [R.boundaryVertexCount_eq_degreeVertexCount]
    _ = Real.pi * ((S.degreeCounts.vertexCount : Real) - 2) := by
          rw [Nat.cast_sub htwoCounts]
          ring
    _ = S.degreeCounts.polygonAngleSum := by
          rfl

/-- The native subpolygon boundary interior-angle sum equals the E13
polygon-angle side under the explicit triangulation rows. -/
theorem boundaryInteriorAngleSum_eq_subpolygonPolygonAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S) :
    boundaryInteriorAngleSum C R.previousIndex =
      S.degreeCounts.polygonAngleSum := by
  classical
  rw [R.boundaryInteriorAngleSum_eq_triangleAngleSum]
  exact R.triangleAngleSum_eq_subpolygonPolygonAngleSum

/-- Inequality form consumed by aggregate subpolygon angle packages. -/
theorem boundaryInteriorAngleSum_le_subpolygonPolygonAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S) :
    boundaryInteriorAngleSum C R.previousIndex <=
      S.degreeCounts.polygonAngleSum :=
  le_of_eq R.boundaryInteriorAngleSum_eq_subpolygonPolygonAngleSum

/-- Build the existing aggregate subpolygon angle-bound package from a real
geometric angle sum once that sum is identified with the triangulated
subpolygon boundary interior-angle sum. -/
def toConcreteAngleBounds
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S)
    (geometricAngleSum : Real)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hgeometric :
      geometricAngleSum = boundaryInteriorAngleSum C R.previousIndex) :
    ConcreteAngleBounds G C S where
  geometricAngleSum := geometricAngleSum
  forced_le_geometric := hforced
  geometric_le_polygon := by
    rw [hgeometric]
    exact R.boundaryInteriorAngleSum_le_subpolygonPolygonAngleSum

/-- Build aggregate concrete angle bounds by taking the genuine triangulated
subpolygon boundary interior-angle sum as the geometric angle sum. -/
def toConcreteAngleBoundsOfBoundaryInteriorAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <=
        boundaryInteriorAngleSum C R.previousIndex) :
    ConcreteAngleBounds G C S :=
  R.toConcreteAngleBounds
    (boundaryInteriorAngleSum C R.previousIndex) hforced rfl

@[simp]
theorem toConcreteAngleBoundsOfBoundaryInteriorAngleSum_geometricAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <=
        boundaryInteriorAngleSum C R.previousIndex) :
    (R.toConcreteAngleBoundsOfBoundaryInteriorAngleSum hforced).geometricAngleSum =
      boundaryInteriorAngleSum C R.previousIndex :=
  rfl

/-- A genuine triangulation plus the pointwise forced-angle lower bound for
the actual boundary interior-angle sum gives the computed E13 angle lower
bound. -/
theorem angleLowerBound_of_forced_le_boundaryInteriorAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <=
        boundaryInteriorAngleSum C R.previousIndex) :
    S.degreeCounts.AngleLowerBound :=
  (R.toConcreteAngleBoundsOfBoundaryInteriorAngleSum hforced).angleLowerBound

/-- Direct E13 high-degree slack from genuine triangulation rows and the
forced-angle lower bound for the actual boundary interior-angle sum. -/
theorem lowDegreeWithHighDegreeSlack_of_forced_le_boundaryInteriorAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <=
        boundaryInteriorAngleSum C R.previousIndex) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  (R.toConcreteAngleBoundsOfBoundaryInteriorAngleSum hforced).lowDegreeWithHighDegreeSlack

/-- Direct low-degree E13 conclusion from genuine triangulation rows and the
forced-angle lower bound for the actual boundary interior-angle sum. -/
theorem lowDegreeInequality_of_forced_le_boundaryInteriorAngleSum
    (R : ConcreteSubpolygonInteriorAngleTriangulationRows.{u} G C S)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <=
        boundaryInteriorAngleSum C R.previousIndex) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  (R.toConcreteAngleBoundsOfBoundaryInteriorAngleSum hforced).lowDegreeInequality

end ConcreteSubpolygonInteriorAngleTriangulationRows

/-! ## Pointwise real angle realizations -/

/--
Explicit real angle data realizing the E13 subpolygon angle count for computed
induced boundary degrees.

The five families are the pieces of geometric angle mass assigned to boundary
vertices of induced degrees `2`, ..., `6`.  `unaccountedAngle` is the remaining
geometric angle mass; its nonnegativity is the only fact about unused angle
mass required here.
-/
structure ConcreteAngleRealization
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : BoundaryCycle G) (S : InducedVertexSet G C) where
  degree2Angle : Fin S.degreeCounts.D2 -> Real
  degree3Angle : Fin S.degreeCounts.D3 -> Real
  degree4Angle : Fin S.degreeCounts.D4 -> Real
  degree5Angle : Fin S.degreeCounts.D5 -> Real
  degree6Angle : Fin S.degreeCounts.D6 -> Real
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2)) degree2Angle +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3)) degree3Angle +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4)) degree4Angle +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5)) degree5Angle +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6)) degree6Angle +
      unaccountedAngle
  degree2_lower :
    forall i, Real.pi / 3 <= degree2Angle i
  degree3_lower :
    forall i, (Real.pi / 3) * (2 : Real) <= degree3Angle i
  degree4_lower :
    forall i, (Real.pi / 3) * (3 : Real) <= degree4Angle i
  degree5_lower :
    forall i, (Real.pi / 3) * (4 : Real) <= degree5Angle i
  degree6_lower :
    forall i, (Real.pi / 3) * (5 : Real) <= degree6Angle i
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon :
    geometricAngleSum <= S.degreeCounts.polygonAngleSum

namespace ConcreteAngleRealization

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {S : InducedVertexSet G C}

/-- The geometric angle mass explicitly assigned to E13 degree classes. -/
def accountedAngleSum
    (R : ConcreteAngleRealization G C S) : Real :=
  Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2)) R.degree2Angle +
    Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3)) R.degree3Angle +
    Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4)) R.degree4Angle +
    Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5)) R.degree5Angle +
    Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6)) R.degree6Angle

/-- The formal sum of the lower-bound contributions used by E13. -/
def lowerContributionSum (c : SubpolygonDegreeCounts) : Real :=
  Finset.sum (Finset.univ : Finset (Fin c.D2))
      (fun _ => Real.pi / 3) +
    Finset.sum (Finset.univ : Finset (Fin c.D3))
      (fun _ => (Real.pi / 3) * (2 : Real)) +
    Finset.sum (Finset.univ : Finset (Fin c.D4))
      (fun _ => (Real.pi / 3) * (3 : Real)) +
    Finset.sum (Finset.univ : Finset (Fin c.D5))
      (fun _ => (Real.pi / 3) * (4 : Real)) +
    Finset.sum (Finset.univ : Finset (Fin c.D6))
      (fun _ => (Real.pi / 3) * (5 : Real))

/-- The lower-contribution sum is exactly the forced E13 angle side. -/
theorem forcedSubpolygonAngleSum_eq_lowerContributionSum
    (c : SubpolygonDegreeCounts) :
    c.forcedSubpolygonAngleSum = lowerContributionSum c := by
  simp [SubpolygonDegreeCounts.forcedSubpolygonAngleSum,
    lowerContributionSum, Finset.sum_const]
  ring

/-- Build a pointwise real realization from an already-proved E13 angle lower
bound on the computed induced counts.

This is a concrete extraction: every accounted angle is set to its sharp
formal lower contribution, the unaccounted angle is zero, and the supplied
angle lower bound gives the polygon-angle comparison.
-/
def ofAngleLowerBound
    (hangle : S.degreeCounts.AngleLowerBound) :
    ConcreteAngleRealization G C S where
  degree2Angle := fun _ => Real.pi / 3
  degree3Angle := fun _ => (Real.pi / 3) * (2 : Real)
  degree4Angle := fun _ => (Real.pi / 3) * (3 : Real)
  degree5Angle := fun _ => (Real.pi / 3) * (4 : Real)
  degree6Angle := fun _ => (Real.pi / 3) * (5 : Real)
  unaccountedAngle := 0
  geometricAngleSum := S.degreeCounts.forcedSubpolygonAngleSum
  geometricAngleSum_eq := by
    simpa [lowerContributionSum] using
      forcedSubpolygonAngleSum_eq_lowerContributionSum S.degreeCounts
  degree2_lower := fun _ => le_rfl
  degree3_lower := fun _ => le_rfl
  degree4_lower := fun _ => le_rfl
  degree5_lower := fun _ => le_rfl
  degree6_lower := fun _ => le_rfl
  unaccounted_nonnegative := le_rfl
  geometric_le_polygon := hangle

/-- Pointwise geometric lower bounds imply the forced contribution bound. -/
theorem lowerContributionSum_le_accountedAngleSum
    (R : ConcreteAngleRealization G C S) :
    lowerContributionSum S.degreeCounts <= R.accountedAngleSum := by
  have h2 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2))
          (fun _ => Real.pi / 3) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2))
          R.degree2Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D2)))
      (fun i _hi => R.degree2_lower i)
  have h3 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3))
          (fun _ => (Real.pi / 3) * (2 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3))
          R.degree3Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D3)))
      (fun i _hi => R.degree3_lower i)
  have h4 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4))
          (fun _ => (Real.pi / 3) * (3 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4))
          R.degree4Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D4)))
      (fun i _hi => R.degree4_lower i)
  have h5 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5))
          (fun _ => (Real.pi / 3) * (4 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5))
          R.degree5Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D5)))
      (fun i _hi => R.degree5_lower i)
  have h6 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6))
          (fun _ => (Real.pi / 3) * (5 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6))
          R.degree6Angle :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D6)))
      (fun i _hi => R.degree6_lower i)
  unfold lowerContributionSum accountedAngleSum
  nlinarith [h2, h3, h4, h5, h6]

/-- The explicit geometric accounting gives the forced-vs-geometric bound. -/
theorem forced_le_geometricAngleSum
    (R : ConcreteAngleRealization G C S) :
    S.degreeCounts.forcedSubpolygonAngleSum <= R.geometricAngleSum := by
  rw [forcedSubpolygonAngleSum_eq_lowerContributionSum]
  have haccounted := R.lowerContributionSum_le_accountedAngleSum
  have hgeom_eq :
      R.geometricAngleSum = R.accountedAngleSum + R.unaccountedAngle := by
    simpa [accountedAngleSum] using R.geometricAngleSum_eq
  rw [hgeom_eq]
  nlinarith [haccounted, R.unaccounted_nonnegative]

/-- Forget the explicit angle realization to the aggregate angle-bound package. -/
def toConcreteAngleBounds
    (R : ConcreteAngleRealization G C S) :
    ConcreteAngleBounds G C S where
  geometricAngleSum := R.geometricAngleSum
  forced_le_geometric := R.forced_le_geometricAngleSum
  geometric_le_polygon := R.geometric_le_polygon

/-- Forget the explicit angle realization to the boundary-angle interface
package. -/
def toSubpolygonAngleLowerBoundPackage
    (R : ConcreteAngleRealization G C S) :
    SubpolygonAngleLowerBoundPackage :=
  R.toConcreteAngleBounds.toSubpolygonAngleLowerBoundPackage

@[simp]
theorem toConcreteAngleBounds_geometricAngleSum
    (R : ConcreteAngleRealization G C S) :
    R.toConcreteAngleBounds.geometricAngleSum = R.geometricAngleSum :=
  rfl

@[simp]
theorem toSubpolygonAngleLowerBoundPackage_counts
    (R : ConcreteAngleRealization G C S) :
    R.toSubpolygonAngleLowerBoundPackage.counts = S.degreeCounts :=
  rfl

/-- The counting-layer angle lower bound for the computed counts. -/
theorem angleLowerBound
    (R : ConcreteAngleRealization G C S) :
    S.degreeCounts.AngleLowerBound :=
  R.toConcreteAngleBounds.angleLowerBound

/-- Convert the explicit angle realization to the core degree-count package. -/
def toDegreeCountData
    (R : ConcreteAngleRealization G C S) :
    DegreeCountData G C S :=
  R.toConcreteAngleBounds.toDegreeCountData

/-- E13 with high-degree slack for the computed induced subpolygon counts. -/
theorem lowDegreeWithHighDegreeSlack
    (R : ConcreteAngleRealization G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  R.toConcreteAngleBounds.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for the computed counts. -/
theorem lowDegreeInequality
    (R : ConcreteAngleRealization G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  R.toConcreteAngleBounds.lowDegreeInequality

end ConcreteAngleRealization

/-! ## Full concrete subpolygon packages -/

/--
Concrete subpolygon boundary data, its induced vertex set, and the explicit
angle comparisons for the computed induced boundary degree counts.
-/
structure ConcreteSubpolygon
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  vertexSet : InducedVertexSet G boundary
  angleBounds : ConcreteAngleBounds G boundary vertexSet

namespace ConcreteSubpolygon

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The computed degree counts carried by the concrete subpolygon. -/
def counts (P : ConcreteSubpolygon G) : SubpolygonDegreeCounts :=
  P.vertexSet.degreeCounts

/-- Convert to the boundary-angle interface package. -/
def toSubpolygonAngleLowerBoundPackage
    (P : ConcreteSubpolygon G) :
    SubpolygonAngleLowerBoundPackage :=
  P.angleBounds.toSubpolygonAngleLowerBoundPackage

/-- Convert to the core degree-count data package. -/
def toDegreeCountData
    (P : ConcreteSubpolygon G) :
    DegreeCountData G P.boundary P.vertexSet :=
  P.angleBounds.toDegreeCountData

/-- Convert to the full `SubpolygonCore` package. -/
def toSubpolygonPackage (P : ConcreteSubpolygon G) :
    SubpolygonPackage G where
  boundary := P.boundary
  vertexSet := P.vertexSet
  degreeData := P.toDegreeCountData

/-- The counting-layer angle lower bound for the computed counts. -/
theorem angleLowerBound
    (P : ConcreteSubpolygon G) :
    P.counts.AngleLowerBound := by
  simpa [counts] using P.angleBounds.angleLowerBound

/-- E13 with high-degree slack for the concrete subpolygon. -/
theorem lowDegreeWithHighDegreeSlack
    (P : ConcreteSubpolygon G) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 := by
  simpa [counts] using P.angleBounds.lowDegreeWithHighDegreeSlack

/-- The same slack conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeWithHighDegreeSlack_viaSubpolygonCore
    (P : ConcreteSubpolygon G) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 := by
  simpa [toSubpolygonPackage, counts, SubpolygonPackage.counts] using
    P.toSubpolygonPackage.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for the concrete subpolygon. -/
theorem lowDegreeInequality
    (P : ConcreteSubpolygon G) :
    6 <= 2 * P.counts.D2 + P.counts.D3 := by
  simpa [counts] using P.angleBounds.lowDegreeInequality

/-- The same low-degree conclusion routed through `SubpolygonCore`. -/
theorem lowDegreeInequality_viaSubpolygonCore
    (P : ConcreteSubpolygon G) :
    6 <= 2 * P.counts.D2 + P.counts.D3 := by
  simpa [toSubpolygonPackage, counts, SubpolygonPackage.counts] using
    P.toSubpolygonPackage.lowDegreeInequality

end ConcreteSubpolygon

/-! ## Direct wrappers -/

/-- Direct high-degree slack bridge from concrete induced subpolygon counts and
supplied geometric angle comparisons. -/
theorem lowDegreeWithHighDegreeSlack_of_concreteAngleBounds
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (geometricAngleSum : Real)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  subpolygonLowDegreeWithHighDegreeSlack_of_geometricAngleSum
    S.degreeCounts geometricAngleSum hforced hpolygon

/-- Direct low-degree bridge from concrete induced subpolygon counts and
supplied geometric angle comparisons. -/
theorem lowDegreeInequality_of_concreteAngleBounds
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (geometricAngleSum : Real)
    (hforced :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  subpolygonLowDegreeInequality_of_geometricAngleSum
    S.degreeCounts geometricAngleSum hforced hpolygon

end

end SubpolygonAngleRealization
end Swanepoel
end ErdosProblems1066
