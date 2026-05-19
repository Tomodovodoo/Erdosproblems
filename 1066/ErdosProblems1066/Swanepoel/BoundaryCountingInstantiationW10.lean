import ErdosProblems1066.Swanepoel.BoundaryPartitionInstantiation
import ErdosProblems1066.Swanepoel.BoundaryAngleWitnessConstruction
import ErdosProblems1066.Swanepoel.LongArcGapConcrete

/-!
# W10 boundary counting instantiation

This module combines the concrete classified boundary partitions, explicit
local unit-separated angle witnesses, and the long-arc count-gap route into
small checked adapters.  It keeps all geometric inputs explicit and only
reindexes the concrete boundary subtypes into the count-indexed consumers.
-/

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryCountingInstantiationW10

open BoundaryCounting
open BoundaryWalkClassificationConcrete

noncomputable section

universe u

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

namespace ClassifiedBoundary

variable (D : OuterBoundaryClassificationInputs P)

/-- The real value of the angle-mass certificate built from explicit
unit-separated local angle witnesses. -/
def angleMassValue {m : Nat}
    (angle :
      Fin m -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle G) :
    Real :=
  (BoundaryAngleWitnessConstruction.angleMassCertificate angle).value

/-- A classified local angle-mass value is bounded above by `pi` times the
number of certified angle slots.  This is only the pointwise geometric upper
bound; disjoint containment in boundary sectors is the additional S3 content. -/
theorem angleMassValue_le_pi_mul_card {m : Nat}
    (angle :
      Fin m -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle G) :
    angleMassValue angle <= Real.pi * (m : Real) := by
  simpa [angleMassValue] using
    (BoundaryAngleWitnessConstruction.angleMassCertificate angle).value_le_pi_mul_card

/-- A classified local angle-mass value is nonnegative. -/
theorem angleMassValue_nonnegative {m : Nat}
    (angle :
      Fin m -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle G) :
    0 <= angleMassValue angle := by
  simpa [angleMassValue] using
    BoundaryAngleCertificatesConcrete.AngleMassCertificate.value_nonnegative
      (BoundaryAngleWitnessConstruction.angleMassCertificate angle)

/--
Concrete unit-separated local angle witnesses indexed by the actual classified
boundary subtypes.

The geometric sum equation is stated after reindexing through the concrete
partition equivalences, so it can be fed directly to
`BoundaryAngleWitnessConstruction.OuterBoundaryUnitSeparatedWitness`.
-/
structure UnitSeparatedAngleFamilies where
  degree3 :
    D.degree3Indices -> Fin 2 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree4 :
    D.degree4Indices -> Fin 3 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree5 :
    D.degree5Indices -> Fin 4 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree6 :
    D.degree6Indices -> Fin 5 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  nontriangle :
    D.nontriangleEdgeIndices -> Fin 1 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  longArc :
    D.longArcIndices -> Fin 1 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
          (fun i =>
            angleMassValue
              (degree3
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
          (fun i =>
            angleMassValue
              (degree4
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
          (fun i =>
            angleMassValue
              (degree5
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
          (fun i =>
            angleMassValue
              (degree6
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.b))
          (fun i =>
            angleMassValue
              (nontriangle
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
                  D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.B))
          (fun i =>
            angleMassValue
              (longArc
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
                  D).symm i))) +
      unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon :
    geometricAngleSum <= D.counts.polygonAngleSum

/-- The classified boundary count polygon angle sum is the same expression as
the selected outer cycle's simple polygon angle sum. -/
theorem counts_polygonAngleSum_eq_boundaryCycleAngleSum
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.polygonAngleSum =
      Real.pi * ((P.outerCycle.length : Real) - 2) := by
  have hvertex :
      (D.counts.vertexCount : Real) = (P.outerCycle.length : Real) := by
    exact_mod_cast
      BoundaryPartitionInstantiation.ClassifiedBoundary.counts_vertexCount_eq_length
        D
  rw [BoundaryCounts.polygonAngleSum, hvertex]

/--
The concrete unit-separated local angle witnesses, before the global
polygon-angle comparison is attached.

This is the exact local geometry part of `UnitSeparatedAngleFamilies`: all
fields are actual graph-angle certificates at unit-distance separated triples.
-/
structure UnitSeparatedLocalAngleFamilies where
  degree3 :
    D.degree3Indices -> Fin 2 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree4 :
    D.degree4Indices -> Fin 3 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree5 :
    D.degree5Indices -> Fin 4 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  degree6 :
    D.degree6Indices -> Fin 5 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  nontriangle :
    D.nontriangleEdgeIndices -> Fin 1 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  longArc :
    D.longArcIndices -> Fin 1 ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G

namespace UnitSeparatedLocalAngleFamilies

variable {D}

/-- The concrete local angle mass accounted for by a local separated-angle
family, after reindexing through the finite classified-boundary partitions. -/
def accountedAngleSum
    (L : UnitSeparatedLocalAngleFamilies D) : Real :=
  Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
      (fun i =>
        angleMassValue
          (L.degree3
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
              D).symm i))) +
    Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
      (fun i =>
        angleMassValue
          (L.degree4
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
              D).symm i))) +
    Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
      (fun i =>
        angleMassValue
          (L.degree5
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
              D).symm i))) +
    Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
      (fun i =>
        angleMassValue
          (L.degree6
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
              D).symm i))) +
    Finset.sum (Finset.univ : Finset (Fin D.counts.b))
      (fun i =>
        angleMassValue
          (L.nontriangle
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
              D).symm i))) +
    Finset.sum (Finset.univ : Finset (Fin D.counts.B))
      (fun i =>
        angleMassValue
          (L.longArc
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
              D).symm i)))

/-- The accounted local Euclidean angle mass is nonnegative. -/
theorem accountedAngleSum_nonnegative
    (L : UnitSeparatedLocalAngleFamilies D) :
    0 <= L.accountedAngleSum := by
  have h3 :
      0 <= Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
        (fun i =>
          angleMassValue
            (L.degree3
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
                D).symm i))) := by
    exact Finset.sum_nonneg
      (fun i _hi =>
        angleMassValue_nonnegative
          (L.degree3
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
              D).symm i)))
  have h4 :
      0 <= Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
        (fun i =>
          angleMassValue
            (L.degree4
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
                D).symm i))) := by
    exact Finset.sum_nonneg
      (fun i _hi =>
        angleMassValue_nonnegative
          (L.degree4
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
              D).symm i)))
  have h5 :
      0 <= Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
        (fun i =>
          angleMassValue
            (L.degree5
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
                D).symm i))) := by
    exact Finset.sum_nonneg
      (fun i _hi =>
        angleMassValue_nonnegative
          (L.degree5
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
              D).symm i)))
  have h6 :
      0 <= Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
        (fun i =>
          angleMassValue
            (L.degree6
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
                D).symm i))) := by
    exact Finset.sum_nonneg
      (fun i _hi =>
        angleMassValue_nonnegative
          (L.degree6
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
              D).symm i)))
  have hb :
      0 <= Finset.sum (Finset.univ : Finset (Fin D.counts.b))
        (fun i =>
          angleMassValue
            (L.nontriangle
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
                D).symm i))) := by
    exact Finset.sum_nonneg
      (fun i _hi =>
        angleMassValue_nonnegative
          (L.nontriangle
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
              D).symm i)))
  have hB :
      0 <= Finset.sum (Finset.univ : Finset (Fin D.counts.B))
        (fun i =>
          angleMassValue
            (L.longArc
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
                D).symm i))) := by
    exact Finset.sum_nonneg
      (fun i _hi =>
        angleMassValue_nonnegative
          (L.longArc
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
              D).symm i)))
  change 0 <=
    (((((Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
        (fun i =>
          angleMassValue
            (L.degree3
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
                D).symm i))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
        (fun i =>
          angleMassValue
            (L.degree4
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
                D).symm i)))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
        (fun i =>
          angleMassValue
            (L.degree5
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
                D).symm i)))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
        (fun i =>
          angleMassValue
            (L.degree6
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
                D).symm i)))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.b))
        (fun i =>
          angleMassValue
            (L.nontriangle
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
                D).symm i)))) +
      Finset.sum (Finset.univ : Finset (Fin D.counts.B))
        (fun i =>
          angleMassValue
            (L.longArc
              ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
                D).symm i))))
  exact
    add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg h3 h4) h5) h6) hb) hB

/-- The accounted local Euclidean angle mass is bounded by the sum of the
basic `pi` caps for all certified angle slots.  The stronger S3 requirement is
that these slots occupy disjoint ordered outer-face sectors. -/
theorem accountedAngleSum_le_pi_slotSum
    (L : UnitSeparatedLocalAngleFamilies D) :
    L.accountedAngleSum <=
      Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
          (fun _ => Real.pi * (2 : Real)) +
        Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
          (fun _ => Real.pi * (3 : Real)) +
        Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
          (fun _ => Real.pi * (4 : Real)) +
        Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
          (fun _ => Real.pi * (5 : Real)) +
        Finset.sum (Finset.univ : Finset (Fin D.counts.b))
          (fun _ => Real.pi * (1 : Real)) +
        Finset.sum (Finset.univ : Finset (Fin D.counts.B))
          (fun _ => Real.pi * (1 : Real)) := by
  unfold accountedAngleSum
  have h3 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
          (fun i =>
            angleMassValue
              (L.degree3
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
                  D).symm i))) <=
        Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
          (fun _ => Real.pi * (2 : Real)) := by
    exact Finset.sum_le_sum
      (fun i _hi =>
        angleMassValue_le_pi_mul_card
          (L.degree3
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
              D).symm i)))
  have h4 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
          (fun i =>
            angleMassValue
              (L.degree4
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
                  D).symm i))) <=
        Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
          (fun _ => Real.pi * (3 : Real)) := by
    exact Finset.sum_le_sum
      (fun i _hi =>
        angleMassValue_le_pi_mul_card
          (L.degree4
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
              D).symm i)))
  have h5 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
          (fun i =>
            angleMassValue
              (L.degree5
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
                  D).symm i))) <=
        Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
          (fun _ => Real.pi * (4 : Real)) := by
    exact Finset.sum_le_sum
      (fun i _hi =>
        angleMassValue_le_pi_mul_card
          (L.degree5
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
              D).symm i)))
  have h6 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
          (fun i =>
            angleMassValue
              (L.degree6
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
                  D).symm i))) <=
        Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
          (fun _ => Real.pi * (5 : Real)) := by
    exact Finset.sum_le_sum
      (fun i _hi =>
        angleMassValue_le_pi_mul_card
          (L.degree6
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
              D).symm i)))
  have hb :
      Finset.sum (Finset.univ : Finset (Fin D.counts.b))
          (fun i =>
            angleMassValue
              (L.nontriangle
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
                  D).symm i))) <=
        Finset.sum (Finset.univ : Finset (Fin D.counts.b))
          (fun _ => Real.pi * (1 : Real)) := by
    exact Finset.sum_le_sum
      (fun i _hi =>
        by
          simpa using
            angleMassValue_le_pi_mul_card
              (L.nontriangle
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
                  D).symm i)))
  have hB :
      Finset.sum (Finset.univ : Finset (Fin D.counts.B))
          (fun i =>
            angleMassValue
              (L.longArc
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
                  D).symm i))) <=
        Finset.sum (Finset.univ : Finset (Fin D.counts.B))
          (fun _ => Real.pi * (1 : Real)) := by
    exact Finset.sum_le_sum
      (fun i _hi =>
        by
          simpa using
            angleMassValue_le_pi_mul_card
              (L.longArc
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
                  D).symm i)))
  exact
    add_le_add
      (add_le_add
        (add_le_add
          (add_le_add
            (add_le_add h3 h4) h5) h6) hb) hB

/-- If the concrete accounted angle mass is bounded by the polygon angle sum
written with the selected boundary-cycle length, then it is bounded by the
same polygon sum written through the classified boundary counts. -/
theorem accountedAngleSum_le_polygon_of_le_boundaryCycleAngleSum
    (L : UnitSeparatedLocalAngleFamilies D)
    (h :
      L.accountedAngleSum <=
        Real.pi * ((P.outerCycle.length : Real) - 2)) :
    L.accountedAngleSum <= D.counts.polygonAngleSum := by
  simpa [counts_polygonAngleSum_eq_boundaryCycleAngleSum D] using h

/-- The local accounted-angle comparison can be moved freely between the
classified count polygon sum and the selected boundary-cycle polygon sum. -/
theorem accountedAngleSum_le_polygon_iff_le_boundaryCycleAngleSum
    (L : UnitSeparatedLocalAngleFamilies D) :
    L.accountedAngleSum <= D.counts.polygonAngleSum ↔
      L.accountedAngleSum <=
        Real.pi * ((P.outerCycle.length : Real) - 2) := by
  simp [counts_polygonAngleSum_eq_boundaryCycleAngleSum D]

/-- The reverse form of
`accountedAngleSum_le_polygon_of_le_boundaryCycleAngleSum`, useful when a full
angle witness is projected back down to local geometry. -/
theorem accountedAngleSum_le_boundaryCycleAngleSum_of_le_polygon
    (L : UnitSeparatedLocalAngleFamilies D)
    (h : L.accountedAngleSum <= D.counts.polygonAngleSum) :
    L.accountedAngleSum <=
      Real.pi * ((P.outerCycle.length : Real) - 2) :=
  (L.accountedAngleSum_le_polygon_iff_le_boundaryCycleAngleSum).1 h

end UnitSeparatedLocalAngleFamilies

/-- The simple-polygon interior angle sum written directly from the selected
outer-boundary cycle length.  `OuterBoundaryAngleSourceW34` has the same
quantity under its selected-topology-facing name. -/
def boundaryCyclePolygonAngleSum
    (P : OuterBoundaryCore G) : Real :=
  Real.pi * ((P.outerCycle.length : Real) - 2)

/-- The actual predecessor/current/successor interior angle at one selected
outer-boundary vertex.  This is the angle that a simple-polygon interior-angle
sum theorem should control. -/
def simplePolygonInteriorAngleAt
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) : Real :=
  AngleGeometry.angleAt
    (P.outerCycle.prevPoint k) (P.outerCycle.point k) (P.outerCycle.nextPoint k)

/-- The simple-polygon interior-angle sum over the selected outer cycle,
written as the sum of the real predecessor/current/successor angles. -/
def simplePolygonInteriorAngleSum
    (P : OuterBoundaryCore G) : Real :=
  Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
    (fun k => simplePolygonInteriorAngleAt P k)

/-- A finite triangulation angle sum with `length - 2` triangles is exactly
the selected outer cycle's polygon angle sum.  The triangle rows are supplied
as actual angle sums; this lemma only performs the finite aggregation and the
cycle-length normalization. -/
theorem triangulationAngleSum_eq_boundaryCyclePolygonAngleSum
    (P : OuterBoundaryCore G)
    (h2 : 2 <= P.outerCycle.length)
    {Triangle : Type u} [Fintype Triangle]
    (triangleCount_eq_boundaryLength_sub_two :
      Fintype.card Triangle = P.outerCycle.length - 2)
    (triangleAngle : Triangle -> Fin 3 -> Real)
    (triangleAngleSum_eq_pi :
      forall T : Triangle,
        Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T) =
          Real.pi) :
    Finset.sum (Finset.univ : Finset Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T)) =
      boundaryCyclePolygonAngleSum P := by
  calc
    Finset.sum (Finset.univ : Finset Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T)) =
        Finset.sum (Finset.univ : Finset Triangle) (fun _ => Real.pi) := by
          exact Finset.sum_congr rfl
            (fun T _ => triangleAngleSum_eq_pi T)
    _ = (Fintype.card Triangle : Real) * Real.pi := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ((P.outerCycle.length - 2 : Nat) : Real) * Real.pi := by
          rw [triangleCount_eq_boundaryLength_sub_two]
    _ = Real.pi * ((P.outerCycle.length : Real) - 2) := by
          rw [Nat.cast_sub h2]
          ring
    _ = boundaryCyclePolygonAngleSum P := by
          rfl

/-- Equality form of the genuine simple-polygon angle theorem obtained from
finite triangulation rows. -/
theorem simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum_of_triangulationAngleSum
    (P : OuterBoundaryCore G)
    (h2 : 2 <= P.outerCycle.length)
    {Triangle : Type u} [Fintype Triangle]
    (triangleCount_eq_boundaryLength_sub_two :
      Fintype.card Triangle = P.outerCycle.length - 2)
    (triangleAngle : Triangle -> Fin 3 -> Real)
    (triangleAngleSum_eq_pi :
      forall T : Triangle,
        Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T) =
          Real.pi)
    (simplePolygonInteriorAngleSum_eq_triangleAngleSum :
      simplePolygonInteriorAngleSum P =
        Finset.sum (Finset.univ : Finset Triangle)
          (fun T =>
            Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T))) :
    simplePolygonInteriorAngleSum P = boundaryCyclePolygonAngleSum P := by
  rw [simplePolygonInteriorAngleSum_eq_triangleAngleSum]
  exact triangulationAngleSum_eq_boundaryCyclePolygonAngleSum
    P h2 triangleCount_eq_boundaryLength_sub_two
    triangleAngle triangleAngleSum_eq_pi

/-- Inequality form of the triangulation-derived simple-polygon angle theorem,
ready for the boundary-neighbor sector row constructor. -/
theorem simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum_of_triangulationAngleSum
    (P : OuterBoundaryCore G)
    (h2 : 2 <= P.outerCycle.length)
    {Triangle : Type u} [Fintype Triangle]
    (triangleCount_eq_boundaryLength_sub_two :
      Fintype.card Triangle = P.outerCycle.length - 2)
    (triangleAngle : Triangle -> Fin 3 -> Real)
    (triangleAngleSum_eq_pi :
      forall T : Triangle,
        Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T) =
          Real.pi)
    (simplePolygonInteriorAngleSum_eq_triangleAngleSum :
      simplePolygonInteriorAngleSum P =
        Finset.sum (Finset.univ : Finset Triangle)
          (fun T =>
            Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T))) :
    simplePolygonInteriorAngleSum P <= boundaryCyclePolygonAngleSum P :=
  le_of_eq
    (simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum_of_triangulationAngleSum
      P h2 triangleCount_eq_boundaryLength_sub_two triangleAngle
      triangleAngleSum_eq_pi simplePolygonInteriorAngleSum_eq_triangleAngleSum)

/-- The classified-boundary polygon angle sum agrees with the cycle-length
form used by the selected outer-boundary sector rows. -/
theorem counts_polygonAngleSum_eq_boundaryCyclePolygonAngleSum
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.polygonAngleSum =
      boundaryCyclePolygonAngleSum P := by
  simpa [boundaryCyclePolygonAngleSum] using
    counts_polygonAngleSum_eq_boundaryCycleAngleSum D

/--
Actual outer-boundary sector angles together with the genuine polygon
angle-sum comparison for those sectors.

The sector at `k` is intentionally constrained to be the boundary
predecessor/current/successor angle.  This package isolates the real S3
polygon side needed by the actual-sector containment route; it does not
manufacture a scalar budget.
-/
structure BoundaryNeighborSectorAngleSumRows
    (P : OuterBoundaryCore G) where
  boundarySector :
    Fin P.outerCycle.length ->
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle G
  boundarySector_left_is_boundary_predecessor :
    forall k : Fin P.outerCycle.length,
      Exists fun pred : Fin P.outerCycle.length =>
        (boundarySector k).left = P.outerCycle.vertex pred /\
          P.outerCycle.next pred = k
  boundarySector_center_eq :
    forall k : Fin P.outerCycle.length,
      (boundarySector k).center = P.outerCycle.vertex k
  boundarySector_right_eq :
    forall k : Fin P.outerCycle.length,
      (boundarySector k).right =
        P.outerCycle.vertex (P.outerCycle.next k)
  boundarySectorAngleSum_le_boundaryCyclePolygonAngleSum :
    Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
        (fun k => (boundarySector k).value) <=
      boundaryCyclePolygonAngleSum P

namespace BoundaryNeighborSectorAngleSumRows

/-- Project the exact sector-sum inequality in the form used by selected S3
boundary-neighbor sector rows. -/
theorem sectorAngleSum_le_boundaryCyclePolygonAngleSum
    (R : BoundaryNeighborSectorAngleSumRows P) :
    Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
        (fun k => (R.boundarySector k).value) <=
      boundaryCyclePolygonAngleSum P :=
  R.boundarySectorAngleSum_le_boundaryCyclePolygonAngleSum

/-- The left endpoint of a recorded boundary-neighbor sector is the canonical
cyclic predecessor vertex. -/
theorem boundarySector_left_eq_boundary_prevVertex
    (R : BoundaryNeighborSectorAngleSumRows P)
    (k : Fin P.outerCycle.length) :
    (R.boundarySector k).left = P.outerCycle.prevVertex k := by
  rcases R.boundarySector_left_is_boundary_predecessor k with
    ⟨pred, hleft, hnext⟩
  have hpred : pred = P.outerCycle.prev k := by
    apply PlanarInterface.cyclicSucc_injective P.outerCycle.length_pos
    have hnext' :
        P.outerCycle.next pred =
          P.outerCycle.next (P.outerCycle.prev k) := by
      rw [hnext, P.outerCycle.next_prev k]
    simpa [OuterBoundaryInterface.BoundaryCycle.next] using hnext'
  rw [hleft, hpred]
  rfl

/-- Every recorded boundary-neighbor sector has exactly the predecessor/
current/successor simple-polygon interior-angle value. -/
theorem boundarySector_value_eq_simplePolygonInteriorAngleAt
    (R : BoundaryNeighborSectorAngleSumRows P)
    (k : Fin P.outerCycle.length) :
    (R.boundarySector k).value = simplePolygonInteriorAngleAt P k := by
  have hleft := R.boundarySector_left_eq_boundary_prevVertex k
  have hcenter := R.boundarySector_center_eq k
  have hright := R.boundarySector_right_eq k
  simp [simplePolygonInteriorAngleAt,
    BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value,
    OuterBoundaryInterface.BoundaryCycle.prevPoint,
    OuterBoundaryInterface.BoundaryCycle.nextPoint,
    OuterBoundaryInterface.BoundaryCycle.point,
    OuterBoundaryInterface.BoundaryCycle.prevVertex,
    hleft, hcenter, hright]

/-- The recorded sector angle sum is the actual PCS simple-polygon interior
angle sum. -/
theorem sectorAngleSum_eq_simplePolygonInteriorAngleSum
    (R : BoundaryNeighborSectorAngleSumRows P) :
    Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
        (fun k => (R.boundarySector k).value) =
      simplePolygonInteriorAngleSum P := by
  unfold simplePolygonInteriorAngleSum
  exact Finset.sum_congr rfl
    (fun k _ => R.boundarySector_value_eq_simplePolygonInteriorAngleAt k)

/-- Project the row package back to the genuine simple-polygon angle theorem. -/
theorem simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
    (R : BoundaryNeighborSectorAngleSumRows P) :
    simplePolygonInteriorAngleSum P <= boundaryCyclePolygonAngleSum P := by
  rw [<- R.sectorAngleSum_eq_simplePolygonInteriorAngleSum]
  exact R.sectorAngleSum_le_boundaryCyclePolygonAngleSum

/-- The canonical boundary-neighbor sector sum is exactly the simple-polygon
predecessor/current/successor interior-angle sum.  This is the reindexing
bridge from the W10 row package to the honest polygon-angle theorem still
needed by S3. -/
theorem outerBoundaryCoreIndex_sectorAngleSum_eq_simplePolygonInteriorAngleSum
    (h3 : 3 <= P.outerCycle.length) :
    Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
        (fun k =>
          (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
            P h3 k).value) =
      simplePolygonInteriorAngleSum P := by
  simp [simplePolygonInteriorAngleSum, simplePolygonInteriorAngleAt,
    BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value,
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex,
    OuterBoundaryInterface.BoundaryCycle.prevPoint,
    OuterBoundaryInterface.BoundaryCycle.nextPoint,
    OuterBoundaryInterface.BoundaryCycle.point]

/-- A genuine simple-polygon interior-angle theorem for the selected outer
cycle supplies the final sector-sum comparison needed by
`ofOuterBoundaryCoreIndex`. -/
theorem outerBoundaryCoreIndex_sectorAngleSum_le_of_simplePolygonInteriorAngleSum_le
    (h3 : 3 <= P.outerCycle.length)
    (hinterior :
      simplePolygonInteriorAngleSum P <= boundaryCyclePolygonAngleSum P) :
    Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
        (fun k =>
          (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
            P h3 k).value) <=
      boundaryCyclePolygonAngleSum P := by
  rw [outerBoundaryCoreIndex_sectorAngleSum_eq_simplePolygonInteriorAngleSum
    (P := P) h3]
  exact hinterior

/-- Build the row package from the canonical predecessor/current/successor
sector at every boundary vertex, leaving only the genuine polygon sector-sum
comparison as an explicit premise. -/
def ofOuterBoundaryCoreIndex
    (h3 : 3 <= P.outerCycle.length)
    (hsectorSum :
      Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
          (fun k =>
            (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
              P h3 k).value) <=
        boundaryCyclePolygonAngleSum P) :
    BoundaryNeighborSectorAngleSumRows P where
  boundarySector := fun k =>
    BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
      P h3 k
  boundarySector_left_is_boundary_predecessor := fun k => by
    refine Exists.intro (P.outerCycle.prev k) ?_
    constructor
    · rfl
    · exact P.outerCycle.next_prev k
  boundarySector_center_eq := fun _ => rfl
  boundarySector_right_eq := fun _ => rfl
  boundarySectorAngleSum_le_boundaryCyclePolygonAngleSum := hsectorSum

@[simp]
theorem ofOuterBoundaryCoreIndex_boundarySector
    (h3 : 3 <= P.outerCycle.length)
    (hsectorSum :
      Finset.sum (Finset.univ : Finset (Fin P.outerCycle.length))
          (fun k =>
            (BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
              P h3 k).value) <=
        boundaryCyclePolygonAngleSum P)
    (k : Fin P.outerCycle.length) :
    ((ofOuterBoundaryCoreIndex (P := P) h3 hsectorSum).boundarySector k) =
      BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex
        P h3 k :=
  rfl

/-- Build the boundary-neighbor sector rows directly from the honest
simple-polygon interior-angle sum theorem. -/
def ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum
    (h3 : 3 <= P.outerCycle.length)
    (hinterior :
      simplePolygonInteriorAngleSum P <= boundaryCyclePolygonAngleSum P) :
    BoundaryNeighborSectorAngleSumRows P :=
  ofOuterBoundaryCoreIndex h3
    (outerBoundaryCoreIndex_sectorAngleSum_le_of_simplePolygonInteriorAngleSum_le
      (P := P) h3 hinterior)

/-- Build the canonical predecessor/current/successor sector rows directly
from finite triangulation angle sums for the selected outer polygon. -/
def ofOuterBoundaryCoreIndexOfTriangulationAngleSum
    (h3 : 3 <= P.outerCycle.length)
    {Triangle : Type u} [Fintype Triangle]
    (triangleCount_eq_boundaryLength_sub_two :
      Fintype.card Triangle = P.outerCycle.length - 2)
    (triangleAngle : Triangle -> Fin 3 -> Real)
    (triangleAngleSum_eq_pi :
      forall T : Triangle,
        Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T) =
          Real.pi)
    (simplePolygonInteriorAngleSum_eq_triangleAngleSum :
      simplePolygonInteriorAngleSum P =
        Finset.sum (Finset.univ : Finset Triangle)
          (fun T =>
            Finset.sum (Finset.univ : Finset (Fin 3)) (triangleAngle T))) :
    BoundaryNeighborSectorAngleSumRows P := by
  refine ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum h3 ?_
  exact simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum_of_triangulationAngleSum
    P (Nat.le_trans (by norm_num) h3)
    triangleCount_eq_boundaryLength_sub_two triangleAngle triangleAngleSum_eq_pi
    simplePolygonInteriorAngleSum_eq_triangleAngleSum

end BoundaryNeighborSectorAngleSumRows

namespace UnitSeparatedLocalAngleFamilies

variable {D}

/-- Bound the accounted local Euclidean angle mass by explicit budgets for
each classified local certificate. -/
theorem accountedAngleSum_le_sum_angleMassBudgets
    (L : UnitSeparatedLocalAngleFamilies D)
    (degree3Budget : D.degree3Indices -> Real)
    (degree4Budget : D.degree4Indices -> Real)
    (degree5Budget : D.degree5Indices -> Real)
    (degree6Budget : D.degree6Indices -> Real)
    (nontriangleBudget : D.nontriangleEdgeIndices -> Real)
    (longArcBudget : D.longArcIndices -> Real)
    (hdegree3 : forall i : D.degree3Indices,
      angleMassValue (L.degree3 i) <= degree3Budget i)
    (hdegree4 : forall i : D.degree4Indices,
      angleMassValue (L.degree4 i) <= degree4Budget i)
    (hdegree5 : forall i : D.degree5Indices,
      angleMassValue (L.degree5 i) <= degree5Budget i)
    (hdegree6 : forall i : D.degree6Indices,
      angleMassValue (L.degree6 i) <= degree6Budget i)
    (hnontriangle : forall i : D.nontriangleEdgeIndices,
      angleMassValue (L.nontriangle i) <= nontriangleBudget i)
    (hlongArc : forall i : D.longArcIndices,
      angleMassValue (L.longArc i) <= longArcBudget i) :
    L.accountedAngleSum <=
      Finset.sum Finset.univ degree3Budget +
        Finset.sum Finset.univ degree4Budget +
        Finset.sum Finset.univ degree5Budget +
        Finset.sum Finset.univ degree6Budget +
        Finset.sum Finset.univ nontriangleBudget +
        Finset.sum Finset.univ longArcBudget := by
  unfold accountedAngleSum
  have h3 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d3))
          (fun i =>
            angleMassValue
              (L.degree3
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
                  D).symm i))) <=
        Finset.sum Finset.univ degree3Budget := by
    rw [Fintype.sum_equiv
      (BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin D).symm
      (fun i : Fin D.counts.d3 =>
        angleMassValue
          (L.degree3
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin
              D).symm i)))
      (fun i : D.degree3Indices => angleMassValue (L.degree3 i))
      (fun _ => rfl)]
    exact Finset.sum_le_sum (fun i _ => hdegree3 i)
  have h4 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d4))
          (fun i =>
            angleMassValue
              (L.degree4
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
                  D).symm i))) <=
        Finset.sum Finset.univ degree4Budget := by
    rw [Fintype.sum_equiv
      (BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin D).symm
      (fun i : Fin D.counts.d4 =>
        angleMassValue
          (L.degree4
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin
              D).symm i)))
      (fun i : D.degree4Indices => angleMassValue (L.degree4 i))
      (fun _ => rfl)]
    exact Finset.sum_le_sum (fun i _ => hdegree4 i)
  have h5 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d5))
          (fun i =>
            angleMassValue
              (L.degree5
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
                  D).symm i))) <=
        Finset.sum Finset.univ degree5Budget := by
    rw [Fintype.sum_equiv
      (BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin D).symm
      (fun i : Fin D.counts.d5 =>
        angleMassValue
          (L.degree5
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin
              D).symm i)))
      (fun i : D.degree5Indices => angleMassValue (L.degree5 i))
      (fun _ => rfl)]
    exact Finset.sum_le_sum (fun i _ => hdegree5 i)
  have h6 :
      Finset.sum (Finset.univ : Finset (Fin D.counts.d6))
          (fun i =>
            angleMassValue
              (L.degree6
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
                  D).symm i))) <=
        Finset.sum Finset.univ degree6Budget := by
    rw [Fintype.sum_equiv
      (BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin D).symm
      (fun i : Fin D.counts.d6 =>
        angleMassValue
          (L.degree6
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin
              D).symm i)))
      (fun i : D.degree6Indices => angleMassValue (L.degree6 i))
      (fun _ => rfl)]
    exact Finset.sum_le_sum (fun i _ => hdegree6 i)
  have hb :
      Finset.sum (Finset.univ : Finset (Fin D.counts.b))
          (fun i =>
            angleMassValue
              (L.nontriangle
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
                  D).symm i))) <=
        Finset.sum Finset.univ nontriangleBudget := by
    rw [Fintype.sum_equiv
      (BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin D).symm
      (fun i : Fin D.counts.b =>
        angleMassValue
          (L.nontriangle
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
              D).symm i)))
      (fun i : D.nontriangleEdgeIndices =>
        angleMassValue (L.nontriangle i))
      (fun _ => rfl)]
    exact Finset.sum_le_sum (fun i _ => hnontriangle i)
  have hB :
      Finset.sum (Finset.univ : Finset (Fin D.counts.B))
          (fun i =>
            angleMassValue
              (L.longArc
                ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
                  D).symm i))) <=
        Finset.sum Finset.univ longArcBudget := by
    rw [Fintype.sum_equiv
      (BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin D).symm
      (fun i : Fin D.counts.B =>
        angleMassValue
          (L.longArc
            ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin
              D).symm i)))
      (fun i : D.longArcIndices => angleMassValue (L.longArc i))
      (fun _ => rfl)]
    exact Finset.sum_le_sum (fun i _ => hlongArc i)
  exact
    add_le_add
      (add_le_add
        (add_le_add
          (add_le_add
            (add_le_add h3 h4) h5) h6) hb) hB

/-- Bound the accounted local Euclidean angle mass by explicit budgets for
each classified local certificate, then transfer the resulting boundary-cycle
polygon sum to the classified count polygon sum.

This is the concrete accounting lemma used by the selected outer-boundary S3
route: the geometric work is to provide the six pointwise budget comparisons
and prove that those budgets occupy no more than the outer-cycle simple
polygon angle sum. -/
theorem accountedAngleSum_le_polygon_of_angleMassBudgets
    (L : UnitSeparatedLocalAngleFamilies D)
    (degree3Budget : D.degree3Indices -> Real)
    (degree4Budget : D.degree4Indices -> Real)
    (degree5Budget : D.degree5Indices -> Real)
    (degree6Budget : D.degree6Indices -> Real)
    (nontriangleBudget : D.nontriangleEdgeIndices -> Real)
    (longArcBudget : D.longArcIndices -> Real)
    (hdegree3 : forall i : D.degree3Indices,
      angleMassValue (L.degree3 i) <= degree3Budget i)
    (hdegree4 : forall i : D.degree4Indices,
      angleMassValue (L.degree4 i) <= degree4Budget i)
    (hdegree5 : forall i : D.degree5Indices,
      angleMassValue (L.degree5 i) <= degree5Budget i)
    (hdegree6 : forall i : D.degree6Indices,
      angleMassValue (L.degree6 i) <= degree6Budget i)
    (hnontriangle : forall i : D.nontriangleEdgeIndices,
      angleMassValue (L.nontriangle i) <= nontriangleBudget i)
    (hlongArc : forall i : D.longArcIndices,
      angleMassValue (L.longArc i) <= longArcBudget i)
    (hbudget :
      Finset.sum Finset.univ degree3Budget +
          Finset.sum Finset.univ degree4Budget +
          Finset.sum Finset.univ degree5Budget +
          Finset.sum Finset.univ degree6Budget +
          Finset.sum Finset.univ nontriangleBudget +
          Finset.sum Finset.univ longArcBudget <=
        Real.pi * ((P.outerCycle.length : Real) - 2)) :
    L.accountedAngleSum <= D.counts.polygonAngleSum := by
  refine L.accountedAngleSum_le_polygon_of_le_boundaryCycleAngleSum ?_
  exact le_trans
    (L.accountedAngleSum_le_sum_angleMassBudgets
      degree3Budget degree4Budget degree5Budget degree6Budget
      nontriangleBudget longArcBudget hdegree3 hdegree4 hdegree5 hdegree6
      hnontriangle hlongArc)
    hbudget

/-- Attach the single remaining polygon angle-sum comparison to the local
unit-separated angle geometry. -/
def toUnitSeparatedAngleFamilies
    (L : UnitSeparatedLocalAngleFamilies D)
    (accounted_le_polygon :
      L.accountedAngleSum <= D.counts.polygonAngleSum) :
    UnitSeparatedAngleFamilies D where
  degree3 := L.degree3
  degree4 := L.degree4
  degree5 := L.degree5
  degree6 := L.degree6
  nontriangle := L.nontriangle
  longArc := L.longArc
  unaccountedAngle := 0
  geometricAngleSum := L.accountedAngleSum
  geometricAngleSum_eq := by
    rw [accountedAngleSum]
    ring
  unaccounted_nonnegative := by
    norm_num
  geometric_le_polygon := accounted_le_polygon

end UnitSeparatedLocalAngleFamilies

namespace UnitSeparatedAngleFamilies

variable {D}

/-- Forget the global polygon angle-sum comparison, retaining the concrete
local separated-angle geometry. -/
def toLocalAngleGeometry
    (W : UnitSeparatedAngleFamilies D) :
    UnitSeparatedLocalAngleFamilies D where
  degree3 := W.degree3
  degree4 := W.degree4
  degree5 := W.degree5
  degree6 := W.degree6
  nontriangle := W.nontriangle
  longArc := W.longArc

/-- The full geometric sum decomposes as the local accounted mass plus the
explicit unaccounted nonnegative remainder. -/
theorem geometricAngleSum_eq_toLocalAngleGeometry_accountedAngleSum_add_unaccountedAngle
    (W : UnitSeparatedAngleFamilies D) :
    W.geometricAngleSum =
      W.toLocalAngleGeometry.accountedAngleSum + W.unaccountedAngle := by
  simpa only [toLocalAngleGeometry,
    UnitSeparatedLocalAngleFamilies.accountedAngleSum]
    using W.geometricAngleSum_eq

/-- Dropping the nonnegative unaccounted remainder gives an order bound from
local accounted mass to the full geometric angle sum. -/
theorem toLocalAngleGeometry_accountedAngleSum_le_geometricAngleSum
    (W : UnitSeparatedAngleFamilies D) :
    W.toLocalAngleGeometry.accountedAngleSum <= W.geometricAngleSum := by
  have hgeom :=
    W.geometricAngleSum_eq_toLocalAngleGeometry_accountedAngleSum_add_unaccountedAngle
  nlinarith [W.unaccounted_nonnegative]

/-- Existing full angle-family data imply the reduced accounted-angle
comparison for the underlying local separated-angle geometry. -/
theorem toLocalAngleGeometry_accountedAngleSum_le_polygon
    (W : UnitSeparatedAngleFamilies D) :
    W.toLocalAngleGeometry.accountedAngleSum <=
      D.counts.polygonAngleSum := by
  exact le_trans W.toLocalAngleGeometry_accountedAngleSum_le_geometricAngleSum
    W.geometric_le_polygon

/-- Convert the subtype-indexed unit-separated witnesses to the concrete
partition-indexed angle-mass family from `BoundaryPartitionInstantiation`. -/
def toLocalAngleFamilies
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LocalAngleFamilies D where
  degree3 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree3 i)
  degree4 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree4 i)
  degree5 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree5 i)
  degree6 := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.degree6 i)
  nontriangle := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.nontriangle i)
  longArc := fun i =>
    BoundaryAngleWitnessConstruction.angleMassCertificate (W.longArc i)

/-- The count-indexed local angle package obtained via the concrete boundary
partition equivalences. -/
def toOuterBoundaryLocalAngles
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleAssembly.OuterBoundaryLocalAngles G D.counts :=
  W.toLocalAngleFamilies.toOuterBoundaryLocalAngles D

/-- Reindex concrete subtype witnesses into the unit-separated witness record
consumed by `BoundaryAngleWitnessConstruction`. -/
def toOuterBoundaryUnitSeparatedWitness
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleWitnessConstruction.OuterBoundaryUnitSeparatedWitness
      G D.counts where
  degree3 := fun i =>
    W.degree3
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree3EquivFin D).symm
        i)
  degree4 := fun i =>
    W.degree4
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree4EquivFin D).symm
        i)
  degree5 := fun i =>
    W.degree5
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree5EquivFin D).symm
        i)
  degree6 := fun i =>
    W.degree6
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.degree6EquivFin D).symm
        i)
  nontriangle := fun i =>
    W.nontriangle
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.nontriangleEquivFin
        D).symm i)
  longArc := fun i =>
    W.longArc
      ((BoundaryPartitionInstantiation.ClassifiedBoundary.longArcEquivFin D).symm
        i)
  unaccountedAngle := W.unaccountedAngle
  geometricAngleSum := W.geometricAngleSum
  geometricAngleSum_eq := by
    simpa only [angleMassValue] using W.geometricAngleSum_eq
  unaccounted_nonnegative := W.unaccounted_nonnegative
  geometric_le_polygon := W.geometric_le_polygon

@[simp]
theorem toOuterBoundaryUnitSeparatedWitness_toLocalAngles
    (W : UnitSeparatedAngleFamilies D) :
    W.toOuterBoundaryUnitSeparatedWitness.toLocalAngles =
      W.toOuterBoundaryLocalAngles :=
  rfl

@[simp]
theorem toOuterBoundaryUnitSeparatedWitness_geometricAngleSum
    (W : UnitSeparatedAngleFamilies D) :
    W.toOuterBoundaryUnitSeparatedWitness.geometricAngleSum =
      W.geometricAngleSum :=
  rfl

/-- The assembled geometric witness for the reindexed local angles. -/
def toGeometricWitness
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleAssembly.OuterBoundaryGeometricWitness
      W.toOuterBoundaryLocalAngles := by
  simpa using W.toOuterBoundaryUnitSeparatedWitness.toGeometricWitness

/-- Concrete angle certificates obtained from the subtype-indexed local
unit-separated witnesses. -/
def toConcreteCertificates
    (W : UnitSeparatedAngleFamilies D) :
    BoundaryAngleCertificatesConcrete.OuterBoundaryAngleCertificates
      G D.counts :=
  W.toOuterBoundaryUnitSeparatedWitness.toConcreteCertificates

/-- The local angle witnesses prove the forced boundary-angle side is below
the supplied geometric angle sum. -/
theorem forced_le_geometricAngleSum
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.forcedBoundaryAngleSum <= W.geometricAngleSum :=
  BoundaryAngleAssembly.OuterBoundaryGeometricWitness.forced_le_geometricAngleSum
    W.toOuterBoundaryUnitSeparatedWitness.toGeometricWitness

/-- The counting-layer E12 angle lower bound from concrete local angle
witnesses. -/
theorem angleLowerBound
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.AngleLowerBound :=
  W.toOuterBoundaryUnitSeparatedWitness.angleLowerBound

/-- E12 in count form, after concrete partition reindexing. -/
theorem boundaryAngleCountInequality
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  W.toOuterBoundaryUnitSeparatedWitness.boundaryAngleCountInequality

/-- Negative-element E12 in count form, after concrete partition reindexing. -/
theorem boundaryNegativeCountInequality
    (W : UnitSeparatedAngleFamilies D) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  W.toOuterBoundaryUnitSeparatedWitness.boundaryNegativeCountInequality

end UnitSeparatedAngleFamilies

/-! ## Combined boundary-count and turn-bound input -/

/--
A classified boundary with explicit local angle witnesses and the long-arc
coverage/count-gap fields tied to the same geometric angle sum.
-/
structure CountTurnInput
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) where
  angleWitness : UnitSeparatedAngleFamilies D
  longArcFields :
    BoundaryPartitionInstantiation.ClassifiedBoundary.LongArcExistenceFields
      D angleWitness.geometricAngleSum
        angleWitness.forced_le_geometricAngleSum
        angleWitness.geometric_le_polygon Subpolygon subpolygonData

namespace CountTurnInput

variable {D}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G}

/-- The planar-boundary package built from the same classification, angle
witness, and subpolygon data. -/
def planarBoundary
    (I : CountTurnInput D Subpolygon subpolygonData) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  I.longArcFields.planarBoundary

@[simp]
theorem planarBoundary_outerBoundaryCounts
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.planarBoundary.outerBoundaryCounts = D.counts := by
  simp [planarBoundary]

/-- The long-arc existence/count-gap fields for the constructed planar
boundary. -/
def toBoundaryLongArcExistenceFields
    (I : CountTurnInput D Subpolygon subpolygonData) :
    LongArcExistenceConcrete.BoundaryLongArcExistenceFields.{u}
      I.planarBoundary := by
  simpa [planarBoundary] using
    I.longArcFields.toBoundaryLongArcExistenceFields

/-- The classified-boundary count-gap wrapper from `LongArcGapConcrete`. -/
def toClassifiedBoundaryCountGapInput
    (I : CountTurnInput D Subpolygon subpolygonData) :
    LongArcGapConcrete.ClassifiedBoundaryCountGapInput
      D I.angleWitness.geometricAngleSum
        I.angleWitness.forced_le_geometricAngleSum
        I.angleWitness.geometric_le_polygon Subpolygon subpolygonData :=
  I.longArcFields.toClassifiedBoundaryCountGapInput

/-- The full reusable boundary-count-gap to M8-turn-bound route. -/
def toBoundaryCountGapToM8TurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    LongArcGapConcrete.BoundaryCountGapToM8TurnBounds
      I.toBoundaryLongArcExistenceFields :=
  LongArcGapConcrete.BoundaryCountGapToM8TurnBounds.ofBoundaryLongArcExistenceFields
    I.toBoundaryLongArcExistenceFields

/-- Boundary-attached nonconcave-arc budget data selected by the count gap. -/
def toNonconcaveArcBoundaryBudgetData
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u} G :=
  I.toBoundaryLongArcExistenceFields.toNonconcaveArcBoundaryBudgetData

/-- The reusable boundary-count fields attached to the selected arc budget. -/
def boundaryAngleCountFields
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.BoundaryAngleCountFields
      I.toNonconcaveArcBoundaryBudgetData :=
  I.toNonconcaveArcBoundaryBudgetData.boundaryAngleCountFields

/-- The reusable boundary-to-M8 turn-bound field package. -/
def boundaryToM8TurnBoundFields
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      I.toNonconcaveArcBoundaryBudgetData :=
  I.toNonconcaveArcBoundaryBudgetData.boundaryToM8TurnBoundFields

/-- Honest turn bounds produced by the selected nonconcave long arc. -/
def honestTurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    TurnBoundsInterface.HonestTurnBounds :=
  I.toNonconcaveArcBoundaryBudgetData.toHonestTurnBounds

/-- Construction-level M8 turn bounds produced by the selected nonconcave
long arc. -/
def m8TurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    M8ConstructionInterface.M8TurnBounds :=
  I.toClassifiedBoundaryCountGapInput.toM8TurnBounds

@[simp]
theorem boundaryToM8TurnBoundFields_m8TurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.boundaryToM8TurnBoundFields.m8TurnBounds =
      I.toNonconcaveArcBoundaryBudgetData.toM8TurnBounds :=
  rfl

@[simp]
theorem boundaryToM8TurnBoundFields_honestTurnBounds
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.boundaryToM8TurnBoundFields.honestTurnBounds =
      I.honestTurnBounds :=
  rfl

/-- E12 in count form from the local angle witness part of the combined
input. -/
theorem boundaryAngleCountInequality
    (I : CountTurnInput D Subpolygon subpolygonData) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b +
        D.counts.B + 6 <= D.counts.d3 :=
  I.angleWitness.boundaryAngleCountInequality

/-- Negative-element E12 in count form from the local angle witness part of
the combined input. -/
theorem boundaryNegativeCountInequality
    (I : CountTurnInput D Subpolygon subpolygonData) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  I.angleWitness.boundaryNegativeCountInequality

/-- The checked long-arc count gap in the combined route. -/
theorem concaveLongArcCount_lt_longArcCount
    (I : CountTurnInput D Subpolygon subpolygonData) :
    I.toBoundaryLongArcExistenceFields.concaveLongArcCount <
      I.toBoundaryLongArcExistenceFields.longArcCount :=
  I.toBoundaryLongArcExistenceFields.concaveLongArcCount_lt_longArcCount

/-- A nonconcave concrete long-arc index selected by the count gap. -/
noncomputable def selectedLongArc
    (I : CountTurnInput D Subpolygon subpolygonData) :
    D.longArcIndices :=
  I.toBoundaryLongArcExistenceFields.selectedLongArc

/-- The selected long arc is nonconcave. -/
theorem selectedLongArc_not_concave
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Not (I.longArcFields.concave I.selectedLongArc) :=
  I.toBoundaryLongArcExistenceFields.selectedLongArc_not_concave

/-- The selected long arc has raw total turn below `pi / 3`. -/
theorem selectedLongArc_totalTurn_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Lemma10Inequalities.totalTurn
        (I.longArcFields.rawTurn I.selectedLongArc) <
      Real.pi / 3 :=
  LongArcExistenceConcrete.BoundaryLongArcExistenceFields.selectedLongArc_totalTurn_lt_pi_div_three
    I.toBoundaryLongArcExistenceFields

/-- Pointwise nonnegativity of the construction-level M8 turn bounds. -/
theorem m8TurnBounds_turn_nonnegative
    (I : CountTurnInput D Subpolygon subpolygonData) (k : Nat) :
    0 <= I.m8TurnBounds.turn k :=
  I.toClassifiedBoundaryCountGapInput.toM8TurnBounds_turn_nonnegative k

/-- The construction-level M8 total turn is below `pi / 3`. -/
theorem m8TurnBounds_totalTurn_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Lemma10Inequalities.totalTurn I.m8TurnBounds.turn < Real.pi / 3 :=
  LongArcGapConcrete.ClassifiedBoundaryCountGapInput.toM8TurnBounds_totalTurn_lt_pi_div_three
    I.toClassifiedBoundaryCountGapInput

/-- The explicit thirteen-turn M8 sum is below `pi / 3`. -/
theorem m8TurnBounds_thirteenTurnSum_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    NonconcaveArcBudgetFromBoundary.m8ThirteenTurnSum
      I.m8TurnBounds.turn < Real.pi / 3 :=
  LongArcGapConcrete.ClassifiedBoundaryCountGapInput.toM8TurnBounds_thirteenTurnSum_lt_pi_div_three
    I.toClassifiedBoundaryCountGapInput

/-- Pointwise nonnegativity of the honest turn-bound package. -/
theorem honestTurnBounds_turn_nonnegative
    (I : CountTurnInput D Subpolygon subpolygonData) (k : Nat) :
    0 <= I.honestTurnBounds.turn k :=
  I.honestTurnBounds.turn_nonnegative k

/-- The honest turn-bound package has total turn below `pi / 3`. -/
theorem honestTurnBounds_totalTurn_lt_pi_div_three
    (I : CountTurnInput D Subpolygon subpolygonData) :
    Lemma10Inequalities.totalTurn I.honestTurnBounds.turn <
      Real.pi / 3 :=
  I.honestTurnBounds.total_turn_lt_pi_div_three

end CountTurnInput

end ClassifiedBoundary

end

end BoundaryCountingInstantiationW10
end Swanepoel
end ErdosProblems1066
