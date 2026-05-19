import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.AngleGeometry

set_option autoImplicit false

/-!
# Concrete boundary angle certificates

This module turns actual local Euclidean angle witnesses in a canonical
unit-distance graph into the angle lower-bound packages consumed by the E12 and
E13 counting layers.

The local primitive is not a bare real lower-bound assumption: it records three
vertices, two incident unit graph edges, and distinct endpoints.  The endpoint
separation comes from the ambient `UDConfig.sep` field, and the angle lower
bound is then the checked `AngleGeometry` theorem.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleCertificatesConcrete

open BoundaryCounting
open FaceReduction
open PlanarInterface

universe u

noncomputable section

variable {n : Nat}

/-! ## Local Euclidean angle certificates -/

/-- A concrete angle at `center`, with both sides unit graph edges and the two
outer endpoints distinct.  In a `UDConfig`, distinct endpoints are separated by
distance at least one, so this is enough to force an angle of at least
`pi / 3`. -/
structure UnitSeparatedAngle
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  left : Fin n
  center : Fin n
  right : Fin n
  left_adj : G.Adj left center
  right_adj : G.Adj right center
  endpoints_ne : Ne left right

namespace UnitSeparatedAngle

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The actual mathlib/Swanepoel angle determined by the three certified
vertices. -/
def value (A : UnitSeparatedAngle G) : Real :=
  AngleGeometry.angleAt (G.point A.left) (G.point A.center) (G.point A.right)

theorem left_eucUnit (A : UnitSeparatedAngle G) :
    AngleBridgeFacts.EucUnit (G.point A.left) (G.point A.center) := by
  simpa [AngleBridgeFacts.EucUnit, AngleBridgeFacts.eucDist] using
    G.adj_geometry_dist_eq_one A.left_adj

theorem right_eucUnit (A : UnitSeparatedAngle G) :
    AngleBridgeFacts.EucUnit (G.point A.right) (G.point A.center) := by
  simpa [AngleBridgeFacts.EucUnit, AngleBridgeFacts.eucDist] using
    G.adj_geometry_dist_eq_one A.right_adj

theorem endpoints_eucSeparated (A : UnitSeparatedAngle G) :
    AngleBridgeFacts.EucSeparated (G.point A.left) (G.point A.right) := by
  unfold AngleBridgeFacts.EucSeparated AngleBridgeFacts.eucDist
  simpa [PlanarInterface.geometry_eucDist_eq_root,
    PlanarInterface.StraightLineUnitDistanceGraph.point] using
      G.config.sep A.left A.right A.endpoints_ne

/-- The checked Euclidean lower bound for one certified local angle. -/
theorem pi_div_three_le_value (A : UnitSeparatedAngle G) :
    Real.pi / 3 <= A.value := by
  simpa [value] using
    AngleGeometry.pi_div_three_le_angleAt_of_eucUnit_sides_eucSeparated_base
      A.left_eucUnit A.right_eucUnit A.endpoints_eucSeparated

/-- The unoriented angle carried by a unit-separated local certificate is
nonnegative. -/
theorem value_nonnegative (A : UnitSeparatedAngle G) :
    0 <= A.value := by
  simpa [value] using
    AngleGeometry.angleAt_nonneg
      (G.point A.left) (G.point A.center) (G.point A.right)

/-- The unoriented angle carried by a unit-separated local certificate is at
most `pi`. -/
theorem value_le_pi (A : UnitSeparatedAngle G) :
    A.value <= Real.pi := by
  simpa [value] using
    AngleGeometry.angleAt_le_pi
      (G.point A.left) (G.point A.center) (G.point A.right)

end UnitSeparatedAngle

/-- A finite angle mass made from `m` concrete local `pi / 3` angle
certificates. -/
structure AngleMassCertificate
    (G : CanonicalStraightLineUnitDistanceGraph n) (m : Nat) where
  angle : Fin m -> UnitSeparatedAngle G

namespace AngleMassCertificate

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {m : Nat}

/-- The actual real angle mass represented by this certificate. -/
def value (M : AngleMassCertificate G m) : Real :=
  Finset.sum (Finset.univ : Finset (Fin m)) fun i => (M.angle i).value

/-- The angle mass represented by finitely many certified local angles is
nonnegative. -/
theorem value_nonnegative (M : AngleMassCertificate G m) :
    0 <= M.value := by
  unfold value
  exact Finset.sum_nonneg
    (fun i _hi => UnitSeparatedAngle.value_nonnegative (M.angle i))

theorem value_le_pi_mul_card (M : AngleMassCertificate G m) :
    M.value <= Real.pi * (m : Real) := by
  unfold value
  calc
    Finset.sum (Finset.univ : Finset (Fin m))
        (fun i => (M.angle i).value) <=
        Finset.sum (Finset.univ : Finset (Fin m))
          (fun _ => Real.pi) := by
      exact Finset.sum_le_sum
        (s := (Finset.univ : Finset (Fin m)))
        (fun i _hi => (M.angle i).value_le_pi)
    _ = Real.pi * (m : Real) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem sum_pi_div_three_le_value (M : AngleMassCertificate G m) :
    Finset.sum (Finset.univ : Finset (Fin m)) (fun _ => Real.pi / 3) <=
      M.value := by
  exact Finset.sum_le_sum
    (s := (Finset.univ : Finset (Fin m)))
    (fun i _hi => (M.angle i).pi_div_three_le_value)

theorem pi_div_three_mul_card_le_value (M : AngleMassCertificate G m) :
    (Real.pi / 3) * (m : Real) <= M.value := by
  have hsum :
      Finset.sum (Finset.univ : Finset (Fin m)) (fun _ => Real.pi / 3) =
        (Real.pi / 3) * (m : Real) := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  simpa [hsum] using M.sum_pi_div_three_le_value

theorem lower_one (M : AngleMassCertificate G 1) :
    Real.pi / 3 <= M.value := by
  simpa using M.pi_div_three_mul_card_le_value

theorem lower_two (M : AngleMassCertificate G 2) :
    (Real.pi / 3) * (2 : Real) <= M.value := by
  simpa using M.pi_div_three_mul_card_le_value

theorem lower_three (M : AngleMassCertificate G 3) :
    (Real.pi / 3) * (3 : Real) <= M.value := by
  simpa using M.pi_div_three_mul_card_le_value

theorem lower_four (M : AngleMassCertificate G 4) :
    (Real.pi / 3) * (4 : Real) <= M.value := by
  simpa using M.pi_div_three_mul_card_le_value

theorem lower_five (M : AngleMassCertificate G 5) :
    (Real.pi / 3) * (5 : Real) <= M.value := by
  simpa using M.pi_div_three_mul_card_le_value

end AngleMassCertificate

/-! ## Outer-boundary E12 certificates -/

/-- Concrete per-class angle certificates for the outer-boundary E12 count.

Degree `d` vertices carry `d - 1` certified local angles.  Nontriangle edges
and long arcs each carry one certified local angle.  The remaining fields
record the actual polygon angle-sum comparison for this concrete accounting. -/
structure OuterBoundaryAngleCertificates
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (counts : BoundaryCounts) where
  degree3 : Fin counts.d3 -> AngleMassCertificate G 2
  degree4 : Fin counts.d4 -> AngleMassCertificate G 3
  degree5 : Fin counts.d5 -> AngleMassCertificate G 4
  degree6 : Fin counts.d6 -> AngleMassCertificate G 5
  nontriangle : Fin counts.b -> AngleMassCertificate G 1
  longArc : Fin counts.B -> AngleMassCertificate G 1
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin counts.d3))
          (fun i => (degree3 i).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.d4))
          (fun i => (degree4 i).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.d5))
          (fun i => (degree5 i).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.d6))
          (fun i => (degree6 i).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.b))
          (fun i => (nontriangle i).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.B))
          (fun i => (longArc i).value) +
      unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon : geometricAngleSum <= counts.polygonAngleSum

namespace OuterBoundaryAngleCertificates

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {counts : BoundaryCounts}

/-- Forget the concrete graph-angle witnesses to the existing explicit
outer-boundary angle realization. -/
def toOuterBoundaryAngleRealization
    (A : OuterBoundaryAngleCertificates G counts) :
    BoundaryAngleRealization.OuterBoundaryAngleRealization where
  counts := counts
  degree3Angle := fun i => (A.degree3 i).value
  degree4Angle := fun i => (A.degree4 i).value
  degree5Angle := fun i => (A.degree5 i).value
  degree6Angle := fun i => (A.degree6 i).value
  nontriangleExtra := fun i => (A.nontriangle i).value
  longArcExtra := fun i => (A.longArc i).value
  unaccountedAngle := A.unaccountedAngle
  geometricAngleSum := A.geometricAngleSum
  geometricAngleSum_eq := A.geometricAngleSum_eq
  degree3_lower := fun i => (A.degree3 i).lower_two
  degree4_lower := fun i => (A.degree4 i).lower_three
  degree5_lower := fun i => (A.degree5 i).lower_four
  degree6_lower := fun i => (A.degree6 i).lower_five
  nontriangle_lower := fun i => (A.nontriangle i).lower_one
  longArc_lower := fun i => (A.longArc i).lower_one
  unaccounted_nonnegative := A.unaccounted_nonnegative
  geometric_le_polygon := A.geometric_le_polygon

/-- The forced E12 lower side is bounded by the concrete geometric angle sum. -/
theorem forced_le_geometricAngleSum
    (A : OuterBoundaryAngleCertificates G counts) :
    counts.forcedBoundaryAngleSum <= A.geometricAngleSum :=
  A.toOuterBoundaryAngleRealization.forced_le_geometricAngleSum

/-- The counting-layer E12 angle lower bound produced by the concrete
certificates. -/
theorem angleLowerBound
    (A : OuterBoundaryAngleCertificates G counts) :
    counts.AngleLowerBound :=
  A.toOuterBoundaryAngleRealization.angleLowerBound

/-- E12, routed directly through `BoundaryCounting`, from concrete graph-angle
certificates. -/
theorem boundaryAngleCountInequality
    (A : OuterBoundaryAngleCertificates G counts) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  BoundaryCounts.boundary_angle_count_inequality counts A.angleLowerBound

/-- Negative-element E12 form from concrete graph-angle certificates. -/
theorem boundaryNegativeCountInequality
    (A : OuterBoundaryAngleCertificates G counts) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  BoundaryCounts.boundary_negative_count_inequality counts A.angleLowerBound

/-- Canonical boundary-count hypotheses for `PlanarBoundaryFinal`, built from
an honest outer-boundary core and concrete graph-angle certificates. -/
def canonicalBoundaryCountHypothesesOfCore
    (core : OuterBoundaryCore G)
    (A : OuterBoundaryAngleCertificates G counts) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  PlanarBoundaryFinal.canonicalBoundaryCountHypothesesOfCore
    core counts A.geometricAngleSum A.forced_le_geometricAngleSum
    A.geometric_le_polygon

/-- E12 through the `PlanarBoundaryFinal` facade, using concrete graph-angle
certificates rather than a bare angle-lower-bound assumption. -/
theorem boundaryAngleCountInequalityOfCore
    (core : OuterBoundaryCore G)
    (A : OuterBoundaryAngleCertificates G counts) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  PlanarBoundaryFinal.boundaryAngleCountInequalityOfCore
    core counts A.geometricAngleSum A.forced_le_geometricAngleSum
    A.geometric_le_polygon

/-- Negative-element E12 through the `PlanarBoundaryFinal` facade. -/
theorem boundaryNegativeCountInequalityOfCore
    (core : OuterBoundaryCore G)
    (A : OuterBoundaryAngleCertificates G counts) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  PlanarBoundaryFinal.boundaryNegativeCountInequalityOfCore
    core counts A.geometricAngleSum A.forced_le_geometricAngleSum
    A.geometric_le_polygon

end OuterBoundaryAngleCertificates

/-! ## Subpolygon E13 certificates -/

/-- Concrete per-degree angle certificates for the subpolygon E13 count. -/
structure SubpolygonAngleCertificates
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : SubpolygonCore.BoundaryCycle G)
    (S : SubpolygonCore.InducedVertexSet G C) where
  degree2 : Fin S.degreeCounts.D2 -> AngleMassCertificate G 1
  degree3 : Fin S.degreeCounts.D3 -> AngleMassCertificate G 2
  degree4 : Fin S.degreeCounts.D4 -> AngleMassCertificate G 3
  degree5 : Fin S.degreeCounts.D5 -> AngleMassCertificate G 4
  degree6 : Fin S.degreeCounts.D6 -> AngleMassCertificate G 5
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2))
          (fun i => (degree2 i).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3))
          (fun i => (degree3 i).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4))
          (fun i => (degree4 i).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5))
          (fun i => (degree5 i).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6))
          (fun i => (degree6 i).value) +
      unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon : geometricAngleSum <= S.degreeCounts.polygonAngleSum

namespace SubpolygonAngleCertificates

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : SubpolygonCore.BoundaryCycle G}
variable {S : SubpolygonCore.InducedVertexSet G C}

/-- The geometric angle mass explicitly accounted for by the E13 classes. -/
def accountedAngleSum
    (A : SubpolygonAngleCertificates G C S) : Real :=
  Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2))
      (fun i => (A.degree2 i).value) +
  Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3))
      (fun i => (A.degree3 i).value) +
  Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4))
      (fun i => (A.degree4 i).value) +
  Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5))
      (fun i => (A.degree5 i).value) +
  Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6))
      (fun i => (A.degree6 i).value)

/-- The formal lower-bound contribution sum for E13. -/
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

/-- The E13 lower-contribution sum is exactly the forced subpolygon angle
side. -/
theorem forcedSubpolygonAngleSum_eq_lowerContributionSum
    (c : SubpolygonDegreeCounts) :
    c.forcedSubpolygonAngleSum = lowerContributionSum c := by
  simp [SubpolygonDegreeCounts.forcedSubpolygonAngleSum,
    lowerContributionSum, Finset.sum_const]
  ring

/-- Pointwise concrete angle certificates imply the accounted E13 lower bound. -/
theorem lowerContributionSum_le_accountedAngleSum
    (A : SubpolygonAngleCertificates G C S) :
    lowerContributionSum S.degreeCounts <= A.accountedAngleSum := by
  have h2 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2))
          (fun _ => Real.pi / 3) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2))
          (fun i => (A.degree2 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D2)))
      (fun i _hi => (A.degree2 i).lower_one)
  have h3 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3))
          (fun _ => (Real.pi / 3) * (2 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3))
          (fun i => (A.degree3 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D3)))
      (fun i _hi => (A.degree3 i).lower_two)
  have h4 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4))
          (fun _ => (Real.pi / 3) * (3 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4))
          (fun i => (A.degree4 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D4)))
      (fun i _hi => (A.degree4 i).lower_three)
  have h5 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5))
          (fun _ => (Real.pi / 3) * (4 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5))
          (fun i => (A.degree5 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D5)))
      (fun i _hi => (A.degree5 i).lower_four)
  have h6 :
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6))
          (fun _ => (Real.pi / 3) * (5 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6))
          (fun i => (A.degree6 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin S.degreeCounts.D6)))
      (fun i _hi => (A.degree6 i).lower_five)
  unfold lowerContributionSum accountedAngleSum
  nlinarith [h2, h3, h4, h5, h6]

/-- The concrete E13 accounting gives the forced-vs-geometric bound. -/
theorem forced_le_geometricAngleSum
    (A : SubpolygonAngleCertificates G C S) :
    S.degreeCounts.forcedSubpolygonAngleSum <= A.geometricAngleSum := by
  rw [forcedSubpolygonAngleSum_eq_lowerContributionSum]
  have haccounted := A.lowerContributionSum_le_accountedAngleSum
  have hgeom_eq :
      A.geometricAngleSum = A.accountedAngleSum + A.unaccountedAngle := by
    simpa [accountedAngleSum] using A.geometricAngleSum_eq
  rw [hgeom_eq]
  nlinarith [haccounted, A.unaccounted_nonnegative]

/-- Concrete angle certificates as the existing computed-count subpolygon
angle package. -/
def toConcreteAngleBounds
    (A : SubpolygonAngleCertificates G C S) :
    SubpolygonAngleRealization.ConcreteAngleBounds G C S where
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := A.forced_le_geometricAngleSum
  geometric_le_polygon := A.geometric_le_polygon

/-- The counting-layer E13 angle lower bound produced by the concrete
certificates. -/
theorem angleLowerBound
    (A : SubpolygonAngleCertificates G C S) :
    S.degreeCounts.AngleLowerBound :=
  A.toConcreteAngleBounds.angleLowerBound

/-- E13 with high-degree slack from concrete graph-angle certificates. -/
theorem lowDegreeWithHighDegreeSlack
    (A : SubpolygonAngleCertificates G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    S.degreeCounts A.angleLowerBound

/-- Swanepoel Lemma 4's low-degree conclusion from concrete graph-angle
certificates. -/
theorem lowDegreeInequality
    (A : SubpolygonAngleCertificates G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    S.degreeCounts A.angleLowerBound

/-- Turn an honest geometric subpolygon plus concrete angle certificates into
the existing honest subpolygon angle-data package. -/
def toHonestGeometricSubpolygonAngleData
    (P : SubpolygonAssembly.HonestGeometricSubpolygon G)
    (A : SubpolygonAngleCertificates G P.boundary P.vertexSet) :
    SubpolygonAssembly.HonestGeometricSubpolygonAngleData G where
  subpolygon := P
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [SubpolygonAssembly.HonestGeometricSubpolygon.counts] using
      A.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [SubpolygonAssembly.HonestGeometricSubpolygon.counts] using
      A.geometric_le_polygon

/-- Turn an honest geometric subpolygon plus concrete angle certificates into
the `PlanarBoundaryClosure`-facing subpolygon data. -/
def toSubpolygonCycleCountAngleData
    (P : SubpolygonAssembly.HonestGeometricSubpolygon G)
    (A : SubpolygonAngleCertificates G P.boundary P.vertexSet) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData G :=
  (toHonestGeometricSubpolygonAngleData P A).toSubpolygonCycleCountAngleData

end SubpolygonAngleCertificates

/-! ## Planar-boundary-facing certified families -/

/-- A family of honest subpolygons whose angle lower bounds are supplied by
concrete local graph-angle certificates. -/
structure SubpolygonAngleCertificateFamily
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  Subpolygon : Type u
  subpolygon : Subpolygon -> SubpolygonAssembly.HonestGeometricSubpolygon G
  angleCertificates :
    forall S : Subpolygon,
      SubpolygonAngleCertificates G (subpolygon S).boundary
        (subpolygon S).vertexSet

namespace SubpolygonAngleCertificateFamily

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Forget concrete local angle witnesses to the existing planar-boundary
subpolygon input family. -/
def toPlanarBoundarySubpolygonInputs
    (F : SubpolygonAngleCertificateFamily.{u} G) :
    SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G where
  faceBoundary := F.faceBoundary
  Subpolygon := F.Subpolygon
  subpolygonAngleData := fun S =>
    SubpolygonAngleCertificates.toHonestGeometricSubpolygonAngleData
      (F.subpolygon S) (F.angleCertificates S)

@[simp]
theorem toPlanarBoundarySubpolygonInputs_faceBoundary
    (F : SubpolygonAngleCertificateFamily.{u} G) :
    F.toPlanarBoundarySubpolygonInputs.faceBoundary = F.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundarySubpolygonInputs_Subpolygon
    (F : SubpolygonAngleCertificateFamily.{u} G) :
    F.toPlanarBoundarySubpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

/-- E13 with high-degree slack for one member of the certified family. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (F : SubpolygonAngleCertificateFamily.{u} G) (S : F.Subpolygon) :
    (F.subpolygon S).counts.D5 + 2 * (F.subpolygon S).counts.D6 + 6 <=
      2 * (F.subpolygon S).counts.D2 + (F.subpolygon S).counts.D3 := by
  simpa [SubpolygonAssembly.HonestGeometricSubpolygon.counts] using
    (F.angleCertificates S).lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for one member of the certified
family. -/
theorem subpolygonLowDegree
    (F : SubpolygonAngleCertificateFamily.{u} G) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygon S).counts.D2 + (F.subpolygon S).counts.D3 := by
  simpa [SubpolygonAssembly.HonestGeometricSubpolygon.counts] using
    (F.angleCertificates S).lowDegreeInequality

end SubpolygonAngleCertificateFamily

/-! ## Planar-boundary facade constructors -/

/-- Build `PlanarBoundaryData` from concrete outer-boundary angle certificates
and a certified honest subpolygon family. -/
def planarBoundaryDataOfWalk
    {G : CanonicalStraightLineUnitDistanceGraph n}
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (outer : OuterBoundaryAngleCertificates G walk.counts)
    (family : SubpolygonAngleCertificateFamily.{u} G)
    (sameFaceBoundary : family.faceBoundary = core.faceBoundary) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  PlanarBoundaryFinal.PlanarBoundaryData.ofOuterBoundaryWalkSubpolygonInputs
    walk outer.geometricAngleSum outer.forced_le_geometricAngleSum
    outer.geometric_le_polygon family.toPlanarBoundarySubpolygonInputs
    sameFaceBoundary

/-- The concrete face-counting package exposed by `PlanarBoundaryFinal`, built
from concrete graph-angle certificates. -/
def concreteFaceCountingDataOfWalk
    {G : CanonicalStraightLineUnitDistanceGraph n}
    {core : OuterBoundaryCore G}
    {IsTriangle IsNontriangle : PlanarInterface.Edge n -> Prop}
    {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}
    (walk :
      BoundaryWalkConstruction.OuterBoundaryWalkBookkeeping core
        IsTriangle IsNontriangle IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (outer : OuterBoundaryAngleCertificates G walk.counts)
    (family : SubpolygonAngleCertificateFamily.{u} G)
    (sameFaceBoundary : family.faceBoundary = core.faceBoundary) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      (planarBoundaryDataOfWalk walk outer family sameFaceBoundary) :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData _

end

end BoundaryAngleCertificatesConcrete
end Swanepoel
end ErdosProblems1066
