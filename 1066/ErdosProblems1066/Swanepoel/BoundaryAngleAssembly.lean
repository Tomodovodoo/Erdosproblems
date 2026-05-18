import ErdosProblems1066.Swanepoel.AngleBridgeFacts
import ErdosProblems1066.Swanepoel.TriangleAngleFacts
import ErdosProblems1066.Swanepoel.BoundaryAngleCertificatesConcrete
import ErdosProblems1066.Swanepoel.BoundaryCounting

set_option autoImplicit false

/-!
# Boundary angle assembly

This file is the W8 assembly facade for Swanepoel E12/E13 boundary-angle
certificates.  The local geometric work is still explicit: callers provide
concrete unit-separated local angles and a separate real angle-sum witness.
The assembly layer proves the real lower-bound transfer from those local
certificates and projects the result to the already checked
`BoundaryAngleCertificatesConcrete` consumers.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleAssembly

open BoundaryCounting
open FaceReduction
open PlanarInterface
open BoundaryAngleRealization.OuterBoundaryAngleRealization
open BoundaryAngleCertificatesConcrete.SubpolygonAngleCertificates

universe u

noncomputable section

variable {n : Nat}

namespace UnitSeparatedAngle

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Dot-product form of the local unit-separated angle lower bound. -/
theorem dotAt_le_half
    (A : BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G) :
    TriangleAngleFacts.dotAt
        (G.point A.left) (G.point A.center) (G.point A.right) <= 1 / 2 :=
  AngleBridgeFacts.dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    A.left_eucUnit A.right_eucUnit A.endpoints_eucSeparated

/-- Real angle form of the local unit-separated angle lower bound. -/
theorem pi_div_three_le_value
    (A : BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G) :
    Real.pi / 3 <= A.value :=
  A.pi_div_three_le_value

end UnitSeparatedAngle

/-! ## Outer-boundary E12 assembly -/

/-- The concrete local angle certificates that account for the E12 boundary
classes.  The remaining polygon angle-sum fields are intentionally not hidden
in this record; they live in `OuterBoundaryGeometricWitness` below. -/
structure OuterBoundaryLocalAngles
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (counts : BoundaryCounts) where
  degree3 : Fin counts.d3 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 2
  degree4 : Fin counts.d4 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 3
  degree5 : Fin counts.d5 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 4
  degree6 : Fin counts.d6 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 5
  nontriangle : Fin counts.b -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 1
  longArc : Fin counts.B -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 1

namespace OuterBoundaryLocalAngles

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {counts : BoundaryCounts}

/-- The real angle mass accounted for by the supplied concrete E12 local
certificates. -/
def accountedAngleSum (A : OuterBoundaryLocalAngles G counts) : Real :=
  Finset.sum (Finset.univ : Finset (Fin counts.d3))
      (fun i => (A.degree3 i).value) +
    Finset.sum (Finset.univ : Finset (Fin counts.d4))
      (fun i => (A.degree4 i).value) +
    Finset.sum (Finset.univ : Finset (Fin counts.d5))
      (fun i => (A.degree5 i).value) +
    Finset.sum (Finset.univ : Finset (Fin counts.d6))
      (fun i => (A.degree6 i).value) +
    Finset.sum (Finset.univ : Finset (Fin counts.b))
      (fun i => (A.nontriangle i).value) +
    Finset.sum (Finset.univ : Finset (Fin counts.B))
      (fun i => (A.longArc i).value)

/-- Pointwise concrete angle certificates transfer to the E12 real lower
contribution sum. -/
theorem lowerContributionSum_le_accountedAngleSum
    (A : OuterBoundaryLocalAngles G counts) :
    BoundaryAngleRealization.OuterBoundaryAngleRealization.lowerContributionSum counts <=
      A.accountedAngleSum := by
  have h3 :
      Finset.sum (Finset.univ : Finset (Fin counts.d3))
          (fun _ => (Real.pi / 3) * (2 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin counts.d3))
          (fun i => (A.degree3 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin counts.d3)))
      (fun i _hi => (A.degree3 i).lower_two)
  have h4 :
      Finset.sum (Finset.univ : Finset (Fin counts.d4))
          (fun _ => (Real.pi / 3) * (3 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin counts.d4))
          (fun i => (A.degree4 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin counts.d4)))
      (fun i _hi => (A.degree4 i).lower_three)
  have h5 :
      Finset.sum (Finset.univ : Finset (Fin counts.d5))
          (fun _ => (Real.pi / 3) * (4 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin counts.d5))
          (fun i => (A.degree5 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin counts.d5)))
      (fun i _hi => (A.degree5 i).lower_four)
  have h6 :
      Finset.sum (Finset.univ : Finset (Fin counts.d6))
          (fun _ => (Real.pi / 3) * (5 : Real)) <=
        Finset.sum (Finset.univ : Finset (Fin counts.d6))
          (fun i => (A.degree6 i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin counts.d6)))
      (fun i _hi => (A.degree6 i).lower_five)
  have hb :
      Finset.sum (Finset.univ : Finset (Fin counts.b))
          (fun _ => Real.pi / 3) <=
        Finset.sum (Finset.univ : Finset (Fin counts.b))
          (fun i => (A.nontriangle i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin counts.b)))
      (fun i _hi => (A.nontriangle i).lower_one)
  have hB :
      Finset.sum (Finset.univ : Finset (Fin counts.B))
          (fun _ => Real.pi / 3) <=
        Finset.sum (Finset.univ : Finset (Fin counts.B))
          (fun i => (A.longArc i).value) :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin counts.B)))
      (fun i _hi => (A.longArc i).lower_one)
  unfold BoundaryAngleRealization.OuterBoundaryAngleRealization.lowerContributionSum
    accountedAngleSum
  nlinarith [h3, h4, h5, h6, hb, hB]

/-- The concrete local angles account for at least the forced E12 angle side. -/
theorem forcedBoundaryAngleSum_le_accountedAngleSum
    (A : OuterBoundaryLocalAngles G counts) :
    counts.forcedBoundaryAngleSum <= A.accountedAngleSum := by
  rw [forcedBoundaryAngleSum_eq_lowerContributionSum]
  exact A.lowerContributionSum_le_accountedAngleSum

end OuterBoundaryLocalAngles

/-- Explicit remaining real geometric data needed to turn local E12 angle
certificates into a concrete boundary-angle certificate. -/
structure OuterBoundaryGeometricWitness
    {G : CanonicalStraightLineUnitDistanceGraph n}
    {counts : BoundaryCounts}
    (angles : OuterBoundaryLocalAngles G counts) where
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum = angles.accountedAngleSum + unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon : geometricAngleSum <= counts.polygonAngleSum

namespace OuterBoundaryGeometricWitness

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {counts : BoundaryCounts}
variable {angles : OuterBoundaryLocalAngles G counts}

/-- The explicit real witness transfers the local E12 lower bound to the full
geometric angle sum. -/
theorem forced_le_geometricAngleSum
    (W : OuterBoundaryGeometricWitness angles) :
    counts.forcedBoundaryAngleSum <= W.geometricAngleSum := by
  rw [W.geometricAngleSum_eq]
  nlinarith [angles.forcedBoundaryAngleSum_le_accountedAngleSum,
    W.unaccounted_nonnegative]

/-- Assemble the explicit local E12 angles and real geometric witness into the
existing concrete certificate consumer. -/
def toConcreteCertificates
    (W : OuterBoundaryGeometricWitness angles) :
    BoundaryAngleCertificatesConcrete.OuterBoundaryAngleCertificates G counts where
  degree3 := angles.degree3
  degree4 := angles.degree4
  degree5 := angles.degree5
  degree6 := angles.degree6
  nontriangle := angles.nontriangle
  longArc := angles.longArc
  unaccountedAngle := W.unaccountedAngle
  geometricAngleSum := W.geometricAngleSum
  geometricAngleSum_eq := by
    simpa [OuterBoundaryLocalAngles.accountedAngleSum] using W.geometricAngleSum_eq
  unaccounted_nonnegative := W.unaccounted_nonnegative
  geometric_le_polygon := W.geometric_le_polygon

/-- The counting-layer E12 angle lower bound produced by the assembled
concrete certificates. -/
theorem angleLowerBound
    (W : OuterBoundaryGeometricWitness angles) :
    counts.AngleLowerBound :=
  W.toConcreteCertificates.angleLowerBound

/-- E12 from assembled concrete local angle certificates. -/
theorem boundaryAngleCountInequality
    (W : OuterBoundaryGeometricWitness angles) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  W.toConcreteCertificates.boundaryAngleCountInequality

/-- Negative-element E12 from assembled concrete local angle certificates. -/
theorem boundaryNegativeCountInequality
    (W : OuterBoundaryGeometricWitness angles) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  W.toConcreteCertificates.boundaryNegativeCountInequality

end OuterBoundaryGeometricWitness

/-! ## Subpolygon E13 assembly -/

/-- The concrete local angle certificates that account for the E13 subpolygon
degree classes. -/
structure SubpolygonLocalAngles
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : SubpolygonCore.BoundaryCycle G)
    (S : SubpolygonCore.InducedVertexSet G C) where
  degree2 :
    Fin S.degreeCounts.D2 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 1
  degree3 :
    Fin S.degreeCounts.D3 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 2
  degree4 :
    Fin S.degreeCounts.D4 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 3
  degree5 :
    Fin S.degreeCounts.D5 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 4
  degree6 :
    Fin S.degreeCounts.D6 -> BoundaryAngleCertificatesConcrete.AngleMassCertificate G 5

namespace SubpolygonLocalAngles

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : SubpolygonCore.BoundaryCycle G}
variable {S : SubpolygonCore.InducedVertexSet G C}

/-- The real angle mass accounted for by the supplied concrete E13 local
certificates. -/
def accountedAngleSum (A : SubpolygonLocalAngles G C S) : Real :=
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

/-- Pointwise concrete angle certificates transfer to the E13 real lower
contribution sum. -/
theorem lowerContributionSum_le_accountedAngleSum
    (A : SubpolygonLocalAngles G C S) :
    BoundaryAngleCertificatesConcrete.SubpolygonAngleCertificates.lowerContributionSum
        S.degreeCounts <=
      A.accountedAngleSum := by
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
  unfold BoundaryAngleCertificatesConcrete.SubpolygonAngleCertificates.lowerContributionSum
    accountedAngleSum
  nlinarith [h2, h3, h4, h5, h6]

/-- The concrete local angles account for at least the forced E13 angle side. -/
theorem forcedSubpolygonAngleSum_le_accountedAngleSum
    (A : SubpolygonLocalAngles G C S) :
    S.degreeCounts.forcedSubpolygonAngleSum <= A.accountedAngleSum := by
  rw [forcedSubpolygonAngleSum_eq_lowerContributionSum]
  exact A.lowerContributionSum_le_accountedAngleSum

end SubpolygonLocalAngles

/-- Explicit remaining real geometric data needed to turn local E13 angle
certificates into a concrete subpolygon angle certificate. -/
structure SubpolygonGeometricWitness
    {G : CanonicalStraightLineUnitDistanceGraph n}
    {C : SubpolygonCore.BoundaryCycle G}
    {S : SubpolygonCore.InducedVertexSet G C}
    (angles : SubpolygonLocalAngles G C S) where
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum = angles.accountedAngleSum + unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon : geometricAngleSum <= S.degreeCounts.polygonAngleSum

namespace SubpolygonGeometricWitness

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : SubpolygonCore.BoundaryCycle G}
variable {S : SubpolygonCore.InducedVertexSet G C}
variable {angles : SubpolygonLocalAngles G C S}

/-- The explicit real witness transfers the local E13 lower bound to the full
geometric angle sum. -/
theorem forced_le_geometricAngleSum
    (W : SubpolygonGeometricWitness angles) :
    S.degreeCounts.forcedSubpolygonAngleSum <= W.geometricAngleSum := by
  rw [W.geometricAngleSum_eq]
  nlinarith [angles.forcedSubpolygonAngleSum_le_accountedAngleSum,
    W.unaccounted_nonnegative]

/-- Assemble the explicit local E13 angles and real geometric witness into the
existing concrete certificate consumer. -/
def toConcreteCertificates
    (W : SubpolygonGeometricWitness angles) :
    BoundaryAngleCertificatesConcrete.SubpolygonAngleCertificates G C S where
  degree2 := angles.degree2
  degree3 := angles.degree3
  degree4 := angles.degree4
  degree5 := angles.degree5
  degree6 := angles.degree6
  unaccountedAngle := W.unaccountedAngle
  geometricAngleSum := W.geometricAngleSum
  geometricAngleSum_eq := by
    simpa [SubpolygonLocalAngles.accountedAngleSum] using W.geometricAngleSum_eq
  unaccounted_nonnegative := W.unaccounted_nonnegative
  geometric_le_polygon := W.geometric_le_polygon

/-- The counting-layer E13 angle lower bound produced by the assembled
concrete certificates. -/
theorem angleLowerBound
    (W : SubpolygonGeometricWitness angles) :
    S.degreeCounts.AngleLowerBound :=
  W.toConcreteCertificates.angleLowerBound

/-- E13 with high-degree slack from assembled concrete local angle
certificates. -/
theorem lowDegreeWithHighDegreeSlack
    (W : SubpolygonGeometricWitness angles) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  W.toConcreteCertificates.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion from assembled concrete local
angle certificates. -/
theorem lowDegreeInequality
    (W : SubpolygonGeometricWitness angles) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  W.toConcreteCertificates.lowDegreeInequality

end SubpolygonGeometricWitness

end

end BoundaryAngleAssembly
end Swanepoel
end ErdosProblems1066
