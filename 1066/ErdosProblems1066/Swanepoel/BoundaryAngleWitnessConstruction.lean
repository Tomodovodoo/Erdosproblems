import ErdosProblems1066.Swanepoel.AngleBridgeFacts
import ErdosProblems1066.Swanepoel.BoundaryAngleCertificatesConcrete
import ErdosProblems1066.Swanepoel.BoundaryAngleAssembly

set_option autoImplicit false

/-!
# Boundary angle witness construction

This file builds the `BoundaryAngleAssembly` witness packages from explicit
unit-separated local angle data.  The only remaining geometric inputs are the
real angle-sum comparison fields: the construction does not hide the polygon
angle accounting behind a bare counting assumption.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleWitnessConstruction

open BoundaryCounting
open FaceReduction
open PlanarInterface

universe u

noncomputable section

variable {n : Nat}

abbrev UnitSeparatedAngle
    (G : CanonicalStraightLineUnitDistanceGraph n) :=
  BoundaryAngleCertificatesConcrete.UnitSeparatedAngle G

abbrev AngleMassCertificate
    (G : CanonicalStraightLineUnitDistanceGraph n) (m : Nat) :=
  BoundaryAngleCertificatesConcrete.AngleMassCertificate G m

namespace UnitSeparatedAngle

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The dot-product form of the checked local angle lower bound, directly from
the explicit unit/separation data. -/
theorem dotAt_le_half (A : UnitSeparatedAngle G) :
    TriangleAngleFacts.dotAt
        (G.point A.left) (G.point A.center) (G.point A.right) <= 1 / 2 :=
  AngleBridgeFacts.dotAt_le_half_of_eucUnit_sides_eucSeparated_base
    A.left_eucUnit A.right_eucUnit A.endpoints_eucSeparated

/-- The real-angle form consumed by the angle-mass certificates. -/
theorem pi_div_three_le_value (A : UnitSeparatedAngle G) :
    Real.pi / 3 <= A.value :=
  BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.pi_div_three_le_value A

end UnitSeparatedAngle

/-- Build an angle-mass certificate from exactly `m` explicit local
unit-separated angles. -/
def angleMassCertificate
    {G : CanonicalStraightLineUnitDistanceGraph n} {m : Nat}
    (angle : Fin m -> UnitSeparatedAngle G) :
    AngleMassCertificate G m where
  angle := angle

/-! ## Outer-boundary E12 witnesses -/

/-- Explicit unit-separated local angle data for the E12 outer-boundary
classes, plus the remaining real geometric angle-sum comparison. -/
structure OuterBoundaryUnitSeparatedWitness
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (counts : BoundaryCounts) where
  degree3 : Fin counts.d3 -> Fin 2 -> UnitSeparatedAngle G
  degree4 : Fin counts.d4 -> Fin 3 -> UnitSeparatedAngle G
  degree5 : Fin counts.d5 -> Fin 4 -> UnitSeparatedAngle G
  degree6 : Fin counts.d6 -> Fin 5 -> UnitSeparatedAngle G
  nontriangle : Fin counts.b -> Fin 1 -> UnitSeparatedAngle G
  longArc : Fin counts.B -> Fin 1 -> UnitSeparatedAngle G
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin counts.d3))
          (fun i => (angleMassCertificate (degree3 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.d4))
          (fun i => (angleMassCertificate (degree4 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.d5))
          (fun i => (angleMassCertificate (degree5 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.d6))
          (fun i => (angleMassCertificate (degree6 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.b))
          (fun i => (angleMassCertificate (nontriangle i)).value) +
      Finset.sum (Finset.univ : Finset (Fin counts.B))
          (fun i => (angleMassCertificate (longArc i)).value) +
      unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon : geometricAngleSum <= counts.polygonAngleSum

namespace OuterBoundaryUnitSeparatedWitness

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {counts : BoundaryCounts}

/-- Package the raw local E12 angle witnesses for `BoundaryAngleAssembly`. -/
def toLocalAngles
    (W : OuterBoundaryUnitSeparatedWitness G counts) :
    BoundaryAngleAssembly.OuterBoundaryLocalAngles G counts where
  degree3 := fun i => angleMassCertificate (W.degree3 i)
  degree4 := fun i => angleMassCertificate (W.degree4 i)
  degree5 := fun i => angleMassCertificate (W.degree5 i)
  degree6 := fun i => angleMassCertificate (W.degree6 i)
  nontriangle := fun i => angleMassCertificate (W.nontriangle i)
  longArc := fun i => angleMassCertificate (W.longArc i)

/-- The full E12 assembly witness built from explicit local angle data and the
exposed geometric angle-sum comparison fields. -/
def toGeometricWitness
    (W : OuterBoundaryUnitSeparatedWitness G counts) :
    BoundaryAngleAssembly.OuterBoundaryGeometricWitness W.toLocalAngles where
  unaccountedAngle := W.unaccountedAngle
  geometricAngleSum := W.geometricAngleSum
  geometricAngleSum_eq := by
    simpa [toLocalAngles,
      BoundaryAngleAssembly.OuterBoundaryLocalAngles.accountedAngleSum]
      using W.geometricAngleSum_eq
  unaccounted_nonnegative := W.unaccounted_nonnegative
  geometric_le_polygon := W.geometric_le_polygon

/-- Concrete E12 certificates obtained from the raw unit-separated local angle
witnesses. -/
def toConcreteCertificates
    (W : OuterBoundaryUnitSeparatedWitness G counts) :
    BoundaryAngleCertificatesConcrete.OuterBoundaryAngleCertificates G counts :=
  W.toGeometricWitness.toConcreteCertificates

/-- The E12 counting lower-bound package projected from explicit local angle
witnesses. -/
theorem angleLowerBound
    (W : OuterBoundaryUnitSeparatedWitness G counts) :
    counts.AngleLowerBound :=
  W.toGeometricWitness.angleLowerBound

/-- E12 from explicit local unit-separated angle witnesses. -/
theorem boundaryAngleCountInequality
    (W : OuterBoundaryUnitSeparatedWitness G counts) :
    counts.d5 + 2 * counts.d6 + counts.b + counts.B + 6 <= counts.d3 :=
  W.toGeometricWitness.boundaryAngleCountInequality

/-- Negative-element E12 from explicit local unit-separated angle witnesses. -/
theorem boundaryNegativeCountInequality
    (W : OuterBoundaryUnitSeparatedWitness G counts) :
    counts.negativeCount + counts.B + 6 <= counts.d3 :=
  W.toGeometricWitness.boundaryNegativeCountInequality

end OuterBoundaryUnitSeparatedWitness

/-! ## Subpolygon E13 witnesses -/

/-- Explicit unit-separated local angle data for the E13 subpolygon degree
classes, plus the remaining real geometric angle-sum comparison. -/
structure SubpolygonUnitSeparatedWitness
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : SubpolygonCore.BoundaryCycle G)
    (S : SubpolygonCore.InducedVertexSet G C) where
  degree2 : Fin S.degreeCounts.D2 -> Fin 1 -> UnitSeparatedAngle G
  degree3 : Fin S.degreeCounts.D3 -> Fin 2 -> UnitSeparatedAngle G
  degree4 : Fin S.degreeCounts.D4 -> Fin 3 -> UnitSeparatedAngle G
  degree5 : Fin S.degreeCounts.D5 -> Fin 4 -> UnitSeparatedAngle G
  degree6 : Fin S.degreeCounts.D6 -> Fin 5 -> UnitSeparatedAngle G
  unaccountedAngle : Real
  geometricAngleSum : Real
  geometricAngleSum_eq :
    geometricAngleSum =
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D2))
          (fun i => (angleMassCertificate (degree2 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D3))
          (fun i => (angleMassCertificate (degree3 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D4))
          (fun i => (angleMassCertificate (degree4 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D5))
          (fun i => (angleMassCertificate (degree5 i)).value) +
      Finset.sum (Finset.univ : Finset (Fin S.degreeCounts.D6))
          (fun i => (angleMassCertificate (degree6 i)).value) +
      unaccountedAngle
  unaccounted_nonnegative : 0 <= unaccountedAngle
  geometric_le_polygon :
    geometricAngleSum <= S.degreeCounts.polygonAngleSum

namespace SubpolygonUnitSeparatedWitness

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : SubpolygonCore.BoundaryCycle G}
variable {S : SubpolygonCore.InducedVertexSet G C}

/-- Package the raw local E13 angle witnesses for `BoundaryAngleAssembly`. -/
def toLocalAngles
    (W : SubpolygonUnitSeparatedWitness G C S) :
    BoundaryAngleAssembly.SubpolygonLocalAngles G C S where
  degree2 := fun i => angleMassCertificate (W.degree2 i)
  degree3 := fun i => angleMassCertificate (W.degree3 i)
  degree4 := fun i => angleMassCertificate (W.degree4 i)
  degree5 := fun i => angleMassCertificate (W.degree5 i)
  degree6 := fun i => angleMassCertificate (W.degree6 i)

/-- The full E13 assembly witness built from explicit local angle data and the
exposed geometric angle-sum comparison fields. -/
def toGeometricWitness
    (W : SubpolygonUnitSeparatedWitness G C S) :
    BoundaryAngleAssembly.SubpolygonGeometricWitness W.toLocalAngles where
  unaccountedAngle := W.unaccountedAngle
  geometricAngleSum := W.geometricAngleSum
  geometricAngleSum_eq := by
    simpa [toLocalAngles,
      BoundaryAngleAssembly.SubpolygonLocalAngles.accountedAngleSum]
      using W.geometricAngleSum_eq
  unaccounted_nonnegative := W.unaccounted_nonnegative
  geometric_le_polygon := W.geometric_le_polygon

/-- Concrete E13 certificates obtained from the raw unit-separated local angle
witnesses. -/
def toConcreteCertificates
    (W : SubpolygonUnitSeparatedWitness G C S) :
    BoundaryAngleCertificatesConcrete.SubpolygonAngleCertificates G C S :=
  W.toGeometricWitness.toConcreteCertificates

/-- The E13 counting lower-bound package projected from explicit local angle
witnesses. -/
theorem angleLowerBound
    (W : SubpolygonUnitSeparatedWitness G C S) :
    S.degreeCounts.AngleLowerBound :=
  W.toGeometricWitness.angleLowerBound

/-- E13 with high-degree slack from explicit local unit-separated angle
witnesses. -/
theorem lowDegreeWithHighDegreeSlack
    (W : SubpolygonUnitSeparatedWitness G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  W.toGeometricWitness.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree E13 conclusion from explicit local
unit-separated angle witnesses. -/
theorem lowDegreeInequality
    (W : SubpolygonUnitSeparatedWitness G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 :=
  W.toGeometricWitness.lowDegreeInequality

end SubpolygonUnitSeparatedWitness

end

end BoundaryAngleWitnessConstruction
end Swanepoel
end ErdosProblems1066
