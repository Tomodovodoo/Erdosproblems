import ErdosProblems1066.Swanepoel.SubpolygonAngleW10

set_option autoImplicit false

/-!
# W12 subpolygon angle worker

This module supplies a narrow concrete worker for the E13 subpolygon angle
lower bound.  It keeps the local geometry explicit: adjacent unit-distance
edges with distinct endpoints give a checked `pi / 3` angle, and assembled
subpolygon angle witnesses are routed through
`SubpolygonAssembly.SubpolygonCycleCountAngleData`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonAngleW12

open BoundaryAngleWitnessConstruction
open BoundaryCounting
open FaceReduction
open PlanarInterface
open SubpolygonAssembly
open SubpolygonCore

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-! ## Pointwise Euclidean angle comparisons -/

/-- Build the concrete local angle certificate from two incident graph edges
and distinct outer endpoints. -/
def unitSeparatedAngleOfAdjDistinct
    (left center right : Fin n)
    (left_adj : G.Adj left center)
    (right_adj : G.Adj right center)
    (endpoints_ne : left ≠ right) :
    UnitSeparatedAngle G where
  left := left
  center := center
  right := right
  left_adj := left_adj
  right_adj := right_adj
  endpoints_ne := endpoints_ne

/-- Dot-product form of the local comparison used by the angle certificate. -/
theorem dotAt_le_half_of_adjacent_distinct_endpoints
    (left center right : Fin n)
    (left_adj : G.Adj left center)
    (right_adj : G.Adj right center)
    (endpoints_ne : left ≠ right) :
    TriangleAngleFacts.dotAt
        (G.point left) (G.point center) (G.point right) <= 1 / 2 :=
  UnitSeparatedAngle.dotAt_le_half
    (unitSeparatedAngleOfAdjDistinct left center right
      left_adj right_adj endpoints_ne)

/-- Real-angle form: two incident unit graph edges whose other endpoints are
distinct force a local angle of at least `pi / 3`. -/
theorem pi_div_three_le_angleAt_of_adjacent_distinct_endpoints
    (left center right : Fin n)
    (left_adj : G.Adj left center)
    (right_adj : G.Adj right center)
    (endpoints_ne : left ≠ right) :
    Real.pi / 3 <=
      AngleGeometry.angleAt (G.point left) (G.point center) (G.point right) := by
  simpa [unitSeparatedAngleOfAdjDistinct,
    BoundaryAngleCertificatesConcrete.UnitSeparatedAngle.value] using
      UnitSeparatedAngle.pi_div_three_le_value
        (unitSeparatedAngleOfAdjDistinct left center right
          left_adj right_adj endpoints_ne)

/-! ## Feeding `SubpolygonCycleCountAngleData` -/

/-- The assembled local subpolygon angle witness as explicit
`SubpolygonCycleCountAngleData`.  The count realization is canonical, so the
target counts are definitionally the induced boundary counts. -/
def cycleCountAngleDataOfGeometricWitness
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    {angles : BoundaryAngleAssembly.SubpolygonLocalAngles G C S}
    (W : BoundaryAngleAssembly.SubpolygonGeometricWitness angles) :
    SubpolygonCycleCountAngleData G where
  boundary := C
  vertexSet := S
  countRealization := SubpolygonCountRealization.canonical S
  geometricAngleSum := W.geometricAngleSum
  forced_le_geometric := by
    simpa [SubpolygonCountRealization.canonical] using
      W.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [SubpolygonCountRealization.canonical] using W.geometric_le_polygon

@[simp]
theorem cycleCountAngleDataOfGeometricWitness_counts
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    {angles : BoundaryAngleAssembly.SubpolygonLocalAngles G C S}
    (W : BoundaryAngleAssembly.SubpolygonGeometricWitness angles) :
    (cycleCountAngleDataOfGeometricWitness W).counts = S.degreeCounts :=
  rfl

/-- The cycle/count package produced by a geometric witness has the E13 angle
lower bound through `SubpolygonCycleCountAngleData.angleLowerBound`. -/
theorem angleLowerBound_viaCycleCountAngleData
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    {angles : BoundaryAngleAssembly.SubpolygonLocalAngles G C S}
    (W : BoundaryAngleAssembly.SubpolygonGeometricWitness angles) :
    S.degreeCounts.AngleLowerBound := by
  simpa using (cycleCountAngleDataOfGeometricWitness W).angleLowerBound

/-- E13 high-degree slack routed specifically through
`SubpolygonCycleCountAngleData.lowDegreeWithHighDegreeSlack`. -/
theorem lowDegreeWithHighDegreeSlack_viaCycleCountAngleData
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    {angles : BoundaryAngleAssembly.SubpolygonLocalAngles G C S}
    (W : BoundaryAngleAssembly.SubpolygonGeometricWitness angles) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa using
    (cycleCountAngleDataOfGeometricWitness W).lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion routed specifically through
`SubpolygonCycleCountAngleData.lowDegreeInequality`. -/
theorem lowDegreeInequality_viaCycleCountAngleData
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    {angles : BoundaryAngleAssembly.SubpolygonLocalAngles G C S}
    (W : BoundaryAngleAssembly.SubpolygonGeometricWitness angles) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa using (cycleCountAngleDataOfGeometricWitness W).lowDegreeInequality

/-! ## Unit-separated witness specialization -/

/-- A raw unit-separated subpolygon witness as explicit
`SubpolygonCycleCountAngleData`. -/
def cycleCountAngleDataOfUnitSeparatedWitness
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    (W : SubpolygonUnitSeparatedWitness G C S) :
    SubpolygonCycleCountAngleData G :=
  cycleCountAngleDataOfGeometricWitness W.toGeometricWitness

@[simp]
theorem cycleCountAngleDataOfUnitSeparatedWitness_counts
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    (W : SubpolygonUnitSeparatedWitness G C S) :
    (cycleCountAngleDataOfUnitSeparatedWitness W).counts = S.degreeCounts :=
  rfl

/-- The checked E13 angle lower bound produced by unit-separated local angles,
via the cycle/count data package. -/
theorem angleLowerBound_of_unitSeparatedWitness
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    (W : SubpolygonUnitSeparatedWitness G C S) :
    S.degreeCounts.AngleLowerBound := by
  simpa using
    (cycleCountAngleDataOfUnitSeparatedWitness W).angleLowerBound

/-- E13 high-degree slack from a unit-separated witness, routed through
`SubpolygonCycleCountAngleData`. -/
theorem lowDegreeWithHighDegreeSlack_of_unitSeparatedWitness
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    (W : SubpolygonUnitSeparatedWitness G C S) :
    S.degreeCounts.D5 + 2 * S.degreeCounts.D6 + 6 <=
      2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa using
    (cycleCountAngleDataOfUnitSeparatedWitness W).lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion from a unit-separated witness,
routed through `SubpolygonCycleCountAngleData`. -/
theorem lowDegreeInequality_of_unitSeparatedWitness
    {C : BoundaryCycle G} {S : InducedVertexSet G C}
    (W : SubpolygonUnitSeparatedWitness G C S) :
    6 <= 2 * S.degreeCounts.D2 + S.degreeCounts.D3 := by
  simpa using (cycleCountAngleDataOfUnitSeparatedWitness W).lowDegreeInequality

end

end SubpolygonAngleW12
end Swanepoel
end ErdosProblems1066
