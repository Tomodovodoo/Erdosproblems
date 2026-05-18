import ErdosProblems1066.Swanepoel.SubpolygonInstantiation
import ErdosProblems1066.Swanepoel.BoundaryAngleWitnessConstruction

set_option autoImplicit false

/-!
# W10 subpolygon angle/count instantiation

This module tightens the W9 subpolygon facade by replacing bare real
subpolygon angle comparisons with explicit unit-separated local angle
witnesses.  The finite face fields still supply the subpolygon, its induced
vertex set, and the inside/on predicates.  The unit-separated witness supplies
the checked E13 angle lower bound used by the low-degree count inequalities.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonAngleW10

open BoundaryAngleWitnessConstruction
open BoundaryCounting
open FaceReduction
open SubpolygonCore
open SubpolygonDataConcrete
open SubpolygonInstantiation

universe u

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-! ## One face subpolygon -/

/-- Explicit face-subpolygon fields plus checked local angle witnesses.

The geometry is the flattened W9 face-subpolygon data.  The angle witness is
indexed by the boundary cycle and induced vertex set computed from that same
geometry, so the count projections below are definitionally tied to the
finite vertex fields.
-/
structure FaceSubpolygonAngleCountFields
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  geometry : FaceSubpolygonFields D
  angleWitness :
    SubpolygonUnitSeparatedWitness G
      geometry.toGeometryData.boundary
      geometry.toGeometryData.vertexSet

namespace FaceSubpolygonAngleCountFields

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- The induced E13 counts determined by the explicit finite vertex set. -/
def counts (S : FaceSubpolygonAngleCountFields D) :
    SubpolygonDegreeCounts :=
  S.geometry.counts

@[simp]
theorem counts_eq_geometry_counts
    (S : FaceSubpolygonAngleCountFields D) :
    S.counts = S.geometry.counts :=
  rfl

@[simp]
theorem counts_eq_witness_degreeCounts
    (S : FaceSubpolygonAngleCountFields D) :
    S.counts =
      S.geometry.toGeometryData.vertexSet.degreeCounts :=
  rfl

/-- The checked E13 angle lower bound projected from the local witnesses. -/
theorem angleLowerBound
    (S : FaceSubpolygonAngleCountFields D) :
    S.counts.AngleLowerBound := by
  simpa [counts] using S.angleWitness.angleLowerBound

/-- The lower angle side is bounded by the supplied geometric angle sum. -/
theorem forced_le_geometricAngleSum
    (S : FaceSubpolygonAngleCountFields D) :
    S.counts.forcedSubpolygonAngleSum <=
      S.angleWitness.geometricAngleSum := by
  simpa [counts] using
    S.angleWitness.toGeometricWitness.forced_le_geometricAngleSum

/-- The supplied geometric angle sum is bounded by the polygon angle sum. -/
theorem geometricAngleSum_le_polygon
    (S : FaceSubpolygonAngleCountFields D) :
    S.angleWitness.geometricAngleSum <= S.counts.polygonAngleSum := by
  simpa [counts] using S.angleWitness.geometric_le_polygon

/-- Forget the local angle witnesses to the W9 angle-field facade. -/
def toFaceSubpolygonAngleFields
    (S : FaceSubpolygonAngleCountFields D) :
    FaceSubpolygonAngleFields D where
  geometry := S.geometry
  geometricAngleSum := S.angleWitness.geometricAngleSum
  forced_le_geometric := S.forced_le_geometricAngleSum
  geometric_le_polygon := S.geometricAngleSum_le_polygon

@[simp]
theorem toFaceSubpolygonAngleFields_counts
    (S : FaceSubpolygonAngleCountFields D) :
    S.toFaceSubpolygonAngleFields.counts = S.counts :=
  rfl

@[simp]
theorem toFaceSubpolygonAngleFields_geometricAngleSum
    (S : FaceSubpolygonAngleCountFields D) :
    S.toFaceSubpolygonAngleFields.geometricAngleSum =
      S.angleWitness.geometricAngleSum :=
  rfl

/-- Forget all the way to the concrete core face-subpolygon angle package. -/
def toCoreFaceSubpolygonAngleData
    (S : FaceSubpolygonAngleCountFields D) :
    CoreFaceSubpolygonAngleData D.core :=
  S.toFaceSubpolygonAngleFields.toCoreFaceSubpolygonAngleData

@[simp]
theorem toCoreFaceSubpolygonAngleData_counts
    (S : FaceSubpolygonAngleCountFields D) :
    S.toCoreFaceSubpolygonAngleData.counts = S.counts :=
  rfl

/-- E13 with high-degree slack from explicit finite fields and local angles. -/
theorem lowDegreeWithHighDegreeSlack
    (S : FaceSubpolygonAngleCountFields D) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using
    SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
      S.counts S.angleLowerBound

/-- Swanepoel Lemma 4's low-degree conclusion from explicit fields. -/
theorem lowDegree
    (S : FaceSubpolygonAngleCountFields D) :
    6 <= 2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using
    SubpolygonDegreeCounts.subpolygon_low_degree_inequality
      S.counts S.angleLowerBound

/-- The same high-degree-slack inequality routed through the instantiated
subpolygon angle data. -/
theorem lowDegreeWithHighDegreeSlack_viaInstantiation
    (S : FaceSubpolygonAngleCountFields D) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 := by
  simpa using S.toFaceSubpolygonAngleFields.lowDegreeWithHighDegreeSlack

/-- The same low-degree conclusion routed through the instantiated
subpolygon angle data. -/
theorem lowDegree_viaInstantiation
    (S : FaceSubpolygonAngleCountFields D) :
    6 <= 2 * S.counts.D2 + S.counts.D3 := by
  simpa using S.toFaceSubpolygonAngleFields.lowDegree

end FaceSubpolygonAngleCountFields

/-! ## Families and planar-boundary projections -/

/-- A family of face subpolygons with explicit local angle witnesses. -/
structure FaceSubpolygonAngleCountFamilyFields
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  Subpolygon : Type u
  subpolygonFields :
    Subpolygon -> FaceSubpolygonAngleCountFields D

namespace FaceSubpolygonAngleCountFamilyFields

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- Forget a W10 family to the W9 flattened angle-field family. -/
def toFaceSubpolygonFamilyFields
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    FaceSubpolygonFamilyFields D where
  Subpolygon := F.Subpolygon
  subpolygonFields :=
    fun S => (F.subpolygonFields S).toFaceSubpolygonAngleFields

@[simp]
theorem toFaceSubpolygonFamilyFields_Subpolygon
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    F.toFaceSubpolygonFamilyFields.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toFaceSubpolygonFamilyFields_subpolygonFields_counts
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    (F.toFaceSubpolygonFamilyFields.subpolygonFields S).counts =
      (F.subpolygonFields S).counts :=
  rfl

/-- Instantiate the concrete core face-subpolygon family. -/
def toCoreFaceSubpolygonFamilyData
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    CoreFaceSubpolygonFamilyData.{u} D.core :=
  F.toFaceSubpolygonFamilyFields.toCoreFaceSubpolygonFamilyData

@[simp]
theorem toCoreFaceSubpolygonFamilyData_Subpolygon
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    F.toCoreFaceSubpolygonFamilyData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toCoreFaceSubpolygonFamilyData_subpolygonData_counts
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    (F.toCoreFaceSubpolygonFamilyData.subpolygonData S).counts =
      (F.subpolygonFields S).counts :=
  rfl

/-- The planar-boundary subpolygon inputs induced by the W10 family. -/
def subpolygonInputs
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G :=
  D.subpolygonInputs F.toCoreFaceSubpolygonFamilyData

@[simp]
theorem subpolygonInputs_Subpolygon
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    F.subpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem subpolygonInputs_subpolygonDegreeCounts
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    F.subpolygonInputs.subpolygonDegreeCounts S =
      (F.subpolygonFields S).counts :=
  rfl

/-- The full planar-boundary package instantiated from explicit W10 fields. -/
def toPlanarBoundaryData
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  F.toFaceSubpolygonFamilyFields.toPlanarBoundaryData

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    F.toPlanarBoundaryData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData_counts
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    (F.toPlanarBoundaryData.subpolygonData S).counts =
      (F.subpolygonFields S).counts :=
  rfl

/-- Concrete face-counting data projected from the instantiated package. -/
def concreteFaceCountingData
    (F : FaceSubpolygonAngleCountFamilyFields D) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      F.toPlanarBoundaryData :=
  F.toFaceSubpolygonFamilyFields.concreteFaceCountingData

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    F.concreteFaceCountingData.subpolygonCounts S =
      (F.subpolygonFields S).counts :=
  rfl

/-- E13 with high-degree slack for every instantiated W10 subpolygon. -/
theorem lowDegreeWithHighDegreeSlack
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    (F.subpolygonFields S).counts.D5 +
        2 * (F.subpolygonFields S).counts.D6 + 6 <=
      2 * (F.subpolygonFields S).counts.D2 +
        (F.subpolygonFields S).counts.D3 :=
  (F.subpolygonFields S).lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for every instantiated W10
subpolygon. -/
theorem lowDegree
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonFields S).counts.D2 +
      (F.subpolygonFields S).counts.D3 :=
  (F.subpolygonFields S).lowDegree

/-- The high-degree-slack inequality as projected by the concrete
face-counting package. -/
theorem lowDegreeWithHighDegreeSlack_viaConcreteFaceCountingData
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    (F.subpolygonFields S).counts.D5 +
        2 * (F.subpolygonFields S).counts.D6 + 6 <=
      2 * (F.subpolygonFields S).counts.D2 +
        (F.subpolygonFields S).counts.D3 := by
  simpa using
    F.concreteFaceCountingData.subpolygonLowDegreeWithHighDegreeSlack S

/-- The low-degree conclusion as projected by the concrete face-counting
package. -/
theorem lowDegree_viaConcreteFaceCountingData
    (F : FaceSubpolygonAngleCountFamilyFields D)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonFields S).counts.D2 +
      (F.subpolygonFields S).counts.D3 := by
  simpa using F.concreteFaceCountingData.subpolygonLowDegree S

end FaceSubpolygonAngleCountFamilyFields

end

end SubpolygonAngleW10
end Swanepoel
end ErdosProblems1066
