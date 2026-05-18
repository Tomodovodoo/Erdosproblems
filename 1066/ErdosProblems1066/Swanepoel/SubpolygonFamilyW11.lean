import ErdosProblems1066.Swanepoel.SubpolygonAngleW10
import ErdosProblems1066.Swanepoel.SubpolygonFaceConstruction
import ErdosProblems1066.Swanepoel.SubpolygonAssembly
import ErdosProblems1066.Swanepoel.SubpolygonDataConcrete
import ErdosProblems1066.Swanepoel.SubpolygonInstantiation

set_option autoImplicit false

/-!
# W11 subpolygon family package

This module is a small facade over the W10 subpolygon angle/count package.
It exposes the remaining fields for each concrete face-boundary subpolygon
directly: the chosen face cycle, the finite induced vertex set, the inside/on
predicates, and the unit-separated local angle witnesses.  The projections
below check that these explicit fields feed the existing angle and count
low-degree interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonFamilyW11

open BoundaryAngleWitnessConstruction
open BoundaryCounting
open FaceReduction
open PlanarInterface
open SubpolygonAngleW10
open SubpolygonAssembly
open SubpolygonCore
open SubpolygonDataConcrete
open SubpolygonFaceConstruction
open SubpolygonInstantiation

universe u

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-! ## One concrete boundary-cycle subpolygon -/

/--
The explicit fields still needed for one concrete subpolygon boundary cycle
after the outer face data has been fixed.

The boundary cycle and induced vertex set are computed from the chosen face
and finite vertex set.  The angle witness is indexed by those computed data,
so every downstream count is tied to the same concrete boundary fields.
-/
structure ConcreteBoundaryCycleFields
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  face : D.core.faceBoundary.Face
  vertices : Finset (Fin n)
  boundary_subset :
    (boundaryCycleOfFaceBoundary D.core.faceBoundary face).vertexFinset ⊆
      vertices
  insideOrOn : Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin (D.core.faceBoundary.boundaryLength face),
      onBoundary (D.core.faceBoundary.boundaryVertex face k)
  vertices_iff_insideOrOn :
    forall v : Fin n, v ∈ vertices <-> insideOrOn (G.point v)
  onBoundary_iff_cycle :
    forall v : Fin n,
      onBoundary v <->
        Exists fun k : Fin (D.core.faceBoundary.boundaryLength face) =>
          D.core.faceBoundary.boundaryVertex face k = v
  angleWitness :
    SubpolygonUnitSeparatedWitness G
      (boundaryCycleOfFaceBoundary D.core.faceBoundary face)
      (inducedVertexSetOfFinset
        (boundaryCycleOfFaceBoundary D.core.faceBoundary face)
        vertices boundary_subset)

namespace ConcreteBoundaryCycleFields

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- The concrete boundary cycle projected from the supplied face-boundary data. -/
def boundary (S : ConcreteBoundaryCycleFields D) :
    BoundaryCycle G :=
  boundaryCycleOfFaceBoundary D.core.faceBoundary S.face

@[simp]
theorem boundary_length (S : ConcreteBoundaryCycleFields D) :
    S.boundary.length = D.core.faceBoundary.boundaryLength S.face :=
  rfl

/-- The induced vertex set determined by the explicit finite set. -/
def vertexSet (S : ConcreteBoundaryCycleFields D) :
    InducedVertexSet G S.boundary :=
  inducedVertexSetOfFinset S.boundary S.vertices S.boundary_subset

@[simp]
theorem vertexSet_vertices (S : ConcreteBoundaryCycleFields D) :
    S.vertexSet.vertices = S.vertices :=
  rfl

/-- The computed E13 counts for the induced boundary cycle. -/
def counts (S : ConcreteBoundaryCycleFields D) :
    SubpolygonDegreeCounts :=
  S.vertexSet.degreeCounts

@[simp]
theorem counts_eq_degreeCounts (S : ConcreteBoundaryCycleFields D) :
    S.counts = S.vertexSet.degreeCounts :=
  rfl

/-- Forget the W11 field surface to the W9 explicit geometry fields. -/
def toFaceSubpolygonFields
    (S : ConcreteBoundaryCycleFields D) :
    FaceSubpolygonFields D where
  face := S.face
  vertices := S.vertices
  boundary_subset := S.boundary_subset
  insideOrOn := S.insideOrOn
  onBoundary := S.onBoundary
  boundary_vertex_onBoundary := S.boundary_vertex_onBoundary
  vertices_iff_insideOrOn := S.vertices_iff_insideOrOn
  onBoundary_iff_cycle := S.onBoundary_iff_cycle

@[simp]
theorem toFaceSubpolygonFields_face
    (S : ConcreteBoundaryCycleFields D) :
    S.toFaceSubpolygonFields.face = S.face :=
  rfl

@[simp]
theorem toFaceSubpolygonFields_vertices
    (S : ConcreteBoundaryCycleFields D) :
    S.toFaceSubpolygonFields.vertices = S.vertices :=
  rfl

@[simp]
theorem toFaceSubpolygonFields_counts
    (S : ConcreteBoundaryCycleFields D) :
    S.toFaceSubpolygonFields.counts = S.counts :=
  rfl

/-- The W10 one-subpolygon angle/count package. -/
def toFaceSubpolygonAngleCountFields
    (S : ConcreteBoundaryCycleFields D) :
    FaceSubpolygonAngleCountFields D where
  geometry := S.toFaceSubpolygonFields
  angleWitness := S.angleWitness

@[simp]
theorem toFaceSubpolygonAngleCountFields_counts
    (S : ConcreteBoundaryCycleFields D) :
    S.toFaceSubpolygonAngleCountFields.counts = S.counts :=
  rfl

/-- The concrete angle-bound interface over the computed induced counts. -/
def toConcreteAngleBounds
    (S : ConcreteBoundaryCycleFields D) :
    SubpolygonAngleRealization.ConcreteAngleBounds G S.boundary S.vertexSet :=
  S.angleWitness.toConcreteCertificates.toConcreteAngleBounds

/-- Projection to the angle low-degree interface. -/
def toSubpolygonAngleLowerBoundPackage
    (S : ConcreteBoundaryCycleFields D) :
    BoundaryAngleInterface.SubpolygonAngleLowerBoundPackage :=
  S.toConcreteAngleBounds.toSubpolygonAngleLowerBoundPackage

@[simp]
theorem toSubpolygonAngleLowerBoundPackage_counts
    (S : ConcreteBoundaryCycleFields D) :
    S.toSubpolygonAngleLowerBoundPackage.counts = S.counts :=
  rfl

/-- Projection to the core degree-count interface. -/
def toDegreeCountData
    (S : ConcreteBoundaryCycleFields D) :
    DegreeCountData G S.boundary S.vertexSet :=
  S.toConcreteAngleBounds.toDegreeCountData

/-- Projection to the full core subpolygon package. -/
def toSubpolygonPackage
    (S : ConcreteBoundaryCycleFields D) :
    SubpolygonPackage G where
  boundary := S.boundary
  vertexSet := S.vertexSet
  degreeData := S.toDegreeCountData

@[simp]
theorem toSubpolygonPackage_counts
    (S : ConcreteBoundaryCycleFields D) :
    S.toSubpolygonPackage.counts = S.counts :=
  rfl

/-- Projection to the count low-degree interface used by `FaceCountingBridge`. -/
def toCanonicalSubpolygonCountHypotheses
    (S : ConcreteBoundaryCycleFields D) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G where
  faceBoundary := D.core.faceBoundary
  counts := S.counts
  angleLowerBound := by
    simpa [counts] using S.angleWitness.angleLowerBound

@[simp]
theorem toCanonicalSubpolygonCountHypotheses_faceBoundary
    (S : ConcreteBoundaryCycleFields D) :
    S.toCanonicalSubpolygonCountHypotheses.faceBoundary =
      D.core.faceBoundary :=
  rfl

@[simp]
theorem toCanonicalSubpolygonCountHypotheses_counts
    (S : ConcreteBoundaryCycleFields D) :
    S.toCanonicalSubpolygonCountHypotheses.counts = S.counts :=
  rfl

/-- The checked E13 angle lower bound for the computed counts. -/
theorem angleLowerBound
    (S : ConcreteBoundaryCycleFields D) :
    S.counts.AngleLowerBound := by
  simpa [counts] using S.angleWitness.angleLowerBound

/-- E13 with high-degree slack from the explicit W11 fields. -/
theorem lowDegreeWithHighDegreeSlack
    (S : ConcreteBoundaryCycleFields D) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using S.angleWitness.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion from the explicit W11 fields. -/
theorem lowDegree
    (S : ConcreteBoundaryCycleFields D) :
    6 <= 2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using S.angleWitness.lowDegreeInequality

/-- The high-degree-slack inequality routed through the angle interface. -/
theorem lowDegreeWithHighDegreeSlack_viaAngleInterface
    (S : ConcreteBoundaryCycleFields D) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 := by
  simpa using
    S.toSubpolygonAngleLowerBoundPackage.lowDegreeWithHighDegreeSlack

/-- The low-degree conclusion routed through the angle interface. -/
theorem lowDegree_viaAngleInterface
    (S : ConcreteBoundaryCycleFields D) :
    6 <= 2 * S.counts.D2 + S.counts.D3 := by
  simpa using S.toSubpolygonAngleLowerBoundPackage.lowDegreeInequality

/-- The high-degree-slack inequality routed through the count interface. -/
theorem lowDegreeWithHighDegreeSlack_viaCountInterface
    (S : ConcreteBoundaryCycleFields D) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 := by
  simpa using
    S.toCanonicalSubpolygonCountHypotheses.subpolygonLowDegreeWithHighDegreeSlack

/-- The low-degree conclusion routed through the count interface. -/
theorem lowDegree_viaCountInterface
    (S : ConcreteBoundaryCycleFields D) :
    6 <= 2 * S.counts.D2 + S.counts.D3 := by
  simpa using
    S.toCanonicalSubpolygonCountHypotheses.subpolygonLowDegreeInequality

end ConcreteBoundaryCycleFields

/-! ## Families and checked projections -/

/--
A W11 family of explicit concrete boundary-cycle subpolygon fields.

The only supplied data after `D` is fixed is the family index type and the
remaining boundary-cycle fields for each index.
-/
structure SubpolygonFamilyPackage
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  Subpolygon : Type u
  fields : Subpolygon -> ConcreteBoundaryCycleFields D

namespace SubpolygonFamilyPackage

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- The computed counts for one member of the W11 family. -/
def subpolygonCounts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    SubpolygonDegreeCounts :=
  (F.fields S).counts

/-- Forget the W11 family to the W10 angle/count family. -/
def toAngleCountFamilyFields
    (F : SubpolygonFamilyPackage D) :
    FaceSubpolygonAngleCountFamilyFields D where
  Subpolygon := F.Subpolygon
  subpolygonFields :=
    fun S => (F.fields S).toFaceSubpolygonAngleCountFields

@[simp]
theorem toAngleCountFamilyFields_Subpolygon
    (F : SubpolygonFamilyPackage D) :
    F.toAngleCountFamilyFields.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toAngleCountFamilyFields_subpolygonFields_counts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.toAngleCountFamilyFields.subpolygonFields S).counts =
      F.subpolygonCounts S :=
  rfl

/-- Forget further to the flattened W9 subpolygon-angle family. -/
def toFaceSubpolygonFamilyFields
    (F : SubpolygonFamilyPackage D) :
    FaceSubpolygonFamilyFields D :=
  F.toAngleCountFamilyFields.toFaceSubpolygonFamilyFields

@[simp]
theorem toFaceSubpolygonFamilyFields_Subpolygon
    (F : SubpolygonFamilyPackage D) :
    F.toFaceSubpolygonFamilyFields.Subpolygon = F.Subpolygon :=
  rfl

/-- The concrete core face-subpolygon family induced by the W11 fields. -/
def toCoreFaceSubpolygonFamilyData
    (F : SubpolygonFamilyPackage D) :
    CoreFaceSubpolygonFamilyData.{u} D.core :=
  F.toAngleCountFamilyFields.toCoreFaceSubpolygonFamilyData

@[simp]
theorem toCoreFaceSubpolygonFamilyData_Subpolygon
    (F : SubpolygonFamilyPackage D) :
    F.toCoreFaceSubpolygonFamilyData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toCoreFaceSubpolygonFamilyData_subpolygonData_counts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.toCoreFaceSubpolygonFamilyData.subpolygonData S).counts =
      F.subpolygonCounts S :=
  rfl

/-- The planar-boundary subpolygon inputs induced by the W11 family. -/
def subpolygonInputs
    (F : SubpolygonFamilyPackage D) :
    PlanarBoundarySubpolygonInputs.{u} G :=
  F.toAngleCountFamilyFields.subpolygonInputs

@[simp]
theorem subpolygonInputs_Subpolygon
    (F : SubpolygonFamilyPackage D) :
    F.subpolygonInputs.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem subpolygonInputs_subpolygonDegreeCounts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    F.subpolygonInputs.subpolygonDegreeCounts S =
      F.subpolygonCounts S :=
  rfl

/-- The full planar-boundary package induced by the W11 family. -/
def toPlanarBoundaryData
    (F : SubpolygonFamilyPackage D) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  F.toAngleCountFamilyFields.toPlanarBoundaryData

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (F : SubpolygonFamilyPackage D) :
    F.toPlanarBoundaryData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData_counts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.toPlanarBoundaryData.subpolygonData S).counts =
      F.subpolygonCounts S :=
  rfl

/-- Concrete face-counting data extracted from the W11 planar-boundary package. -/
def concreteFaceCountingData
    (F : SubpolygonFamilyPackage D) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      F.toPlanarBoundaryData :=
  F.toAngleCountFamilyFields.concreteFaceCountingData

@[simp]
theorem concreteFaceCountingData_Subpolygon
    (F : SubpolygonFamilyPackage D) :
    F.concreteFaceCountingData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    F.concreteFaceCountingData.subpolygonCounts S =
      F.subpolygonCounts S :=
  rfl

/-- The assembled face-counting bridge package. -/
def toFaceCountingBridgeData
    (F : SubpolygonFamilyPackage D) :
    PlanarBoundaryClosure.FaceCountingBridgeData.{u} G :=
  F.toPlanarBoundaryData.toFaceCountingBridgeData

@[simp]
theorem toFaceCountingBridgeData_Subpolygon
    (F : SubpolygonFamilyPackage D) :
    F.toFaceCountingBridgeData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonDegreeCounts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    F.toFaceCountingBridgeData.subpolygonDegreeCounts S =
      F.subpolygonCounts S :=
  rfl

/-- The count-interface package for one member of the W11 family. -/
def canonicalSubpolygonCountHypotheses
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  (F.fields S).toCanonicalSubpolygonCountHypotheses

@[simp]
theorem canonicalSubpolygonCountHypotheses_counts
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.canonicalSubpolygonCountHypotheses S).counts =
      F.subpolygonCounts S :=
  rfl

/-- The checked angle lower bound for every W11 subpolygon. -/
theorem subpolygonAngleLowerBound
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.subpolygonCounts S).AngleLowerBound :=
  (F.fields S).angleLowerBound

/-- E13 with high-degree slack for every W11 subpolygon. -/
theorem lowDegreeWithHighDegreeSlack
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 :=
  (F.fields S).lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for every W11 subpolygon. -/
theorem lowDegree
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 :=
  (F.fields S).lowDegree

/-- The high-degree-slack inequality routed through the W10 family package. -/
theorem lowDegreeWithHighDegreeSlack_viaW10
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using
    F.toAngleCountFamilyFields.lowDegreeWithHighDegreeSlack S

/-- The low-degree conclusion routed through the W10 family package. -/
theorem lowDegree_viaW10
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa [subpolygonCounts] using F.toAngleCountFamilyFields.lowDegree S

/-- The high-degree-slack inequality routed through concrete face-count data. -/
theorem lowDegreeWithHighDegreeSlack_viaConcreteFaceCountingData
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa using
    F.concreteFaceCountingData.subpolygonLowDegreeWithHighDegreeSlack S

/-- The low-degree conclusion routed through concrete face-count data. -/
theorem lowDegree_viaConcreteFaceCountingData
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa using F.concreteFaceCountingData.subpolygonLowDegree S

/-- The high-degree-slack inequality routed through the face-counting bridge. -/
theorem lowDegreeWithHighDegreeSlack_viaBridge
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    (F.subpolygonCounts S).D5 + 2 * (F.subpolygonCounts S).D6 + 6 <=
      2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa using F.toFaceCountingBridgeData.subpolygonLowDegreeWithHighDegreeSlack S

/-- The low-degree conclusion routed through the face-counting bridge. -/
theorem lowDegree_viaBridge
    (F : SubpolygonFamilyPackage D) (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonCounts S).D2 + (F.subpolygonCounts S).D3 := by
  simpa using F.toFaceCountingBridgeData.subpolygonLowDegree S

/-- The full checked counting-theorem summary for the W11 planar-boundary data. -/
theorem faceCountingTheorems
    (F : SubpolygonFamilyPackage D) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      F.toPlanarBoundaryData :=
  F.toPlanarBoundaryData.faceCountingTheorems

/-- The same theorem summary re-indexed to the assembled face-counting bridge. -/
theorem bridgeCountingTheorems
    (F : SubpolygonFamilyPackage D) :
    PlanarBoundaryClosure.FaceCountingBridgeData.CountingTheorems
      F.toFaceCountingBridgeData :=
  F.toFaceCountingBridgeData.countingTheorems

end SubpolygonFamilyPackage

end

end SubpolygonFamilyW11
end Swanepoel
end ErdosProblems1066
