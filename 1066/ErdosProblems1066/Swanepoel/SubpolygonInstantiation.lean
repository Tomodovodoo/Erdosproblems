import ErdosProblems1066.Swanepoel.SubpolygonFaceConstruction

set_option autoImplicit false

/-!
# Instantiating subpolygon data from explicit outer-face data

This file is a small facade over `SubpolygonFaceConstruction` and
`SubpolygonDataConcrete`.  It starts from explicit selected outer-face data
and enclosure data, exposes the exact remaining per-subpolygon fields, and
projects the resulting family to `PlanarBoundaryData` and the E13 low-degree
inequalities.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonInstantiation

open BoundaryCounting
open FaceReduction
open SubpolygonAssembly
open SubpolygonDataConcrete
open SubpolygonFaceConstruction
open SubpolygonCore

universe u

noncomputable section

variable {n : Nat}
variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-! ## Explicit outer-boundary face input -/

/--
The outer-boundary face data needed before subpolygons are instantiated.

The topology layer supplies the selected face-boundary witness, the selected
outer face, and the enclosure predicates.  The angle layer supplies the checked
outer-boundary bookkeeping bounds consumed by `PlanarBoundaryData`.
-/
structure ExplicitOuterBoundaryFaceData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  outerFaceData : OuterBoundaryCoreConstruction.OuterFaceData.{u} G
  enclosureData :
    OuterBoundaryCoreConstruction.EnclosureData outerFaceData
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}

namespace ExplicitOuterBoundaryFaceData

/-- The checked outer-boundary core determined by the explicit face data. -/
def core (D : ExplicitOuterBoundaryFaceData.{u} G) :
    OuterBoundaryCore G :=
  coreOfEnclosureData D.enclosureData

@[simp]
theorem core_faceBoundary (D : ExplicitOuterBoundaryFaceData.{u} G) :
    D.core.faceBoundary = D.outerFaceData.faceBoundary :=
  rfl

@[simp]
theorem core_outerFace (D : ExplicitOuterBoundaryFaceData.{u} G) :
    D.core.outerFace = D.outerFaceData.outerFace :=
  rfl

@[simp]
theorem core_outerEnclosure (D : ExplicitOuterBoundaryFaceData.{u} G) :
    D.core.outerEnclosure = D.enclosureData.outerEnclosure :=
  rfl

/-- The exact subpolygon inputs carried by a supplied face-subpolygon family. -/
def subpolygonInputs
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    SubpolygonAssembly.PlanarBoundarySubpolygonInputs.{u} G :=
  inputsOfCoreFaceFamily D.core F

@[simp]
theorem subpolygonInputs_faceBoundary
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.subpolygonInputs F).faceBoundary = D.outerFaceData.faceBoundary :=
  rfl

@[simp]
theorem subpolygonInputs_Subpolygon
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.subpolygonInputs F).Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem subpolygonInputs_subpolygonDegreeCounts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core)
    (S : F.Subpolygon) :
    (D.subpolygonInputs F).subpolygonDegreeCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- Instantiate `PlanarBoundaryData` from explicit outer-face data and a
supplied face-subpolygon family. -/
def toPlanarBoundaryData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  planarBoundaryDataOfCoreFaceFamily D.core D.outerAngleBounds F

@[simp]
theorem toPlanarBoundaryData_core
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.toPlanarBoundaryData F).core = D.core :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.toPlanarBoundaryData F).faceBoundary =
      D.outerFaceData.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.toPlanarBoundaryData F).outerFace =
      D.outerFaceData.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.toPlanarBoundaryData F).outerBoundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.toPlanarBoundaryData F).Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core)
    (S : F.Subpolygon) :
    (D.toPlanarBoundaryData F).subpolygonData S =
      (F.subpolygonData S).toSubpolygonCycleCountAngleData :=
  rfl

/-- Concrete face-counting data extracted after instantiation. -/
def concreteFaceCountingData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      (D.toPlanarBoundaryData F) :=
  concreteFaceCountingDataOfCoreFaceFamily D.core D.outerAngleBounds F

@[simp]
theorem concreteFaceCountingData_faceBoundary
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core) :
    (D.concreteFaceCountingData F).faceBoundary =
      D.outerFaceData.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core)
    (S : F.Subpolygon) :
    (D.concreteFaceCountingData F).subpolygonCounts S =
      (F.subpolygonData S).counts :=
  rfl

/-- E13 with high-degree slack for the supplied face-subpolygon family. -/
theorem lowDegreeWithHighDegreeSlack
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core)
    (S : F.Subpolygon) :
    (F.subpolygonData S).counts.D5 +
        2 * (F.subpolygonData S).counts.D6 + 6 <=
      2 * (F.subpolygonData S).counts.D2 +
        (F.subpolygonData S).counts.D3 :=
  lowDegreeWithHighDegreeSlackOfCoreFaceFamily
    D.core D.outerAngleBounds F S

/-- Swanepoel Lemma 4's low-degree conclusion for the supplied family. -/
theorem lowDegree
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (F : CoreFaceSubpolygonFamilyData.{u} D.core)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonData S).counts.D2 +
      (F.subpolygonData S).counts.D3 :=
  lowDegreeOfCoreFaceFamily D.core D.outerAngleBounds F S

end ExplicitOuterBoundaryFaceData

/-! ## Exact remaining per-subpolygon fields -/

/--
The exact face and finite induced-vertex fields still needed for one
subpolygon once the outer face data has been fixed.
-/
structure FaceSubpolygonFields
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  face : D.core.faceBoundary.Face
  vertices : Finset (Fin n)
  boundary_subset :
    (boundaryCycleOfFaceBoundary D.core.faceBoundary face).vertexFinset ⊆
      vertices
  insideOrOn : PlanarInterface.Point -> Prop
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

namespace FaceSubpolygonFields

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- Package the explicit fields as `SubpolygonDataConcrete` geometry data. -/
def toGeometryData (S : FaceSubpolygonFields D) :
    CoreFaceSubpolygonGeometryData D.core where
  face := S.face
  vertices := S.vertices
  boundary_subset := S.boundary_subset
  insideOrOn := S.insideOrOn
  onBoundary := S.onBoundary
  boundary_vertex_onBoundary := S.boundary_vertex_onBoundary
  vertices_iff_insideOrOn := S.vertices_iff_insideOrOn
  onBoundary_iff_cycle := S.onBoundary_iff_cycle

@[simp]
theorem toGeometryData_face (S : FaceSubpolygonFields D) :
    S.toGeometryData.face = S.face :=
  rfl

@[simp]
theorem toGeometryData_vertices (S : FaceSubpolygonFields D) :
    S.toGeometryData.vertices = S.vertices :=
  rfl

/-- The induced E13 counts determined by the explicit finite vertex set. -/
def counts (S : FaceSubpolygonFields D) :
    SubpolygonDegreeCounts :=
  S.toGeometryData.counts

@[simp]
theorem counts_eq_geometry_counts (S : FaceSubpolygonFields D) :
    S.counts = S.toGeometryData.counts :=
  rfl

end FaceSubpolygonFields

/--
The exact real angle fields still needed for one face-boundary subpolygon.
-/
structure FaceSubpolygonAngleFields
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  geometry : FaceSubpolygonFields D
  geometricAngleSum : Real
  forced_le_geometric :
    geometry.counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= geometry.counts.polygonAngleSum

namespace FaceSubpolygonAngleFields

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- The induced E13 counts determined by the explicit subpolygon fields. -/
def counts (S : FaceSubpolygonAngleFields D) :
    SubpolygonDegreeCounts :=
  S.geometry.counts

/-- Package the explicit fields as `SubpolygonDataConcrete` angle data. -/
def toCoreFaceSubpolygonAngleData
    (S : FaceSubpolygonAngleFields D) :
    CoreFaceSubpolygonAngleData D.core where
  geometry := S.geometry.toGeometryData
  geometricAngleSum := S.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, FaceSubpolygonFields.counts] using
      S.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, FaceSubpolygonFields.counts] using
      S.geometric_le_polygon

@[simp]
theorem toCoreFaceSubpolygonAngleData_counts
    (S : FaceSubpolygonAngleFields D) :
    S.toCoreFaceSubpolygonAngleData.counts = S.counts :=
  rfl

/-- E13 with high-degree slack from the explicit subpolygon fields. -/
theorem lowDegreeWithHighDegreeSlack
    (S : FaceSubpolygonAngleFields D) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using
    S.toCoreFaceSubpolygonAngleData.lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion from the explicit fields. -/
theorem lowDegree
    (S : FaceSubpolygonAngleFields D) :
    6 <= 2 * S.counts.D2 + S.counts.D3 := by
  simpa [counts] using
    S.toCoreFaceSubpolygonAngleData.lowDegree

end FaceSubpolygonAngleFields

/--
A supplied family of explicit face-boundary subpolygon fields.

This is the flattened obligation surface: after `ExplicitOuterBoundaryFaceData`
is supplied, each family member only needs a face, an exact finite induced
vertex set with inside/on predicates, and the two real angle comparisons.
-/
structure FaceSubpolygonFamilyFields
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  Subpolygon : Type u
  subpolygonFields : Subpolygon -> FaceSubpolygonAngleFields D

namespace FaceSubpolygonFamilyFields

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- Instantiate the concrete face-subpolygon family expected downstream. -/
def toCoreFaceSubpolygonFamilyData
    (F : FaceSubpolygonFamilyFields D) :
    CoreFaceSubpolygonFamilyData.{u} D.core where
  Subpolygon := F.Subpolygon
  subpolygonData :=
    fun S => (F.subpolygonFields S).toCoreFaceSubpolygonAngleData

@[simp]
theorem toCoreFaceSubpolygonFamilyData_Subpolygon
    (F : FaceSubpolygonFamilyFields D) :
    F.toCoreFaceSubpolygonFamilyData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toCoreFaceSubpolygonFamilyData_subpolygonData
    (F : FaceSubpolygonFamilyFields D) (S : F.Subpolygon) :
    F.toCoreFaceSubpolygonFamilyData.subpolygonData S =
      (F.subpolygonFields S).toCoreFaceSubpolygonAngleData :=
  rfl

/-- The `PlanarBoundaryData` package instantiated from the flattened fields. -/
def toPlanarBoundaryData
    (F : FaceSubpolygonFamilyFields D) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  D.toPlanarBoundaryData F.toCoreFaceSubpolygonFamilyData

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (F : FaceSubpolygonFamilyFields D) :
    F.toPlanarBoundaryData.faceBoundary = D.outerFaceData.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (F : FaceSubpolygonFamilyFields D) :
    F.toPlanarBoundaryData.outerFace = D.outerFaceData.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (F : FaceSubpolygonFamilyFields D) :
    F.toPlanarBoundaryData.Subpolygon = F.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData_counts
    (F : FaceSubpolygonFamilyFields D)
    (S : F.Subpolygon) :
    (F.toPlanarBoundaryData.subpolygonData S).counts =
      (F.subpolygonFields S).counts :=
  rfl

/-- Concrete face-counting data extracted from the instantiated package. -/
def concreteFaceCountingData
    (F : FaceSubpolygonFamilyFields D) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      F.toPlanarBoundaryData :=
  D.concreteFaceCountingData F.toCoreFaceSubpolygonFamilyData

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (F : FaceSubpolygonFamilyFields D)
    (S : F.Subpolygon) :
    (F.concreteFaceCountingData).subpolygonCounts S =
      (F.subpolygonFields S).counts :=
  rfl

/-- E13 with high-degree slack for every supplied subpolygon. -/
theorem lowDegreeWithHighDegreeSlack
    (F : FaceSubpolygonFamilyFields D)
    (S : F.Subpolygon) :
    (F.subpolygonFields S).counts.D5 +
        2 * (F.subpolygonFields S).counts.D6 + 6 <=
      2 * (F.subpolygonFields S).counts.D2 +
        (F.subpolygonFields S).counts.D3 := by
  simpa using
    (F.subpolygonFields S).lowDegreeWithHighDegreeSlack

/-- Swanepoel Lemma 4's low-degree conclusion for every supplied subpolygon. -/
theorem lowDegree
    (F : FaceSubpolygonFamilyFields D)
    (S : F.Subpolygon) :
    6 <= 2 * (F.subpolygonFields S).counts.D2 +
      (F.subpolygonFields S).counts.D3 := by
  simpa using (F.subpolygonFields S).lowDegree

end FaceSubpolygonFamilyFields

end

end SubpolygonInstantiation
end Swanepoel
end ErdosProblems1066
