import ErdosProblems1066.Swanepoel.SubpolygonCore
import ErdosProblems1066.Swanepoel.SubpolygonAngleRealization

/-!
# Subpolygon assembly

This module assembles the concrete subpolygon boundary and induced-count data
with explicit real angle comparisons.  It does not construct subpolygons,
faces, or angle sums; those remain supplied hypotheses.  Its role is only to
transport the explicit cycle/count/angle data through the checked E13
subpolygon counting interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonAssembly

open BoundaryCounting
open FaceReduction
open PlanarInterface
open SubpolygonCore
open SubpolygonAngleRealization

universe u

noncomputable section

variable {n : Nat}

/-! ## Face-boundary and induced-set constructors -/

/-- The subpolygon boundary cycle obtained from a supplied face-boundary
witness and one of its recorded faces.  This is a genuine projection from
the existing face-boundary data: no face or cycle existence is manufactured
here. -/
def boundaryCycleOfFaceBoundary
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (face : faceBoundary.Face) :
    BoundaryCycle G where
  length := faceBoundary.boundaryLength face
  length_pos := faceBoundary.boundaryLength_pos face
  vertex := faceBoundary.boundaryVertex face
  adjacent := faceBoundary.boundaryAdjacent face
  simple := faceBoundary.boundarySimple face

@[simp]
theorem boundaryCycleOfFaceBoundary_length
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (face : faceBoundary.Face) :
    (boundaryCycleOfFaceBoundary faceBoundary face).length =
      faceBoundary.boundaryLength face :=
  rfl

@[simp]
theorem boundaryCycleOfFaceBoundary_vertex
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (face : faceBoundary.Face)
    (k : Fin ((boundaryCycleOfFaceBoundary faceBoundary face).length)) :
    (boundaryCycleOfFaceBoundary faceBoundary face).vertex k =
      faceBoundary.boundaryVertex face k :=
  rfl

/-- Build an induced subpolygon vertex set from an explicit finite set
containing the boundary cycle. -/
def inducedVertexSetOfFinset
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (vertices : Finset (Fin n))
    (boundary_subset : C.vertexFinset ⊆ vertices) :
    InducedVertexSet G C where
  vertices := vertices
  boundary_subset := boundary_subset

/-- The boundary-only induced set for a recorded boundary cycle.  This is often
useful as a canonical low-degree input when a caller really wants exactly the
cycle vertices and no interior vertices. -/
def boundaryOnlyInducedVertexSet
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) :
    InducedVertexSet G C where
  vertices := C.vertexFinset
  boundary_subset := by
    intro v hv
    exact hv

/-- The boundary-only induced set attached to one recorded face boundary. -/
def boundaryOnlyInducedVertexSetOfFaceBoundary
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (face : faceBoundary.Face) :
    InducedVertexSet G (boundaryCycleOfFaceBoundary faceBoundary face) :=
  boundaryOnlyInducedVertexSet (boundaryCycleOfFaceBoundary faceBoundary face)

/-! ## Realized subpolygon counts -/

/-- Explicit subpolygon counts together with the proof that they are the
counts computed from the supplied induced boundary degrees. -/
structure SubpolygonCountRealization
    (G : CanonicalStraightLineUnitDistanceGraph n)
    (C : BoundaryCycle G) (S : InducedVertexSet G C) where
  counts : SubpolygonDegreeCounts
  realizes : S.degreeCounts = counts

namespace SubpolygonCountRealization

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {S : InducedVertexSet G C}

/-- The canonical realization by the counts computed from the induced vertex
set. -/
def canonical (S : InducedVertexSet G C) :
    SubpolygonCountRealization G C S where
  counts := S.degreeCounts
  realizes := rfl

/-- Projection to the existing E13 count record. -/
def toSubpolygonDegreeCounts
    (R : SubpolygonCountRealization G C S) :
    SubpolygonDegreeCounts :=
  R.counts

/-- The realized counts agree with the computed induced-boundary counts. -/
theorem counts_eq_computed
    (R : SubpolygonCountRealization G C S) :
    R.counts = S.degreeCounts :=
  R.realizes.symm

/-- Transport an angle lower bound on the realized counts to the computed
induced-boundary counts. -/
theorem computedAngleLowerBound
    (R : SubpolygonCountRealization G C S)
    (hangle : R.counts.AngleLowerBound) :
    S.degreeCounts.AngleLowerBound := by
  simpa [R.realizes] using hangle

end SubpolygonCountRealization

/-! ## Cycle, count, and angle packages -/

/-- Explicit data for one subpolygon boundary, its induced vertex set, realized
degree counts, and the geometric angle comparisons for those realized counts. -/
structure SubpolygonCycleCountAngleData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  vertexSet : InducedVertexSet G boundary
  countRealization :
    SubpolygonCountRealization G boundary vertexSet
  geometricAngleSum : Real
  forced_le_geometric :
    countRealization.counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= countRealization.counts.polygonAngleSum

namespace SubpolygonCycleCountAngleData

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The explicit E13 count record carried by the assembly data. -/
def counts (A : SubpolygonCycleCountAngleData G) :
    SubpolygonDegreeCounts :=
  A.countRealization.counts

/-- The computed induced-boundary counts agree with the explicit counts. -/
theorem computed_counts_eq
    (A : SubpolygonCycleCountAngleData G) :
    A.vertexSet.degreeCounts = A.counts :=
  A.countRealization.realizes

/-- The explicit angle comparisons imply the angle lower bound for the
explicit realized counts. -/
theorem angleLowerBound
    (A : SubpolygonCycleCountAngleData G) :
    A.counts.AngleLowerBound :=
  le_trans A.forced_le_geometric A.geometric_le_polygon

/-- Convert the explicit count and angle data into the concrete angle package
whose counts are computed from the induced subpolygon. -/
def toConcreteAngleBounds
    (A : SubpolygonCycleCountAngleData G) :
    ConcreteAngleBounds G A.boundary A.vertexSet where
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, A.countRealization.realizes] using A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, A.countRealization.realizes] using A.geometric_le_polygon

/-- Convert to the core degree-count package after the angle lower bound has
been transported to the computed induced counts. -/
def toDegreeCountData
    (A : SubpolygonCycleCountAngleData G) :
    DegreeCountData G A.boundary A.vertexSet :=
  A.toConcreteAngleBounds.toDegreeCountData

/-- Convert to the concrete subpolygon package used by
`SubpolygonAngleRealization`. -/
def toConcreteSubpolygon
    (A : SubpolygonCycleCountAngleData G) :
    ConcreteSubpolygon G where
  boundary := A.boundary
  vertexSet := A.vertexSet
  angleBounds := A.toConcreteAngleBounds

/-- Convert to the full core package. -/
def toSubpolygonPackage
    (A : SubpolygonCycleCountAngleData G) :
    SubpolygonPackage G :=
  A.toConcreteSubpolygon.toSubpolygonPackage

/-- Package the explicit counts for the canonical face-counting bridge.  The
face-boundary data is still an explicit input. -/
def toCanonicalSubpolygonCountHypotheses
    (A : SubpolygonCycleCountAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G where
  faceBoundary := faceBoundary
  counts := A.counts
  angleLowerBound := A.angleLowerBound

/-- E13 with high-degree slack for the explicit realized subpolygon counts. -/
theorem lowDegreeWithHighDegreeSlack
    (A : SubpolygonCycleCountAngleData G) :
    A.counts.D5 + 2 * A.counts.D6 + 6 <=
      2 * A.counts.D2 + A.counts.D3 := by
  have h := A.toConcreteAngleBounds.lowDegreeWithHighDegreeSlack_viaSubpolygonCore
  simpa [counts, A.countRealization.realizes] using h

/-- Swanepoel's E13 low-degree conclusion for the explicit realized
subpolygon counts. -/
theorem lowDegreeInequality
    (A : SubpolygonCycleCountAngleData G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 := by
  have h := A.toConcreteAngleBounds.lowDegreeInequality_viaSubpolygonCore
  simpa [counts, A.countRealization.realizes] using h

/-- The same low-degree conclusion routed through the canonical face-counting
bridge while keeping the face-boundary data explicit. -/
theorem lowDegreeInequality_viaFaceCountingBridge
    (A : SubpolygonCycleCountAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 :=
  (A.toCanonicalSubpolygonCountHypotheses faceBoundary).subpolygonLowDegreeInequality

end SubpolygonCycleCountAngleData

/-! ## Honest geometric subpolygon packages -/

/-- Honest geometric data for one supplied subpolygon.

The boundary cycle and induced vertex set are concrete.  The `insideOrOn` and
`onBoundary` predicates are explicit geometric data supplied by the caller;
this record only ties them to the cycle and to the finite induced vertex set.
The degree counts below are always computed from `vertexSet`. -/
structure HonestGeometricSubpolygon
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  boundary : BoundaryCycle G
  vertexSet : InducedVertexSet G boundary
  insideOrOn : Point -> Prop
  onBoundary : Fin n -> Prop
  boundary_vertex_onBoundary :
    forall k : Fin boundary.length, onBoundary (boundary.vertex k)
  vertices_insideOrOn :
    forall v : Fin n, v ∈ vertexSet.vertices -> insideOrOn (G.point v)
  onBoundary_iff_cycle :
    forall v : Fin n,
      onBoundary v <->
        Exists fun k : Fin boundary.length => boundary.vertex k = v

namespace HonestGeometricSubpolygon

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- Construct a geometric subpolygon whose boundary is one of the supplied
face-boundary cycles.  The finite induced vertex set and enclosure predicates
remain explicit inputs. -/
def ofFaceBoundary
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (face : faceBoundary.Face)
    (vertices : Finset (Fin n))
    (boundary_subset :
      (boundaryCycleOfFaceBoundary faceBoundary face).vertexFinset ⊆ vertices)
    (insideOrOn : Point -> Prop) (onBoundary : Fin n -> Prop)
    (boundary_vertex_onBoundary :
      forall k : Fin (faceBoundary.boundaryLength face),
        onBoundary (faceBoundary.boundaryVertex face k))
    (vertices_insideOrOn :
      forall v : Fin n, v ∈ vertices -> insideOrOn (G.point v))
    (onBoundary_iff_cycle :
      forall v : Fin n,
        onBoundary v <->
          Exists fun k : Fin (faceBoundary.boundaryLength face) =>
            faceBoundary.boundaryVertex face k = v) :
    HonestGeometricSubpolygon G where
  boundary := boundaryCycleOfFaceBoundary faceBoundary face
  vertexSet :=
    inducedVertexSetOfFinset
      (boundaryCycleOfFaceBoundary faceBoundary face)
      vertices boundary_subset
  insideOrOn := insideOrOn
  onBoundary := onBoundary
  boundary_vertex_onBoundary := boundary_vertex_onBoundary
  vertices_insideOrOn := vertices_insideOrOn
  onBoundary_iff_cycle := onBoundary_iff_cycle

/-- The computed E13 counts for the induced subpolygon. -/
def counts (P : HonestGeometricSubpolygon G) :
    SubpolygonDegreeCounts :=
  P.vertexSet.degreeCounts

/-- Forget the geometric predicates and expose the existing computed-count
record. -/
def toSubpolygonDegreeCounts (P : HonestGeometricSubpolygon G) :
    SubpolygonDegreeCounts :=
  P.counts

@[simp]
theorem toSubpolygonDegreeCounts_eq_counts
    (P : HonestGeometricSubpolygon G) :
    P.toSubpolygonDegreeCounts = P.counts :=
  rfl

/-- The count realization is canonical: the stored counts are precisely the
counts computed from the induced vertex set. -/
def toCountRealization
    (P : HonestGeometricSubpolygon G) :
    SubpolygonCountRealization G P.boundary P.vertexSet :=
  SubpolygonCountRealization.canonical P.vertexSet

@[simp]
theorem toCountRealization_counts
    (P : HonestGeometricSubpolygon G) :
    P.toCountRealization.counts = P.counts :=
  rfl

@[simp]
theorem counts_eq_computed
    (P : HonestGeometricSubpolygon G) :
    P.counts = P.vertexSet.degreeCounts :=
  rfl

/-- Turn a supplied angle lower bound for the computed counts into the core
degree-count package. -/
def toDegreeCountData
    (P : HonestGeometricSubpolygon G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    DegreeCountData G P.boundary P.vertexSet where
  angleLowerBound := by
    simpa [counts] using angleLowerBound

/-- Turn a supplied angle lower bound for the computed counts into the full
core subpolygon package. -/
def toSubpolygonPackage
    (P : HonestGeometricSubpolygon G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    SubpolygonPackage G where
  boundary := P.boundary
  vertexSet := P.vertexSet
  degreeData := P.toDegreeCountData angleLowerBound

/-- Package the computed counts for the canonical face-counting bridge. -/
def toCanonicalSubpolygonCountHypotheses
    (P : HonestGeometricSubpolygon G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  (P.toDegreeCountData angleLowerBound).toCanonicalSubpolygonCountHypotheses
    faceBoundary

/-- E13 with high-degree slack for a geometric subpolygon once its computed
counts have the angle lower bound. -/
theorem lowDegreeWithHighDegreeSlack
    (P : HonestGeometricSubpolygon G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    P.counts.D5 + 2 * P.counts.D6 + 6 <=
      2 * P.counts.D2 + P.counts.D3 := by
  simpa [counts] using
    (P.toDegreeCountData angleLowerBound).lowDegreeWithHighDegreeSlack

/-- Swanepoel's low-degree conclusion for a geometric subpolygon once its
computed counts have the angle lower bound. -/
theorem lowDegreeInequality
    (P : HonestGeometricSubpolygon G)
    (angleLowerBound : P.counts.AngleLowerBound) :
    6 <= 2 * P.counts.D2 + P.counts.D3 := by
  simpa [counts] using
    (P.toDegreeCountData angleLowerBound).lowDegreeInequality

end HonestGeometricSubpolygon

/-- Honest geometric subpolygon data plus the real angle comparisons needed
for E13.  Unlike older count-only inputs, this package exposes the boundary
cycle and induced vertex set whose degrees define the counts. -/
structure HonestGeometricSubpolygonAngleData
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  subpolygon : HonestGeometricSubpolygon G
  geometricAngleSum : Real
  forced_le_geometric :
    subpolygon.counts.forcedSubpolygonAngleSum <= geometricAngleSum
  geometric_le_polygon :
    geometricAngleSum <= subpolygon.counts.polygonAngleSum

namespace HonestGeometricSubpolygonAngleData

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The computed E13 counts carried by the geometric package. -/
def counts (A : HonestGeometricSubpolygonAngleData G) :
    SubpolygonDegreeCounts :=
  A.subpolygon.counts

/-- Adapter to the raw `SubpolygonDegreeCounts` input. -/
def toSubpolygonDegreeCounts
    (A : HonestGeometricSubpolygonAngleData G) :
    SubpolygonDegreeCounts :=
  A.counts

@[simp]
theorem counts_eq_computed
    (A : HonestGeometricSubpolygonAngleData G) :
    A.counts = A.subpolygon.vertexSet.degreeCounts :=
  rfl

/-- The real angle comparisons as a concrete angle-bound package over the
computed induced counts. -/
def toConcreteAngleBounds
    (A : HonestGeometricSubpolygonAngleData G) :
    ConcreteAngleBounds G A.subpolygon.boundary A.subpolygon.vertexSet where
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, HonestGeometricSubpolygon.counts] using
      A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, HonestGeometricSubpolygon.counts] using
      A.geometric_le_polygon

/-- The counting-layer angle lower bound for the computed induced counts. -/
theorem angleLowerBound
    (A : HonestGeometricSubpolygonAngleData G) :
    A.counts.AngleLowerBound := by
  simpa [counts, HonestGeometricSubpolygon.counts] using
    A.toConcreteAngleBounds.angleLowerBound

/-- Adapter to `SubpolygonCycleCountAngleData`, preserving the honest boundary
cycle and induced vertex set. -/
def toSubpolygonCycleCountAngleData
    (A : HonestGeometricSubpolygonAngleData G) :
    SubpolygonCycleCountAngleData G where
  boundary := A.subpolygon.boundary
  vertexSet := A.subpolygon.vertexSet
  countRealization := A.subpolygon.toCountRealization
  geometricAngleSum := A.geometricAngleSum
  forced_le_geometric := by
    simpa [counts, HonestGeometricSubpolygon.counts] using
      A.forced_le_geometric
  geometric_le_polygon := by
    simpa [counts, HonestGeometricSubpolygon.counts] using
      A.geometric_le_polygon

@[simp]
theorem toSubpolygonCycleCountAngleData_counts
    (A : HonestGeometricSubpolygonAngleData G) :
    A.toSubpolygonCycleCountAngleData.counts = A.counts :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_boundary
    (A : HonestGeometricSubpolygonAngleData G) :
    A.toSubpolygonCycleCountAngleData.boundary = A.subpolygon.boundary :=
  rfl

@[simp]
theorem toSubpolygonCycleCountAngleData_vertexSet
    (A : HonestGeometricSubpolygonAngleData G) :
    A.toSubpolygonCycleCountAngleData.vertexSet = A.subpolygon.vertexSet :=
  rfl

/-- Adapter to the canonical face-counting bridge package. -/
def toCanonicalSubpolygonCountHypotheses
    (A : HonestGeometricSubpolygonAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  A.toSubpolygonCycleCountAngleData.toCanonicalSubpolygonCountHypotheses
    faceBoundary

@[simp]
theorem toCanonicalSubpolygonCountHypotheses_counts
    (A : HonestGeometricSubpolygonAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    (A.toCanonicalSubpolygonCountHypotheses faceBoundary).counts =
      A.counts :=
  rfl

@[simp]
theorem toCanonicalSubpolygonCountHypotheses_faceBoundary
    (A : HonestGeometricSubpolygonAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    (A.toCanonicalSubpolygonCountHypotheses faceBoundary).faceBoundary =
      faceBoundary :=
  rfl

/-- E13 with high-degree slack for the computed induced counts. -/
theorem lowDegreeWithHighDegreeSlack
    (A : HonestGeometricSubpolygonAngleData G) :
    A.counts.D5 + 2 * A.counts.D6 + 6 <=
      2 * A.counts.D2 + A.counts.D3 := by
  simpa [counts] using
    A.toSubpolygonCycleCountAngleData.lowDegreeWithHighDegreeSlack

/-- Swanepoel's E13 low-degree conclusion for the computed induced counts. -/
theorem lowDegreeInequality
    (A : HonestGeometricSubpolygonAngleData G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 := by
  simpa [counts] using
    A.toSubpolygonCycleCountAngleData.lowDegreeInequality

/-- The same low-degree conclusion routed through the canonical face-counting
bridge and the supplied face-boundary witness. -/
theorem lowDegreeInequality_viaFaceCountingBridge
    (A : HonestGeometricSubpolygonAngleData G)
    (faceBoundary : UnitDistanceFaceBoundaryHypotheses G) :
    6 <= 2 * A.counts.D2 + A.counts.D3 := by
  simpa [counts] using
    (A.toCanonicalSubpolygonCountHypotheses faceBoundary).subpolygonLowDegreeInequality

end HonestGeometricSubpolygonAngleData

/-! ## Planar-boundary-facing subpolygon families -/

/-- A family of honest subpolygon angle packages tied to one supplied
face-boundary witness.

The two projection fields `Subpolygon` and `subpolygonData` are exactly the
subpolygon inputs expected by `PlanarBoundaryClosure.PlanarBoundaryData`.
This record does not assert that such subpolygons exist; it packages whatever
index type and honest subpolygon data the caller has already constructed. -/
structure PlanarBoundarySubpolygonInputs
    (G : CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : UnitDistanceFaceBoundaryHypotheses G
  Subpolygon : Type u
  subpolygonAngleData :
    Subpolygon -> HonestGeometricSubpolygonAngleData G

namespace PlanarBoundarySubpolygonInputs

variable {G : CanonicalStraightLineUnitDistanceGraph n}

/-- The `PlanarBoundaryClosure`-facing subpolygon data projection. -/
def subpolygonData
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    SubpolygonCycleCountAngleData G :=
  (I.subpolygonAngleData S).toSubpolygonCycleCountAngleData

/-- The computed E13 counts for a supplied subpolygon in the family. -/
def subpolygonDegreeCounts
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    SubpolygonDegreeCounts :=
  (I.subpolygonAngleData S).counts

@[simp]
theorem subpolygonData_counts
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    (I.subpolygonData S).counts = I.subpolygonDegreeCounts S :=
  rfl

@[simp]
theorem subpolygonDegreeCounts_eq_computed
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    I.subpolygonDegreeCounts S =
      (I.subpolygonAngleData S).subpolygon.vertexSet.degreeCounts :=
  rfl

/-- Package one supplied subpolygon for the canonical face-counting bridge,
using the same face-boundary witness as the surrounding planar-boundary data. -/
def canonicalSubpolygonCountHypotheses
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses G :=
  (I.subpolygonData S).toCanonicalSubpolygonCountHypotheses I.faceBoundary

@[simp]
theorem canonicalSubpolygonCountHypotheses_faceBoundary
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    (I.canonicalSubpolygonCountHypotheses S).faceBoundary =
      I.faceBoundary :=
  rfl

@[simp]
theorem canonicalSubpolygonCountHypotheses_counts
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    (I.canonicalSubpolygonCountHypotheses S).counts =
      I.subpolygonDegreeCounts S :=
  rfl

/-- E13 with high-degree slack for any honest subpolygon in the family. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    (I.subpolygonDegreeCounts S).D5 +
        2 * (I.subpolygonDegreeCounts S).D6 + 6 <=
      2 * (I.subpolygonDegreeCounts S).D2 +
        (I.subpolygonDegreeCounts S).D3 := by
  simpa [subpolygonDegreeCounts] using
    (I.subpolygonAngleData S).lowDegreeWithHighDegreeSlack

/-- Swanepoel's low-degree conclusion for any honest subpolygon in the family. -/
theorem subpolygonLowDegree
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    6 <= 2 * (I.subpolygonDegreeCounts S).D2 +
      (I.subpolygonDegreeCounts S).D3 := by
  simpa [subpolygonDegreeCounts] using
    (I.subpolygonAngleData S).lowDegreeInequality

/-- The same low-degree conclusion routed through the face-counting bridge
package that `PlanarBoundaryClosure` will consume. -/
theorem subpolygonLowDegree_viaFaceCountingBridge
    (I : PlanarBoundarySubpolygonInputs.{u} G)
    (S : I.Subpolygon) :
    6 <= 2 * (I.subpolygonDegreeCounts S).D2 +
      (I.subpolygonDegreeCounts S).D3 := by
  simpa [subpolygonDegreeCounts] using
    (I.canonicalSubpolygonCountHypotheses S).subpolygonLowDegreeInequality

end PlanarBoundarySubpolygonInputs

/-! ## Direct theorem form -/

/-- Direct E13 high-degree-slack theorem from explicit cycle, count, and angle
data. -/
theorem e13LowDegreeWithHighDegreeSlack_of_explicitCycleCountAngleData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (counts : SubpolygonDegreeCounts)
    (hcounts : S.degreeCounts = counts)
    (geometricAngleSum : Real)
    (hforced :
      counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= counts.polygonAngleSum) :
    counts.D5 + 2 * counts.D6 + 6 <=
      2 * counts.D2 + counts.D3 := by
  have hforced' :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum := by
    simpa [hcounts] using hforced
  have hpolygon' :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum := by
    simpa [hcounts] using hpolygon
  have h :=
    lowDegreeWithHighDegreeSlack_of_concreteAngleBounds
      C S geometricAngleSum hforced' hpolygon'
  simpa [hcounts] using h

/-- Direct E13 subpolygon low-degree theorem from explicit cycle, count, and
angle data. -/
theorem e13LowDegreeInequality_of_explicitCycleCountAngleData
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G) (S : InducedVertexSet G C)
    (counts : SubpolygonDegreeCounts)
    (hcounts : S.degreeCounts = counts)
    (geometricAngleSum : Real)
    (hforced :
      counts.forcedSubpolygonAngleSum <= geometricAngleSum)
    (hpolygon :
      geometricAngleSum <= counts.polygonAngleSum) :
    6 <= 2 * counts.D2 + counts.D3 := by
  have hforced' :
      S.degreeCounts.forcedSubpolygonAngleSum <= geometricAngleSum := by
    simpa [hcounts] using hforced
  have hpolygon' :
      geometricAngleSum <= S.degreeCounts.polygonAngleSum := by
    simpa [hcounts] using hpolygon
  have h :=
    lowDegreeInequality_of_concreteAngleBounds
      C S geometricAngleSum hforced' hpolygon'
  simpa [hcounts] using h

end

end SubpolygonAssembly
end Swanepoel
end ErdosProblems1066
