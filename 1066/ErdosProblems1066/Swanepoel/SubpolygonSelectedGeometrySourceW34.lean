import ErdosProblems1066.Swanepoel.BoundaryWalkClassificationConcrete
import ErdosProblems1066.Swanepoel.PlanarBoundaryFaceDataRefinement
import ErdosProblems1066.Swanepoel.PlanarInterface
import ErdosProblems1066.Swanepoel.SubpolygonPackageW12
import ErdosProblems1066.Swanepoel.SubpolygonConcreteRealizationW33
import ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12
import ErdosProblems1066.Swanepoel.K23RouteCoverageSourceW34

set_option autoImplicit false

/-!
# W34 selected subpolygon geometry source

The W33 bridge consumes selected face-subpolygon geometry together with an
explicit pointwise angle realization.  This module supplies the geometry part
from the existing selected outer-boundary/enclosure data: the selected outer
face, all ambient vertices as the induced finite set, and the already recorded
outer enclosure predicates.

The remaining source named at the end is exactly the pointwise real-angle
realization required to turn this checked geometry into W33 realization data.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SubpolygonSelectedGeometrySourceW34

open BoundaryCounting
open PlanarInterface
open SubpolygonConcreteRealizationW33
open SubpolygonDataConcrete
open SubpolygonInstantiation
open SubpolygonPackageW12
open K23RouteCoverageSourceW34
open SwanepoelW32RouteAudit.ActualRouteSource

universe u

noncomputable section

variable {n : Nat}
variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}

/-! ## Explicit selected outer-face geometry -/

/-- The selected outer face as a concrete face-subpolygon geometry.

The finite induced set is all vertices of the ambient finite configuration.
This is a genuine geometry source because `OuterBoundaryCore` already records
that every ambient vertex lies inside or on the selected outer enclosure and
that the boundary predicate is exactly the selected outer cycle.
-/
def selectedOuterFaceGeometry
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    FaceSubpolygonFields D where
  face := D.core.outerFace
  vertices := Finset.univ
  boundary_subset := by
    intro v _hv
    simp
  insideOrOn := D.core.outerEnclosure.insideOrOn
  onBoundary := D.core.outerEnclosure.onBoundary
  boundary_vertex_onBoundary := by
    intro k
    exact D.core.boundary_vertex_onBoundary k
  vertices_iff_insideOrOn := by
    intro v
    constructor
    · intro _hv
      exact D.core.all_vertices_insideOrOn v
    · intro _hv
      simp
  onBoundary_iff_cycle := by
    intro v
    exact D.core.onBoundary_iff_outer_cycle v

@[simp]
theorem selectedOuterFaceGeometry_face
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    (selectedOuterFaceGeometry D).face = D.core.outerFace :=
  rfl

@[simp]
theorem selectedOuterFaceGeometry_vertices
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    (selectedOuterFaceGeometry D).vertices = Finset.univ :=
  rfl

@[simp]
theorem selectedOuterFaceGeometry_insideOrOn
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    (selectedOuterFaceGeometry D).insideOrOn =
      D.core.outerEnclosure.insideOrOn :=
  rfl

@[simp]
theorem selectedOuterFaceGeometry_onBoundary
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    (selectedOuterFaceGeometry D).onBoundary =
      D.core.outerEnclosure.onBoundary :=
  rfl

/-- The selected outer-face geometry in the core face-subpolygon format. -/
def selectedOuterFaceCoreGeometry
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    CoreFaceSubpolygonGeometryData D.core :=
  (selectedOuterFaceGeometry D).toGeometryData

@[simp]
theorem selectedOuterFaceCoreGeometry_face
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    (selectedOuterFaceCoreGeometry D).face = D.core.outerFace :=
  rfl

@[simp]
theorem selectedOuterFaceCoreGeometry_vertices
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    (selectedOuterFaceCoreGeometry D).vertices = Finset.univ :=
  rfl

/-- A geometry-only one-member family for the selected outer face. -/
structure SelectedOuterFaceGeometryFamily
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  Subpolygon : Type u
  geometry : Subpolygon -> FaceSubpolygonFields D

namespace SelectedOuterFaceGeometryFamily

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- The induced degree counts for one geometry-family member. -/
def counts
    (F : SelectedOuterFaceGeometryFamily D)
    (S : F.Subpolygon) :
    SubpolygonDegreeCounts :=
  (F.geometry S).counts

end SelectedOuterFaceGeometryFamily

/-- The selected outer-face geometry as a one-member family. -/
def selectedOuterFaceGeometryFamily
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    SelectedOuterFaceGeometryFamily D where
  Subpolygon := PUnit.{u + 1}
  geometry := fun _ => selectedOuterFaceGeometry D

@[simp]
theorem selectedOuterFaceGeometryFamily_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (S : (selectedOuterFaceGeometryFamily D).Subpolygon) :
    (selectedOuterFaceGeometryFamily D).counts S =
      (selectedOuterFaceGeometry D).counts :=
  rfl

/-- Build the explicit selected-face data expected by subpolygon
instantiation from refined planar-boundary data.
-/
def explicitFaceDataOfPlanarBoundaryFaceData
    {C : _root_.UDConfig n}
    (D :
      PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{u} C) :
    ExplicitOuterBoundaryFaceData.{u}
      (PlanarBoundaryFaceDataRefinement.CanonicalGraph C) where
  outerFaceData := {
    faceBoundary := D.topology.faceBoundary
    outerFace := D.topology.outerFace
    outerFace_isOuter := D.topology.outerFace_isOuter
  }
  enclosureData := {
    outerEnclosure := D.topology.outerEnclosure
  }
  outerAngleBounds := D.outerAngleBounds

@[simp]
theorem explicitFaceDataOfPlanarBoundaryFaceData_core
    {C : _root_.UDConfig n}
    (D :
      PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{u} C) :
    (explicitFaceDataOfPlanarBoundaryFaceData D).core =
      D.topology.toCore :=
  rfl

@[simp]
theorem explicitFaceDataOfPlanarBoundaryFaceData_outerAngleBounds
    {C : _root_.UDConfig n}
    (D :
      PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{u} C) :
    (explicitFaceDataOfPlanarBoundaryFaceData D).outerAngleBounds =
      D.outerAngleBounds :=
  rfl

/-- Build the explicit selected-face data expected by subpolygon
instantiation directly from missing-topology fields and outer-angle
bookkeeping.
-/
def explicitFaceDataOfMissingTopologyFacts
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}) :
    ExplicitOuterBoundaryFaceData.{u}
      (PlanarBoundaryFaceDataRefinement.CanonicalGraph C) where
  outerFaceData := {
    faceBoundary := topology.faceBoundary
    outerFace := topology.outerFace
    outerFace_isOuter := topology.outerFace_isOuter
  }
  enclosureData := {
    outerEnclosure := topology.outerEnclosure
  }
  outerAngleBounds := outerAngleBounds

@[simp]
theorem explicitFaceDataOfMissingTopologyFacts_core
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}) :
    (explicitFaceDataOfMissingTopologyFacts topology outerAngleBounds).core =
      topology.toCore :=
  rfl

@[simp]
theorem explicitFaceDataOfMissingTopologyFacts_outerAngleBounds
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}) :
    (explicitFaceDataOfMissingTopologyFacts topology outerAngleBounds).outerAngleBounds =
      outerAngleBounds :=
  rfl

/-! ## Exact remaining pointwise angle source for W33 -/

/-- The exact remaining W33 source for the selected outer-face geometry:
pointwise real-angle data indexed by the boundary cycle and induced vertex set
computed above.
-/
abbrev SelectedOuterFaceAngleRealizationSource
    (D : ExplicitOuterBoundaryFaceData.{u} G) : Type :=
  SubpolygonAngleRealization.ConcreteAngleRealization G
    (selectedOuterFaceGeometry D).toGeometryData.boundary
    (selectedOuterFaceGeometry D).toGeometryData.vertexSet

/-- The selected outer-face pointwise angle source extracted from the sharp
E13 angle lower bound for the induced selected-geometry counts.
-/
def selectedOuterFaceAngleRealizationSourceOfAngleLowerBound
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (hangle : (selectedOuterFaceGeometry D).counts.AngleLowerBound) :
    SelectedOuterFaceAngleRealizationSource D :=
  SubpolygonAngleRealization.ConcreteAngleRealization.ofAngleLowerBound
    (G := G)
    (C := (selectedOuterFaceGeometry D).toGeometryData.boundary)
    (S := (selectedOuterFaceGeometry D).toGeometryData.vertexSet)
    (by
      simpa [FaceSubpolygonFields.counts,
        SubpolygonDataConcrete.CoreFaceSubpolygonGeometryData.counts]
        using hangle)

/-- Use pointwise concrete angle rows already indexed by the selected
outer-face geometry as the selected W33 angle source. -/
def selectedOuterFaceAngleRealizationSourceOfConcreteAngleRealization
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R :
      SubpolygonAngleRealization.ConcreteAngleRealization G
        (selectedOuterFaceGeometry D).toGeometryData.boundary
        (selectedOuterFaceGeometry D).toGeometryData.vertexSet) :
    SelectedOuterFaceAngleRealizationSource D :=
  R

/-- Use aggregate concrete angle bounds over the selected outer-face geometry
to build the pointwise selected W33 angle source. -/
def selectedOuterFaceAngleRealizationSourceOfConcreteAngleBounds
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (A :
      SubpolygonAngleRealization.ConcreteAngleBounds G
        (selectedOuterFaceGeometry D).toGeometryData.boundary
        (selectedOuterFaceGeometry D).toGeometryData.vertexSet) :
    SelectedOuterFaceAngleRealizationSource D :=
  selectedOuterFaceAngleRealizationSourceOfAngleLowerBound D
    (by
      simpa [FaceSubpolygonFields.counts,
        SubpolygonDataConcrete.CoreFaceSubpolygonGeometryData.counts]
        using A.angleLowerBound)

/-- Native concrete subpolygon triangulation rows for the selected outer face
reduce the selected W33 angle source to the remaining forced-angle lower bound
and the equality identifying the geometric angle sum with the triangulated
boundary interior-angle sum. -/
def selectedOuterFaceAngleRealizationSourceOfConcreteSubpolygonInteriorAngleTriangulationRows
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G
        (selectedOuterFaceGeometry D).toGeometryData.boundary
        (selectedOuterFaceGeometry D).toGeometryData.vertexSet)
    (geometricAngleSum : Real)
    (hforced :
      (selectedOuterFaceGeometry D).counts.forcedSubpolygonAngleSum <=
        geometricAngleSum)
    (hgeometric :
      geometricAngleSum =
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          (selectedOuterFaceGeometry D).toGeometryData.boundary
          R.previousIndex) :
    SelectedOuterFaceAngleRealizationSource D :=
  selectedOuterFaceAngleRealizationSourceOfConcreteAngleBounds D
    (R.toConcreteAngleBounds geometricAngleSum
      (by
        simpa [FaceSubpolygonFields.counts,
          SubpolygonDataConcrete.CoreFaceSubpolygonGeometryData.counts]
          using hforced)
      hgeometric)

/-- Extract the selected W33 angle source from concrete core face-subpolygon
realization data once its geometry is identified with the selected outer face. -/
def selectedOuterFaceAngleRealizationSourceOfCoreFaceSubpolygonAngleRealizationData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : CoreFaceSubpolygonAngleRealizationData D.core)
    (hgeometry : R.geometry = selectedOuterFaceCoreGeometry D) :
    SelectedOuterFaceAngleRealizationSource D := by
  change
    SubpolygonAngleRealization.ConcreteAngleRealization G
      (selectedOuterFaceCoreGeometry D).boundary
      (selectedOuterFaceCoreGeometry D).vertexSet
  rw [<- hgeometry]
  exact R.angleRealization

/-- With the selected geometry's vertex set equal to all ambient vertices, its
induced degree is the ambient unit-distance degree used by the boundary
classification layer. -/
theorem selectedOuterFaceGeometry_inducedDegree_eq_ambientDegree
    (D : ExplicitOuterBoundaryFaceData.{u} G) (v : Fin n) :
    (selectedOuterFaceGeometry D).toGeometryData.vertexSet.inducedDegree v =
      BoundaryWalkClassificationConcrete.ambientDegree G v := by
  classical
  unfold SubpolygonCore.InducedVertexSet.inducedDegree
  unfold SubpolygonCore.InducedVertexSet.inducedNeighborSet
  unfold BoundaryWalkClassificationConcrete.ambientDegree
  unfold BoundaryWalkClassificationConcrete.unitLocalGraph
  unfold LocalExclusions.LocalGraph.degree
  unfold LocalExclusions.LocalGraph.neighborFinset
  apply congrArg Finset.card
  ext u
  simp [selectedOuterFaceGeometry, FaceSubpolygonFields.toGeometryData,
    SubpolygonDataConcrete.CoreFaceSubpolygonGeometryData.toCoreSubpolygonGeometryData,
    SubpolygonDataConcrete.CoreFaceSubpolygonGeometryData.vertexSet,
    SubpolygonDataConcrete.CoreSubpolygonGeometryData.vertexSet,
    SubpolygonAssembly.inducedVertexSetOfFinset,
    G.adj_iff_unitDistanceAdj, GraphBridge.UnitDistanceAdj,
    Combinatorics.UDConfig.UnitAdj]

/-- Boundary-index count for selected outer-face vertices with ambient
unit-distance degree `d`. -/
def selectedOuterFaceAmbientDegreeCount
    (D : ExplicitOuterBoundaryFaceData.{u} G) (d : Nat) : Nat := by
  classical
  exact
    ((Finset.univ : Finset (Fin D.core.outerCycle.length)).filter
      fun k =>
        BoundaryWalkClassificationConcrete.IsDegree G d
          (D.core.outerCycle.vertex k)).card

/-- The selected outer-face count of boundary vertices with induced degree `d`
is the concrete classified-boundary filter count for ambient degree `d`. -/
theorem selectedOuterFaceGeometry_countBoundaryDegree_eq_degreeFilter
    (D : ExplicitOuterBoundaryFaceData.{u} G) (d : Nat) :
    (selectedOuterFaceGeometry D).toGeometryData.vertexSet.countBoundaryDegree d =
      selectedOuterFaceAmbientDegreeCount D d := by
  classical
  unfold selectedOuterFaceAmbientDegreeCount
  unfold SubpolygonCore.InducedVertexSet.countBoundaryDegree
  apply congrArg Finset.card
  ext k
  have hdegree :=
    selectedOuterFaceGeometry_inducedDegree_eq_ambientDegree
      (D := D) ((selectedOuterFaceGeometry D).toGeometryData.boundary.vertex k)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rw [hdegree] at h
    simpa [BoundaryWalkClassificationConcrete.IsDegree, selectedOuterFaceGeometry,
      FaceSubpolygonFields.toGeometryData,
      SubpolygonDataConcrete.CoreFaceSubpolygonGeometryData.boundary,
      SubpolygonAssembly.boundaryCycleOfFaceBoundary,
      OuterBoundaryCore.outerCycle,
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary] using h
  · intro h
    rw [hdegree]
    simpa [BoundaryWalkClassificationConcrete.IsDegree, selectedOuterFaceGeometry,
      FaceSubpolygonFields.toGeometryData,
      SubpolygonDataConcrete.CoreFaceSubpolygonGeometryData.boundary,
      SubpolygonAssembly.boundaryCycleOfFaceBoundary,
      OuterBoundaryCore.outerCycle,
      OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary] using h

/-- Convert the selected ambient-degree filter count into the classification's
degree-three count. -/
theorem selectedOuterFaceAmbientDegreeCount_eq_classification_D3
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core) :
    selectedOuterFaceAmbientDegreeCount D 3 = classification.counts.d3 := by
  classical
  unfold selectedOuterFaceAmbientDegreeCount
  rw [classification.counts_d3]
  have hsub :
      ((Finset.univ : Finset (Fin D.core.outerCycle.length)).filter
        fun k =>
          BoundaryWalkClassificationConcrete.IsDegree G 3
            (D.core.outerCycle.vertex k)).card =
        @Fintype.card
          { k : Fin D.core.outerCycle.length //
            BoundaryWalkClassificationConcrete.IsDegree G 3
              (D.core.outerCycle.vertex k) }
          (Subtype.fintype _) :=
    (Fintype.card_subtype
      (fun k : Fin D.core.outerCycle.length =>
        BoundaryWalkClassificationConcrete.IsDegree G 3
          (D.core.outerCycle.vertex k))).symm
  refine hsub.trans ?_
  exact Fintype.card_congr (Equiv.refl _)

/-- Convert the selected ambient-degree filter count into the classification's
degree-four count. -/
theorem selectedOuterFaceAmbientDegreeCount_eq_classification_D4
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core) :
    selectedOuterFaceAmbientDegreeCount D 4 = classification.counts.d4 := by
  classical
  unfold selectedOuterFaceAmbientDegreeCount
  rw [classification.counts_d4]
  have hsub :
      ((Finset.univ : Finset (Fin D.core.outerCycle.length)).filter
        fun k =>
          BoundaryWalkClassificationConcrete.IsDegree G 4
            (D.core.outerCycle.vertex k)).card =
        @Fintype.card
          { k : Fin D.core.outerCycle.length //
            BoundaryWalkClassificationConcrete.IsDegree G 4
              (D.core.outerCycle.vertex k) }
          (Subtype.fintype _) :=
    (Fintype.card_subtype
      (fun k : Fin D.core.outerCycle.length =>
        BoundaryWalkClassificationConcrete.IsDegree G 4
          (D.core.outerCycle.vertex k))).symm
  refine hsub.trans ?_
  exact Fintype.card_congr (Equiv.refl _)

/-- Convert the selected ambient-degree filter count into the classification's
degree-five count. -/
theorem selectedOuterFaceAmbientDegreeCount_eq_classification_D5
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core) :
    selectedOuterFaceAmbientDegreeCount D 5 = classification.counts.d5 := by
  classical
  unfold selectedOuterFaceAmbientDegreeCount
  rw [classification.counts_d5]
  have hsub :
      ((Finset.univ : Finset (Fin D.core.outerCycle.length)).filter
        fun k =>
          BoundaryWalkClassificationConcrete.IsDegree G 5
            (D.core.outerCycle.vertex k)).card =
        @Fintype.card
          { k : Fin D.core.outerCycle.length //
            BoundaryWalkClassificationConcrete.IsDegree G 5
              (D.core.outerCycle.vertex k) }
          (Subtype.fintype _) :=
    (Fintype.card_subtype
      (fun k : Fin D.core.outerCycle.length =>
        BoundaryWalkClassificationConcrete.IsDegree G 5
          (D.core.outerCycle.vertex k))).symm
  refine hsub.trans ?_
  exact Fintype.card_congr (Equiv.refl _)

/-- Convert the selected ambient-degree filter count into the classification's
degree-six count. -/
theorem selectedOuterFaceAmbientDegreeCount_eq_classification_D6
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core) :
    selectedOuterFaceAmbientDegreeCount D 6 = classification.counts.d6 := by
  classical
  unfold selectedOuterFaceAmbientDegreeCount
  rw [classification.counts_d6]
  have hsub :
      ((Finset.univ : Finset (Fin D.core.outerCycle.length)).filter
        fun k =>
          BoundaryWalkClassificationConcrete.IsDegree G 6
            (D.core.outerCycle.vertex k)).card =
        @Fintype.card
          { k : Fin D.core.outerCycle.length //
            BoundaryWalkClassificationConcrete.IsDegree G 6
              (D.core.outerCycle.vertex k) }
          (Subtype.fintype _) :=
    (Fintype.card_subtype
      (fun k : Fin D.core.outerCycle.length =>
        BoundaryWalkClassificationConcrete.IsDegree G 6
          (D.core.outerCycle.vertex k))).symm
  refine hsub.trans ?_
  exact Fintype.card_congr (Equiv.refl _)

/-- The selected outer-face geometry has no induced degree-two boundary
vertices once it is matched to a concrete outer-boundary classification. -/
theorem selectedOuterFaceGeometry_counts_D2_of_classification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core) :
    (selectedOuterFaceGeometry D).counts.D2 = 0 := by
  classical
  change
    (selectedOuterFaceGeometry D).toGeometryData.vertexSet.countBoundaryDegree 2 =
      0
  rw [selectedOuterFaceGeometry_countBoundaryDegree_eq_degreeFilter]
  unfold selectedOuterFaceAmbientDegreeCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  have hge := classification.degree_ge_three k
  have hdeg : BoundaryWalkClassificationConcrete.ambientDegree G
      (D.core.outerCycle.vertex k) = 2 := hk
  omega

/-- Degree-three selected outer-face counts match concrete classified
outer-boundary counts when the stored outer-angle counts come from that
classification. -/
theorem selectedOuterFaceGeometry_counts_D3_of_classification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts) :
    (selectedOuterFaceGeometry D).counts.D3 =
      D.outerAngleBounds.counts.d3 := by
  classical
  have hclass :
      (selectedOuterFaceGeometry D).counts.D3 =
        classification.counts.d3 := by
    change
      (selectedOuterFaceGeometry D).toGeometryData.vertexSet.countBoundaryDegree 3 =
        classification.counts.d3
    rw [selectedOuterFaceGeometry_countBoundaryDegree_eq_degreeFilter]
    exact selectedOuterFaceAmbientDegreeCount_eq_classification_D3
      D classification
  simpa [hcounts] using hclass

/-- Degree-four selected outer-face counts match concrete classified
outer-boundary counts when the stored outer-angle counts come from that
classification. -/
theorem selectedOuterFaceGeometry_counts_D4_of_classification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts) :
    (selectedOuterFaceGeometry D).counts.D4 =
      D.outerAngleBounds.counts.d4 := by
  classical
  have hclass :
      (selectedOuterFaceGeometry D).counts.D4 =
        classification.counts.d4 := by
    change
      (selectedOuterFaceGeometry D).toGeometryData.vertexSet.countBoundaryDegree 4 =
        classification.counts.d4
    rw [selectedOuterFaceGeometry_countBoundaryDegree_eq_degreeFilter]
    exact selectedOuterFaceAmbientDegreeCount_eq_classification_D4
      D classification
  simpa [hcounts] using hclass

/-- Degree-five selected outer-face counts match concrete classified
outer-boundary counts when the stored outer-angle counts come from that
classification. -/
theorem selectedOuterFaceGeometry_counts_D5_of_classification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts) :
    (selectedOuterFaceGeometry D).counts.D5 =
      D.outerAngleBounds.counts.d5 := by
  classical
  have hclass :
      (selectedOuterFaceGeometry D).counts.D5 =
        classification.counts.d5 := by
    change
      (selectedOuterFaceGeometry D).toGeometryData.vertexSet.countBoundaryDegree 5 =
        classification.counts.d5
    rw [selectedOuterFaceGeometry_countBoundaryDegree_eq_degreeFilter]
    exact selectedOuterFaceAmbientDegreeCount_eq_classification_D5
      D classification
  simpa [hcounts] using hclass

/-- Degree-six selected outer-face counts match concrete classified
outer-boundary counts when the stored outer-angle counts come from that
classification. -/
theorem selectedOuterFaceGeometry_counts_D6_of_classification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts) :
    (selectedOuterFaceGeometry D).counts.D6 =
      D.outerAngleBounds.counts.d6 := by
  classical
  have hclass :
      (selectedOuterFaceGeometry D).counts.D6 =
        classification.counts.d6 := by
    change
      (selectedOuterFaceGeometry D).toGeometryData.vertexSet.countBoundaryDegree 6 =
        classification.counts.d6
    rw [selectedOuterFaceGeometry_countBoundaryDegree_eq_degreeFilter]
    exact selectedOuterFaceAmbientDegreeCount_eq_classification_D6
      D classification
  simpa [hcounts] using hclass

/-- The selected outer-face E13 angle lower bound follows from the existing
outer-boundary E12 angle data once the induced selected counts are identified
with the outer-boundary degree bookkeeping and degree-two selected boundary
vertices are ruled out.

These count-identification hypotheses are the concrete geometric/combinatorial
link not present in `ExplicitOuterBoundaryFaceData` itself.
-/
theorem selectedOuterFaceAngleLowerBoundOfOuterBoundaryCountIdentifications
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (hD2 : (selectedOuterFaceGeometry D).counts.D2 = 0)
    (hD3 :
      (selectedOuterFaceGeometry D).counts.D3 =
        D.outerAngleBounds.counts.d3)
    (hD4 :
      (selectedOuterFaceGeometry D).counts.D4 =
        D.outerAngleBounds.counts.d4)
    (hD5 :
      (selectedOuterFaceGeometry D).counts.D5 =
        D.outerAngleBounds.counts.d5)
    (hD6 :
      (selectedOuterFaceGeometry D).counts.D6 =
        D.outerAngleBounds.counts.d6) :
    (selectedOuterFaceGeometry D).counts.AngleLowerBound := by
  have houter : D.outerAngleBounds.counts.AngleLowerBound :=
    D.outerAngleBounds.angleLowerBound
  have hb : 0 <= (D.outerAngleBounds.counts.b : Real) :=
    Nat.cast_nonneg _
  have hB : 0 <= (D.outerAngleBounds.counts.B : Real) :=
    Nat.cast_nonneg _
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold SubpolygonDegreeCounts.AngleLowerBound
  unfold SubpolygonDegreeCounts.forcedSubpolygonAngleSum
  unfold SubpolygonDegreeCounts.polygonAngleSum
  unfold SubpolygonDegreeCounts.vertexCount
  rw [hD2, hD3, hD4, hD5, hD6]
  unfold BoundaryCounting.BoundaryCounts.AngleLowerBound at houter
  unfold BoundaryCounting.BoundaryCounts.forcedBoundaryAngleSum at houter
  unfold BoundaryCounting.BoundaryCounts.polygonAngleSum at houter
  unfold BoundaryCounting.BoundaryCounts.vertexCount at houter
  norm_num [Nat.cast_add, Nat.cast_mul] at houter ⊢
  nlinarith

/-- The selected outer-face pointwise source extracted from the existing
outer-boundary E12 angle data plus the exact selected-count identifications.
-/
def selectedOuterFaceAngleRealizationSourceOfOuterBoundaryCountIdentifications
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (hD2 : (selectedOuterFaceGeometry D).counts.D2 = 0)
    (hD3 :
      (selectedOuterFaceGeometry D).counts.D3 =
        D.outerAngleBounds.counts.d3)
    (hD4 :
      (selectedOuterFaceGeometry D).counts.D4 =
        D.outerAngleBounds.counts.d4)
    (hD5 :
      (selectedOuterFaceGeometry D).counts.D5 =
        D.outerAngleBounds.counts.d5)
    (hD6 :
      (selectedOuterFaceGeometry D).counts.D6 =
        D.outerAngleBounds.counts.d6) :
    SelectedOuterFaceAngleRealizationSource D :=
  selectedOuterFaceAngleRealizationSourceOfAngleLowerBound D
    (selectedOuterFaceAngleLowerBoundOfOuterBoundaryCountIdentifications D
      hD2 hD3 hD4 hD5 hD6)

/-- The selected outer-face E13 angle lower bound follows from a concrete
outer-boundary classification whose counts are the stored outer-angle counts. -/
theorem selectedOuterFaceAngleLowerBoundOfClassification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts) :
    (selectedOuterFaceGeometry D).counts.AngleLowerBound :=
  selectedOuterFaceAngleLowerBoundOfOuterBoundaryCountIdentifications D
    (selectedOuterFaceGeometry_counts_D2_of_classification D classification)
    (selectedOuterFaceGeometry_counts_D3_of_classification D classification
      hcounts)
    (selectedOuterFaceGeometry_counts_D4_of_classification D classification
      hcounts)
    (selectedOuterFaceGeometry_counts_D5_of_classification D classification
      hcounts)
    (selectedOuterFaceGeometry_counts_D6_of_classification D classification
      hcounts)

/-- The selected outer-face pointwise source extracted from a concrete
outer-boundary classification whose counts are the stored outer-angle counts. -/
def selectedOuterFaceAngleRealizationSourceOfClassification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts) :
    SelectedOuterFaceAngleRealizationSource D :=
  selectedOuterFaceAngleRealizationSourceOfAngleLowerBound D
    (selectedOuterFaceAngleLowerBoundOfClassification D classification
      hcounts)

/-- The selected outer-face pointwise source obtained from refined face data
built by `PlanarBoundaryFaceData.ofClassification`.
-/
def selectedOuterFaceAngleRealizationSourceOfPlanarBoundaryClassification
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts C)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (PlanarBoundaryFaceDataRefinement.CanonicalGraph C)) :
    SelectedOuterFaceAngleRealizationSource
      (explicitFaceDataOfPlanarBoundaryFaceData
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.ofClassification
          topology classification angleWitness Subpolygon subpolygonData)) :=
  selectedOuterFaceAngleRealizationSourceOfClassification
    (explicitFaceDataOfPlanarBoundaryFaceData
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.ofClassification
        topology classification angleWitness Subpolygon subpolygonData))
    (by
      change
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
          topology.toCore
      exact classification)
    (by rfl)

/-- The selected outer-face pointwise source obtained from refined face data
built by the minimal-failure selected-classification constructor.
-/
def selectedOuterFaceAngleRealizationSourceOfMinimalFailureSelectedClassification
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (PlanarBoundaryFaceDataRefinement.CanonicalGraph C)) :
    SelectedOuterFaceAngleRealizationSource
      (explicitFaceDataOfPlanarBoundaryFaceData
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.ofMinimalFailureSelectedClassification
          topology hmin longArc angleWitness Subpolygon subpolygonData)) :=
  selectedOuterFaceAngleRealizationSourceOfClassification
    (explicitFaceDataOfPlanarBoundaryFaceData
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.ofMinimalFailureSelectedClassification
        topology hmin longArc angleWitness Subpolygon subpolygonData))
    (by
      change
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
          topology.toCore
      exact
        PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)
    (by rfl)

/-- The selected outer-face pointwise source obtained directly from the
minimal-failure selected classification data, before choosing any
subpolygon family for `PlanarBoundaryFaceData`.
-/
def selectedOuterFaceAngleRealizationSourceOfMinimalFailureSelectedClassificationFields
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    SelectedOuterFaceAngleRealizationSource
      (explicitFaceDataOfMissingTopologyFacts topology
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
          topology hmin longArc angleWitness)) :=
  selectedOuterFaceAngleRealizationSourceOfClassification
    (explicitFaceDataOfMissingTopologyFacts topology
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness))
    (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
      topology hmin longArc)
    (by rfl)

/-- Once the exact angle source is supplied, W33's flattened realization data
is inhabited for the selected outer face.
-/
def selectedOuterFaceRealizationData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    FaceSubpolygonRealizationData D where
  geometry := selectedOuterFaceGeometry D
  angleRealization := R

@[simp]
theorem selectedOuterFaceRealizationData_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    (selectedOuterFaceRealizationData D R).counts =
      (selectedOuterFaceGeometry D).counts :=
  rfl

/-- Build the flattened selected W33 realization data from concrete core
face-subpolygon realization rows whose geometry is the selected outer face. -/
def selectedOuterFaceRealizationDataOfCoreFaceSubpolygonAngleRealizationData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : CoreFaceSubpolygonAngleRealizationData D.core)
    (hgeometry : R.geometry = selectedOuterFaceCoreGeometry D) :
    FaceSubpolygonRealizationData D :=
  selectedOuterFaceRealizationData D
    (selectedOuterFaceAngleRealizationSourceOfCoreFaceSubpolygonAngleRealizationData
      D R hgeometry)

/-- The selected outer-face W33 realization family, once the pointwise angle
source is supplied.
-/
def selectedOuterFaceRealizationFamilyData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    FaceSubpolygonRealizationFamilyData.{u} D where
  Subpolygon := PUnit.{u + 1}
  subpolygonData := fun _ => selectedOuterFaceRealizationData D R

@[simp]
theorem selectedOuterFaceRealizationFamilyData_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (S : (selectedOuterFaceRealizationFamilyData D R).Subpolygon) :
    (selectedOuterFaceRealizationFamilyData D R).subpolygonCounts S =
      (selectedOuterFaceGeometry D).counts :=
  rfl

/-- Carrier rows for the concrete four-field boundary-gap component pattern
over the selected W33 realization family are equivalent to pointwise exclusion
of that pattern.
-/
theorem selectedOuterFaceRealizationFamilyData_componentPatternCarrierRows_iff_noBadRows
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core) :
    (forall k : Fin D.core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyData D R).toCoreFaceSubpolygonFamilyData))) <->
      forall k : Fin D.core.outerCycle.length,
        Not (BoundaryGapTriangleDegree34ComponentPattern classification k) :=
  (selectedOuterFaceRealizationFamilyData D R).componentPatternCarrierRows_iff_noBadRows
    classification

/-- Component-pattern carrier rows over the selected W33 realization family
produce the selected boundary no-gap rows consumed by the K23 branch.
-/
theorem selectedOuterFaceRealizationFamilyData_no_boundaryGapTriangleDegree34Rows_of_componentCarrierRows
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcarrier :
      forall k : Fin D.core.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyData D R).toCoreFaceSubpolygonFamilyData))) :
    forall k : Fin D.core.outerCycle.length,
      Not
        (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) :=
  (selectedOuterFaceRealizationFamilyData D R).no_boundaryGapTriangleDegree34Rows_of_componentCarrierRows
    classification hcarrier

/-- Carrier rows for the named boundary-gap row itself are equivalent to the
selected no-gap row over the selected W33 realization family.
-/
theorem selectedOuterFaceRealizationFamilyData_boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core) :
    (forall k : Fin D.core.outerCycle.length,
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyData D R).toCoreFaceSubpolygonFamilyData))) <->
      forall k : Fin D.core.outerCycle.length,
        Not
          (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k) :=
  (selectedOuterFaceRealizationFamilyData D R).boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
    classification

/-- Named boundary-gap carrier rows over the selected W33 realization family
produce the selected no-gap rows directly.
-/
theorem selectedOuterFaceRealizationFamilyData_no_boundaryGapTriangleDegree34Rows_of_boundaryGapCarrierRows
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcarrier :
      forall k : Fin D.core.outerCycle.length,
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyData D R).toCoreFaceSubpolygonFamilyData))) :
    forall k : Fin D.core.outerCycle.length,
      Not
        (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) :=
  ((selectedOuterFaceRealizationFamilyData D R).boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
    classification).1 hcarrier

/-! ## Actual selected-row no-gap bridge -/

/-- The explicit selected-face data attached to an actual selected component
row, with the angle bounds taken from that same component row. -/
def explicitFaceDataOfActualSelectedComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin) :
    ExplicitOuterBoundaryFaceData.{0}
      (PlanarBoundaryFaceDataRefinement.CanonicalGraph C) where
  outerFaceData := {
    faceBoundary := R.topology.selectedOuterFace.faceBoundary
    outerFace := R.topology.selectedOuterFace.outerFace
    outerFace_isOuter := R.topology.selectedOuterFace.outerFace_isOuter
  }
  enclosureData := {
    outerEnclosure := R.topology.enclosure.outerEnclosure
  }
  outerAngleBounds := R.components.angleComparison.outerAngleBounds

@[simp]
theorem explicitFaceDataOfActualSelectedComponentRow_core
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin) :
    (explicitFaceDataOfActualSelectedComponentRow R).core =
      actualSelectedOuterBoundaryCore R :=
  rfl

/-- The actual selected component row supplies the selected outer-face angle
realization source directly from its exact selected topology, classification,
and stored outer-angle bounds.
-/
def selectedOuterFaceAngleRealizationSourceOfActualSelectedComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin) :
    SelectedOuterFaceAngleRealizationSource
      (explicitFaceDataOfActualSelectedComponentRow R) :=
  selectedOuterFaceAngleRealizationSourceOfClassification
    (explicitFaceDataOfActualSelectedComponentRow R)
    (actualSelectedBoundaryClassification R)
    (by rfl)

/-- The selected outer face in an actual selected component row as flattened
W33 face-subpolygon realization data.
-/
def selectedOuterFaceRealizationDataOfActualSelectedComponentRow
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin) :
    FaceSubpolygonRealizationData
      (explicitFaceDataOfActualSelectedComponentRow R) :=
  selectedOuterFaceRealizationData
    (explicitFaceDataOfActualSelectedComponentRow R)
    (selectedOuterFaceAngleRealizationSourceOfActualSelectedComponentRow R)

/-- Selected face realization rows for the actual selected subpolygon index:
each index is realized by the selected outer-face geometry attached to the
same exact topology and angle bounds.
-/
def actualSelectedFaceRealizationRowsOfSelectedOuterFace
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin) :
    actualSelectedSubpolygonType R ->
      FaceSubpolygonRealizationData
        (explicitFaceDataOfActualSelectedComponentRow R) :=
  fun _ => selectedOuterFaceRealizationDataOfActualSelectedComponentRow R

/-- Package selected outer-face realization fields over an actual selected
component row as the W33 flattened face-subpolygon realization family. -/
def actualSelectedFaceSubpolygonRealizationFamilyData
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin)
    (realizationRows :
      actualSelectedSubpolygonType R ->
        FaceSubpolygonRealizationData
          (explicitFaceDataOfActualSelectedComponentRow R)) :
    FaceSubpolygonRealizationFamilyData.{0}
      (explicitFaceDataOfActualSelectedComponentRow R) where
  Subpolygon := actualSelectedSubpolygonType R
  subpolygonData := realizationRows

/-- Forget the actual selected face-realization fields to the core-subpolygon
realization rows expected by the K23 actual-selected no-gap surface. -/
def actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin)
    (realizationRows :
      actualSelectedSubpolygonType R ->
        FaceSubpolygonRealizationData
          (explicitFaceDataOfActualSelectedComponentRow R)) :
    actualSelectedSubpolygonType R ->
      CoreSubpolygonAngleRealizationData
        (actualSelectedOuterBoundaryCore R) :=
  fun S =>
    (realizationRows S).toCoreFaceSubpolygonAngleRealizationData
      |>.toCoreSubpolygonAngleRealizationData

/-- The W33 family bridge has the same aggregate core-subpolygon family as the
K23 actual-selected realization-row bridge. -/
@[simp]
theorem actualSelectedFaceSubpolygonRealizationFamilyData_toCoreSubpolygonFamilyData
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (R :
      ExtractedComponentsConcreteClosureW32.FixedActualTopologyExtractedComponentPackage.{0}
        C hmin)
    (realizationRows :
      actualSelectedSubpolygonType R ->
        FaceSubpolygonRealizationData
          (explicitFaceDataOfActualSelectedComponentRow R)) :
    CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
        (FaceSubpolygonRealizationFamilyData.toCoreFaceSubpolygonFamilyData
          (actualSelectedFaceSubpolygonRealizationFamilyData R realizationRows)) =
      actualSelectedCoreSubpolygonFamilyData R
        (actualSelectedCoreSubpolygonDataOfRealizationRows R
          (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
            R realizationRows)) :=
  rfl

/-- Fixed-frame K23 no-gap rows sourced directly from selected outer-face
realization fields and pointwise component-pattern carrier rows.

The proof is the current W33 contradiction route: package the selected fields
as a `FaceSubpolygonRealizationFamilyData`, use its component-pattern carrier
bridge to refute the raw four-field pattern pointwise, and then return the
actual K23 no-gap row with the supplied downstream boundary equality. -/
theorem actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_selectedFaceRealizationRows
    {componentClosure : ActualTopologyComponentClosurePackage.{0}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{0} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (realizationRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          actualSelectedSubpolygonType (componentClosure.row C hmin) ->
            FaceSubpolygonRealizationData
              (explicitFaceDataOfActualSelectedComponentRow
                (componentClosure.row C hmin)))
    (hboundary :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (actualSelectedBoundaryClassification
              (componentClosure.row C hmin)).toPlanarBoundaryData
              (actualSelectedGeometricAngleSum
                (componentClosure.row C hmin))
              (actualSelected_forced_le_geometric
                (componentClosure.row C hmin))
              (actualSelected_geometric_le_polygon
                (componentClosure.row C hmin))
              (actualSelectedCoreSubpolygonFamilyData
                (componentClosure.row C hmin)
                (actualSelectedCoreSubpolygonDataOfRealizationRows
                  (componentClosure.row C hmin)
                  (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                    (componentClosure.row C hmin)
                    (realizationRows C hmin)))).Subpolygon
              (fun S =>
                ((actualSelectedCoreSubpolygonFamilyData
                  (componentClosure.row C hmin)
                  (actualSelectedCoreSubpolygonDataOfRealizationRows
                    (componentClosure.row C hmin)
                    (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                      (componentClosure.row C hmin)
                      (realizationRows C hmin)))).subpolygonData
                    S).toSubpolygonCycleCountAngleData) =
            Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                (componentFamilyOfActualTopologyClosurePackage
                  componentClosure))
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin)
    (hcarrier :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          forall k :
            Fin (actualSelectedOuterBoundaryCore
              (componentClosure.row C hmin)).outerCycle.length,
            ActualSelectedBoundaryGapTriangleDegree34ComponentRow
                (componentClosure.row C hmin) k ->
              Nonempty
                (CoreSubpolygonCarrierCountData
                  ((actualSelectedFaceSubpolygonRealizationFamilyData
                    (componentClosure.row C hmin)
                    (realizationRows C hmin))
                      |>.toCoreFaceSubpolygonFamilyData
                      |>.toCoreSubpolygonFamilyData))) :
    ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
      componentClosure rows := by
  intro n C hmin
  let R := componentClosure.row C hmin
  let coreRows :=
    actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
      R (realizationRows C hmin)
  refine
    ⟨actualSelectedCoreSubpolygonDataOfRealizationRows R coreRows,
      hboundary C hmin, ?_⟩
  exact
    (actualSelectedFaceSubpolygonRealizationFamilyData R
      (realizationRows C hmin)).no_boundaryGapTriangleDegree34Rows_of_componentCarrierRows
        (actualSelectedBoundaryClassification R)
        (hcarrier C hmin)

/-- Selected-frame source theorem version of the selected outer-face
realization bridge.  The hypotheses are still the concrete rows themselves:
realization fields over the actual selected component row, the equality to the
downstream selected `RowBoundary`, and pointwise component-pattern carrier
rows over the same W33 family. -/
theorem selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_selectedFaceRealizationRows
    (realizationRows :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{0})
        (_frameSource :
          FrameCyclicSourcePackage.{0}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              actualSelectedSubpolygonType (componentClosure.row C hmin) ->
                FaceSubpolygonRealizationData
                  (explicitFaceDataOfActualSelectedComponentRow
                    (componentClosure.row C hmin)))
    (hboundary :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{0})
        (frameSource :
          FrameCyclicSourcePackage.{0}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              (actualSelectedBoundaryClassification
                  (componentClosure.row C hmin)).toPlanarBoundaryData
                  (actualSelectedGeometricAngleSum
                    (componentClosure.row C hmin))
                  (actualSelected_forced_le_geometric
                    (componentClosure.row C hmin))
                  (actualSelected_geometric_le_polygon
                    (componentClosure.row C hmin))
                  (actualSelectedCoreSubpolygonFamilyData
                    (componentClosure.row C hmin)
                    (actualSelectedCoreSubpolygonDataOfRealizationRows
                      (componentClosure.row C hmin)
                      (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                        (componentClosure.row C hmin)
                        (realizationRows H componentClosure frameSource C hmin)))).Subpolygon
                  (fun S =>
                    ((actualSelectedCoreSubpolygonFamilyData
                      (componentClosure.row C hmin)
                      (actualSelectedCoreSubpolygonDataOfRealizationRows
                        (componentClosure.row C hmin)
                        (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                          (componentClosure.row C hmin)
                          (realizationRows H componentClosure frameSource C hmin)))).subpolygonData
                        S).toSubpolygonCycleCountAngleData) =
                Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
                  (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    (noCutDependencyOfNoCutVertexFamily H))
                  (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    (componentFamilyOfActualTopologyClosurePackage
                      componentClosure))
                  (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                    (geometry
                      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
                  C hmin)
    (hcarrier :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{0})
        (frameSource :
          FrameCyclicSourcePackage.{0}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              forall k :
                Fin (actualSelectedOuterBoundaryCore
                  (componentClosure.row C hmin)).outerCycle.length,
                ActualSelectedBoundaryGapTriangleDegree34ComponentRow
                    (componentClosure.row C hmin) k ->
                  Nonempty
                    (CoreSubpolygonCarrierCountData
                      ((actualSelectedFaceSubpolygonRealizationFamilyData
                        (componentClosure.row C hmin)
                        (realizationRows H componentClosure frameSource C hmin))
                          |>.toCoreFaceSubpolygonFamilyData
                          |>.toCoreSubpolygonFamilyData))) :
    SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0} := by
  intro H componentClosure frameSource
  exact
    actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_selectedFaceRealizationRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (realizationRows H componentClosure frameSource)
      (hboundary H componentClosure frameSource)
      (hcarrier H componentClosure frameSource)

/-- Actual selected no-gap rows from the positive selected outer-face
realization rows.  The selected topology and angle bounds now produce the W33
realization rows; the remaining inputs are the downstream `RowBoundary`
identification and carrier rows for each selected bad component pattern.
-/
theorem actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_selectedOuterFaceRealizationRows
    {componentClosure : ActualTopologyComponentClosurePackage.{0}}
    {noCut : NoCutDependency}
    {rows :
      FrameCyclicRows.{0} noCut
        (componentFamilyOfActualTopologyClosurePackage componentClosure)}
    (hboundary :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (actualSelectedBoundaryClassification
              (componentClosure.row C hmin)).toPlanarBoundaryData
              (actualSelectedGeometricAngleSum
                (componentClosure.row C hmin))
              (actualSelected_forced_le_geometric
                (componentClosure.row C hmin))
              (actualSelected_geometric_le_polygon
                (componentClosure.row C hmin))
              (actualSelectedCoreSubpolygonFamilyData
                (componentClosure.row C hmin)
                (actualSelectedCoreSubpolygonDataOfRealizationRows
                  (componentClosure.row C hmin)
                  (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                    (componentClosure.row C hmin)
                    (actualSelectedFaceRealizationRowsOfSelectedOuterFace
                      (componentClosure.row C hmin))))).Subpolygon
              (fun S =>
                ((actualSelectedCoreSubpolygonFamilyData
                  (componentClosure.row C hmin)
                  (actualSelectedCoreSubpolygonDataOfRealizationRows
                    (componentClosure.row C hmin)
                    (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                      (componentClosure.row C hmin)
                      (actualSelectedFaceRealizationRowsOfSelectedOuterFace
                        (componentClosure.row C hmin))))).subpolygonData
                    S).toSubpolygonCycleCountAngleData) =
            Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
              (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut noCut)
              (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                (componentFamilyOfActualTopologyClosurePackage
                  componentClosure))
              (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                (geometry rows))
              C hmin)
    (hcarrier :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          forall k :
            Fin (actualSelectedOuterBoundaryCore
              (componentClosure.row C hmin)).outerCycle.length,
            ActualSelectedBoundaryGapTriangleDegree34ComponentRow
                (componentClosure.row C hmin) k ->
              Nonempty
                (CoreSubpolygonCarrierCountData
                  ((actualSelectedFaceSubpolygonRealizationFamilyData
                    (componentClosure.row C hmin)
                    (actualSelectedFaceRealizationRowsOfSelectedOuterFace
                      (componentClosure.row C hmin)))
                      |>.toCoreFaceSubpolygonFamilyData
                      |>.toCoreSubpolygonFamilyData))) :
    ActualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows
      componentClosure rows :=
  actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_selectedFaceRealizationRows
    (fun C hmin =>
      actualSelectedFaceRealizationRowsOfSelectedOuterFace
        (componentClosure.row C hmin))
    hboundary
    hcarrier

/-- Selected-frame source theorem version of the positive selected outer-face
realization rows for the K23 no-gap consumer.
-/
theorem selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_selectedOuterFaceRealizationRows
    (hboundary :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{0})
        (frameSource :
          FrameCyclicSourcePackage.{0}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              (actualSelectedBoundaryClassification
                  (componentClosure.row C hmin)).toPlanarBoundaryData
                  (actualSelectedGeometricAngleSum
                    (componentClosure.row C hmin))
                  (actualSelected_forced_le_geometric
                    (componentClosure.row C hmin))
                  (actualSelected_geometric_le_polygon
                    (componentClosure.row C hmin))
                  (actualSelectedCoreSubpolygonFamilyData
                    (componentClosure.row C hmin)
                    (actualSelectedCoreSubpolygonDataOfRealizationRows
                      (componentClosure.row C hmin)
                      (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                        (componentClosure.row C hmin)
                        (actualSelectedFaceRealizationRowsOfSelectedOuterFace
                          (componentClosure.row C hmin))))).Subpolygon
                  (fun S =>
                    ((actualSelectedCoreSubpolygonFamilyData
                      (componentClosure.row C hmin)
                      (actualSelectedCoreSubpolygonDataOfRealizationRows
                        (componentClosure.row C hmin)
                        (actualSelectedCoreSubpolygonRealizationRowsOfSelectedFaceRealizationRows
                          (componentClosure.row C hmin)
                          (actualSelectedFaceRealizationRowsOfSelectedOuterFace
                            (componentClosure.row C hmin))))).subpolygonData
                        S).toSubpolygonCycleCountAngleData) =
                Lemma9NoEarlyObstructionInhabitationW25.RowBoundary
                  (PointwiseLaneProductInhabitationW31.PayForCutOfNoCut
                    (noCutDependencyOfNoCutVertexFamily H))
                  (PointwiseLaneProductInhabitationW31.TopologyArcOfComponents
                    (componentFamilyOfActualTopologyClosurePackage
                      componentClosure))
                  (PointwiseLaneProductInhabitationW31.Lemma8ConcreteOfGeometrySource
                    (geometry
                      (frameCyclicRowsOfFrameCyclicSourcePackage frameSource)))
                  C hmin)
    (hcarrier :
      forall
        (H : NoCutVertexFamily)
        (componentClosure : ActualTopologyComponentClosurePackage.{0})
        (_frameSource :
          FrameCyclicSourcePackage.{0}
            (noCutDependencyOfNoCutVertexFamily H)
            (componentFamilyOfActualTopologyClosurePackage componentClosure)),
          forall {n : Nat} (C : _root_.UDConfig n)
            (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
              forall k :
                Fin (actualSelectedOuterBoundaryCore
                  (componentClosure.row C hmin)).outerCycle.length,
                ActualSelectedBoundaryGapTriangleDegree34ComponentRow
                    (componentClosure.row C hmin) k ->
                  Nonempty
                    (CoreSubpolygonCarrierCountData
                      ((actualSelectedFaceSubpolygonRealizationFamilyData
                        (componentClosure.row C hmin)
                        (actualSelectedFaceRealizationRowsOfSelectedOuterFace
                          (componentClosure.row C hmin)))
                          |>.toCoreFaceSubpolygonFamilyData
                          |>.toCoreSubpolygonFamilyData))) :
    SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem.{0} := by
  intro H componentClosure frameSource
  exact
    actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_selectedOuterFaceRealizationRows
      (rows := frameCyclicRowsOfFrameCyclicSourcePackage frameSource)
      (hboundary H componentClosure frameSource)
      (hcarrier H componentClosure frameSource)

/-- The selected outer-face family in the concrete core face-subpolygon
realization format, before forgetting pointwise angle rows. -/
def selectedOuterFaceCoreFaceSubpolygonAngleRealizationFamilyData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    CoreFaceSubpolygonAngleRealizationFamilyData.{u} D.core :=
  (selectedOuterFaceRealizationFamilyData D R).toCoreFaceSubpolygonAngleRealizationFamilyData

@[simp]
theorem selectedOuterFaceCoreFaceSubpolygonAngleRealizationFamilyData_Subpolygon
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    (selectedOuterFaceCoreFaceSubpolygonAngleRealizationFamilyData D R).Subpolygon =
      PUnit.{u + 1} :=
  rfl

@[simp]
theorem selectedOuterFaceCoreFaceSubpolygonAngleRealizationFamilyData_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (S :
      (selectedOuterFaceCoreFaceSubpolygonAngleRealizationFamilyData D R).Subpolygon) :
    ((selectedOuterFaceCoreFaceSubpolygonAngleRealizationFamilyData D R).subpolygonData
        S).counts =
      (selectedOuterFaceGeometry D).counts := by
  cases S
  rfl

/-- The selected outer-face family in the generic core-subpolygon realization
format used by downstream realization-carrier sources. -/
def selectedOuterFaceCoreSubpolygonAngleRealizationFamilyData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    CoreSubpolygonAngleRealizationFamilyData.{u} D.core :=
  (selectedOuterFaceCoreFaceSubpolygonAngleRealizationFamilyData D R)
    |>.toCoreSubpolygonAngleRealizationFamilyData

@[simp]
theorem selectedOuterFaceCoreSubpolygonAngleRealizationFamilyData_Subpolygon
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    (selectedOuterFaceCoreSubpolygonAngleRealizationFamilyData D R).Subpolygon =
      PUnit.{u + 1} :=
  rfl

@[simp]
theorem selectedOuterFaceCoreSubpolygonAngleRealizationFamilyData_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (S :
      (selectedOuterFaceCoreSubpolygonAngleRealizationFamilyData D R).Subpolygon) :
    ((selectedOuterFaceCoreSubpolygonAngleRealizationFamilyData D R).subpolygonData
        S).counts =
      (selectedOuterFaceGeometry D).counts := by
  cases S
  rfl

/-- The selected outer-face realization family in the exact core-subpolygon
format consumed by the Lemma 6 strict carrier branch. -/
def selectedOuterFaceCoreSubpolygonFamilyData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    CoreSubpolygonFamilyData.{u} D.core :=
  (selectedOuterFaceRealizationFamilyData D R).toCoreFaceSubpolygonFamilyData
    |>.toCoreSubpolygonFamilyData

@[simp]
theorem selectedOuterFaceCoreSubpolygonFamilyData_Subpolygon
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    (selectedOuterFaceCoreSubpolygonFamilyData D R).Subpolygon =
      PUnit.{u + 1} :=
  rfl

@[simp]
theorem selectedOuterFaceCoreSubpolygonFamilyData_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (S : (selectedOuterFaceCoreSubpolygonFamilyData D R).Subpolygon) :
    ((selectedOuterFaceCoreSubpolygonFamilyData D R).subpolygonData S).counts =
      (selectedOuterFaceGeometry D).counts := by
  cases S
  rfl

/-- Selected outer-face count data in the exact core-family carrier format
consumed by the classified-walk Lemma 6 strict subpolygon branch.

This is only a projection: once the selected-face `D2`/`D3` row is supplied, it
is transported through the W34 selected outer-face subpolygon integration and is
ready to hand to the `H` premise of
`boundaryWalkLemma6E14NegativeAfterFact_of_classificationCoreSubpolygonCarrierCountData`.
-/
theorem selectedOuterFaceCoreSubpolygonCarrierCountData
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (H :
      Exists fun D2 : Nat =>
        Exists fun D3 : Nat =>
          (selectedOuterFaceGeometry D).counts.D2 = D2 /\
          (selectedOuterFaceGeometry D).counts.D3 = D3 /\
          2 * D2 + D3 < 6) :
    Exists fun S : (selectedOuterFaceCoreSubpolygonFamilyData D R).Subpolygon =>
      Exists fun D2 : Nat =>
        Exists fun D3 : Nat =>
          ((selectedOuterFaceCoreSubpolygonFamilyData D R).subpolygonData S).counts.D2 =
            D2 /\
          ((selectedOuterFaceCoreSubpolygonFamilyData D R).subpolygonData S).counts.D3 =
            D3 /\
          2 * D2 + D3 < 6 := by
  rcases H with ⟨D2, D3, hD2, hD3, hstrict⟩
  refine ⟨PUnit.unit, D2, D3, ?_, ?_, hstrict⟩
  · simpa using hD2
  · simpa using hD3

/-- A concrete classification supplies the selected outer-face carrier counts
as exact `CoreSubpolygonCarrierCountData`, keeping the chosen selected
outer-face subpolygon visible for the Lemma 6 strict-carrier route. -/
def selectedOuterFaceCoreSubpolygonCarrierCountDataExact_of_classification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts)
    (hstrict : 2 * 0 + D.outerAngleBounds.counts.d3 < 6) :
    CoreSubpolygonCarrierCountData
      (selectedOuterFaceCoreSubpolygonFamilyData D R) := by
  refine
    { carrier := PUnit.unit
      D2 := 0
      D3 := D.outerAngleBounds.counts.d3
      counts_D2 := ?_
      counts_D3 := ?_
      strict := hstrict }
  · simpa using
      selectedOuterFaceGeometry_counts_D2_of_classification D classification
  · simpa using
      selectedOuterFaceGeometry_counts_D3_of_classification D classification
        hcounts

/-- A concrete classification supplies the selected outer-face carrier counts
with `D2 = 0` and `D3` equal to the stored outer-boundary degree-three count.
-/
theorem selectedOuterFaceCoreSubpolygonCarrierCountData_of_classification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts)
    (hstrict : 2 * 0 + D.outerAngleBounds.counts.d3 < 6) :
    Exists fun S : (selectedOuterFaceCoreSubpolygonFamilyData D R).Subpolygon =>
      Exists fun D2 : Nat =>
        Exists fun D3 : Nat =>
          ((selectedOuterFaceCoreSubpolygonFamilyData D R).subpolygonData S).counts.D2 =
            D2 /\
          ((selectedOuterFaceCoreSubpolygonFamilyData D R).subpolygonData S).counts.D3 =
            D3 /\
          2 * D2 + D3 < 6 :=
  (selectedOuterFaceCoreSubpolygonCarrierCountDataExact_of_classification
    D R classification hcounts hstrict).toExists

/-- Concrete selected outer-face strict carrier using the classification-derived
angle realization from the `D2`-through-`D6` selected count projections.

Thus the angle/source fields are closed here; the only remaining row is the
strict count inequality `2 * 0 + d3 < 6`.
-/
def selectedOuterFaceCoreSubpolygonCarrierCountDataExactOfClassification
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts)
    (hstrict : 2 * 0 + D.outerAngleBounds.counts.d3 < 6) :
    CoreSubpolygonCarrierCountData
      (selectedOuterFaceCoreSubpolygonFamilyData D
        (selectedOuterFaceAngleRealizationSourceOfClassification D
          classification hcounts)) :=
  selectedOuterFaceCoreSubpolygonCarrierCountDataExact_of_classification
    D
    (selectedOuterFaceAngleRealizationSourceOfClassification D classification
      hcounts)
    classification hcounts hstrict

/-- The selected outer-face strict carrier in the exact local source shape
consumed by `Lemma6Lemma7AssemblyW13`.

The `D2`-through-`D6` selected count projections supply the classification
angle realization and the carrier count fields.  What remains, exactly, is the
strict row `2 * 0 + D.outerAngleBounds.counts.d3 < 6`.
-/
theorem selectedOuterFaceLocalGapTriangleDegree34CoreSubpolygonCarrierCountDataOfClassification
    {Cfg : _root_.UDConfig n}
    (D :
      ExplicitOuterBoundaryFaceData.{u}
        (BoundaryFaceCountingToM8.CanonicalUDGraph Cfg))
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        D.core)
    (hcounts : D.outerAngleBounds.counts = classification.counts)
    (hstrict : 2 * 0 + D.outerAngleBounds.counts.d3 < 6) :
    Lemma6NegativeAfterGapW12.LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
      D.core classification.longArc
      (selectedOuterFaceCoreSubpolygonFamilyData D
        (selectedOuterFaceAngleRealizationSourceOfClassification D
          classification hcounts)) :=
  Lemma6NegativeAfterGapW12.localGapTriangleDegree34CoreSubpolygonCarrierCountData_of_coreSubpolygonCarrierCountData
    (Pcfg := D.core) (longArc := classification.longArc)
    (selectedOuterFaceCoreSubpolygonCarrierCountDataExactOfClassification
      D classification hcounts hstrict)

/-- The selected outer-face realization family obtained directly from the
minimal-failure selected classification fields.
-/
def selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    FaceSubpolygonRealizationFamilyData.{u}
      (explicitFaceDataOfMissingTopologyFacts topology
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
          topology hmin longArc angleWitness)) :=
  selectedOuterFaceRealizationFamilyData
    (explicitFaceDataOfMissingTopologyFacts topology
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness))
    (selectedOuterFaceAngleRealizationSourceOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness)

@[simp]
theorem selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_Subpolygon
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness).Subpolygon = PUnit.{u + 1} :=
  rfl

/-- The directly usable subpolygon field for the minimal-failure selected
classification constructor: the one-member family is the selected outer face
itself, with its checked pointwise realization.
-/
def selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    PUnit.{u + 1} ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData
        (PlanarBoundaryFaceDataRefinement.CanonicalGraph C) :=
  fun S =>
    (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness).toPlanarBoundarySubpolygonInputs.subpolygonData S

@[simp]
theorem selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S : PUnit.{u + 1}) :
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts =
      (selectedOuterFaceGeometry
        (explicitFaceDataOfMissingTopologyFacts topology
          (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
            topology hmin longArc angleWitness))).counts := by
  cases S
  rfl

@[simp]
theorem selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D2
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S : PUnit.{u + 1}) :
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D2 = 0 := by
  rw [selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts]
  exact selectedOuterFaceGeometry_counts_D2_of_classification _
    (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
      topology hmin longArc)

@[simp]
theorem selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D3
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S : PUnit.{u + 1}) :
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D3 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d3 := by
  rw [selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts]
  exact selectedOuterFaceGeometry_counts_D3_of_classification _
    (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
      topology hmin longArc) (by rfl)

@[simp]
theorem selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D4
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S : PUnit.{u + 1}) :
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D4 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d4 := by
  rw [selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts]
  exact selectedOuterFaceGeometry_counts_D4_of_classification _
    (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
      topology hmin longArc) (by rfl)

@[simp]
theorem selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D5
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S : PUnit.{u + 1}) :
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D5 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d5 := by
  rw [selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts]
  exact selectedOuterFaceGeometry_counts_D5_of_classification _
    (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
      topology hmin longArc) (by rfl)

@[simp]
theorem selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D6
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S : PUnit.{u + 1}) :
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D6 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d6 := by
  rw [selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts]
  exact selectedOuterFaceGeometry_counts_D6_of_classification _
    (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
      topology hmin longArc) (by rfl)

/-- A closed refined face-data constructor for the selected/minimal-failure
classification lane.  Unlike `ofMinimalFailureSelectedClassification`, this
fills the subpolygon family with the selected outer face and therefore needs
no arbitrary `ExplicitOuterBoundaryFaceData` count-equality premise
downstream.
-/
def planarBoundaryFaceDataOfMinimalFailureSelectedClassification
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.{u} C :=
  PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.ofMinimalFailureSelectedClassification
    topology hmin longArc angleWitness
    PUnit.{u + 1}
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness)

@[simp]
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_Subpolygon
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).Subpolygon = PUnit.{u + 1} :=
  rfl

@[simp]
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonData
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S : PUnit.{u + 1}) :
    (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S =
      selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness S :=
  rfl

theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonAngleLowerBound
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).counts.AngleLowerBound :=
  ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
    topology hmin longArc angleWitness).subpolygonData S).angleLowerBound

/-- The subpolygon data in the selected/minimal-failure refined face package is
exactly the planar-boundary projection of the selected outer-face realization
family built above.

This keeps the S3 skeleton field reducible to the named W33 realization source,
instead of hiding the selected outer-face realization behind the refined
face-data record projection.
-/
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonData_eq_realizationFamily
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S =
      (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
        topology hmin longArc angleWitness).toPlanarBoundarySubpolygonInputs.subpolygonData S := by
  cases S
  rfl

/-- The named selected outer-face realization family provides the E13
high-degree-slack row used after the S3 skeleton has projected its subpolygon
field.
-/
theorem selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_lowDegreeWithHighDegreeSlack
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
        topology hmin longArc angleWitness).Subpolygon) :
    ((selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness).subpolygonCounts S).D5 +
        2 * ((selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
          topology hmin longArc angleWitness).subpolygonCounts S).D6 + 6 <=
      2 * ((selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
        topology hmin longArc angleWitness).subpolygonCounts S).D2 +
        ((selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
          topology hmin longArc angleWitness).subpolygonCounts S).D3 :=
  (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
    topology hmin longArc angleWitness).lowDegreeWithHighDegreeSlack S

/-- In the selected/minimal-failure classification lane, component-pattern
carrier rows over the named W33 realization family are equivalent to excluding
the concrete four-field boundary-gap pattern pointwise.
-/
theorem selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_componentPatternCarrierRows_iff_noBadRows
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    (forall k : Fin topology.toCore.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern
            (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
              topology hmin longArc) k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
                  topology hmin longArc angleWitness).toCoreFaceSubpolygonFamilyData))) <->
      forall k : Fin topology.toCore.outerCycle.length,
        Not
          (BoundaryGapTriangleDegree34ComponentPattern
            (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
              topology hmin longArc) k) :=
  (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
    topology hmin longArc angleWitness).componentPatternCarrierRows_iff_noBadRows
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
        topology hmin longArc)

/-- The selected/minimal-failure W33 realization family turns actual
component-pattern carrier rows into the boundary no-gap rows used downstream by
the K23 route.
-/
theorem selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_no_boundaryGapTriangleDegree34Rows_of_componentCarrierRows
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (hcarrier :
      forall k : Fin topology.toCore.outerCycle.length,
        BoundaryGapTriangleDegree34ComponentPattern
            (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
              topology hmin longArc) k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
                  topology hmin longArc angleWitness).toCoreFaceSubpolygonFamilyData))) :
    forall k : Fin topology.toCore.outerCycle.length,
      Not
        (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
            topology hmin longArc) k) :=
  (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
    topology hmin longArc angleWitness).no_boundaryGapTriangleDegree34Rows_of_componentCarrierRows
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
        topology hmin longArc)
      hcarrier

/-- In the selected/minimal-failure lane, named boundary-gap carrier rows over
the W33 realization family are equivalent to the selected no-gap row itself.
-/
theorem selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    (forall k : Fin topology.toCore.outerCycle.length,
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
              topology hmin longArc) k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
                  topology hmin longArc angleWitness).toCoreFaceSubpolygonFamilyData))) <->
      forall k : Fin topology.toCore.outerCycle.length,
        Not
          (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
              topology hmin longArc) k) :=
  (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
    topology hmin longArc angleWitness).boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
        topology hmin longArc)

/-- Named boundary-gap carrier rows over the selected/minimal-failure W33
realization family produce the downstream selected no-gap rows.
-/
theorem selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_no_boundaryGapTriangleDegree34Rows_of_boundaryGapCarrierRows
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (hcarrier :
      forall k : Fin topology.toCore.outerCycle.length,
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
              topology hmin longArc) k ->
          Nonempty
            (CoreSubpolygonCarrierCountData
              (CoreFaceSubpolygonFamilyData.toCoreSubpolygonFamilyData
                (selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
                  topology hmin longArc angleWitness).toCoreFaceSubpolygonFamilyData))) :
    forall k : Fin topology.toCore.outerCycle.length,
      Not
        (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
            topology hmin longArc) k) :=
  ((selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields
    topology hmin longArc angleWitness).boundaryGapTriangleDegree34CarrierRows_iff_noBadRows
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
        topology hmin longArc)).1 hcarrier

/-- The selected/minimal-failure refined face package exposes the same E13
high-degree-slack row on its planar-boundary subpolygon projection.
-/
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonLowDegreeWithHighDegreeSlack
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).counts.D5 +
        2 * ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
          topology hmin longArc angleWitness).subpolygonData S).counts.D6 + 6 <=
      2 * ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).subpolygonData S).counts.D2 +
        ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
          topology hmin longArc angleWitness).subpolygonData S).counts.D3 := by
  exact
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).lowDegreeWithHighDegreeSlack

/-- The selected outer-face family in the exact core-subpolygon format over
the minimal-failure selected-classification fields.
-/
def selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    CoreSubpolygonFamilyData.{u} topology.toCore :=
  selectedOuterFaceCoreSubpolygonFamilyData
    (explicitFaceDataOfMissingTopologyFacts topology
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness))
    (selectedOuterFaceAngleRealizationSourceOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness)

@[simp]
theorem selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields_Subpolygon
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    (selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness).Subpolygon = PUnit.{u + 1} :=
  rfl

/-- E13 high-degree slack in the exact core-subpolygon family format used by
strict-carrier and no-gap routes.
-/
theorem selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields_lowDegreeWithHighDegreeSlack
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
        topology hmin longArc angleWitness).Subpolygon) :
    ((selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness).subpolygonData S).counts.D5 +
        2 * ((selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
          topology hmin longArc angleWitness).subpolygonData S).counts.D6 + 6 <=
      2 * ((selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
        topology hmin longArc angleWitness).subpolygonData S).counts.D2 +
        ((selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
          topology hmin longArc angleWitness).subpolygonData S).counts.D3 := by
  exact
    ((selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness).subpolygonData S).lowDegreeWithHighDegreeSlack

/-- Any strict carrier over the selected minimal-failure core-subpolygon
family contradicts the E13 row carried by that same family.
-/
theorem false_of_selectedOuterFaceCoreSubpolygonCarrierCountDataOfMinimalFailureSelectedClassificationFields
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (carrier :
      CoreSubpolygonCarrierCountData
        (selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
          topology hmin longArc angleWitness)) :
    False :=
  carrier.false

/-- Nonempty strict-carrier rows over the selected minimal-failure
core-subpolygon family are impossible, in the exact shape used by no-gap
carrier contradictions.
-/
theorem not_nonempty_selectedOuterFaceCoreSubpolygonCarrierCountDataOfMinimalFailureSelectedClassificationFields
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc)) :
    Not
      (Nonempty
        (CoreSubpolygonCarrierCountData
          (selectedOuterFaceCoreSubpolygonFamilyDataOfMinimalFailureSelectedClassificationFields
            topology hmin longArc angleWitness))) := by
  intro hcarrier
  rcases hcarrier with ⟨carrier⟩
  exact
    false_of_selectedOuterFaceCoreSubpolygonCarrierCountDataOfMinimalFailureSelectedClassificationFields
      topology hmin longArc angleWitness carrier

@[simp]
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonCounts_D2
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).counts.D2 = 0 := by
  change
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D2 = 0
  exact
    selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D2
      topology hmin longArc angleWitness S

@[simp]
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonCounts_D3
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).counts.D3 =
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).outerAngleBounds.counts.d3 := by
  change
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D3 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d3
  exact
    selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D3
      topology hmin longArc angleWitness S

@[simp]
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonCounts_D4
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).counts.D4 =
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).outerAngleBounds.counts.d4 := by
  change
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D4 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d4
  exact
    selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D4
      topology hmin longArc angleWitness S

@[simp]
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonCounts_D5
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).counts.D5 =
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).outerAngleBounds.counts.d5 := by
  change
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D5 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d5
  exact
    selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D5
      topology hmin longArc angleWitness S

@[simp]
theorem planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonCounts_D6
    {C : _root_.UDConfig n}
    (topology :
      JordanBoundaryConcrete.MissingTopologyFacts.{u} C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.selectedClassificationOfMinimalFailure
          topology hmin longArc))
    (S :
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).Subpolygon) :
    ((planarBoundaryFaceDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).subpolygonData S).counts.D6 =
      (planarBoundaryFaceDataOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).outerAngleBounds.counts.d6 := by
  change
    (selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness S).counts.D6 =
      (PlanarBoundaryFaceDataRefinement.PlanarBoundaryFaceData.outerAngleBoundsOfMinimalFailureSelectedClassification
        topology hmin longArc angleWitness).counts.d6
  exact
    selectedOuterFaceSubpolygonDataOfMinimalFailureSelectedClassification_counts_D6
      topology hmin longArc angleWitness S

/-- The selected outer-face geometry as a W12 honest subpolygon package. -/
def selectedOuterFaceHonestSubpolygonPackage
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    HonestSubpolygonPackage G where
  boundary := (selectedOuterFaceGeometry D).toGeometryData.boundary
  insideOrOn := (selectedOuterFaceGeometry D).insideOrOn
  onBoundary := (selectedOuterFaceGeometry D).onBoundary
  vertices := (selectedOuterFaceGeometry D).vertices
  boundary_subset := (selectedOuterFaceGeometry D).boundary_subset
  vertices_iff_insideOrOn :=
    (selectedOuterFaceGeometry D).vertices_iff_insideOrOn
  boundary_vertex_onBoundary :=
    (selectedOuterFaceGeometry D).boundary_vertex_onBoundary
  onBoundary_iff_cycle := (selectedOuterFaceGeometry D).onBoundary_iff_cycle

@[simp]
theorem selectedOuterFaceHonestSubpolygonPackage_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    (selectedOuterFaceHonestSubpolygonPackage D).counts =
      (selectedOuterFaceGeometry D).counts :=
  rfl

/-- The selected outer-face geometry and pointwise angle source as a W12
honest aggregate angle package.
-/
def selectedOuterFaceHonestAnglePackage
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    HonestSubpolygonAnglePackage G where
  package := selectedOuterFaceHonestSubpolygonPackage D
  geometricAngleSum := R.geometricAngleSum
  forced_le_geometric := by
    simpa [selectedOuterFaceHonestSubpolygonPackage,
      HonestSubpolygonPackage.counts] using
      R.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa [selectedOuterFaceHonestSubpolygonPackage,
      HonestSubpolygonPackage.counts] using
      R.geometric_le_polygon

@[simp]
theorem selectedOuterFaceHonestAnglePackage_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    (selectedOuterFaceHonestAnglePackage D R).counts =
      (selectedOuterFaceGeometry D).counts :=
  rfl

/-- The selected outer-face family as the W12 honest aggregate angle package. -/
def selectedOuterFaceHonestFamilyPackage
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D) :
    HonestSubpolygonFamilyPackage.{u} G where
  faceBoundary := D.core.faceBoundary
  Subpolygon := PUnit.{u + 1}
  package := fun _ => selectedOuterFaceHonestAnglePackage D R

@[simp]
theorem selectedOuterFaceHonestFamilyPackage_counts
    (D : ExplicitOuterBoundaryFaceData.{u} G)
    (R : SelectedOuterFaceAngleRealizationSource D)
    (S : (selectedOuterFaceHonestFamilyPackage D R).Subpolygon) :
    (selectedOuterFaceHonestFamilyPackage D R).subpolygonCounts S =
      (selectedOuterFaceGeometry D).counts :=
  rfl

/-- The exact remaining source needed to upgrade the checked geometry in this
file to W33 realization data.
-/
structure SelectedOuterFaceRealizationSource
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  angleRealization : SelectedOuterFaceAngleRealizationSource D

namespace SelectedOuterFaceRealizationSource

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- Constructor from pointwise concrete angle rows on the selected geometry. -/
def ofConcreteAngleRealization
    (R :
      SubpolygonAngleRealization.ConcreteAngleRealization G
        (selectedOuterFaceGeometry D).toGeometryData.boundary
        (selectedOuterFaceGeometry D).toGeometryData.vertexSet) :
    SelectedOuterFaceRealizationSource D where
  angleRealization :=
    selectedOuterFaceAngleRealizationSourceOfConcreteAngleRealization D R

/-- Constructor from aggregate concrete angle bounds on the selected geometry. -/
def ofConcreteAngleBounds
    (A :
      SubpolygonAngleRealization.ConcreteAngleBounds G
        (selectedOuterFaceGeometry D).toGeometryData.boundary
        (selectedOuterFaceGeometry D).toGeometryData.vertexSet) :
    SelectedOuterFaceRealizationSource D where
  angleRealization :=
    selectedOuterFaceAngleRealizationSourceOfConcreteAngleBounds D A

/-- Constructor from native triangulation rows for the selected subpolygon. -/
def ofConcreteSubpolygonInteriorAngleTriangulationRows
    (R :
      SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows.{u}
        G
        (selectedOuterFaceGeometry D).toGeometryData.boundary
        (selectedOuterFaceGeometry D).toGeometryData.vertexSet)
    (geometricAngleSum : Real)
    (hforced :
      (selectedOuterFaceGeometry D).counts.forcedSubpolygonAngleSum <=
        geometricAngleSum)
    (hgeometric :
      geometricAngleSum =
        SubpolygonAngleRealization.boundaryInteriorAngleSum
          (selectedOuterFaceGeometry D).toGeometryData.boundary
          R.previousIndex) :
    SelectedOuterFaceRealizationSource D where
  angleRealization :=
    selectedOuterFaceAngleRealizationSourceOfConcreteSubpolygonInteriorAngleTriangulationRows
      D R geometricAngleSum hforced hgeometric

/-- Constructor from concrete core face-subpolygon realization rows matching
the selected outer-face geometry. -/
def ofCoreFaceSubpolygonAngleRealizationData
    (R : CoreFaceSubpolygonAngleRealizationData D.core)
    (hgeometry : R.geometry = selectedOuterFaceCoreGeometry D) :
    SelectedOuterFaceRealizationSource D where
  angleRealization :=
    selectedOuterFaceAngleRealizationSourceOfCoreFaceSubpolygonAngleRealizationData
      D R hgeometry

/-- Package the exact source as W33 realization data. -/
def toFaceSubpolygonRealizationData
    (S : SelectedOuterFaceRealizationSource D) :
    FaceSubpolygonRealizationData D :=
  selectedOuterFaceRealizationData D S.angleRealization

/-- Package the exact source as a one-member W33 realization family. -/
def toFaceSubpolygonRealizationFamilyData
    (S : SelectedOuterFaceRealizationSource D) :
    FaceSubpolygonRealizationFamilyData.{u} D :=
  selectedOuterFaceRealizationFamilyData D S.angleRealization

/-- Package the exact source as a W12 honest aggregate angle family. -/
def toHonestSubpolygonFamilyPackage
    (S : SelectedOuterFaceRealizationSource D) :
    HonestSubpolygonFamilyPackage.{u} G :=
  selectedOuterFaceHonestFamilyPackage D S.angleRealization

end SelectedOuterFaceRealizationSource

/-- The exact remaining source for a selected outer-face W12 honest family is
still only the pointwise angle realization over the checked selected geometry.
-/
structure SelectedOuterFaceHonestFamilySource
    (D : ExplicitOuterBoundaryFaceData.{u} G) where
  angleRealization : SelectedOuterFaceAngleRealizationSource D

namespace SelectedOuterFaceHonestFamilySource

variable {D : ExplicitOuterBoundaryFaceData.{u} G}

/-- Package the exact source as a W12 honest aggregate angle family. -/
def toHonestSubpolygonFamilyPackage
    (S : SelectedOuterFaceHonestFamilySource D) :
    HonestSubpolygonFamilyPackage.{u} G :=
  selectedOuterFaceHonestFamilyPackage D S.angleRealization

end SelectedOuterFaceHonestFamilySource

/-- Exact blocker statement: the selected outer-face W33 source is precisely a
pointwise angle realization over the checked geometry above.
-/
theorem nonempty_selectedOuterFaceRealizationSource_iff_angleSource
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    Nonempty (SelectedOuterFaceRealizationSource D) <->
      Nonempty (SelectedOuterFaceAngleRealizationSource D) := by
  constructor
  · intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.angleRealization
  · intro h
    cases h with
    | intro R =>
        exact Nonempty.intro { angleRealization := R }

/-- Exact blocker statement for the W12 honest-family projection of the
selected outer face: after the geometry in this file, the only remaining
source is the same pointwise angle realization.
-/
theorem nonempty_selectedOuterFaceHonestFamilySource_iff_angleSource
    (D : ExplicitOuterBoundaryFaceData.{u} G) :
    Nonempty (SelectedOuterFaceHonestFamilySource D) <->
      Nonempty (SelectedOuterFaceAngleRealizationSource D) := by
  constructor
  · intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.angleRealization
  · intro h
    cases h with
    | intro R =>
        exact Nonempty.intro { angleRealization := R }

end

end SubpolygonSelectedGeometrySourceW34
end Swanepoel
end ErdosProblems1066
