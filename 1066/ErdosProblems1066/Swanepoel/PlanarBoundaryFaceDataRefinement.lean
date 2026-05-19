import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete
import ErdosProblems1066.Swanepoel.BoundaryFaceCountingToM8
import ErdosProblems1066.Swanepoel.BoundaryCountingInstantiationW10
import ErdosProblems1066.Swanepoel.Lemma6NegativeAfterGapW12
import ErdosProblems1066.Swanepoel.MinimumDegree
import Mathlib.Geometry.Euclidean.Triangle

set_option autoImplicit false

/-!
# Refined planar face data for the M8 boundary route

This module keeps the remaining face and boundary inputs in one visible
package.  The Jordan-style topology fields are supplied through
`JordanBoundaryConcrete.MissingTopologyFacts`; the angle and subpolygon count
data are the fields already consumed by `PlanarBoundaryClosure`.

The checked content here is deterministic projection: from this refined
package to `PlanarBoundaryData`, then onward to the face-counting facade and
the `m = 8` boundary route.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PlanarBoundaryFaceDataRefinement

open BoundaryFaceCountingToM8
open CutVertexClosure
open JordanBoundaryConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a
configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryConcrete.canonicalGraph C

/-- The canonical enclosure predicates determined by a selected face boundary.
All vertices are inside-or-on, and boundary membership is exactly membership in
the selected boundary walk. -/
def boundarySetEnclosureFromOuterFaceData
    {C : _root_.UDConfig n}
    (D : MissingOuterFaceData.{u} C) :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) D.faceBoundary D.outerFace where
  insideOrOn := fun _ => True
  onBoundary := fun v =>
    Exists fun k : Fin (D.faceBoundary.boundaryLength D.outerFace) =>
      D.faceBoundary.boundaryVertex D.outerFace k = v
  boundary_vertex_onBoundary := fun k => Exists.intro k rfl
  boundary_point_insideOrOn := fun _ => trivial
  all_vertices_insideOrOn := fun _ => trivial
  onBoundary_iff_outer_cycle := fun _ => Iff.rfl

/-- Build the topology package from selected face-boundary data alone, filling
the enclosure layer with the boundary-set predicates. -/
def missingTopologyFactsOfOuterFaceData
    {C : _root_.UDConfig n}
    (D : MissingOuterFaceData.{u} C) :
    MissingTopologyFacts.{u} C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter
  outerEnclosure := boundarySetEnclosureFromOuterFaceData D

theorem nonempty_missingTopologyFacts_iff_missingOuterFaceData
    (C : _root_.UDConfig n) :
    Nonempty (MissingTopologyFacts.{u} C) <->
      Nonempty (MissingOuterFaceData.{u} C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
        exact Nonempty.intro
          (show MissingOuterFaceData.{u} C from T.toOuterFaceData)
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (show MissingTopologyFacts.{u} C from
            missingTopologyFactsOfOuterFaceData D)

/-! ## Refined face and boundary package -/

/--
Refined planar face data for a concrete configuration.

Compared with `PlanarBoundaryClosure.PlanarBoundaryData`, this record keeps
the source of the outer-boundary core visible as the concrete Jordan/topology
package for the canonical graph of `C`.
-/
structure PlanarBoundaryFaceData (C : _root_.UDConfig n) where
  topology : MissingTopologyFacts C
  outerAngleBounds :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}
  Subpolygon : Type u
  subpolygonData :
    Subpolygon ->
      SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)

namespace PlanarBoundaryFaceData

variable {C : _root_.UDConfig n}

/-! ### Concrete selected-boundary classification source -/

/-- The concrete ambient degree used by the boundary classification is the
finite unit-neighbor count from the degree pipeline. -/
theorem ambientDegree_eq_unitDistanceNeighborSet_card
    (C : _root_.UDConfig n) (v : Fin n) :
    BoundaryWalkClassificationConcrete.ambientDegree (CanonicalGraph C) v =
      (DegreePipeline.unitDistanceNeighborSet C v).card := by
  classical
  unfold BoundaryWalkClassificationConcrete.ambientDegree
  unfold LocalExclusions.LocalGraph.degree
  apply congrArg Finset.card
  ext u
  rw [LocalExclusions.LocalGraph.mem_neighborFinset,
    DegreePipeline.mem_unitDistanceNeighborSet]
  constructor
  · intro h
    change (GraphBridge.unitDistanceLocalGraph C).Adj v u at h
    have hne : u ≠ v := by
      intro huv
      subst u
      exact GraphBridge.unitDistanceAdj_loopless C v h
    have hneBool : (u != v) = true := by
      simpa [bne_iff_ne] using hne
    refine And.intro hneBool ?_
    simpa [GraphBridge.UnitDistanceAdj, _root_.eucDist_comm] using h
  · intro h
    change (GraphBridge.unitDistanceLocalGraph C).Adj v u
    change GraphBridge.UnitDistanceAdj C v u
    simpa [GraphBridge.UnitDistanceAdj, _root_.eucDist_comm] using h.2

/-- Minimal cleared failures supply the boundary-classification lower-degree
premise on every vertex of the selected outer cycle. -/
theorem selectedBoundary_degree_ge_three_of_minimalFailure
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C) :
    forall k : Fin topology.toCore.outerCycle.length,
      3 <= BoundaryWalkClassificationConcrete.ambientDegree
        (CanonicalGraph C) (topology.toCore.outerCycle.vertex k) := by
  intro k
  rw [ambientDegree_eq_unitDistanceNeighborSet_card C
    (topology.toCore.outerCycle.vertex k)]
  exact
    MinimumDegree.unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
      hmin (topology.toCore.outerCycle.vertex k)

/-- Assemble refined planar-boundary data from selected face-boundary data and
the existing angle/subpolygon rows.  The enclosure predicates are supplied by
`missingTopologyFactsOfOuterFaceData`. -/
def ofOuterFaceData
    (D : MissingOuterFaceData.{u} C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceData.{u} C where
  topology := missingTopologyFactsOfOuterFaceData D
  outerAngleBounds := outerAngleBounds
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

/-- The outer-boundary core obtained from the concrete Jordan/topology data. -/
def core (D : PlanarBoundaryFaceData.{u} C) :
    OuterBoundaryCore (CanonicalGraph C) :=
  D.topology.toCore

/-- The supplied canonical face-boundary witness. -/
def faceBoundary (D : PlanarBoundaryFaceData.{u} C) :
    FaceReduction.UnitDistanceFaceBoundaryHypotheses (CanonicalGraph C) :=
  D.topology.faceBoundary

/-- The selected outer face in the supplied face data. -/
def outerFace (D : PlanarBoundaryFaceData.{u} C) :
    D.faceBoundary.Face :=
  D.topology.outerFace

/-- The selected outer face is marked outer. -/
theorem outerFace_isOuter (D : PlanarBoundaryFaceData.{u} C) :
    D.faceBoundary.IsOuterFace D.outerFace :=
  D.topology.outerFace_isOuter

/-- The old planar face-boundary interface attached to the supplied faces. -/
def planarFaceBoundary (D : PlanarBoundaryFaceData.{u} C) :
    PlanarInterface.FaceBoundaryHypotheses (CanonicalGraph C).toStraightLine :=
  D.topology.planarFaceBoundary

/-- The canonical noncrossing fact for the selected unit-distance graph. -/
theorem pairwiseNoncrossing (D : PlanarBoundaryFaceData.{u} C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  D.topology.pairwiseNoncrossing

/-- The selected outer boundary cycle. -/
def outerCycle (D : PlanarBoundaryFaceData.{u} C) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  D.topology.outerCycle

/-- The selected outer boundary cycle is vertex-simple. -/
theorem outerCycle_vertex_injective (D : PlanarBoundaryFaceData.{u} C) :
    Function.Injective D.outerCycle.vertex :=
  D.topology.outerCycle_vertex_injective

/-- Boundary vertices of the selected outer face satisfy the supplied boundary
predicate. -/
theorem boundary_vertex_onBoundary
    (D : PlanarBoundaryFaceData.{u} C)
    (k : Fin (D.faceBoundary.boundaryLength D.outerFace)) :
    D.topology.outerEnclosure.onBoundary
      (D.faceBoundary.boundaryVertex D.outerFace k) :=
  D.topology.boundary_vertex_onBoundary k

/-- Every ambient vertex lies inside or on the supplied outer enclosure. -/
theorem all_vertices_insideOrOn
    (D : PlanarBoundaryFaceData.{u} C) (v : Fin n) :
    D.topology.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  D.topology.all_vertices_insideOrOn v

/-- Forget the refined source fields to the existing planar-boundary package. -/
def toPlanarBoundaryData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) where
  core := D.core
  outerAngleBounds := D.outerAngleBounds
  Subpolygon := D.Subpolygon
  subpolygonData := D.subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.core = D.core :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_planarFaceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.planarFaceBoundary = D.planarFaceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.outerFace = D.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem toPlanarBoundaryData_subpolygonData
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.toPlanarBoundaryData.subpolygonData S = D.subpolygonData S :=
  rfl

/-- The actual boundary classification determined by a selected topology, the
degree lower bound on its selected outer cycle, and the selected long-arc
predicate. -/
def selectedClassification
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toCore :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.ofLongArcPredicate
    (P := topology.toCore) degree_ge_three longArc

/-- The actual boundary classification determined by minimality and a selected
long-arc predicate.  This discharges the `degree_ge_three` input of
`selectedClassification` from the checked unit-distance minimum-degree row. -/
def selectedClassificationOfMinimalFailure
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
      topology.toCore :=
  selectedClassification topology
    (selectedBoundary_degree_ge_three_of_minimalFailure topology hmin)
    longArc

@[simp]
theorem selectedClassificationOfMinimalFailure_longArc
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop) :
    (selectedClassificationOfMinimalFailure topology hmin longArc).longArc =
      longArc :=
  rfl

@[simp]
theorem selectedClassificationOfMinimalFailure_degree_ge_three
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length) :
    (selectedClassificationOfMinimalFailure topology hmin longArc).degree_ge_three k =
      selectedBoundary_degree_ge_three_of_minimalFailure topology hmin k :=
  rfl

@[simp]
theorem selectedClassification_degree_ge_three
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length) :
    (selectedClassification topology degree_ge_three longArc).degree_ge_three k =
      degree_ge_three k :=
  rfl

@[simp]
theorem selectedClassification_longArc
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop) :
    (selectedClassification topology degree_ge_three longArc).longArc =
      longArc :=
  rfl

/-! ### Full selected-boundary index rows -/

/-- Build a concrete core-subpolygon family from row-indexed core subpolygon
angle data over a fixed outer-boundary core. -/
def coreSubpolygonFamilyDataOfCoreRows
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {core : OuterBoundaryCore G}
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonDataConcrete.CoreSubpolygonAngleData core) :
    SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} core where
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

/-- Full-boundary strict carrier rows are equivalent to excluding every
concrete boundary gap/triangle/degree-3-or-4 row.

The forward direction uses the checked E13 contradiction carried by
`CoreSubpolygonCarrierCountData`; the reverse direction fills the carrier row
from the impossible local classification row. -/
theorem boundaryGapTriangleDegree34CarrierRows_iff_no_boundaryGapTriangleDegree34Rows
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {core : OuterBoundaryCore G}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} core) :
    (forall k : Fin core.outerCycle.length,
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        classification k ->
        Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)) <->
      forall k : Fin core.outerCycle.length,
        Not
          (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k) := by
  constructor
  · intro hcarrier k hrow
    rcases hcarrier k hrow with ⟨carrier⟩
    exact carrier.false
  · intro hno k hrow
    exact False.elim (hno k hrow)

/-- The no-gap form of the full-boundary row source. -/
theorem boundaryGapTriangleDegree34CarrierRows_of_no_boundaryGapTriangleDegree34Rows
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {core : OuterBoundaryCore G}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} core)
    (hno :
      forall k : Fin core.outerCycle.length,
        Not
          (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
            classification k)) :
    forall k : Fin core.outerCycle.length,
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        classification k ->
        Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F) :=
  (boundaryGapTriangleDegree34CarrierRows_iff_no_boundaryGapTriangleDegree34Rows
    classification F).2 hno

/-- Pointwise carrier rows are also enough to recover the sharper no-gap row,
because any exact carrier contradicts the E13 low-degree theorem already
stored in the same core-subpolygon family. -/
theorem no_boundaryGapTriangleDegree34Rows_of_boundaryGapTriangleDegree34CarrierRows
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {core : OuterBoundaryCore G}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        core)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} core)
    (hcarrier :
      forall k : Fin core.outerCycle.length,
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k ->
          Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)) :
    forall k : Fin core.outerCycle.length,
      Not
        (BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          classification k) :=
  (boundaryGapTriangleDegree34CarrierRows_iff_no_boundaryGapTriangleDegree34Rows
    classification F).1 hcarrier

/-- The concrete classification row at an arbitrary index of the selected
outer-boundary walk.  This is indexed by the full boundary cycle, not by the
finite `M8` spine. -/
def selectedBoundaryIndexClassificationRow
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryIndexClassificationRow
      (selectedClassification topology degree_ge_three longArc) k :=
  (selectedClassification topology degree_ge_three longArc).boundaryIndexClassificationRow k

/-- Concrete classification rows for every index of the selected outer-boundary
walk. -/
def selectedBoundaryIndexClassificationRows
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop) :
    forall k : Fin topology.toCore.outerCycle.length,
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryIndexClassificationRow
        (selectedClassification topology degree_ge_three longArc) k :=
  (selectedClassification topology degree_ge_three longArc).boundaryIndexClassificationRows

/-- The concrete strict-carrier local row at a selected boundary index,
assembled from the full boundary-walk classifications at that index and its
cyclic successor. -/
def selectedBoundaryGapTriangleDegree34RowOfClassifications
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length)
    (gapDegree :
      (selectedClassification topology degree_ge_three longArc).toOuterBoundaryWalkBookkeeping.data.vertexKind k =
        BoundaryClassification.BoundaryDegreeClass.degree3)
    (notLongArc : Not (longArc k))
    (triangleNext :
      (selectedClassification topology degree_ge_three longArc).toOuterBoundaryWalkBookkeeping.data.edgeKind
          (topology.toCore.outerCycle.next k) =
        BoundaryClassification.BoundaryEdgeClass.triangle)
    (nextDegree :
      (selectedClassification topology degree_ge_three longArc).toOuterBoundaryWalkBookkeeping.data.vertexKind
          (topology.toCore.outerCycle.next k) =
          BoundaryClassification.BoundaryDegreeClass.degree3 \/
        (selectedClassification topology degree_ge_three longArc).toOuterBoundaryWalkBookkeeping.data.vertexKind
          (topology.toCore.outerCycle.next k) =
          BoundaryClassification.BoundaryDegreeClass.degree4) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
      (selectedClassification topology degree_ge_three longArc) k :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.boundaryGapTriangleDegree34RowOfClassifications
    (selectedClassification topology degree_ge_three longArc)
    k gapDegree (by simpa using notLongArc) triangleNext nextDegree

/-- The minimal-failure selected classification row at an arbitrary index of
the selected outer-boundary walk. -/
def selectedMinimalFailureBoundaryIndexClassificationRow
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryIndexClassificationRow
      (selectedClassificationOfMinimalFailure topology hmin longArc) k :=
  (selectedClassificationOfMinimalFailure topology hmin longArc).boundaryIndexClassificationRow k

/-- Minimal-failure classification rows for every selected boundary index. -/
def selectedMinimalFailureBoundaryIndexClassificationRows
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop) :
    forall k : Fin topology.toCore.outerCycle.length,
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryIndexClassificationRow
        (selectedClassificationOfMinimalFailure topology hmin longArc) k :=
  (selectedClassificationOfMinimalFailure topology hmin longArc).boundaryIndexClassificationRows

/-- Minimal-failure version of the full-boundary strict-carrier local row. -/
def selectedMinimalFailureBoundaryGapTriangleDegree34RowOfClassifications
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length)
    (gapDegree :
      (selectedClassificationOfMinimalFailure topology hmin longArc).toOuterBoundaryWalkBookkeeping.data.vertexKind k =
        BoundaryClassification.BoundaryDegreeClass.degree3)
    (notLongArc : Not (longArc k))
    (triangleNext :
      (selectedClassificationOfMinimalFailure topology hmin longArc).toOuterBoundaryWalkBookkeeping.data.edgeKind
          (topology.toCore.outerCycle.next k) =
        BoundaryClassification.BoundaryEdgeClass.triangle)
    (nextDegree :
      (selectedClassificationOfMinimalFailure topology hmin longArc).toOuterBoundaryWalkBookkeeping.data.vertexKind
          (topology.toCore.outerCycle.next k) =
          BoundaryClassification.BoundaryDegreeClass.degree3 \/
        (selectedClassificationOfMinimalFailure topology hmin longArc).toOuterBoundaryWalkBookkeeping.data.vertexKind
          (topology.toCore.outerCycle.next k) =
          BoundaryClassification.BoundaryDegreeClass.degree4) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
      (selectedClassificationOfMinimalFailure topology hmin longArc) k :=
  BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.boundaryGapTriangleDegree34RowOfClassifications
    (selectedClassificationOfMinimalFailure topology hmin longArc)
    k gapDegree (by simpa using notLongArc) triangleNext nextDegree

/-- Convert the full-boundary strict-carrier local row to the exact row shape
consumed by Lemma 6's local carrier source. -/
def concreteLocalGapTriangleDegree34FieldsOfBoundaryGapRow
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length)
    (row :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        (selectedClassification topology degree_ge_three longArc) k) :
    Lemma6NegativeAfterGapW12.ConcreteLocalGapTriangleDegree34Fields
      topology.toCore longArc k where
  gapDegree := row.gapDegree
  notLongArc := row.notLongArc
  triangleNext := row.triangleNext
  nextDegree := row.nextDegree

/-- Minimal-failure version of the full-boundary strict-carrier local row in
the exact Lemma 6 source shape. -/
def concreteLocalGapTriangleDegree34FieldsOfMinimalFailureBoundaryGapRow
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length)
    (row :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
        (selectedClassificationOfMinimalFailure topology hmin longArc) k) :
    Lemma6NegativeAfterGapW12.ConcreteLocalGapTriangleDegree34Fields
      topology.toCore longArc k :=
  concreteLocalGapTriangleDegree34FieldsOfBoundaryGapRow topology
    (selectedBoundary_degree_ge_three_of_minimalFailure topology hmin)
    longArc k row

/-- Convert Lemma 6's concrete local field row back to the full-boundary
classification-row shape. -/
def boundaryGapTriangleDegree34RowOfConcreteLocalFields
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (k : Fin topology.toCore.outerCycle.length)
    (fields :
      Lemma6NegativeAfterGapW12.ConcreteLocalGapTriangleDegree34Fields
        topology.toCore longArc k) :
    BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
      (selectedClassification topology degree_ge_three longArc) k where
  gapDegree := fields.gapDegree
  notLongArc := fields.notLongArc
  triangleNext := fields.triangleNext
  nextDegree := fields.nextDegree

/-- A row-indexed carrier source over every selected boundary index feeds the
strict local carrier source consumed by Lemma 6. -/
def localGapTriangleDegree34CoreSubpolygonCarrierCountDataOfBoundaryGapRows
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} topology.toCore)
    (rows :
      forall k : Fin topology.toCore.outerCycle.length,
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          (selectedClassification topology degree_ge_three longArc) k ->
          Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)) :
    Lemma6NegativeAfterGapW12.LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
      topology.toCore longArc F := by
  intro k fields
  exact
    rows k
      (boundaryGapTriangleDegree34RowOfConcreteLocalFields
        topology degree_ge_three longArc k fields)

/-- Minimal-failure version of the full-boundary row-indexed carrier source. -/
def localGapTriangleDegree34CoreSubpolygonCarrierCountDataOfMinimalFailureBoundaryGapRows
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (F : SubpolygonDataConcrete.CoreSubpolygonFamilyData.{u} topology.toCore)
    (rows :
      forall k : Fin topology.toCore.outerCycle.length,
        BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs.BoundaryGapTriangleDegree34Row
          (selectedClassificationOfMinimalFailure topology hmin longArc) k ->
          Nonempty (SubpolygonDataConcrete.CoreSubpolygonCarrierCountData F)) :
    Lemma6NegativeAfterGapW12.LocalGapTriangleDegree34CoreSubpolygonCarrierCountData
      topology.toCore longArc F :=
  localGapTriangleDegree34CoreSubpolygonCarrierCountDataOfBoundaryGapRows
    topology
    (selectedBoundary_degree_ge_three_of_minimalFailure topology hmin)
    longArc F rows

/-- The outer-boundary angle bookkeeping carried by a concrete selected
classification and its unit-separated angle witnesses, independent of any
subpolygon family. -/
def outerAngleBoundsOfClassification
    {topology : MissingTopologyFacts C}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} where
  countsRealization := classification.countsRealizationLift
  geometricAngleSum := angleWitness.geometricAngleSum
  forced_le_geometric := by
    simpa using angleWitness.forced_le_geometricAngleSum
  geometric_le_polygon := by
    simpa using angleWitness.geometric_le_polygon

@[simp]
theorem outerAngleBoundsOfClassification_counts
    {topology : MissingTopologyFacts C}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification) :
    (outerAngleBoundsOfClassification classification angleWitness).counts =
      classification.counts :=
  rfl

@[simp]
theorem outerAngleBoundsOfClassification_countsRealization
    {topology : MissingTopologyFacts C}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification) :
    (outerAngleBoundsOfClassification classification angleWitness).countsRealization =
      classification.countsRealizationLift :=
  rfl

theorem outerAngleBoundsOfClassification_angleLowerBound
    {topology : MissingTopologyFacts C}
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification) :
    ((outerAngleBoundsOfClassification classification angleWitness :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}).counts).AngleLowerBound := by
  exact angleWitness.angleLowerBound

/-- The selected-minimal-failure classification's outer-angle bookkeeping,
projected before choosing any subpolygon family. -/
def outerAngleBoundsOfMinimalFailureSelectedClassification
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassificationOfMinimalFailure topology hmin longArc)) :
    OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u} :=
  outerAngleBoundsOfClassification
    (selectedClassificationOfMinimalFailure topology hmin longArc)
    angleWitness

@[simp]
theorem outerAngleBoundsOfMinimalFailureSelectedClassification_counts
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassificationOfMinimalFailure topology hmin longArc)) :
    (outerAngleBoundsOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness).counts =
        (selectedClassificationOfMinimalFailure topology hmin longArc).counts :=
  rfl

theorem outerAngleBoundsOfMinimalFailureSelectedClassification_angleLowerBound
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassificationOfMinimalFailure topology hmin longArc)) :
    ((outerAngleBoundsOfMinimalFailureSelectedClassification
      topology hmin longArc angleWitness :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u}).counts).AngleLowerBound := by
  exact angleWitness.angleLowerBound

/-- Build refined planar face data from an already selected concrete
classification and its unit-separated angle witnesses.  This packages the
`degree_ge_three` and `longArc` premises as fields of the existing
classification data. -/
def ofClassification
    (topology : MissingTopologyFacts C)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceData.{u} C where
  topology := topology
  outerAngleBounds :=
    { countsRealization := classification.countsRealizationLift
      geometricAngleSum := angleWitness.geometricAngleSum
      forced_le_geometric := by
        simpa using angleWitness.forced_le_geometricAngleSum
      geometric_le_polygon := by
        simpa using angleWitness.geometric_le_polygon }
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

@[simp]
theorem ofClassification_topology
    (topology : MissingTopologyFacts C)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofClassification topology classification angleWitness
      Subpolygon subpolygonData).topology = topology :=
  rfl

@[simp]
theorem ofClassification_core
    (topology : MissingTopologyFacts C)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofClassification topology classification angleWitness
      Subpolygon subpolygonData).core = topology.toCore :=
  rfl

@[simp]
theorem ofClassification_outerAngleCounts
    (topology : MissingTopologyFacts C)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofClassification topology classification angleWitness
      Subpolygon subpolygonData).outerAngleBounds.counts =
        classification.counts :=
  rfl

@[simp]
theorem ofClassification_outerAngleBounds_countsRealization
    (topology : MissingTopologyFacts C)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofClassification topology classification angleWitness
      Subpolygon subpolygonData).outerAngleBounds.countsRealization =
        classification.countsRealizationLift :=
  rfl

theorem ofClassification_angleLowerBound
    (topology : MissingTopologyFacts C)
    (classification :
      BoundaryWalkClassificationConcrete.OuterBoundaryClassificationInputs
        topology.toCore)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        classification)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofClassification topology classification angleWitness
      Subpolygon subpolygonData).outerAngleBounds.counts.AngleLowerBound := by
  simpa using angleWitness.angleLowerBound

/-- Build refined planar face data from the selected topology, the degree
lower bound on the actual selected outer cycle, the selected long-arc
predicate, and concrete unit-separated angle witnesses for the resulting
classification.  This closes the outer-angle/count field of
`PlanarBoundaryFaceData` from selected boundary data rather than requiring a
prepackaged count realization. -/
def ofSelectedClassification
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceData.{u} C where
  topology := topology
  outerAngleBounds :=
    { countsRealization :=
        (selectedClassification topology degree_ge_three longArc).countsRealizationLift
      geometricAngleSum := angleWitness.geometricAngleSum
      forced_le_geometric := by
        simpa using angleWitness.forced_le_geometricAngleSum
      geometric_le_polygon := by
        simpa using angleWitness.geometric_le_polygon }
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

/-- Build refined planar face data from selected topology, minimality, a
long-arc predicate, and concrete unit-separated angle witnesses for the
classification generated from those data.  The boundary `degree_ge_three`
premise is extracted internally from the minimal-failure degree theorem. -/
def ofMinimalFailureSelectedClassification
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassificationOfMinimalFailure topology hmin longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceData.{u} C :=
  ofSelectedClassification topology
    (selectedBoundary_degree_ge_three_of_minimalFailure topology hmin)
    longArc angleWitness Subpolygon subpolygonData

/-- The local unit-distance angle rows for the selected classification
generated by minimality and the chosen long-arc predicate. -/
abbrev UnitSeparatedLocalAngleFamiliesOfMinimalFailure
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop) :
    Type :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies
    (selectedClassificationOfMinimalFailure topology hmin longArc)

/-- Attach the single polygon-angle accounting inequality to concrete
unit-separated local angle rows for the minimal-failure selected
classification. -/
def unitSeparatedAngleFamiliesOfMinimalFailureLocalAngles
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (localAngles :
      UnitSeparatedLocalAngleFamiliesOfMinimalFailure topology hmin longArc)
    (accounted_le_polygon :
      localAngles.accountedAngleSum <=
        (selectedClassificationOfMinimalFailure
          topology hmin longArc).counts.polygonAngleSum) :
  BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
      (selectedClassificationOfMinimalFailure topology hmin longArc) :=
  localAngles.toUnitSeparatedAngleFamilies accounted_le_polygon

/-! ### Honest simple-polygon angle-sum rows -/

/-- Previous corner in a three-corner triangle, used only to define actual
Euclidean triangle angles from point triples. -/
def triangleCornerPrev (c : Fin 3) : Fin 3 :=
  ⟨(c.1 + 2) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- Next corner in a three-corner triangle, used only to define actual
Euclidean triangle angles from point triples. -/
def triangleCornerNext (c : Fin 3) : Fin 3 :=
  ⟨(c.1 + 1) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The actual interior angle at a corner of a concrete triangle. -/
def triangleCornerAngle
    (trianglePoint : Fin 3 -> PlanarInterface.Point) (c : Fin 3) : Real :=
  AngleGeometry.angleAt
    (trianglePoint (triangleCornerPrev c))
    (trianglePoint c)
    (trianglePoint (triangleCornerNext c))

theorem toVec_vsub_sub_toVec_vsub_eq
    (p : Fin 3 -> PlanarInterface.Point) (i j k : Fin 3) :
    AngleGeometry.toVec (TriangleAngleFacts.vsub (p i) (p k)) -
        AngleGeometry.toVec (TriangleAngleFacts.vsub (p j) (p k)) =
      AngleGeometry.toVec (TriangleAngleFacts.vsub (p i) (p j)) := by
  ext r
  fin_cases r <;> simp [AngleGeometry.toVec, TriangleAngleFacts.vsub]

theorem toVec_vsub_rev_eq_neg (a b : PlanarInterface.Point) :
    AngleGeometry.toVec (TriangleAngleFacts.vsub a b) =
      -AngleGeometry.toVec (TriangleAngleFacts.vsub b a) := by
  ext r
  fin_cases r <;> simp [AngleGeometry.toVec, TriangleAngleFacts.vsub]

/-- Distinct concrete points determine a nonzero embedded side vector. -/
theorem toVec_vsub_ne_zero_of_ne
    {a b : PlanarInterface.Point} (hab : a ≠ b) :
    Ne (AngleGeometry.toVec (TriangleAngleFacts.vsub a b)) 0 := by
  intro hzero
  apply hab
  have hfst :
      a.1 - b.1 = 0 := by
    have hcoord :=
      congrArg (fun v : AngleGeometry.Vec2 => v 0) hzero
    simpa [AngleGeometry.toVec, TriangleAngleFacts.vsub] using hcoord
  have hsnd :
      a.2 - b.2 = 0 := by
    have hcoord :=
      congrArg (fun v : AngleGeometry.Vec2 => v 1) hzero
    simpa [AngleGeometry.toVec, TriangleAngleFacts.vsub] using hcoord
  exact Prod.ext (by linarith) (by linarith)

/-- Distinct vertices of a straight-line unit-distance graph have distinct
realized points, by the ambient separation condition. -/
theorem graph_point_ne_of_vertex_ne
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    {i j : Fin n} (hij : i ≠ j) :
    G.point i ≠ G.point j := by
  intro hpoint
  have hsep : (1 : Real) <= _root_.eucDist (G.config.pts i) (G.config.pts j) :=
    G.config.sep i j hij
  have hpts : G.config.pts i = G.config.pts j := by
    simpa [PlanarInterface.StraightLineUnitDistanceGraph.point] using hpoint
  rw [hpts, _root_.eucDist_self] at hsep
  norm_num at hsep

/-- Distinct selected boundary indices have distinct realized boundary
points. -/
theorem boundaryCycle_point_ne_of_index_ne
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (B : OuterBoundaryInterface.BoundaryCycle G) {i j : Fin B.length}
    (hij : i ≠ j) :
    B.point i ≠ B.point j :=
  graph_point_ne_of_vertex_ne (B.vertex_ne_of_index_ne hij)

/-- Mathlib's Euclidean triangle-angle theorem, specialized to the concrete
corner order used by the outer-boundary triangulation rows.  It reduces each
triangle angle-sum row to one nonzero side vector. -/
theorem triangleCornerAngleSum_eq_pi_of_toVec_vsub_ne_zero
    (trianglePoint : Fin 3 -> PlanarInterface.Point)
    (h02 :
      Ne
        (AngleGeometry.toVec
          (TriangleAngleFacts.vsub (trianglePoint 2) (trianglePoint 0)))
        0) :
    Finset.sum (Finset.univ : Finset (Fin 3))
        (fun c => triangleCornerAngle trianglePoint c) =
      Real.pi := by
  let x :=
    AngleGeometry.toVec
      (TriangleAngleFacts.vsub (trianglePoint 1) (trianglePoint 0))
  let y :=
    AngleGeometry.toVec
      (TriangleAngleFacts.vsub (trianglePoint 2) (trianglePoint 0))
  have hsum :=
    InnerProductGeometry.angle_add_angle_sub_add_angle_sub_eq_pi
      (y := y) x h02
  have hx_sub_y :
      x - y =
        AngleGeometry.toVec
          (TriangleAngleFacts.vsub (trianglePoint 1) (trianglePoint 2)) := by
    simpa [x, y] using
      toVec_vsub_sub_toVec_vsub_eq trianglePoint 1 2 0
  have hy_sub_x :
      y - x =
        AngleGeometry.toVec
          (TriangleAngleFacts.vsub (trianglePoint 2) (trianglePoint 1)) := by
    simpa [x, y] using
      toVec_vsub_sub_toVec_vsub_eq trianglePoint 2 1 0
  rw [hx_sub_y, hy_sub_x] at hsum
  have hcorner0 :
      triangleCornerAngle trianglePoint 0 =
        InnerProductGeometry.angle y x := by
    simp [triangleCornerAngle, triangleCornerPrev, triangleCornerNext, x, y,
      AngleGeometry.angleAt]
  have hcorner1 :
      triangleCornerAngle trianglePoint 1 =
        InnerProductGeometry.angle x
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 1) (trianglePoint 2))) := by
    change
      InnerProductGeometry.angle
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 0) (trianglePoint 1)))
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 2) (trianglePoint 1))) =
        InnerProductGeometry.angle x
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 1) (trianglePoint 2)))
    rw [toVec_vsub_rev_eq_neg (trianglePoint 0) (trianglePoint 1),
      toVec_vsub_rev_eq_neg (trianglePoint 2) (trianglePoint 1)]
    simp [x, InnerProductGeometry.angle_neg_neg]
  have hcorner2 :
      triangleCornerAngle trianglePoint 2 =
        InnerProductGeometry.angle y
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 2) (trianglePoint 1))) := by
    change
      InnerProductGeometry.angle
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 1) (trianglePoint 2)))
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 0) (trianglePoint 2))) =
        InnerProductGeometry.angle y
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint 2) (trianglePoint 1)))
    rw [toVec_vsub_rev_eq_neg (trianglePoint 1) (trianglePoint 2),
      toVec_vsub_rev_eq_neg (trianglePoint 0) (trianglePoint 2)]
    simp [y, InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_comm]
  rw [Fin.sum_univ_three]
  rw [hcorner0, hcorner1, hcorner2]
  rw [InnerProductGeometry.angle_comm y x]
  exact hsum

/-- Explicit geometric triangulation rows for the selected outer polygon.

The rows deliberately use actual triangle corner points and `AngleGeometry`
angles.  The two global fields are the honest triangulation obligations:
each triangle has angle sum `pi`, and the polygon's predecessor/current/
successor angle sum is exactly the sum of the triangle corner angles. -/
structure SimplePolygonInteriorAngleTriangulationRows
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) : Type (u + 1) where
  Triangle : Type u
  triangleFintype : Fintype Triangle
  boundaryLength_ge_three : 3 <= P.outerCycle.length
  triangleCount_eq_boundaryLength_sub_two :
    @Fintype.card Triangle triangleFintype = P.outerCycle.length - 2
  trianglePoint : Triangle -> Fin 3 -> PlanarInterface.Point
  triangleAngleSum_eq_pi :
    forall T : Triangle,
      Finset.sum (Finset.univ : Finset (Fin 3))
          (fun c => triangleCornerAngle (trianglePoint T) c) =
        Real.pi
  polygonInteriorAngleSum_eq_triangleAngleSum :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum P =
      letI := triangleFintype
      Finset.sum (Finset.univ : Finset Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => triangleCornerAngle (trianglePoint T) c))

namespace SimplePolygonInteriorAngleTriangulationRows

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

/-- Constructor for honest triangulation rows when each triangle is supplied
by actual corner points and one nonzero side.  The Euclidean `pi` angle-sum
field is discharged uniformly from mathlib's triangle theorem. -/
def ofNondegenerateTrianglePoints
    (boundaryLength_ge_three : 3 <= P.outerCycle.length)
    (Triangle : Type u) [Fintype Triangle]
    (triangleCount_eq_boundaryLength_sub_two :
      Fintype.card Triangle = P.outerCycle.length - 2)
    (trianglePoint : Triangle -> Fin 3 -> PlanarInterface.Point)
    (triangle_side_ne :
      forall T : Triangle,
        Ne
          (AngleGeometry.toVec
            (TriangleAngleFacts.vsub (trianglePoint T 2) (trianglePoint T 0)))
          0)
    (polygonInteriorAngleSum_eq_triangleAngleSum :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum P =
        Finset.sum (Finset.univ : Finset Triangle)
          (fun T =>
            Finset.sum (Finset.univ : Finset (Fin 3))
              (fun c => triangleCornerAngle (trianglePoint T) c))) :
    SimplePolygonInteriorAngleTriangulationRows.{u} P where
  Triangle := Triangle
  triangleFintype := inferInstance
  boundaryLength_ge_three := boundaryLength_ge_three
  triangleCount_eq_boundaryLength_sub_two := by
    simpa using triangleCount_eq_boundaryLength_sub_two
  trianglePoint := trianglePoint
  triangleAngleSum_eq_pi := fun T =>
    triangleCornerAngleSum_eq_pi_of_toVec_vsub_ne_zero
      (trianglePoint T) (triangle_side_ne T)
  polygonInteriorAngleSum_eq_triangleAngleSum := by
    simpa using polygonInteriorAngleSum_eq_triangleAngleSum

/-- A triangulation with `length - 2` genuine triangles gives exactly the
cycle-length polygon angle sum. -/
theorem triangleAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : SimplePolygonInteriorAngleTriangulationRows.{u} P) :
    letI := R.triangleFintype
    Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => triangleCornerAngle (R.trianglePoint T) c)) =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum P := by
  classical
  letI := R.triangleFintype
  have htwo : 2 <= P.outerCycle.length :=
    Nat.le_trans (by norm_num) R.boundaryLength_ge_three
  calc
    Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => triangleCornerAngle (R.trianglePoint T) c)) =
        Finset.sum (Finset.univ : Finset R.Triangle) (fun _ => Real.pi) := by
          exact Finset.sum_congr rfl
            (fun T _ => R.triangleAngleSum_eq_pi T)
    _ = (Fintype.card R.Triangle : Real) * Real.pi := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ((P.outerCycle.length - 2 : Nat) : Real) * Real.pi := by
          rw [R.triangleCount_eq_boundaryLength_sub_two]
    _ = Real.pi * ((P.outerCycle.length : Real) - 2) := by
          rw [Nat.cast_sub htwo]
          ring
    _ = BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum P := by
          rfl

/-- Checked reduction of the W10 polygon-angle theorem to honest
triangulation rows for the selected outer polygon. -/
theorem simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : SimplePolygonInteriorAngleTriangulationRows.{u} P) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum P =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum P := by
  classical
  rw [R.polygonInteriorAngleSum_eq_triangleAngleSum]
  exact R.triangleAngleSum_eq_boundaryCyclePolygonAngleSum

/-- The inequality form consumed by
`BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum`. -/
theorem simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
    (R : SimplePolygonInteriorAngleTriangulationRows.{u} P) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum P <=
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum P :=
  le_of_eq R.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Honest triangulation rows supply W10's canonical predecessor/current/
successor boundary-sector package. -/
def toBoundaryNeighborSectorAngleSumRows
    (R : SimplePolygonInteriorAngleTriangulationRows.{u} P) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows P :=
  BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum
      R.boundaryLength_ge_three
      R.simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum

/-- Upstream outer-core triangulation rows are the same actual angle data as
the local simple-polygon triangulation rows.  This constructor keeps the
native subpolygon/core source as the triangulation source and only translates
the duplicate triangle-corner-angle spelling used in this downstream file. -/
def ofCoreOuterBoundaryInteriorAngleTriangulationRows
    (R : SubpolygonDataConcrete.CoreOuterBoundaryInteriorAngleTriangulationRows.{u}
      P) :
    SimplePolygonInteriorAngleTriangulationRows.{u} P where
  Triangle := R.Triangle
  triangleFintype := R.triangleFintype
  boundaryLength_ge_three := R.boundaryLength_ge_three
  triangleCount_eq_boundaryLength_sub_two :=
    R.triangleCount_eq_boundaryLength_sub_two
  trianglePoint := R.trianglePoint
  triangleAngleSum_eq_pi := by
    intro T
    simpa [triangleCornerAngle, SubpolygonAngleRealization.triangleCornerAngle,
      triangleCornerPrev, triangleCornerNext,
      SubpolygonAngleRealization.triangleCornerPrev,
      SubpolygonAngleRealization.triangleCornerNext] using
        R.triangleAngleSum_eq_pi T
  polygonInteriorAngleSum_eq_triangleAngleSum := by
    simpa [triangleCornerAngle, SubpolygonAngleRealization.triangleCornerAngle,
      triangleCornerPrev, triangleCornerNext,
      SubpolygonAngleRealization.triangleCornerPrev,
      SubpolygonAngleRealization.triangleCornerNext] using
        R.simplePolygonInteriorAngleSum_eq_triangleAngleSum

end SimplePolygonInteriorAngleTriangulationRows

/-- Actual nondegenerate triangle-point data for the selected outer-boundary
simple polygon.  The per-triangle `pi` angle sums are intentionally absent:
they are proved from `triangle_side_ne` by
`SimplePolygonInteriorAngleTriangulationRows.ofNondegenerateTrianglePoints`. -/
structure SelectedOuterBoundaryNondegenerateTrianglePointRows
    (topology : MissingTopologyFacts C) : Type (u + 1) where
  boundaryLength_ge_three : 3 <= topology.toCore.outerCycle.length
  Triangle : Type u
  triangleFintype : Fintype Triangle
  triangleCount_eq_boundaryLength_sub_two :
    @Fintype.card Triangle triangleFintype =
      topology.toCore.outerCycle.length - 2
  trianglePoint : Triangle -> Fin 3 -> PlanarInterface.Point
  triangle_side_ne :
    forall T : Triangle,
      Ne
        (AngleGeometry.toVec
          (TriangleAngleFacts.vsub (trianglePoint T 2) (trianglePoint T 0)))
        0
  polygonInteriorAngleSum_eq_triangleAngleSum :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore =
      letI := triangleFintype
      Finset.sum (Finset.univ : Finset Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c => triangleCornerAngle (trianglePoint T) c))

namespace SelectedOuterBoundaryNondegenerateTrianglePointRows

variable {topology : MissingTopologyFacts C}

/-- The actual triangle-corner angles carried by selected outer-boundary
point rows are nonnegative. -/
theorem triangleCornerAngle_nonnegative
    (R : SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology)
    (T : R.Triangle) (c : Fin 3) :
    0 <= triangleCornerAngle (R.trianglePoint T) c := by
  exact AngleGeometry.angleAt_nonneg _ _ _

/-- Build selected outer-boundary triangle-point rows when each triangle
corner is specified by an index of the selected outer cycle.

The only nondegeneracy input is the core-polygon fact that the third and first
corner indices of each triangle are distinct; the resulting nonzero side
vector is proved from the selected boundary's vertex injectivity and the
ambient separation condition. -/
def ofCorePolygonTriangleVertices
    (boundaryLength_ge_three : 3 <= topology.toCore.outerCycle.length)
    (Triangle : Type u) [Fintype Triangle]
    (triangleCount_eq_boundaryLength_sub_two :
      Fintype.card Triangle = topology.toCore.outerCycle.length - 2)
    (triangleVertex :
      Triangle -> Fin 3 -> Fin topology.toCore.outerCycle.length)
    (triangle_side_index_ne :
      forall T : Triangle, triangleVertex T 2 ≠ triangleVertex T 0)
    (polygonInteriorAngleSum_eq_triangleAngleSum :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
          topology.toCore =
        Finset.sum (Finset.univ : Finset Triangle)
          (fun T =>
            Finset.sum (Finset.univ : Finset (Fin 3))
              (fun c =>
                triangleCornerAngle
                  (fun d => topology.toCore.outerCycle.point (triangleVertex T d))
                  c))) :
    SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology where
  boundaryLength_ge_three := boundaryLength_ge_three
  Triangle := Triangle
  triangleFintype := inferInstance
  triangleCount_eq_boundaryLength_sub_two := by
    simpa using triangleCount_eq_boundaryLength_sub_two
  trianglePoint := fun T c =>
    topology.toCore.outerCycle.point (triangleVertex T c)
  triangle_side_ne := fun T =>
    toVec_vsub_ne_zero_of_ne
      (boundaryCycle_point_ne_of_index_ne topology.toCore.outerCycle
        (triangle_side_index_ne T))
  polygonInteriorAngleSum_eq_triangleAngleSum := by
    simpa using polygonInteriorAngleSum_eq_triangleAngleSum

/-- Consume the nondegenerate triangle-point data by building the local
simple-polygon triangulation rows. -/
def toSimplePolygonInteriorAngleTriangulationRows
    (R : SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology) :
    SimplePolygonInteriorAngleTriangulationRows.{u} topology.toCore := by
  letI := R.triangleFintype
  exact
    SimplePolygonInteriorAngleTriangulationRows.ofNondegenerateTrianglePoints
      (P := topology.toCore)
      R.boundaryLength_ge_three
      R.Triangle
      (by simpa using R.triangleCount_eq_boundaryLength_sub_two)
      R.trianglePoint
      R.triangle_side_ne
      (by simpa using R.polygonInteriorAngleSum_eq_triangleAngleSum)

/-- Selected outer-boundary point rows prove the W10 simple-polygon
angle-sum theorem for the same outer core. -/
theorem simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore :=
  R.toSimplePolygonInteriorAngleTriangulationRows
    |>.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Inequality form of the selected outer-boundary polygon-angle theorem from
actual nondegenerate triangle points. -/
theorem simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore <=
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore :=
  le_of_eq R.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Actual nondegenerate triangle points supply W10's canonical
predecessor/current/successor boundary-sector package for the selected outer
boundary. -/
def toBoundaryNeighborSectorAngleSumRows
    (R : SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
      topology.toCore :=
  R.toSimplePolygonInteriorAngleTriangulationRows
    |>.toBoundaryNeighborSectorAngleSumRows

end SelectedOuterBoundaryNondegenerateTrianglePointRows

/-- Genuine outer-cycle triangulation source rows for the selected boundary.

The triangles are specified by indices of the actual outer cycle, not by a
generated scalar budget.  The nondegeneracy field records the one distinct
outer-cycle side needed to turn each indexed triangle into concrete
nondegenerate point rows; the remaining global field is the real compatibility
between the PCS simple-polygon angle sum and the triangle-corner angle sum. -/
structure SelectedOuterBoundaryCorePolygonTriangulationRows
    (topology : MissingTopologyFacts C) : Type (u + 1) where
  boundaryLength_ge_three : 3 <= topology.toCore.outerCycle.length
  Triangle : Type u
  triangleFintype : Fintype Triangle
  triangleCount_eq_boundaryLength_sub_two :
    @Fintype.card Triangle triangleFintype =
      topology.toCore.outerCycle.length - 2
  triangleVertex :
    Triangle -> Fin 3 -> Fin topology.toCore.outerCycle.length
  triangle_side_index_ne :
    forall T : Triangle, triangleVertex T 2 ≠ triangleVertex T 0
  polygonInteriorAngleSum_eq_triangleAngleSum :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore =
      letI := triangleFintype
      Finset.sum (Finset.univ : Finset Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c =>
              triangleCornerAngle
                (fun d => topology.toCore.outerCycle.point (triangleVertex T d))
                c))

namespace SelectedOuterBoundaryCorePolygonTriangulationRows

variable {topology : MissingTopologyFacts C}

/-- The actual corner angle carried by an indexed outer-cycle triangulation
row. -/
def triangleAngle
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology)
    (T : R.Triangle) (c : Fin 3) : Real :=
  triangleCornerAngle
    (fun d => topology.toCore.outerCycle.point (R.triangleVertex T d)) c

/-- Indexed triangulation rows carry nonnegative actual triangle-corner
angles. -/
theorem triangleAngle_nonnegative
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology)
    (T : R.Triangle) (c : Fin 3) :
    0 <= R.triangleAngle T c := by
  exact AngleGeometry.angleAt_nonneg _ _ _

/-- Indexed triangulation rows close the Euclidean `pi` angle-sum field for
each actual nondegenerate triangle. -/
theorem triangleAngleSum_eq_pi
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology)
    (T : R.Triangle) :
    Finset.sum (Finset.univ : Finset (Fin 3)) (R.triangleAngle T) =
      Real.pi := by
  classical
  exact
    triangleCornerAngleSum_eq_pi_of_toVec_vsub_ne_zero
      (fun d => topology.toCore.outerCycle.point (R.triangleVertex T d))
      (toVec_vsub_ne_zero_of_ne
        (boundaryCycle_point_ne_of_index_ne topology.toCore.outerCycle
          (R.triangle_side_index_ne T)))

/-- Indexed outer-cycle triangulation rows yield the selected nondegenerate
triangle-point rows used by the S3 simple-polygon angle route. -/
def toSelectedOuterBoundaryNondegenerateTrianglePointRows
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology) :
    SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology := by
  letI := R.triangleFintype
  exact
    SelectedOuterBoundaryNondegenerateTrianglePointRows.ofCorePolygonTriangleVertices
      (topology := topology)
      R.boundaryLength_ge_three
      R.Triangle
      (by simpa using R.triangleCount_eq_boundaryLength_sub_two)
      R.triangleVertex
      R.triangle_side_index_ne
      (by simpa using R.polygonInteriorAngleSum_eq_triangleAngleSum)

/-- Indexed outer-cycle triangulation rows produce the honest local
simple-polygon triangulation package. -/
def toSimplePolygonInteriorAngleTriangulationRows
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology) :
    SimplePolygonInteriorAngleTriangulationRows.{u} topology.toCore :=
  R.toSelectedOuterBoundaryNondegenerateTrianglePointRows
    |>.toSimplePolygonInteriorAngleTriangulationRows

/-- Build selected indexed triangulation rows from the upstream actual
outer-core triangulation data once each triangle corner is identified with an
actual selected outer-cycle index.

The geometric angle fields come from
`SubpolygonDataConcrete.CoreOuterBoundaryInteriorAngleTriangulationRows`; the
only selected-core-specific inputs are the index realization of those points
and the nondegenerate side needed by the indexed selected row. -/
def ofCoreOuterBoundaryInteriorAngleTriangulationRows
    (R : SubpolygonDataConcrete.CoreOuterBoundaryInteriorAngleTriangulationRows.{u}
      topology.toCore)
    (triangleVertex :
      R.Triangle -> Fin 3 -> Fin topology.toCore.outerCycle.length)
    (trianglePoint_eq :
      forall (T : R.Triangle) (c : Fin 3),
        R.trianglePoint T c =
          topology.toCore.outerCycle.point (triangleVertex T c))
    (triangle_side_index_ne :
      forall T : R.Triangle, triangleVertex T 2 ≠ triangleVertex T 0) :
    SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology := by
  classical
  letI := R.triangleFintype
  refine
    { boundaryLength_ge_three := R.boundaryLength_ge_three
      Triangle := R.Triangle
      triangleFintype := R.triangleFintype
      triangleCount_eq_boundaryLength_sub_two :=
        R.triangleCount_eq_boundaryLength_sub_two
      triangleVertex := triangleVertex
      triangle_side_index_ne := triangle_side_index_ne
      polygonInteriorAngleSum_eq_triangleAngleSum := ?_ }
  calc
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore =
      Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c =>
              SubpolygonAngleRealization.triangleCornerAngle
                (R.trianglePoint T) c)) := by
          simpa using R.simplePolygonInteriorAngleSum_eq_triangleAngleSum
    _ =
      Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c =>
              triangleCornerAngle
                (fun d =>
                  topology.toCore.outerCycle.point (triangleVertex T d))
                c)) := by
          apply Finset.sum_congr rfl
          intro T _hT
          apply Finset.sum_congr rfl
          intro c _hc
          simp [triangleCornerAngle, SubpolygonAngleRealization.triangleCornerAngle,
            triangleCornerPrev, triangleCornerNext,
            SubpolygonAngleRealization.triangleCornerPrev,
            SubpolygonAngleRealization.triangleCornerNext, trianglePoint_eq]

/-- The concrete triangle-corner sum of indexed outer-cycle triangulation rows
is the cycle-length polygon angle sum. -/
theorem triangleAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology) :
    letI := R.triangleFintype
    Finset.sum (Finset.univ : Finset R.Triangle)
        (fun T =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c =>
              triangleCornerAngle
                (fun d => topology.toCore.outerCycle.point (R.triangleVertex T d))
                c)) =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore := by
  classical
  letI := R.triangleFintype
  simpa using
    R.toSimplePolygonInteriorAngleTriangulationRows
      |>.triangleAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Indexed outer-cycle triangulation rows give the genuine simple-polygon
interior-angle equality needed by the selected nondegenerate S3 route. -/
theorem simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore :=
  R.toSimplePolygonInteriorAngleTriangulationRows
    |>.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Inequality form of the indexed outer-cycle triangulation theorem, matching
`SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows` pointwise. -/
theorem simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore <=
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore :=
  le_of_eq R.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Indexed outer-cycle triangulation rows supply W10's canonical
predecessor/current/successor boundary-sector package. -/
def toBoundaryNeighborSectorAngleSumRows
    (R : SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
      topology.toCore := by
  letI := R.triangleFintype
  exact
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfTriangulationAngleSum
      (P := topology.toCore)
      R.boundaryLength_ge_three
      (by
        simpa using R.triangleCount_eq_boundaryLength_sub_two)
      (fun T c => R.triangleAngle T c)
      (fun T => R.triangleAngleSum_eq_pi T)
      (by
        simpa [triangleAngle] using
          R.polygonInteriorAngleSum_eq_triangleAngleSum)

end SelectedOuterBoundaryCorePolygonTriangulationRows

/-- The three indexed corners of one selected outer-boundary ear triangle.

The order is previous boundary vertex, ear tip, next boundary vertex. -/
def earTriangleVertex
    {m : Nat} (prev tip next : Fin m) : Fin 3 -> Fin m :=
  fun c =>
    if c = (0 : Fin 3) then prev
    else if c = (1 : Fin 3) then tip
    else next

@[simp]
theorem earTriangleVertex_zero
    {m : Nat} (prev tip next : Fin m) :
    earTriangleVertex prev tip next 0 = prev := by
  simp [earTriangleVertex]

@[simp]
theorem earTriangleVertex_one
    {m : Nat} (prev tip next : Fin m) :
    earTriangleVertex prev tip next 1 = tip := by
  simp [earTriangleVertex]

@[simp]
theorem earTriangleVertex_two
    {m : Nat} (prev tip next : Fin m) :
    earTriangleVertex prev tip next 2 = next := by
  simp [earTriangleVertex]

/-- Precise ear-decomposition source rows for the selected outer polygon.

Each ear is recorded by actual indices of the selected outer cycle, together
with distinctness of the three corners and the real equality between the
predecessor/current/successor polygon-angle sum and the sum of the ear triangle
corner angles.  This is the exact geometric payload needed to build the
stronger indexed triangulation rows, without generated scalar budgets. -/
structure SelectedOuterBoundaryCorePolygonEarDecompositionRows
    (topology : MissingTopologyFacts C) : Type (u + 1) where
  boundaryLength_ge_three : 3 <= topology.toCore.outerCycle.length
  Ear : Type u
  earFintype : Fintype Ear
  earCount_eq_boundaryLength_sub_two :
    @Fintype.card Ear earFintype =
      topology.toCore.outerCycle.length - 2
  earPrev : Ear -> Fin topology.toCore.outerCycle.length
  earTip : Ear -> Fin topology.toCore.outerCycle.length
  earNext : Ear -> Fin topology.toCore.outerCycle.length
  earPrev_ne_earTip :
    forall E : Ear, earPrev E ≠ earTip E
  earTip_ne_earNext :
    forall E : Ear, earTip E ≠ earNext E
  earNext_ne_earPrev :
    forall E : Ear, earNext E ≠ earPrev E
  polygonInteriorAngleSum_eq_earAngleSum :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore =
      letI := earFintype
      Finset.sum (Finset.univ : Finset Ear)
        (fun E =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c =>
              triangleCornerAngle
                (fun d =>
                  topology.toCore.outerCycle.point
                    (earTriangleVertex (earPrev E) (earTip E) (earNext E) d))
                c))

namespace SelectedOuterBoundaryCorePolygonEarDecompositionRows

variable {topology : MissingTopologyFacts C}

/-- The actual angle at a corner of an ear triangle in the selected outer
cycle. -/
def earAngle
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology)
    (E : R.Ear) (c : Fin 3) : Real :=
  triangleCornerAngle
    (fun d =>
      topology.toCore.outerCycle.point
        (earTriangleVertex (R.earPrev E) (R.earTip E) (R.earNext E) d))
    c

/-- Ear-decomposition rows carry nonnegative actual triangle-corner angles. -/
theorem earAngle_nonnegative
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology)
    (E : R.Ear) (c : Fin 3) :
    0 <= R.earAngle E c := by
  exact AngleGeometry.angleAt_nonneg _ _ _

/-- The actual angle sum of each nondegenerate ear triangle is `pi`. -/
theorem earAngleSum_eq_pi
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology)
    (E : R.Ear) :
    Finset.sum (Finset.univ : Finset (Fin 3)) (R.earAngle E) =
      Real.pi := by
  classical
  exact
    triangleCornerAngleSum_eq_pi_of_toVec_vsub_ne_zero
      (fun d =>
        topology.toCore.outerCycle.point
          (earTriangleVertex (R.earPrev E) (R.earTip E) (R.earNext E) d))
      (toVec_vsub_ne_zero_of_ne
        (boundaryCycle_point_ne_of_index_ne topology.toCore.outerCycle
          (R.earNext_ne_earPrev E)))

/-- Ear-decomposition rows construct the strongest selected outer-boundary
core polygon triangulation rows. -/
def toSelectedOuterBoundaryCorePolygonTriangulationRows
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology) :
    SelectedOuterBoundaryCorePolygonTriangulationRows.{u} topology := by
  letI := R.earFintype
  exact
    { boundaryLength_ge_three := R.boundaryLength_ge_three
      Triangle := R.Ear
      triangleFintype := R.earFintype
      triangleCount_eq_boundaryLength_sub_two := by
        simpa using R.earCount_eq_boundaryLength_sub_two
      triangleVertex := fun E =>
        earTriangleVertex (R.earPrev E) (R.earTip E) (R.earNext E)
      triangle_side_index_ne := fun E => by
        simpa using R.earNext_ne_earPrev E
      polygonInteriorAngleSum_eq_triangleAngleSum := by
        simpa using R.polygonInteriorAngleSum_eq_earAngleSum }

/-- Ear-decomposition rows yield the selected nondegenerate triangle-point
rows used by the S3 simple-polygon angle route. -/
def toSelectedOuterBoundaryNondegenerateTrianglePointRows
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology) :
    SelectedOuterBoundaryNondegenerateTrianglePointRows.{u} topology :=
  R.toSelectedOuterBoundaryCorePolygonTriangulationRows
    |>.toSelectedOuterBoundaryNondegenerateTrianglePointRows

/-- Ear-decomposition rows produce the local simple-polygon triangulation
package. -/
def toSimplePolygonInteriorAngleTriangulationRows
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology) :
    SimplePolygonInteriorAngleTriangulationRows.{u} topology.toCore :=
  R.toSelectedOuterBoundaryCorePolygonTriangulationRows
    |>.toSimplePolygonInteriorAngleTriangulationRows

/-- The concrete ear-angle sum is the cycle-length polygon angle sum. -/
theorem earAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology) :
    letI := R.earFintype
    Finset.sum (Finset.univ : Finset R.Ear)
        (fun E =>
          Finset.sum (Finset.univ : Finset (Fin 3))
            (fun c =>
              triangleCornerAngle
                (fun d =>
                  topology.toCore.outerCycle.point
                    (earTriangleVertex (R.earPrev E) (R.earTip E) (R.earNext E) d))
                c)) =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore := by
  classical
  letI := R.earFintype
  simpa using
    R.toSelectedOuterBoundaryCorePolygonTriangulationRows
      |>.triangleAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Ear-decomposition rows give the genuine selected simple-polygon
interior-angle equality. -/
theorem simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore =
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore :=
  R.toSelectedOuterBoundaryCorePolygonTriangulationRows
    |>.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Inequality form of the ear-decomposition polygon-angle theorem. -/
theorem simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.simplePolygonInteriorAngleSum
        topology.toCore <=
      BoundaryCountingInstantiationW10.ClassifiedBoundary.boundaryCyclePolygonAngleSum
        topology.toCore :=
  le_of_eq R.simplePolygonInteriorAngleSum_eq_boundaryCyclePolygonAngleSum

/-- Ear-decomposition rows supply W10's canonical predecessor/current/
successor boundary-sector package. -/
def toBoundaryNeighborSectorAngleSumRows
    (R : SelectedOuterBoundaryCorePolygonEarDecompositionRows.{u} topology) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows
      topology.toCore := by
  letI := R.earFintype
  exact
    BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfTriangulationAngleSum
      (P := topology.toCore)
      R.boundaryLength_ge_three
      (by
        simpa using R.earCount_eq_boundaryLength_sub_two)
      (fun E c => R.earAngle E c)
      (fun E => R.earAngleSum_eq_pi E)
      (by
        simpa [earAngle] using R.polygonInteriorAngleSum_eq_earAngleSum)

end SelectedOuterBoundaryCorePolygonEarDecompositionRows

/-- Concrete row-wise constructor for the remaining generated-classification
angle premise.  The inputs are exactly the unit-separated angle rows indexed by
the boundary classes, plus the accounted-angle polygon comparison. -/
def unitSeparatedAngleFamiliesOfMinimalFailureSeparationRows
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (degree3 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree3Indices ->
        Fin 2 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (degree4 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree4Indices ->
        Fin 3 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (degree5 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree5Indices ->
        Fin 4 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (degree6 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree6Indices ->
        Fin 5 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (nontriangle :
      (selectedClassificationOfMinimalFailure topology hmin longArc).nontriangleEdgeIndices ->
        Fin 1 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (longArcAngle :
      (selectedClassificationOfMinimalFailure topology hmin longArc).longArcIndices ->
        Fin 1 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (accounted_le_polygon :
      ({ degree3 := degree3
         degree4 := degree4
         degree5 := degree5
         degree6 := degree6
         nontriangle := nontriangle
         longArc := longArcAngle } :
        UnitSeparatedLocalAngleFamiliesOfMinimalFailure
          topology hmin longArc).accountedAngleSum <=
        (selectedClassificationOfMinimalFailure
          topology hmin longArc).counts.polygonAngleSum) :
    BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
      (selectedClassificationOfMinimalFailure topology hmin longArc) :=
  unitSeparatedAngleFamiliesOfMinimalFailureLocalAngles
    topology hmin longArc
    { degree3 := degree3
      degree4 := degree4
      degree5 := degree5
      degree6 := degree6
      nontriangle := nontriangle
      longArc := longArcAngle }
    accounted_le_polygon

/-- Feed concrete local unit-separated angle rows directly into the
minimal-failure selected-classification face-data constructor. -/
def ofMinimalFailureSelectedClassificationLocalAngles
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (localAngles :
      UnitSeparatedLocalAngleFamiliesOfMinimalFailure topology hmin longArc)
    (accounted_le_polygon :
      localAngles.accountedAngleSum <=
        (selectedClassificationOfMinimalFailure
          topology hmin longArc).counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceData.{u} C :=
  ofMinimalFailureSelectedClassification topology hmin longArc
    (unitSeparatedAngleFamiliesOfMinimalFailureLocalAngles
      topology hmin longArc localAngles accounted_le_polygon)
    Subpolygon subpolygonData

/-- Row-wise version of
`ofMinimalFailureSelectedClassificationLocalAngles`, exposing the concrete
unit-distance separation rows instead of the bundled local row package. -/
def ofMinimalFailureSelectedClassificationSeparationRows
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (degree3 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree3Indices ->
        Fin 2 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (degree4 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree4Indices ->
        Fin 3 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (degree5 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree5Indices ->
        Fin 4 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (degree6 :
      (selectedClassificationOfMinimalFailure topology hmin longArc).degree6Indices ->
        Fin 5 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (nontriangle :
      (selectedClassificationOfMinimalFailure topology hmin longArc).nontriangleEdgeIndices ->
        Fin 1 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (longArcAngle :
      (selectedClassificationOfMinimalFailure topology hmin longArc).longArcIndices ->
        Fin 1 -> BoundaryAngleWitnessConstruction.UnitSeparatedAngle
          (CanonicalGraph C))
    (accounted_le_polygon :
      ({ degree3 := degree3
         degree4 := degree4
         degree5 := degree5
         degree6 := degree6
         nontriangle := nontriangle
         longArc := longArcAngle } :
        UnitSeparatedLocalAngleFamiliesOfMinimalFailure
          topology hmin longArc).accountedAngleSum <=
        (selectedClassificationOfMinimalFailure
          topology hmin longArc).counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    PlanarBoundaryFaceData.{u} C :=
  ofMinimalFailureSelectedClassification topology hmin longArc
    (unitSeparatedAngleFamiliesOfMinimalFailureSeparationRows
      topology hmin longArc degree3 degree4 degree5 degree6 nontriangle
      longArcAngle accounted_le_polygon)
    Subpolygon subpolygonData

@[simp]
theorem ofSelectedClassification_minimalFailure
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassificationOfMinimalFailure topology hmin longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    ofSelectedClassification topology
        (selectedBoundary_degree_ge_three_of_minimalFailure topology hmin)
        longArc angleWitness Subpolygon subpolygonData =
      ofMinimalFailureSelectedClassification topology hmin longArc angleWitness
        Subpolygon subpolygonData :=
  rfl

@[simp]
theorem ofMinimalFailureSelectedClassification_topology
    (topology : MissingTopologyFacts C)
    (hmin : IsMinimalClearedFailure C)
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassificationOfMinimalFailure topology hmin longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofMinimalFailureSelectedClassification topology hmin longArc angleWitness
      Subpolygon subpolygonData).topology = topology :=
  rfl

@[simp]
theorem ofClassification_selectedClassification
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    ofClassification topology
        (selectedClassification topology degree_ge_three longArc)
        angleWitness Subpolygon subpolygonData =
      ofSelectedClassification topology degree_ge_three longArc angleWitness
        Subpolygon subpolygonData :=
  rfl

@[simp]
theorem ofSelectedClassification_topology
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofSelectedClassification topology degree_ge_three longArc angleWitness
      Subpolygon subpolygonData).topology = topology :=
  rfl

@[simp]
theorem ofSelectedClassification_core
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofSelectedClassification topology degree_ge_three longArc angleWitness
      Subpolygon subpolygonData).core = topology.toCore :=
  rfl

@[simp]
theorem ofSelectedClassification_outerAngleCounts
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofSelectedClassification topology degree_ge_three longArc angleWitness
      Subpolygon subpolygonData).outerAngleBounds.counts =
        (selectedClassification topology degree_ge_three longArc).counts :=
  rfl

@[simp]
theorem ofSelectedClassification_outerAngleBounds_countsRealization
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofSelectedClassification topology degree_ge_three longArc angleWitness
      Subpolygon subpolygonData).outerAngleBounds.countsRealization =
        (selectedClassification topology degree_ge_three longArc).countsRealizationLift :=
  rfl

@[simp]
theorem ofSelectedClassification_outerAngleBounds_bookkeeping
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofSelectedClassification topology degree_ge_three longArc angleWitness
      Subpolygon subpolygonData).outerAngleBounds.countsRealization.bookkeeping =
        (selectedClassification topology degree_ge_three longArc).countsRealizationLift.bookkeeping :=
  rfl

theorem ofSelectedClassification_angleLowerBound
    (topology : MissingTopologyFacts C)
    (degree_ge_three :
      forall k : Fin topology.toCore.outerCycle.length,
        3 <= BoundaryWalkClassificationConcrete.ambientDegree
          (CanonicalGraph C) (topology.toCore.outerCycle.vertex k))
    (longArc : Fin topology.toCore.outerCycle.length -> Prop)
    (angleWitness :
      BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedAngleFamilies
        (selectedClassification topology degree_ge_three longArc))
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C)) :
    (ofSelectedClassification topology degree_ge_three longArc angleWitness
      Subpolygon subpolygonData).outerAngleBounds.counts.AngleLowerBound := by
  simpa using angleWitness.angleLowerBound

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toPlanarBoundaryData.outerBoundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

/-! ### Boundary bookkeeping and realized count projections -/

/-- The finite boundary classification bookkeeping whose cardinalities realize
the outer-boundary count fields. -/
def boundaryBookkeeping
    (D : PlanarBoundaryFaceData.{u} C) :
    BoundaryClassification.BoundaryBookkeeping.{u} :=
  D.outerAngleBounds.countsRealization.bookkeeping

/-- The realization tying the finite boundary classification bookkeeping to
the `BoundaryCounts` used by the angle-counting layer. -/
def boundaryCountsRealization
    (D : PlanarBoundaryFaceData.{u} C) :
    BoundaryClassification.BoundaryCountsRealization.{u} :=
  D.outerAngleBounds.countsRealization

@[simp]
theorem boundaryCountsRealization_toBoundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryCountsRealization.toBoundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

/-- The finite boundary bookkeeping projects to the same `BoundaryCounts`
record supplied to the planar-boundary closure. -/
@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.toBoundaryCounts =
      D.outerAngleBounds.counts :=
  D.boundaryCountsRealization.realizes

@[simp]
theorem outerBoundaryCounts_d3
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d3 = D.boundaryBookkeeping.d3 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d4
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d4 = D.boundaryBookkeeping.d4 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d5
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d5 = D.boundaryBookkeeping.d5 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_d6
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d6 = D.boundaryBookkeeping.d6 := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_b
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.b = D.boundaryBookkeeping.b := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_B
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.B =
      D.boundaryBookkeeping.longArcCount := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

@[simp]
theorem outerBoundaryCounts_negativeCount
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.negativeCount =
      D.boundaryBookkeeping.negativeElementCount := by
  rw [← boundaryBookkeeping_toBoundaryCounts D]
  rfl

/-- The checked angle lower bound on the refined outer-boundary counts. -/
theorem boundaryAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.AngleLowerBound :=
  D.outerAngleBounds.angleLowerBound

/-- The same angle lower bound, pulled back to the finite bookkeeping
projection. -/
theorem boundaryBookkeepingAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.toBoundaryCounts.AngleLowerBound :=
  D.outerAngleBounds.projected_angleLowerBound

/-- E12 stated directly in the finite boundary-classification cardinalities. -/
theorem boundaryAngleCount_bookkeeping
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.d5 + 2 * D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.b + D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounting.BoundaryCounts.boundary_angle_count_inequality
      D.boundaryBookkeeping.toBoundaryCounts
      D.boundaryBookkeepingAngleLowerBound

/-- Negative-element E12 stated directly in finite boundary-classification
cardinalities. -/
theorem boundaryNegativeCount_bookkeeping
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.negativeElementCount +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.toBoundaryCounts] using
    BoundaryCounting.BoundaryCounts.boundary_negative_count_inequality
      D.boundaryBookkeeping.toBoundaryCounts
      D.boundaryBookkeepingAngleLowerBound

/-- Expanded negative-element E12 in the bookkeeping field names. -/
theorem boundaryNegativeCount_bookkeeping_expanded
    (D : PlanarBoundaryFaceData.{u} C) :
    D.boundaryBookkeeping.b + D.boundaryBookkeeping.d5 +
        D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 := by
  simpa [BoundaryClassification.BoundaryBookkeeping.negativeElementCount]
    using D.boundaryNegativeCount_bookkeeping

/-- The canonical outer-boundary count package extracted from the refined
face data. -/
def canonicalBoundaryCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses (CanonicalGraph C) :=
  D.toPlanarBoundaryData.canonicalBoundaryCountHypotheses

@[simp]
theorem canonicalBoundaryCountHypotheses_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.canonicalBoundaryCountHypotheses.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem canonicalBoundaryCountHypotheses_counts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.canonicalBoundaryCountHypotheses.counts =
      D.outerAngleBounds.counts :=
  rfl

/-- The canonical subpolygon count package extracted from the refined face
data. -/
def canonicalSubpolygonCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses (CanonicalGraph C) :=
  D.toPlanarBoundaryData.canonicalSubpolygonCountHypotheses S

@[simp]
theorem canonicalSubpolygonCountHypotheses_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.canonicalSubpolygonCountHypotheses S).faceBoundary =
      D.faceBoundary :=
  rfl

@[simp]
theorem canonicalSubpolygonCountHypotheses_counts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.canonicalSubpolygonCountHypotheses S).counts =
      (D.subpolygonData S).counts :=
  rfl

/-- The existing combined face-counting bridge interface obtained from the
refined face data. -/
def toFaceCountingBridgeData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.FaceCountingBridgeData.{u} (CanonicalGraph C) :=
  D.toPlanarBoundaryData.toFaceCountingBridgeData

@[simp]
theorem toFaceCountingBridgeData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_planarFaceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.planarFaceBoundary =
      D.planarFaceBoundary :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_boundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.boundaryCounts =
      D.canonicalBoundaryCountHypotheses :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_outerCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.outerCounts =
      D.outerAngleBounds.counts :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_Subpolygon
    (D : PlanarBoundaryFaceData.{u} C) :
    D.toFaceCountingBridgeData.Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonCounts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.toFaceCountingBridgeData.subpolygonCounts S =
      D.canonicalSubpolygonCountHypotheses S :=
  rfl

@[simp]
theorem toFaceCountingBridgeData_subpolygonDegreeCounts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.toFaceCountingBridgeData.subpolygonDegreeCounts S =
      (D.subpolygonData S).counts :=
  rfl

theorem toFaceCountingBridgeData_countingTheorems
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.FaceCountingBridgeData.CountingTheorems
      D.toFaceCountingBridgeData :=
  D.toFaceCountingBridgeData.countingTheorems

/-- Concrete face-counting data extracted from the refined package. -/
def concreteFaceCountingData
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      D.toPlanarBoundaryData :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
    D.toPlanarBoundaryData

@[simp]
theorem concreteFaceCountingData_faceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_planarFaceBoundary
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.planarFaceBoundary =
      D.planarFaceBoundary :=
  rfl

@[simp]
theorem concreteFaceCountingData_pairwiseNoncrossing
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.pairwiseNoncrossing =
      D.pairwiseNoncrossing :=
  rfl

@[simp]
theorem concreteFaceCountingData_outerFace
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.outerFace = D.outerFace :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCounts
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.boundaryCounts =
      D.outerAngleBounds.counts :=
  rfl

@[simp]
theorem concreteFaceCountingData_boundaryCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.boundaryCountHypotheses =
      D.canonicalBoundaryCountHypotheses :=
  rfl

/-- The concrete face-counting package retains the checked boundary angle
lower bound on the refined outer counts. -/
theorem concreteFaceCountingData_boundaryAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.boundaryCounts.AngleLowerBound :=
  D.concreteFaceCountingData.boundaryAngleLowerBound

@[simp]
theorem concreteFaceCountingData_Subpolygon
    (D : PlanarBoundaryFaceData.{u} C) :
    D.concreteFaceCountingData.Subpolygon = D.Subpolygon :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCounts
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.concreteFaceCountingData.subpolygonCounts S =
      (D.subpolygonData S).counts :=
  rfl

@[simp]
theorem concreteFaceCountingData_subpolygonCountHypotheses
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    D.concreteFaceCountingData.subpolygonCountHypotheses S =
      D.canonicalSubpolygonCountHypotheses S :=
  rfl

/-- The checked subpolygon angle lower bound carried by the refined package. -/
theorem subpolygonAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.AngleLowerBound :=
  (D.subpolygonData S).angleLowerBound

/-- The concrete face-counting package retains every checked subpolygon angle
lower bound. -/
theorem concreteFaceCountingData_subpolygonAngleLowerBound
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.concreteFaceCountingData.subpolygonCounts S).AngleLowerBound :=
  D.concreteFaceCountingData.subpolygonAngleLowerBound S

/-- The E12 count conclusion from the refined face data. -/
theorem boundaryAngleCount
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.d5 + 2 * D.outerAngleBounds.counts.d6 +
        D.outerAngleBounds.counts.b + D.outerAngleBounds.counts.B + 6 <=
      D.outerAngleBounds.counts.d3 :=
  D.concreteFaceCountingData.boundaryAngleCount

/-- The negative-element E12 count conclusion from the refined face data. -/
theorem boundaryNegativeCount
    (D : PlanarBoundaryFaceData.{u} C) :
    D.outerAngleBounds.counts.negativeCount +
        D.outerAngleBounds.counts.B + 6 <=
      D.outerAngleBounds.counts.d3 :=
  D.concreteFaceCountingData.boundaryNegativeCount

/-- The E13 high-degree-slack conclusion for each supplied subpolygon. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    (D.subpolygonData S).counts.D5 +
        2 * (D.subpolygonData S).counts.D6 + 6 <=
      2 * (D.subpolygonData S).counts.D2 +
        (D.subpolygonData S).counts.D3 :=
  D.concreteFaceCountingData.subpolygonLowDegreeWithHighDegreeSlack S

/-- The Lemma 4 low-degree conclusion for each supplied subpolygon. -/
theorem subpolygonLowDegree
    (D : PlanarBoundaryFaceData.{u} C) (S : D.Subpolygon) :
    6 <= 2 * (D.subpolygonData S).counts.D2 +
      (D.subpolygonData S).counts.D3 :=
  D.concreteFaceCountingData.subpolygonLowDegree S

/-- Proposition-valued face-counting conclusions for the refined package. -/
theorem faceCountingTheorems
    (D : PlanarBoundaryFaceData.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.toPlanarBoundaryData :=
  PlanarBoundaryFinal.PlanarBoundaryData.faceCountingTheorems_of_concreteData
    D.toPlanarBoundaryData

end PlanarBoundaryFaceData

/-! ## Projection into the M8 boundary route -/

/--
Refined face/boundary data plus the still-explicit boundary-label inputs
needed by the `m = 8` route.
-/
structure M8RefinedBoundaryRouteData
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  faceData : PlanarBoundaryFaceData.{u} C
  connectedNoCut : PreconnectedNoCutVertexCertificate C
  spine :
    M8BoundarySpine
      (boundaryCutDegreeContextOfPlanarBoundary
        faceData.toPlanarBoundaryData connectedNoCut hmin)
  lemma8 : M8Lemma8Combinatorics spine

namespace M8RefinedBoundaryRouteData

variable {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

/-- The planar-boundary package obtained from the refined face data. -/
def planarBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  D.faceData.toPlanarBoundaryData

@[simp]
theorem planarBoundary_eq_faceData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.planarBoundary = D.faceData.toPlanarBoundaryData :=
  rfl

/-- The structural M8 context determined by the refined face data. -/
def context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryCutDegreeContext C :=
  boundaryCutDegreeContextOfPlanarBoundary
    D.planarBoundary D.connectedNoCut hmin

@[simp]
theorem context_outerBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary = D.faceData.core :=
  rfl

@[simp]
theorem context_faceBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary.faceBoundary = D.faceData.faceBoundary :=
  rfl

@[simp]
theorem context_outerFace
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.context.outerBoundary.outerFace = D.faceData.outerFace :=
  rfl

/-- The checked face-counting fields determined by the refined face data. -/
def faceCounting
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryFaceCountingFields D.planarBoundary D.context :=
  planarBoundaryFaceCountingFields
    D.planarBoundary D.connectedNoCut hmin

@[simp]
theorem faceCounting_concrete
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete = D.faceData.concreteFaceCountingData :=
  rfl

@[simp]
theorem faceCounting_concrete_faceBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.faceBoundary = D.faceData.faceBoundary :=
  rfl

@[simp]
theorem faceCounting_concrete_boundaryCounts
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCounts =
      D.faceData.outerAngleBounds.counts :=
  rfl

@[simp]
theorem faceCounting_concrete_boundaryCountHypotheses
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.faceCounting.concrete.boundaryCountHypotheses =
      D.faceData.canonicalBoundaryCountHypotheses :=
  rfl

/-- Forget the refined wrapper to the existing M8 boundary route data. -/
def toM8BoundaryRouteData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryRouteData.{u} C hmin where
  planarBoundary := D.planarBoundary
  connectedNoCut := D.connectedNoCut
  spine := D.spine
  lemma8 := D.lemma8

@[simp]
theorem toM8BoundaryRouteData_planarBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.planarBoundary = D.planarBoundary :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_connectedNoCut
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.connectedNoCut = D.connectedNoCut :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_spine
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.spine = D.spine :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_lemma8
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.lemma8 = D.lemma8 :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context = D.context :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_faceBoundary
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context.outerBoundary.faceBoundary =
      D.faceData.faceBoundary :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_outerFace
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.context.outerBoundary.outerFace =
      D.faceData.outerFace :=
  rfl

@[simp]
theorem toM8BoundaryRouteData_faceCounting_concrete
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete =
      D.faceData.concreteFaceCountingData :=
  rfl

/-! ### Boundary bookkeeping and count projections along the route -/

/-- The finite boundary classification bookkeeping carried by the refined M8
route. -/
def boundaryBookkeeping
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    BoundaryClassification.BoundaryBookkeeping.{u} :=
  D.faceData.boundaryBookkeeping

/-- The realization tying the route's boundary classifications to the concrete
outer-boundary counts. -/
def boundaryCountsRealization
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    BoundaryClassification.BoundaryCountsRealization.{u} :=
  D.faceData.boundaryCountsRealization

@[simp]
theorem boundaryBookkeeping_eq_faceData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping = D.faceData.boundaryBookkeeping :=
  rfl

@[simp]
theorem boundaryCountsRealization_eq_faceData
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryCountsRealization = D.faceData.boundaryCountsRealization :=
  rfl

@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.toBoundaryCounts =
      D.faceData.outerAngleBounds.counts :=
  D.faceData.boundaryBookkeeping_toBoundaryCounts

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d3
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 =
      D.boundaryBookkeeping.d3 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d4
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d4 =
      D.boundaryBookkeeping.d4 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d5
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d5 =
      D.boundaryBookkeeping.d5 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_d6
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d6 =
      D.boundaryBookkeeping.d6 := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_b
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.b =
      D.boundaryBookkeeping.b := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_B
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B =
      D.boundaryBookkeeping.longArcCount := by
  simp

@[simp]
theorem toM8BoundaryRouteData_boundaryCounts_negativeCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.negativeCount =
      D.boundaryBookkeeping.negativeElementCount := by
  simp

/-- The checked outer-boundary angle lower bound survives projection into the
M8 route's concrete face-counting package. -/
theorem boundaryAngleLowerBound
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.AngleLowerBound :=
  D.faceData.boundaryAngleLowerBound

/-- The route's finite bookkeeping carries the same checked angle lower
bound. -/
theorem boundaryBookkeepingAngleLowerBound
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.toBoundaryCounts.AngleLowerBound :=
  D.faceData.boundaryBookkeepingAngleLowerBound

/-- E12 on the refined M8 route, stated in finite boundary-classification
cardinalities. -/
theorem boundaryAngleCount_bookkeeping
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.d5 + 2 * D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.b + D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 :=
  D.faceData.boundaryAngleCount_bookkeeping

/-- Negative-element E12 on the refined M8 route, stated in finite
boundary-classification cardinalities. -/
theorem boundaryNegativeCount_bookkeeping
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.negativeElementCount +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 :=
  D.faceData.boundaryNegativeCount_bookkeeping

/-- Expanded negative-element E12 on the refined M8 route. -/
theorem boundaryNegativeCount_bookkeeping_expanded
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.boundaryBookkeeping.b + D.boundaryBookkeeping.d5 +
        D.boundaryBookkeeping.d6 +
        D.boundaryBookkeeping.longArcCount + 6 <=
      D.boundaryBookkeeping.d3 :=
  D.faceData.boundaryNegativeCount_bookkeeping_expanded

/-- The concrete boundary-label package obtained from the M8 route. -/
def toBoundaryLabelPackage
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8BoundaryLabelPackage C :=
  D.toM8BoundaryRouteData.toBoundaryLabelPackage

@[simp]
theorem toBoundaryLabelPackage_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.context = D.context :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_spine
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.spine = D.spine :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_lemma8
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toBoundaryLabelPackage.lemma8 = D.lemma8 :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_p
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8BoundaryIndex) :
    D.toBoundaryLabelPackage.labels.p i = D.spine.p i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_q
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8TriangleIndex) :
    D.toBoundaryLabelPackage.labels.q i = D.spine.q i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_r
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.toBoundaryLabelPackage.labels.r i = D.lemma8.r i :=
  rfl

@[simp]
theorem toBoundaryLabelPackage_labels_s
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (i : M8ExtraIndex) :
    D.toBoundaryLabelPackage.labels.s i = D.lemma8.s i :=
  rfl

/-- The local labels determined by the refined route. -/
def toM8LocalLabels
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    M8LocalLabels C :=
  D.toM8BoundaryRouteData.toM8LocalLabels

@[simp]
theorem toM8LocalLabels_eq
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8LocalLabels =
      D.toBoundaryLabelPackage.toM8LocalLabels :=
  rfl

@[simp]
theorem toM8LocalLabels_labels
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8LocalLabels.labels = D.toBoundaryLabelPackage.labels :=
  rfl

/-- The face-counting package in the route is exactly the one determined by
the refined planar-boundary data. -/
theorem route_faceCounting_eq
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting = D.faceCounting :=
  rfl

/-- The refined route carries the planar-boundary face-counting theorem
summary for the same projected planar-boundary package. -/
theorem faceCountingTheorems
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      D.planarBoundary :=
  D.faceData.faceCountingTheorems

/-- The route's canonical boundary-count package is attached to the same
face-boundary witness as the structural M8 context. -/
theorem boundaryCountHypotheses_faceBoundary_eq_context
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.faceBoundary =
      D.context.outerBoundary.faceBoundary :=
  D.toM8BoundaryRouteData.boundaryCountHypotheses_faceBoundary_eq_context

/-- The route's canonical boundary-count package uses exactly the route's
concrete outer-boundary counts. -/
theorem boundaryCountHypotheses_counts_eq_concrete
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.counts =
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts :=
  D.toM8BoundaryRouteData.boundaryCountHypotheses_counts_eq_concrete

/-- The route keeps the checked outer-boundary count package on the same
face-boundary witness supplied by the refined Jordan/topology data. -/
theorem boundaryCountHypotheses_faceBoundary_eq_refined
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.faceBoundary =
      D.faceData.faceBoundary :=
  rfl

@[simp]
theorem boundaryCountHypotheses_counts_eq_refined
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCountHypotheses.counts =
      D.faceData.outerAngleBounds.counts :=
  rfl

/-- The E12 count conclusion available after projecting to the M8 route. -/
theorem boundaryAngleCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d5 +
        2 * D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d6 +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.b +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 :=
  D.toM8BoundaryRouteData.boundaryAngleCount

/-- The negative-element E12 conclusion available after projecting to the M8
route. -/
theorem boundaryNegativeCount
    (D : M8RefinedBoundaryRouteData.{u} C hmin) :
    D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.negativeCount +
        D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.B + 6 <=
      D.toM8BoundaryRouteData.faceCounting.concrete.boundaryCounts.d3 :=
  D.toM8BoundaryRouteData.boundaryNegativeCount

/-- The E13 high-degree-slack conclusion after projecting to the refined
face data. -/
theorem subpolygonLowDegreeWithHighDegreeSlack
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (S : D.faceData.Subpolygon) :
    (D.faceData.subpolygonData S).counts.D5 +
        2 * (D.faceData.subpolygonData S).counts.D6 + 6 <=
      2 * (D.faceData.subpolygonData S).counts.D2 +
        (D.faceData.subpolygonData S).counts.D3 :=
  D.faceData.subpolygonLowDegreeWithHighDegreeSlack S

/-- The Lemma 4 low-degree conclusion after projecting to the refined face
data. -/
theorem subpolygonLowDegree
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (S : D.faceData.Subpolygon) :
    6 <= 2 * (D.faceData.subpolygonData S).counts.D2 +
      (D.faceData.subpolygonData S).counts.D3 :=
  D.faceData.subpolygonLowDegree S

/-- Assemble the existing clean M8 construction interface from the refined
route once the later M8 fields are supplied. -/
def toM8ConstructionData
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    M8ConstructionData C hmin :=
  D.toM8BoundaryRouteData.toM8ConstructionData
    turnBounds lateTriples windowGeometry

@[simp]
theorem toM8ConstructionData_localLabels
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData
      turnBounds lateTriples windowGeometry).localLabels =
        D.toM8LocalLabels :=
  rfl

@[simp]
theorem toM8ConstructionData_turnBounds
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    (D.toM8ConstructionData
      turnBounds lateTriples windowGeometry).turnBounds =
        turnBounds :=
  rfl

/-- Project the refined route to the existing broken-lattice minimal-failure
interface. -/
def toBrokenLatticeMinimalFailure
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  (D.toM8ConstructionData
    turnBounds lateTriples windowGeometry).toBrokenLatticeMinimalFailure

/-- Final conditional endpoint after projecting the refined route into the
existing M8 construction interface. -/
theorem contradiction
    (D : M8RefinedBoundaryRouteData.{u} C hmin)
    (turnBounds : M8TurnBounds)
    (lateTriples : M8LateTriples D.toM8LocalLabels)
    (windowGeometry : M8WindowGeometry D.toM8LocalLabels turnBounds) :
    False :=
  (D.toBrokenLatticeMinimalFailure
    turnBounds lateTriples windowGeometry).contradiction

end M8RefinedBoundaryRouteData

end

end PlanarBoundaryFaceDataRefinement
end Swanepoel
end ErdosProblems1066
