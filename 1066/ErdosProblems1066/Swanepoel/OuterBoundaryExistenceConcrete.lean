import ErdosProblems1066.Swanepoel.GraphBridge
import ErdosProblems1066.Swanepoel.NoncrossingUnitEdges
import ErdosProblems1066.Swanepoel.FaceReduction
import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstruction

set_option autoImplicit false

/-!
# Concrete outer-boundary existence bridge

This file records the checked part of the route from a concrete `UDConfig` to
the outer-boundary core construction target.

The graph-level input is fully concrete: the canonical graph is the
unit-distance graph of the configuration, its edges are the `GraphBridge`
finite unit-edge set, and noncrossing follows from the separated-unit-edge
obstruction.  The remaining field is therefore exactly the topology/core data:
face-boundary data, a chosen outer face, and enclosure predicates for that face.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryExistenceConcrete

open FaceReduction
open OuterBoundaryCoreConstruction
open OuterBoundaryInterface

noncomputable section

variable {n : Nat}

/-! ## Concrete canonical graph facts -/

/-- The canonical graph used by the outer-boundary construction target. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  OuterBoundaryCoreConstruction.canonicalGraph C

/-- The canonical graph stores exactly the `GraphBridge` unit-distance edges. -/
theorem canonicalGraph_edgeSet_eq_unitDistanceEdges
    (C : _root_.UDConfig n) :
    (canonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C :=
  rfl

/-- Membership in the canonical edge set is membership in the concrete
unit-distance edge set. -/
theorem mem_canonicalGraph_edgeSet_iff_unitDistanceEdges
    (C : _root_.UDConfig n) (e : PlanarInterface.Edge n) :
    e ∈ (canonicalGraph C).edgeSet <->
      e ∈ GraphBridge.unitDistanceEdges C := by
  rw [canonicalGraph_edgeSet_eq_unitDistanceEdges]

/-- Canonical edges are ordered in the concrete finite edge set. -/
theorem canonicalGraph_edge_ordered
    (C : _root_.UDConfig n) {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    e.1 < e.2 := by
  exact GraphBridge.unitDistanceEdges_ordered C
    ((mem_canonicalGraph_edgeSet_iff_unitDistanceEdges C e).1 he)

/-- Canonical edges are concrete unit-distance adjacencies. -/
theorem canonicalGraph_edge_unitDistanceAdj
    (C : _root_.UDConfig n) {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    GraphBridge.UnitDistanceAdj C e.1 e.2 := by
  exact PlanarInterface.mem_unitDistanceEdges_unitDistanceAdj C
    ((mem_canonicalGraph_edgeSet_iff_unitDistanceEdges C e).1 he)

/-- Canonical edges have Euclidean length one. -/
theorem canonicalGraph_edge_dist_eq_one
    (C : _root_.UDConfig n) {e : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet) :
    Geometry.Distance.eucDist (C.pts e.1) (C.pts e.2) = 1 := by
  exact PlanarInterface.mem_unitDistanceEdges_endpoints_geometry_dist_eq_one C
    ((mem_canonicalGraph_edgeSet_iff_unitDistanceEdges C e).1 he)

/-- The analytic noncrossing bridge for the concrete unit-distance edge set. -/
theorem unitDistanceEdges_not_cross
    (C : _root_.UDConfig n) {e f : PlanarInterface.Edge n}
    (hdisj : PlanarInterface.EdgeVertexDisjoint e f)
    (he : e ∈ GraphBridge.unitDistanceEdges C)
    (hf : f ∈ GraphBridge.unitDistanceEdges C) :
    Not (PlanarInterface.EdgeSegmentsCross C e f) :=
  NoncrossingUnitEdges.unitDistanceEdges_not_cross C hdisj he hf

/-- The canonical graph has pairwise noncrossing edges, with no topology input. -/
theorem canonicalGraph_pairwiseNoncrossing (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  OuterBoundaryCoreConstruction.canonicalGraph_pairwiseNoncrossing C

/-- Concrete pairwise noncrossing for `GraphBridge.unitDistanceEdges`. -/
theorem unitDistanceEdges_pairwiseNoncrossing
    (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      C (GraphBridge.unitDistanceEdges C) :=
  FaceReduction.unitDistanceEdges_pairwiseNoncrossing C

/-- A compact record of the graph-level facts already proved from `UDConfig`. -/
structure ConcreteGraphFacts (C : _root_.UDConfig n) : Prop where
  edgeSet_eq_unitDistanceEdges :
    (canonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C
  pairwiseNoncrossing :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet

/-- The concrete graph facts are available for every `UDConfig`. -/
theorem concreteGraphFacts (C : _root_.UDConfig n) :
    ConcreteGraphFacts C where
  edgeSet_eq_unitDistanceEdges := canonicalGraph_edgeSet_eq_unitDistanceEdges C
  pairwiseNoncrossing := canonicalGraph_pairwiseNoncrossing C

/-! ## The exact remaining topology/core field -/

/-- The raw dependent topology field still needed for the canonical graph. -/
def ExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  Exists fun H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C) =>
    Exists fun F : H.Face =>
      H.IsOuterFace F /\
        Nonempty (OuterBoundaryEnclosure (canonicalGraph C) H F)

/-- The raw field is exactly the construction target in
`OuterBoundaryCoreConstruction`. -/
theorem remainingCoreTopologyRequirements_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <-> ExactTopologyFields C := by
  constructor
  · rintro ⟨D, ⟨E⟩⟩
    exact ⟨D.faceBoundary, D.outerFace, D.outerFace_isOuter,
      ⟨E.outerEnclosure⟩⟩
  · rintro ⟨H, F, hF, ⟨E⟩⟩
    let D : OuterFaceData.{0} (canonicalGraph C) := {
      faceBoundary := H
      outerFace := F
      outerFace_isOuter := hF }
    exact ⟨D, ⟨{ outerEnclosure := E }⟩⟩

/-- Supplying exactly face data, a selected outer face, and enclosure data
discharges the remaining core-topology target. -/
theorem remainingCoreTopologyRequirements_of_exactTopologyFields
    {C : _root_.UDConfig n}
    {H : UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C)}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hE : Nonempty (OuterBoundaryEnclosure (canonicalGraph C) H F)) :
    RemainingCoreTopologyRequirements C := by
  exact
    (remainingCoreTopologyRequirements_iff_exactTopologyFields C).2
      ⟨H, F, hF, hE⟩

/-- The remaining target is equivalently nonempty checked core data. -/
theorem remainingCoreTopologyRequirements_iff_coreNonempty
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      Nonempty (OuterBoundaryCore.{0} (canonicalGraph C)) :=
  OuterBoundaryCoreConstruction.remainingCoreTopologyRequirements_iff_outerBoundaryCore C

/-- A checked core discharges the remaining target. -/
theorem remainingCoreTopologyRequirements_of_core
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (canonicalGraph C)) :
    RemainingCoreTopologyRequirements C :=
  (remainingCoreTopologyRequirements_iff_coreNonempty C).2 ⟨P⟩

/-- The remaining target is equivalently the concrete Jordan-boundary topology
frontier already exposed in `JordanBoundaryConcrete`. -/
theorem remainingCoreTopologyRequirements_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :=
  OuterBoundaryCoreConstruction.remainingCoreTopologyRequirements_iff_jordanBoundaryConcrete C

/-- Concrete missing-topology facts discharge the remaining target. -/
theorem remainingCoreTopologyRequirements_of_missingTopologyFacts
    {C : _root_.UDConfig n}
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    RemainingCoreTopologyRequirements C :=
  (remainingCoreTopologyRequirements_iff_missingTopologyFacts C).2 ⟨T⟩

/-- The remaining target is also equivalently nonempty concrete topology facts
from `JordanTopologyFactsConcrete`. -/
theorem remainingCoreTopologyRequirements_iff_topologyFacts
    (C : _root_.UDConfig n) :
    RemainingCoreTopologyRequirements C <->
      Nonempty (JordanTopologyFactsConcrete.TopologyFacts.{0} C) := by
  constructor
  · intro h
    rcases (remainingCoreTopologyRequirements_iff_coreNonempty C).1 h with ⟨P⟩
    exact ⟨JordanTopologyFactsConcrete.TopologyFacts.ofCore P⟩
  · rintro ⟨T⟩
    exact remainingCoreTopologyRequirements_of_core T.toCore

/-- Concrete topology facts discharge the remaining target. -/
theorem remainingCoreTopologyRequirements_of_topologyFacts
    {C : _root_.UDConfig n}
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    RemainingCoreTopologyRequirements C :=
  (remainingCoreTopologyRequirements_iff_topologyFacts C).2 ⟨T⟩

/-- The graph side is complete; the global construction target is exactly the
remaining topology field for every concrete configuration. -/
theorem globalTarget_iff_exactTopologyFields :
    GlobalOuterBoundaryCoreConstructionTarget <->
      forall (n : Nat) (C : _root_.UDConfig n), ExactTopologyFields C := by
  constructor
  · intro h n C
    exact (remainingCoreTopologyRequirements_iff_exactTopologyFields C).1
      (h n C)
  · intro h n C
    exact (remainingCoreTopologyRequirements_iff_exactTopologyFields C).2
      (h n C)

end

end OuterBoundaryExistenceConcrete
end Swanepoel
end ErdosProblems1066
