import ErdosProblems1066.Swanepoel.NoncrossingUnitEdges
import ErdosProblems1066.Swanepoel.FaceReduction
import ErdosProblems1066.Swanepoel.OuterBoundaryExistenceConcrete
import ErdosProblems1066.Swanepoel.JordanBoundaryConcrete

set_option autoImplicit false

/-!
# Topology extraction frontier from canonical noncrossing unit edges

This file records the checked bridge from a concrete `UDConfig` to the exact
topology fields still needed by `OuterBoundaryExistenceConcrete`.

The graph side is complete: the canonical graph is the concrete unit-distance
edge set, and pairwise noncrossing follows from the separated unit-edge
obstruction.  The only remaining inputs are split explicitly below into a
selected outer face and the enclosure predicates for that face.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyExtractionFromNoncrossing

open FaceReduction
open OuterBoundaryExistenceConcrete

noncomputable section

variable {n : Nat}

/-! ## Concrete graph extraction from `UDConfig` -/

/-- The canonical graph used by the concrete outer-boundary target. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  OuterBoundaryExistenceConcrete.canonicalGraph C

/-- The canonical graph is definitionally the graph used in
`JordanBoundaryConcrete`. -/
theorem canonicalGraph_eq_jordanBoundaryConcrete
    (C : _root_.UDConfig n) :
    canonicalGraph C = JordanBoundaryConcrete.canonicalGraph C :=
  rfl

/-- The proved graph-level facts available for every concrete configuration. -/
theorem concreteGraphFacts (C : _root_.UDConfig n) :
    ConcreteGraphFacts C :=
  OuterBoundaryExistenceConcrete.concreteGraphFacts C

/-- The canonical graph stores exactly the concrete finite unit-edge set. -/
theorem canonical_edgeSet_eq_unitDistanceEdges
    (C : _root_.UDConfig n) :
    (canonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C :=
  OuterBoundaryExistenceConcrete.canonicalGraph_edgeSet_eq_unitDistanceEdges C

/-- The concrete unit-edge obstruction gives pairwise noncrossing for the
canonical graph. -/
theorem canonical_pairwiseNoncrossing_from_unit_edges
    (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  OuterBoundaryExistenceConcrete.canonicalGraph_pairwiseNoncrossing C

/-- Disjoint canonical unit edges cannot cross in their relative interiors. -/
theorem canonical_disjoint_edges_do_not_cross
    (C : _root_.UDConfig n) {e f : PlanarInterface.Edge n}
    (he : e ∈ (canonicalGraph C).edgeSet)
    (hf : f ∈ (canonicalGraph C).edgeSet)
    (hdisj : PlanarInterface.EdgeVertexDisjoint e f) :
    Not (PlanarInterface.EdgeSegmentsCross C e f) := by
  exact
    NoncrossingUnitEdges.unitDistanceEdges_not_cross C hdisj
      ((OuterBoundaryExistenceConcrete.mem_canonicalGraph_edgeSet_iff_unitDistanceEdges
        C e).1 he)
      ((OuterBoundaryExistenceConcrete.mem_canonicalGraph_edgeSet_iff_unitDistanceEdges
        C f).1 hf)

/-! ## Exact remaining topology fields, split into the two honest parts -/

/-- Face-boundary data plus a chosen outer face for the canonical graph. -/
structure SelectedOuterFaceFields (C : _root_.UDConfig n) where
  faceBoundary :
    UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace

namespace SelectedOuterFaceFields

variable {C : _root_.UDConfig n}

/-- Convert the selected-face fields to the existing Jordan-boundary package. -/
def toMissingOuterFaceData (D : SelectedOuterFaceFields C) :
    JordanBoundaryConcrete.MissingOuterFaceData.{0} C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

/-- Recover the selected-face fields from the existing Jordan-boundary package. -/
def ofMissingOuterFaceData
    (D : JordanBoundaryConcrete.MissingOuterFaceData.{0} C) :
    SelectedOuterFaceFields C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

@[simp]
theorem toMissingOuterFaceData_faceBoundary
    (D : SelectedOuterFaceFields C) :
    D.toMissingOuterFaceData.faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem ofMissingOuterFaceData_faceBoundary
    (D : JordanBoundaryConcrete.MissingOuterFaceData.{0} C) :
    (ofMissingOuterFaceData D).faceBoundary = D.faceBoundary :=
  rfl

@[simp]
theorem ofMissingOuterFaceData_toMissingOuterFaceData
    (D : SelectedOuterFaceFields C) :
    ofMissingOuterFaceData D.toMissingOuterFaceData = D := by
  cases D
  rfl

@[simp]
theorem toMissingOuterFaceData_ofMissingOuterFaceData
    (D : JordanBoundaryConcrete.MissingOuterFaceData.{0} C) :
    (ofMissingOuterFaceData D).toMissingOuterFaceData = D := by
  cases D
  rfl

end SelectedOuterFaceFields

/-- The enclosure predicates still needed after a selected outer face is fixed. -/
structure EnclosureFields {C : _root_.UDConfig n}
    (D : SelectedOuterFaceFields C) where
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (canonicalGraph C) D.faceBoundary D.outerFace

namespace EnclosureFields

variable {C : _root_.UDConfig n}
variable {D : SelectedOuterFaceFields C}

/-- Convert enclosure fields to the existing Jordan-boundary package. -/
def toMissingEnclosureData (E : EnclosureFields D) :
    JordanBoundaryConcrete.MissingEnclosureData.{0}
      D.toMissingOuterFaceData where
  outerEnclosure := E.outerEnclosure

@[simp]
theorem toMissingEnclosureData_outerEnclosure
    (E : EnclosureFields D) :
    E.toMissingEnclosureData.outerEnclosure = E.outerEnclosure :=
  rfl

end EnclosureFields

/-- The exact topology fields, split into selected-face data and enclosure data. -/
def SplitExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  Exists fun D : SelectedOuterFaceFields C => Nonempty (EnclosureFields D)

/-- The split field list is exactly
`OuterBoundaryExistenceConcrete.ExactTopologyFields`. -/
theorem splitExactTopologyFields_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    SplitExactTopologyFields C <-> ExactTopologyFields C := by
  constructor
  · rintro ⟨D, ⟨E⟩⟩
    exact
      ⟨D.faceBoundary, D.outerFace, D.outerFace_isOuter,
        ⟨E.outerEnclosure⟩⟩
  · rintro ⟨H, F, hF, ⟨E⟩⟩
    let D : SelectedOuterFaceFields C := {
      faceBoundary := H
      outerFace := F
      outerFace_isOuter := hF }
    exact ⟨D, ⟨{ outerEnclosure := E }⟩⟩

/-- Selected outer-face fields plus enclosure fields discharge the exact
topology field target. -/
theorem exactTopologyFields_of_split
    {C : _root_.UDConfig n}
    {D : SelectedOuterFaceFields C}
    (E : EnclosureFields D) :
    ExactTopologyFields C :=
  (splitExactTopologyFields_iff_exactTopologyFields C).1 ⟨D, ⟨E⟩⟩

/-- The exact topology fields are equivalent to the concrete
`JordanBoundaryConcrete` missing-topology package. -/
theorem exactTopologyFields_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    ExactTopologyFields C <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) := by
  constructor
  · rintro ⟨H, F, hF, ⟨E⟩⟩
    exact
      ⟨{
        faceBoundary := H
        outerFace := F
        outerFace_isOuter := hF
        outerEnclosure := E }⟩
  · rintro ⟨T⟩
    exact
      ⟨T.faceBoundary, T.outerFace, T.outerFace_isOuter,
        ⟨T.outerEnclosure⟩⟩

/-- The exact topology fields are the same proposition as the concrete
Jordan-boundary remaining theorem. -/
theorem exactTopologyFields_iff_remainingTopologyTheorem
    (C : _root_.UDConfig n) :
    ExactTopologyFields C <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem C := by
  simpa [JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem]
    using exactTopologyFields_iff_missingTopologyFacts C

/-! ## Frontier statement: graph side done, topology side explicit -/

/-- The noncrossing-to-topology frontier for one concrete configuration.

The first conjunct is already proved for every `UDConfig`; the second conjunct
is precisely the remaining selected-face/enclosure topology data.
-/
def ConcreteNoncrossingTopologyFrontier (C : _root_.UDConfig n) : Prop :=
  ConcreteGraphFacts C /\ SplitExactTopologyFields C

/-- The concrete frontier is equivalent to the exact topology fields because
the graph facts are already theorems of the canonical unit-distance graph. -/
theorem concreteNoncrossingTopologyFrontier_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    ConcreteNoncrossingTopologyFrontier C <-> ExactTopologyFields C := by
  constructor
  · intro h
    exact (splitExactTopologyFields_iff_exactTopologyFields C).1 h.2
  · intro h
    exact
      ⟨concreteGraphFacts C,
        (splitExactTopologyFields_iff_exactTopologyFields C).2 h⟩

/-- Exact topology fields complete the concrete frontier. -/
theorem concreteNoncrossingTopologyFrontier_of_exactTopologyFields
    {C : _root_.UDConfig n}
    (h : ExactTopologyFields C) :
    ConcreteNoncrossingTopologyFrontier C :=
  (concreteNoncrossingTopologyFrontier_iff_exactTopologyFields C).2 h

/-- A completed concrete frontier gives the remaining core-topology target. -/
theorem remainingCoreTopologyRequirements_of_frontier
    {C : _root_.UDConfig n}
    (h : ConcreteNoncrossingTopologyFrontier C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  (OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_exactTopologyFields
    C).2
    ((splitExactTopologyFields_iff_exactTopologyFields C).1 h.2)

/-- Globally, the paper-facing outer-boundary construction target is exactly
the statement that every concrete configuration reaches this frontier. -/
theorem globalTarget_iff_concreteNoncrossingTopologyFrontier :
    OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget <->
      forall (n : Nat) (C : _root_.UDConfig n),
        ConcreteNoncrossingTopologyFrontier C := by
  constructor
  · intro h n C
    exact
      concreteNoncrossingTopologyFrontier_of_exactTopologyFields
        ((OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields).1
          h n C)
  · intro h
    exact
      (OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields).2
        (fun n C =>
          (concreteNoncrossingTopologyFrontier_iff_exactTopologyFields C).1
            (h n C))

end

end TopologyExtractionFromNoncrossing
end Swanepoel
end ErdosProblems1066
