import ErdosProblems1066.Swanepoel.TopologyExtractionFromNoncrossing
import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal

set_option autoImplicit false

/-!
# W10 topology frontier

This file tightens the concrete noncrossing frontier to one explicit
outer-boundary topology record.  The record contains only the fields still
owed by the topology layer: face-boundary data, the selected outer face, its
outer-face proof, and the enclosure predicates for that face.

All graph noncrossing facts are projected from the existing canonical
unit-edge theorems.  The declarations below only repackage supplied fields and
prove equivalences with the existing outer-boundary, Jordan, and final
planar-boundary interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TopologyFrontierW10

open FaceReduction
open OuterBoundaryInterface
open TopologyExtractionFromNoncrossing

universe u

noncomputable section

variable {n : Nat}

/-! ## Canonical graph and completed graph side -/

/-- The canonical graph used by all concrete topology-frontier targets. -/
abbrev canonicalGraph (C : _root_.UDConfig n) :
    CanonicalStraightLineUnitDistanceGraph n :=
  JordanBoundaryConcrete.canonicalGraph C

/-- The W10 canonical graph is definitionally the graph used by the
noncrossing extraction frontier. -/
theorem canonicalGraph_eq_topologyExtraction
    (C : _root_.UDConfig n) :
    canonicalGraph C =
      TopologyExtractionFromNoncrossing.canonicalGraph C :=
  rfl

/-- The W10 canonical graph is definitionally the graph used by concrete
outer-boundary existence. -/
theorem canonicalGraph_eq_outerBoundaryExistence
    (C : _root_.UDConfig n) :
    canonicalGraph C =
      OuterBoundaryExistenceConcrete.canonicalGraph C :=
  rfl

/-- The canonical graph stores exactly the concrete unit-distance edge set. -/
theorem canonical_edgeSet_eq_unitDistanceEdges
    (C : _root_.UDConfig n) :
    (canonicalGraph C).edgeSet = GraphBridge.unitDistanceEdges C :=
  OuterBoundaryExistenceConcrete.canonicalGraph_edgeSet_eq_unitDistanceEdges C

/-- Pairwise noncrossing is already proved for the canonical unit-edge graph. -/
theorem canonical_pairwiseNoncrossing
    (C : _root_.UDConfig n) :
    PlanarInterface.PairwiseNoncrossing
      (canonicalGraph C).config (canonicalGraph C).edgeSet :=
  TopologyExtractionFromNoncrossing.canonical_pairwiseNoncrossing_from_unit_edges C

/-- The graph-side facts needed by the old frontier are available for every
concrete configuration. -/
theorem concreteGraphFacts (C : _root_.UDConfig n) :
    OuterBoundaryExistenceConcrete.ConcreteGraphFacts C :=
  OuterBoundaryExistenceConcrete.concreteGraphFacts C

/-! ## One explicit topology record -/

/-- Exact outer-boundary topology fields for a concrete configuration.

These are supplied fields, not derived topology: the face-boundary surface, a
chosen outer face, its outer-face proof, and the enclosure predicates attached
to that chosen face.
-/
structure ExactOuterBoundaryTopologyFields (C : _root_.UDConfig n) where
  faceBoundary :
    UnitDistanceFaceBoundaryHypotheses.{0} (canonicalGraph C)
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryEnclosure (canonicalGraph C) faceBoundary outerFace

namespace ExactOuterBoundaryTopologyFields

variable {C : _root_.UDConfig n}

/-- Forget the enclosure predicates, retaining selected outer-face data. -/
def toSelectedOuterFaceFields
    (T : ExactOuterBoundaryTopologyFields C) :
    TopologyExtractionFromNoncrossing.SelectedOuterFaceFields C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter

/-- The enclosure predicates over the selected outer face. -/
def toEnclosureFields
    (T : ExactOuterBoundaryTopologyFields C) :
    TopologyExtractionFromNoncrossing.EnclosureFields
      T.toSelectedOuterFaceFields where
  outerEnclosure := T.outerEnclosure

/-- The split frontier fields used by `TopologyExtractionFromNoncrossing`. -/
def toSplitExactTopologyFields
    (T : ExactOuterBoundaryTopologyFields C) :
    TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  Exists.intro T.toSelectedOuterFaceFields
    (Nonempty.intro T.toEnclosureFields)

/-- The raw exact topology proposition used by
`OuterBoundaryExistenceConcrete`. -/
def toExactTopologyFields
    (T : ExactOuterBoundaryTopologyFields C) :
    OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Exists.intro T.faceBoundary
    (Exists.intro T.outerFace
      (And.intro T.outerFace_isOuter
        (Nonempty.intro T.outerEnclosure)))

/-- Selected outer-face data in the concrete Jordan-boundary namespace. -/
def toMissingOuterFaceData
    (T : ExactOuterBoundaryTopologyFields C) :
    JordanBoundaryConcrete.MissingOuterFaceData.{0} C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter

/-- Enclosure data in the concrete Jordan-boundary namespace. -/
def toMissingEnclosureData
    (T : ExactOuterBoundaryTopologyFields C) :
    JordanBoundaryConcrete.MissingEnclosureData.{0}
      T.toMissingOuterFaceData where
  outerEnclosure := T.outerEnclosure

/-- The concrete Jordan-boundary missing-topology package. -/
def toMissingTopologyFacts
    (T : ExactOuterBoundaryTopologyFields C) :
    JordanBoundaryConcrete.MissingTopologyFacts.{0} C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

/-- The graph-generic selected-face data used by the core construction layer. -/
def toCoreOuterFaceData
    (T : ExactOuterBoundaryTopologyFields C) :
    OuterBoundaryCoreConstruction.OuterFaceData.{0} (canonicalGraph C) where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter

/-- The graph-generic enclosure data used by the core construction layer. -/
def toCoreEnclosureData
    (T : ExactOuterBoundaryTopologyFields C) :
    OuterBoundaryCoreConstruction.EnclosureData
      T.toCoreOuterFaceData where
  outerEnclosure := T.outerEnclosure

/-- The split core-topology requirement for the canonical graph. -/
def toCoreTopologyRequirements
    (T : ExactOuterBoundaryTopologyFields C) :
    OuterBoundaryCoreConstruction.CoreTopologyRequirements.{0}
      (canonicalGraph C) :=
  Exists.intro T.toCoreOuterFaceData
    (Nonempty.intro T.toCoreEnclosureData)

/-- The checked outer-boundary core assembled from the explicit fields. -/
def toCore
    (T : ExactOuterBoundaryTopologyFields C) :
    OuterBoundaryCore.{0} (canonicalGraph C) where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

/-- The concrete topology-facts package used by later Jordan adapters. -/
def toTopologyFacts
    (T : ExactOuterBoundaryTopologyFields C) :
    JordanTopologyFactsConcrete.TopologyFacts.{0} C :=
  JordanTopologyFactsConcrete.TopologyFacts.ofMissingTopologyFacts
    T.toMissingTopologyFacts

/-- The extraction facade used by the Jordan boundary layer. -/
def toExtractionData
    (T : ExactOuterBoundaryTopologyFields C) :
    JordanBoundaryExtraction.Data.{0} (canonicalGraph C) :=
  T.toMissingTopologyFacts.toExtractionData

/-- The selected outer boundary cycle. -/
def outerCycle
    (T : ExactOuterBoundaryTopologyFields C) :
    BoundaryCycle (canonicalGraph C) :=
  BoundaryCycle.ofFaceBoundary T.faceBoundary T.outerFace

/-- The selected boundary cycle has the derived simple-polygon witness. -/
def outerSimplePolygon
    (T : ExactOuterBoundaryTopologyFields C) :
    SimplePolygon (canonicalGraph C) T.outerCycle :=
  OuterBoundaryReduction.BoundaryCycle.simplePolygonOfFaceBoundary
    T.faceBoundary T.outerFace

/-- Extend the exact topology fields by already supplied angle and subpolygon
data to the final planar-boundary package. -/
def toPlanarBoundaryData
    (T : ExactOuterBoundaryTopologyFields C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (canonicalGraph C) where
  core := T.toCore
  outerAngleBounds := outerAngleBounds
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData

/-- The concrete face-counting data exposed by `PlanarBoundaryFinal`. -/
def toConcreteFaceCountingData
    (T : ExactOuterBoundaryTopologyFields C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      (T.toPlanarBoundaryData
        outerAngleBounds Subpolygon subpolygonData) :=
  PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData _

/-- Build exact fields from the existing concrete missing-topology package. -/
def ofMissingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    ExactOuterBoundaryTopologyFields C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

/-- Build exact fields from concrete topology facts. -/
def ofTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    ExactOuterBoundaryTopologyFields C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  outerEnclosure := T.outerEnclosure

/-- Build exact fields from an already checked outer-boundary core. -/
def ofCore
    (P : OuterBoundaryCore.{0} (canonicalGraph C)) :
    ExactOuterBoundaryTopologyFields C where
  faceBoundary := P.faceBoundary
  outerFace := P.outerFace
  outerFace_isOuter := P.outerFace_isOuter
  outerEnclosure := P.outerEnclosure

@[simp]
theorem toMissingTopologyFacts_faceBoundary
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toMissingTopologyFacts.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toMissingTopologyFacts_outerFace
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toMissingTopologyFacts.outerFace = T.outerFace :=
  rfl

theorem toMissingTopologyFacts_outerFace_isOuter
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toMissingTopologyFacts.faceBoundary.IsOuterFace
      T.toMissingTopologyFacts.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toMissingTopologyFacts_outerEnclosure
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toMissingTopologyFacts.outerEnclosure = T.outerEnclosure :=
  rfl

@[simp]
theorem toCore_faceBoundary
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toCore.faceBoundary = T.faceBoundary :=
  rfl

@[simp]
theorem toCore_outerFace
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toCore.outerFace = T.outerFace :=
  rfl

theorem toCore_outerFace_isOuter
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toCore.faceBoundary.IsOuterFace T.toCore.outerFace :=
  T.outerFace_isOuter

@[simp]
theorem toCore_outerEnclosure
    (T : ExactOuterBoundaryTopologyFields C) :
    T.toCore.outerEnclosure = T.outerEnclosure :=
  rfl

@[simp]
theorem outerCycle_eq
    (T : ExactOuterBoundaryTopologyFields C) :
    T.outerCycle =
      BoundaryCycle.ofFaceBoundary T.faceBoundary T.outerFace :=
  rfl

@[simp]
theorem outerCycle_length
    (T : ExactOuterBoundaryTopologyFields C) :
    T.outerCycle.length =
      T.faceBoundary.boundaryLength T.outerFace :=
  rfl

@[simp]
theorem outerCycle_vertex
    (T : ExactOuterBoundaryTopologyFields C)
    (k : Fin T.outerCycle.length) :
    T.outerCycle.vertex k =
      T.faceBoundary.boundaryVertex T.outerFace k :=
  rfl

/-- Boundary vertices satisfy the supplied boundary predicate. -/
theorem boundary_vertex_onBoundary
    (T : ExactOuterBoundaryTopologyFields C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.onBoundary
      (T.faceBoundary.boundaryVertex T.outerFace k) :=
  T.outerEnclosure.boundary_vertex_onBoundary k

/-- Boundary points satisfy the supplied inside-or-on predicate. -/
theorem boundary_point_insideOrOn
    (T : ExactOuterBoundaryTopologyFields C)
    (k : Fin (T.faceBoundary.boundaryLength T.outerFace)) :
    T.outerEnclosure.insideOrOn
      ((canonicalGraph C).point
        (T.faceBoundary.boundaryVertex T.outerFace k)) :=
  T.outerEnclosure.boundary_point_insideOrOn k

/-- Every ambient vertex satisfies the supplied inside-or-on predicate. -/
theorem all_vertices_insideOrOn
    (T : ExactOuterBoundaryTopologyFields C) (v : Fin n) :
    T.outerEnclosure.insideOrOn ((canonicalGraph C).point v) :=
  T.outerEnclosure.all_vertices_insideOrOn v

/-- The supplied boundary predicate is exactly the selected outer cycle. -/
theorem onBoundary_iff_outerCycle
    (T : ExactOuterBoundaryTopologyFields C) (v : Fin n) :
    T.outerEnclosure.onBoundary v <->
      Exists fun k : Fin T.outerCycle.length =>
        T.outerCycle.vertex k = v :=
  T.outerEnclosure.onBoundary_iff_outer_cycle v

@[simp]
theorem toPlanarBoundaryData_core
    (T : ExactOuterBoundaryTopologyFields C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).core = T.toCore :=
  rfl

@[simp]
theorem toPlanarBoundaryData_faceBoundary
    (T : ExactOuterBoundaryTopologyFields C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).faceBoundary =
        T.faceBoundary :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerFace
    (T : ExactOuterBoundaryTopologyFields C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).outerFace =
        T.outerFace :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerCycle
    (T : ExactOuterBoundaryTopologyFields C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).outerCycle =
        T.outerCycle :=
  rfl

@[simp]
theorem toPlanarBoundaryData_Subpolygon
    (T : ExactOuterBoundaryTopologyFields C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (canonicalGraph C)) :
    (T.toPlanarBoundaryData
      outerAngleBounds Subpolygon subpolygonData).Subpolygon =
        Subpolygon :=
  rfl

@[simp]
theorem toMissingTopologyFacts_ofMissingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    (ofMissingTopologyFacts T).toMissingTopologyFacts = T := by
  cases T
  rfl

@[simp]
theorem ofMissingTopologyFacts_toMissingTopologyFacts
    (T : ExactOuterBoundaryTopologyFields C) :
    ofMissingTopologyFacts T.toMissingTopologyFacts = T := by
  cases T
  rfl

@[simp]
theorem toCore_ofCore
    (P : OuterBoundaryCore.{0} (canonicalGraph C)) :
    (ofCore P).toCore = P := by
  cases P
  rfl

@[simp]
theorem ofCore_toCore
    (T : ExactOuterBoundaryTopologyFields C) :
    ofCore T.toCore = T := by
  cases T
  rfl

end ExactOuterBoundaryTopologyFields

/-! ## Proposition-level exact frontier -/

/-- The exact field target: nonempty explicit outer-boundary topology fields. -/
def ExactOuterBoundaryTopologyFieldTarget
    (C : _root_.UDConfig n) : Prop :=
  Nonempty (ExactOuterBoundaryTopologyFields C)

/-- Exact explicit fields are equivalent to the raw exact topology proposition. -/
theorem exactFieldTarget_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
      exact T.toExactTopologyFields
  case mpr =>
    intro h
    cases h with
    | intro H hH =>
      cases hH with
      | intro F hF =>
        cases hF.2 with
        | intro E =>
          exact
            Nonempty.intro {
              faceBoundary := H
              outerFace := F
              outerFace_isOuter := hF.1
              outerEnclosure := E }

/-- Exact explicit fields are equivalent to the split noncrossing frontier
topology fields. -/
theorem exactFieldTarget_iff_splitExactTopologyFields
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      TopologyExtractionFromNoncrossing.SplitExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
      exact T.toSplitExactTopologyFields
  case mpr =>
    intro h
    exact
      (exactFieldTarget_iff_exactTopologyFields C).2
        ((TopologyExtractionFromNoncrossing.splitExactTopologyFields_iff_exactTopologyFields
          C).1 h)

/-- Exact explicit fields are equivalent to the concrete missing-topology
package from `JordanBoundaryConcrete`. -/
theorem exactFieldTarget_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
      exact Nonempty.intro T.toMissingTopologyFacts
  case mpr =>
    intro h
    cases h with
    | intro T =>
      exact
        Nonempty.intro
          (ExactOuterBoundaryTopologyFields.ofMissingTopologyFacts T)

/-- Exact explicit fields are equivalent to the concrete remaining
Jordan-boundary theorem. -/
theorem exactFieldTarget_iff_remainingTopologyTheorem
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem C := by
  simpa [JordanBoundaryConcrete.MissingTopologyFacts.RemainingTopologyTheorem]
    using exactFieldTarget_iff_missingTopologyFacts C

/-- Exact explicit fields are equivalent to concrete topology facts. -/
theorem exactFieldTarget_iff_topologyFacts
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      Nonempty (JordanTopologyFactsConcrete.TopologyFacts.{0} C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
      exact Nonempty.intro T.toTopologyFacts
  case mpr =>
    intro h
    cases h with
    | intro T =>
      exact
        Nonempty.intro
          (ExactOuterBoundaryTopologyFields.ofTopologyFacts T)

/-- Exact explicit fields are equivalent to a checked outer-boundary core. -/
theorem exactFieldTarget_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      Nonempty (OuterBoundaryCore.{0} (canonicalGraph C)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
      exact Nonempty.intro T.toCore
  case mpr =>
    intro h
    cases h with
    | intro P =>
      exact
        Nonempty.intro
          (ExactOuterBoundaryTopologyFields.ofCore P)

/-- Exact explicit fields are equivalent to the core construction split
requirements. -/
theorem exactFieldTarget_iff_coreTopologyRequirements
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      OuterBoundaryCoreConstruction.CoreTopologyRequirements.{0}
        (canonicalGraph C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
      exact T.toCoreTopologyRequirements
  case mpr =>
    intro h
    exact
      (exactFieldTarget_iff_outerBoundaryCore C).2
        ((OuterBoundaryCoreConstruction.coreTopologyRequirements_iff_outerBoundaryCore
          (canonicalGraph C)).1 h)

/-- Exact explicit fields are equivalent to the concrete remaining core
topology target. -/
theorem exactFieldTarget_iff_remainingCoreTopologyRequirements
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C := by
  constructor
  case mp =>
    intro h
    exact
      (OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_exactTopologyFields
        C).2
        ((exactFieldTarget_iff_exactTopologyFields C).1 h)
  case mpr =>
    intro h
    exact
      (exactFieldTarget_iff_exactTopologyFields C).2
        ((OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_iff_exactTopologyFields
          C).1 h)

/-- Exact explicit fields are equivalent to the earlier concrete
noncrossing-topology frontier. -/
theorem exactFieldTarget_iff_concreteNoncrossingTopologyFrontier
    (C : _root_.UDConfig n) :
    ExactOuterBoundaryTopologyFieldTarget C <->
      TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C := by
  constructor
  case mp =>
    intro h
    exact
      (TopologyExtractionFromNoncrossing.concreteNoncrossingTopologyFrontier_iff_exactTopologyFields
        C).2
        ((exactFieldTarget_iff_exactTopologyFields C).1 h)
  case mpr =>
    intro h
    exact
      (exactFieldTarget_iff_exactTopologyFields C).2
        ((concreteNoncrossingTopologyFrontier_iff_exactTopologyFields C).1 h)

/-- Exact explicit fields discharge the remaining core topology target. -/
theorem remainingCoreTopologyRequirements_of_exactFields
    {C : _root_.UDConfig n}
    (T : ExactOuterBoundaryTopologyFields C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  (exactFieldTarget_iff_remainingCoreTopologyRequirements C).1
    (Nonempty.intro T)

/-- Exact explicit fields discharge the previous noncrossing frontier. -/
theorem concreteNoncrossingTopologyFrontier_of_exactFields
    {C : _root_.UDConfig n}
    (T : ExactOuterBoundaryTopologyFields C) :
    TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C :=
  (exactFieldTarget_iff_concreteNoncrossingTopologyFrontier C).1
    (Nonempty.intro T)

/-! ## Noncrossing-to-exact W10 frontier -/

/-- W10 frontier: graph noncrossing facts plus the exact explicit topology
fields.  The first conjunct is already proved for every configuration. -/
def NoncrossingToExactOuterBoundaryFrontier
    (C : _root_.UDConfig n) : Prop :=
  OuterBoundaryExistenceConcrete.ConcreteGraphFacts C /\
    ExactOuterBoundaryTopologyFieldTarget C

/-- The W10 frontier is equivalent to the exact explicit field target because
the graph side is already checked. -/
theorem noncrossingToExactFrontier_iff_exactFieldTarget
    (C : _root_.UDConfig n) :
    NoncrossingToExactOuterBoundaryFrontier C <->
      ExactOuterBoundaryTopologyFieldTarget C := by
  constructor
  case mp =>
    intro h
    exact h.2
  case mpr =>
    intro h
    exact And.intro (concreteGraphFacts C) h

/-- The W10 frontier is equivalent to the raw exact topology proposition. -/
theorem noncrossingToExactFrontier_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    NoncrossingToExactOuterBoundaryFrontier C <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C := by
  constructor
  case mp =>
    intro h
    exact
      (exactFieldTarget_iff_exactTopologyFields C).1
        ((noncrossingToExactFrontier_iff_exactFieldTarget C).1 h)
  case mpr =>
    intro h
    exact
      (noncrossingToExactFrontier_iff_exactFieldTarget C).2
        ((exactFieldTarget_iff_exactTopologyFields C).2 h)

/-- The global core construction target is exactly the statement that every
configuration has the W10 frontier. -/
theorem globalTarget_iff_noncrossingToExactFrontier :
    OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget <->
      forall (n : Nat) (C : _root_.UDConfig n),
        NoncrossingToExactOuterBoundaryFrontier C := by
  constructor
  case mp =>
    intro h n C
    exact
      (noncrossingToExactFrontier_iff_exactTopologyFields C).2
        ((OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields).1
          h n C)
  case mpr =>
    intro h
    exact
      (OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields).2
        (fun n C =>
          (noncrossingToExactFrontier_iff_exactTopologyFields C).1
            (h n C))

/-- The global core construction target is exactly the statement that every
configuration has exact explicit outer-boundary topology fields. -/
theorem globalTarget_iff_exactFieldTarget :
    OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget <->
      forall (n : Nat) (C : _root_.UDConfig n),
        ExactOuterBoundaryTopologyFieldTarget C := by
  constructor
  case mp =>
    intro h n C
    exact
      (exactFieldTarget_iff_exactTopologyFields C).2
        ((OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields).1
          h n C)
  case mpr =>
    intro h
    exact
      (OuterBoundaryExistenceConcrete.globalTarget_iff_exactTopologyFields).2
        (fun n C =>
          (exactFieldTarget_iff_exactTopologyFields C).1 (h n C))

end

end TopologyFrontierW10
end Swanepoel
end ErdosProblems1066
