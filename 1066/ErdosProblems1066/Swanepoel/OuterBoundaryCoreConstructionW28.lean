import ErdosProblems1066.Swanepoel.BoundaryWalkBridge
import ErdosProblems1066.Swanepoel.ActualSelectedTopologyDataW27

set_option autoImplicit false

/-!
# W28 outer-boundary core source

This file sharpens the topology source needed by
`ActualSelectedTopologyDataW27`: an actual checked `OuterBoundaryCore` for the
canonical unit-distance graph.

The graph side is not part of this source.  For every `UDConfig`, the canonical
unit-distance graph and its pairwise noncrossing fact are already available.
The remaining topology blocker is exactly the selected outer face together
with enclosure data for that same face.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace OuterBoundaryCoreConstructionW28

open PlanarTopologyActualExtractionW26
open PlanarTopologyExtractionBridgeW25
open TopologyExtractionFromNoncrossing

noncomputable section

universe u

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.CanonicalGraph C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

/-! ## Boundary endpoint-neighbour intervals from the actual cycle -/

/-- The endpoint-neighbour interval forced by any nondegenerate boundary
cycle: predecessor first, successor last, both adjacent to the center. -/
def endpointNeighborIntervalOfBoundaryCycle
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (cycle : OuterBoundaryInterface.BoundaryCycle G)
    (hcycle : 3 <= cycle.length)
    (k : Fin cycle.length) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k :=
  cycle.endpointNeighborInterval hcycle k

@[simp]
theorem endpointNeighborIntervalOfBoundaryCycle_gapCount
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (cycle : OuterBoundaryInterface.BoundaryCycle G)
    (hcycle : 3 <= cycle.length)
    (k : Fin cycle.length) :
    (endpointNeighborIntervalOfBoundaryCycle cycle hcycle k).gapCount = 1 :=
  rfl

/-- Ordered unit-neighbor data at one boundary index, with endpoints tied to
the endpoint-neighbor interval already supplied by the boundary walk.

This is the W28-owned, import-acyclic version of the W34 local ordered-neighbor
payload.  The downstream W34 record can be populated from these fields without
introducing an import cycle back to `OuterBoundaryAngleSourceW34`. -/
structure BoundaryIndexOrderedUnitNeighborData
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (cycle : OuterBoundaryInterface.BoundaryCycle G)
    (k : Fin cycle.length)
    (endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k) where
  gapCount : Nat
  neighbor : Fin (gapCount + 1) -> Fin n
  neighbor_injective : Function.Injective neighbor
  first_neighbor_eq_endpoint :
    neighbor ⟨0, Nat.succ_pos gapCount⟩ =
      endpointInterval.neighbor
        ⟨0, Nat.succ_pos endpointInterval.gapCount⟩
  last_neighbor_eq_endpoint :
    neighbor ⟨gapCount, Nat.lt_succ_self gapCount⟩ =
      endpointInterval.neighbor
        ⟨endpointInterval.gapCount,
          Nat.lt_succ_self endpointInterval.gapCount⟩
  neighbor_unit :
    forall j, G.Adj (neighbor j) (cycle.vertex k)

namespace BoundaryIndexOrderedUnitNeighborData

variable {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
variable {cycle : OuterBoundaryInterface.BoundaryCycle G}
variable {k : Fin cycle.length}
variable {endpointInterval :
  OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k}

/-- Repackage ordered boundary-index data as the endpoint-interval carrier used
by the boundary-data rows. -/
def toEndpointNeighborInterval
    (D : BoundaryIndexOrderedUnitNeighborData cycle k endpointInterval) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k where
  gapCount := D.gapCount
  neighbor := D.neighbor
  neighbor_injective := D.neighbor_injective
  first_neighbor_eq_boundary_predecessor := by
    calc
      D.neighbor ⟨0, Nat.succ_pos D.gapCount⟩ =
          endpointInterval.neighbor
            ⟨0, Nat.succ_pos endpointInterval.gapCount⟩ :=
        D.first_neighbor_eq_endpoint
      _ = cycle.prevVertex k :=
        endpointInterval.first_neighbor_eq_boundary_predecessor
  last_neighbor_eq_boundary_successor := by
    calc
      D.neighbor ⟨D.gapCount, Nat.lt_succ_self D.gapCount⟩ =
          endpointInterval.neighbor
            ⟨endpointInterval.gapCount,
              Nat.lt_succ_self endpointInterval.gapCount⟩ :=
        D.last_neighbor_eq_endpoint
      _ = cycle.nextVertex k :=
        endpointInterval.last_neighbor_eq_boundary_successor
  neighbor_unit := D.neighbor_unit

/-- The endpoint interval itself is a positive ordered-neighbor source: its
two concrete rows are the boundary predecessor and successor. -/
def ofEndpointNeighborInterval
    (endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k) :
    BoundaryIndexOrderedUnitNeighborData cycle k endpointInterval where
  gapCount := endpointInterval.gapCount
  neighbor := endpointInterval.neighbor
  neighbor_injective := endpointInterval.neighbor_injective
  first_neighbor_eq_endpoint := rfl
  last_neighbor_eq_endpoint := rfl
  neighbor_unit := endpointInterval.neighbor_unit

@[simp]
theorem ofEndpointNeighborInterval_gapCount
    (endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k) :
    (ofEndpointNeighborInterval endpointInterval).gapCount =
      endpointInterval.gapCount :=
  rfl

@[simp]
theorem ofEndpointNeighborInterval_neighbor
    (endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k) :
    (ofEndpointNeighborInterval endpointInterval).neighbor =
      endpointInterval.neighbor :=
  rfl

@[simp]
theorem toEndpointNeighborInterval_ofEndpointNeighborInterval
    (endpointInterval :
      OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval cycle k) :
    (ofEndpointNeighborInterval endpointInterval).toEndpointNeighborInterval =
      endpointInterval := by
  cases endpointInterval
  rfl

/-- Build ordered unit-neighbor data directly from a nondegenerate boundary
cycle. -/
def ofBoundaryCycle
    (cycle : OuterBoundaryInterface.BoundaryCycle G)
    (hcycle : 3 <= cycle.length)
    (k : Fin cycle.length) :
    BoundaryIndexOrderedUnitNeighborData cycle k
      (endpointNeighborIntervalOfBoundaryCycle cycle hcycle k) :=
  ofEndpointNeighborInterval
    (endpointNeighborIntervalOfBoundaryCycle cycle hcycle k)

@[simp]
theorem ofBoundaryCycle_gapCount
    (cycle : OuterBoundaryInterface.BoundaryCycle G)
    (hcycle : 3 <= cycle.length)
    (k : Fin cycle.length) :
    (ofBoundaryCycle cycle hcycle k).gapCount = 1 :=
  rfl

end BoundaryIndexOrderedUnitNeighborData

/-- The actual checked outer-boundary core supplies the endpoint-neighbour
interval at every selected boundary index once the selected cycle is
nondegenerate. -/
def endpointNeighborIntervalOfOuterBoundaryCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (hcycle : 3 <= P.outerCycle.length)
    (k : Fin P.outerCycle.length) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      P.outerCycle k :=
  endpointNeighborIntervalOfBoundaryCycle P.outerCycle hcycle k

@[simp]
theorem endpointNeighborIntervalOfOuterBoundaryCore_gapCount
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (hcycle : 3 <= P.outerCycle.length)
    (k : Fin P.outerCycle.length) :
    (endpointNeighborIntervalOfOuterBoundaryCore P hcycle k).gapCount = 1 :=
  rfl

/-- A checked outer-boundary core supplies the endpoint-compatible ordered
unit-neighbor rows at each selected boundary index. -/
def orderedUnitNeighborDataOfOuterBoundaryCore
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (hcycle : 3 <= P.outerCycle.length)
    (k : Fin P.outerCycle.length) :
    BoundaryIndexOrderedUnitNeighborData P.outerCycle k
      (endpointNeighborIntervalOfOuterBoundaryCore P hcycle k) :=
  BoundaryIndexOrderedUnitNeighborData.ofEndpointNeighborInterval
    (endpointNeighborIntervalOfOuterBoundaryCore P hcycle k)

@[simp]
theorem orderedUnitNeighborDataOfOuterBoundaryCore_gapCount
    {G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (hcycle : 3 <= P.outerCycle.length)
    (k : Fin P.outerCycle.length) :
    (orderedUnitNeighborDataOfOuterBoundaryCore P hcycle k).gapCount = 1 :=
  rfl

/--
The concrete W28 source for the outer-boundary topology route.

This packages only the checked core.  The canonical graph facts are projected
separately, since they are already theorems of `UDConfig`.
-/
structure OuterBoundaryCoreSource (C : _root_.UDConfig n) where
  core : OuterBoundaryCore.{0} (CanonicalGraph C)

namespace OuterBoundaryCoreSource

variable {C : _root_.UDConfig n}

def toActualSelectedTopologyData
    (S : OuterBoundaryCoreSource C) :
    ActualSelectedTopologyData C :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
    S.core

def ofActualSelectedTopologyData
    (A : ActualSelectedTopologyData C) :
    OuterBoundaryCoreSource C where
  core :=
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
      A

def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    OuterBoundaryCoreSource C where
  core := P

def ofSelectedOuterFaceAndEnclosure
    (D : PlanarTopologyExtractionBridgeW25.SelectedOuterFaceData C)
    (E : PlanarTopologyExtractionBridgeW25.SelectedEnclosureData D) :
    OuterBoundaryCoreSource C where
  core := PlanarTopologyExtractionBridgeW25.SelectedEnclosureData.toCore E

def ofMissingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    OuterBoundaryCoreSource C where
  core := T.toCore

def ofConcreteTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    OuterBoundaryCoreSource C where
  core := T.toCore

def ofPlanarBoundaryData
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (CanonicalGraph C)) :
    OuterBoundaryCoreSource C where
  core := P.core

def toMissingTopologyFacts
    (S : OuterBoundaryCoreSource C) :
    JordanBoundaryConcrete.MissingTopologyFacts.{0} C :=
  JordanBoundaryConcrete.MissingTopologyFacts.ofCore S.core

def toConcreteTopologyFacts
    (S : OuterBoundaryCoreSource C) :
    JordanTopologyFactsConcrete.TopologyFacts.{0} C :=
  JordanTopologyFactsConcrete.TopologyFacts.ofCore S.core

def toActualOuterBoundaryCycleData
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length) :
    JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C :=
  JordanBoundaryConcrete.ActualOuterBoundaryCycleData.ofCore S.core hcycle

def toRemainingCoreTopologyRequirements
    (S : OuterBoundaryCoreSource C) :
    OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  OuterBoundaryExistenceConcrete.remainingCoreTopologyRequirements_of_core
    S.core

def toConcreteNoncrossingTopologyFrontier
    (S : OuterBoundaryCoreSource C) :
    ConcreteNoncrossingTopologyFrontier C :=
  PlanarTopologyActualExtractionW26.ActualSelectedTopologyData.toConcreteNoncrossingTopologyFrontier
    S.toActualSelectedTopologyData

def toBoundaryCycleCertificate
    (S : OuterBoundaryCoreSource C) :
    OuterBoundaryCoreConstruction.BoundaryCycleCertificate
      (CanonicalGraph C) :=
  OuterBoundaryCoreConstruction.BoundaryCycleCertificate.ofCore S.core

def endpointNeighborInterval
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length)
    (k : Fin S.core.outerCycle.length) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      S.core.outerCycle k :=
  endpointNeighborIntervalOfOuterBoundaryCore S.core hcycle k

def orderedUnitNeighborData
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length)
    (k : Fin S.core.outerCycle.length) :
    BoundaryIndexOrderedUnitNeighborData S.core.outerCycle k
      (S.endpointNeighborInterval hcycle k) :=
  BoundaryIndexOrderedUnitNeighborData.ofEndpointNeighborInterval
    (S.endpointNeighborInterval hcycle k)

@[simp]
theorem toActualSelectedTopologyData_toOuterBoundaryCore
    (S : OuterBoundaryCoreSource C) :
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
        S.toActualSelectedTopologyData =
      S.core := by
  cases S
  rfl

@[simp]
theorem ofActualSelectedTopologyData_core
    (A : ActualSelectedTopologyData C) :
    (ofActualSelectedTopologyData A).core =
      ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
        A :=
  rfl

@[simp]
theorem ofOuterBoundaryCore_core
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (ofOuterBoundaryCore P).core = P :=
  rfl

@[simp]
theorem ofSelectedOuterFaceAndEnclosure_core
    (D : PlanarTopologyExtractionBridgeW25.SelectedOuterFaceData C)
    (E : PlanarTopologyExtractionBridgeW25.SelectedEnclosureData D) :
    (ofSelectedOuterFaceAndEnclosure D E).core =
      PlanarTopologyExtractionBridgeW25.SelectedEnclosureData.toCore E :=
  rfl

@[simp]
theorem ofMissingTopologyFacts_core
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    (ofMissingTopologyFacts T).core = T.toCore :=
  rfl

@[simp]
theorem ofConcreteTopologyFacts_core
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    (ofConcreteTopologyFacts T).core = T.toCore :=
  rfl

@[simp]
theorem ofPlanarBoundaryData_core
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (CanonicalGraph C)) :
    (ofPlanarBoundaryData P).core = P.core :=
  rfl

@[simp]
theorem toMissingTopologyFacts_toCore
    (S : OuterBoundaryCoreSource C) :
    S.toMissingTopologyFacts.toCore = S.core := by
  cases S
  rfl

@[simp]
theorem toConcreteTopologyFacts_toCore
    (S : OuterBoundaryCoreSource C) :
    S.toConcreteTopologyFacts.toCore = S.core := by
  cases S
  rfl

@[simp]
theorem toActualOuterBoundaryCycleData_core
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length) :
    (S.toActualOuterBoundaryCycleData hcycle).core = S.core :=
  rfl

theorem toActualOuterBoundaryCycleData_three_le_outerCycle_length
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length) :
    3 <= (S.toActualOuterBoundaryCycleData hcycle).outerCycle.length := by
  exact hcycle

@[simp]
theorem toBoundaryCycleCertificate_cycle
    (S : OuterBoundaryCoreSource C) :
    S.toBoundaryCycleCertificate.cycle = S.core.outerCycle :=
  rfl

theorem pairwiseNoncrossing
    (S : OuterBoundaryCoreSource C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  S.core.pairwiseNoncrossing

theorem outerCycle_vertex_injective
    (S : OuterBoundaryCoreSource C) :
    Function.Injective S.core.outerCycle.vertex :=
  S.core.outerCycle_vertex_injective

theorem outerCycle_edge_geometry_dist_eq_one
    (S : OuterBoundaryCoreSource C)
    (k : Fin S.core.outerCycle.length) :
    Geometry.Distance.eucDist (S.core.outerCycle.point k)
      (S.core.outerCycle.point
        (PlanarInterface.cyclicSucc S.core.outerCycle.length_pos k)) = 1 :=
  S.core.outerCycle_edge_geometry_dist_eq_one k

theorem all_vertices_insideOrOn
    (S : OuterBoundaryCoreSource C) (v : Fin n) :
    S.core.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  S.core.all_vertices_insideOrOn v

theorem onBoundary_iff_outerCycle
    (S : OuterBoundaryCoreSource C) (v : Fin n) :
    S.core.outerEnclosure.onBoundary v <->
      Exists fun k : Fin S.core.outerCycle.length =>
        S.core.outerCycle.vertex k = v :=
  S.core.onBoundary_iff_outer_cycle v

@[simp]
theorem endpointNeighborInterval_gapCount
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length)
    (k : Fin S.core.outerCycle.length) :
    (S.endpointNeighborInterval hcycle k).gapCount = 1 :=
  rfl

@[simp]
theorem orderedUnitNeighborData_gapCount
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length)
    (k : Fin S.core.outerCycle.length) :
    (S.orderedUnitNeighborData hcycle k).gapCount = 1 :=
  rfl

end OuterBoundaryCoreSource

variable (C : _root_.UDConfig n)

/-- The canonical graph-level facts are already available before any topology
source is supplied. -/
theorem concreteGraphFacts_available :
    OuterBoundaryExistenceConcrete.ConcreteGraphFacts C :=
  PlanarTopologyActualExtractionW26.concreteGraphFacts_available C

/-- The W28 source is exactly a checked outer-boundary core. -/
theorem nonempty_outerBoundaryCoreSource_iff_outerBoundaryCore :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.core
  case mpr =>
    intro h
    cases h with
    | intro P =>
        exact Nonempty.intro (OuterBoundaryCoreSource.ofOuterBoundaryCore P)

/-- A W28 source with a nondegenerate selected cycle is exactly the stronger
actual outer-boundary-cycle payload. -/
theorem nonempty_actualOuterBoundaryCycleData_iff_outerBoundaryCoreSource_with_length :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) <->
      Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact
          Exists.intro
            (OuterBoundaryCoreSource.ofOuterBoundaryCore D.core) (by
              exact D.three_le_outerCycle_length)
  case mpr =>
    intro h
    cases h with
    | intro S hS =>
        exact Nonempty.intro (S.toActualOuterBoundaryCycleData hS)

theorem outerBoundaryCoreSource_with_length_iff_actualOuterBoundaryCycleData :
    (Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length) <->
      Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) :=
  (nonempty_actualOuterBoundaryCycleData_iff_outerBoundaryCoreSource_with_length
    C).symm

/-- A concrete nondegenerate W28 source directly supplies the strong actual
outer-boundary-cycle target. -/
theorem nonempty_actualOuterBoundaryCycleData_of_outerBoundaryCoreSource
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) :=
  Nonempty.intro (S.toActualOuterBoundaryCycleData hcycle)

/-- The W28 nondegenerate source is exactly full missing-topology facts whose
selected cycle has length at least three. -/
theorem outerBoundaryCoreSource_with_length_iff_missingTopologyFacts_with_length :
    (Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length) <->
      Exists fun T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C =>
        3 <= T.outerCycle.length := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S hS =>
        exact Exists.intro S.toMissingTopologyFacts (by
          change 3 <= S.core.outerCycle.length
          exact hS)
  case mpr =>
    intro h
    cases h with
    | intro T hT =>
        exact Exists.intro
          (OuterBoundaryCoreSource.ofMissingTopologyFacts T) (by
            change 3 <= T.outerCycle.length
            exact hT)

/-- The W28 nondegenerate source is exactly the strong remaining topology
theorem from `JordanBoundaryConcrete`. -/
theorem outerBoundaryCoreSource_with_length_iff_remainingActualOuterBoundaryCycleTheorem :
    (Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length) <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C :=
  Iff.trans
    (outerBoundaryCoreSource_with_length_iff_actualOuterBoundaryCycleData C)
    Iff.rfl

theorem remainingActualOuterBoundaryCycleTheorem_iff_outerBoundaryCoreSource_with_length :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C <->
      Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length :=
  (outerBoundaryCoreSource_with_length_iff_remainingActualOuterBoundaryCycleTheorem
    C).symm

/-- A concrete nondegenerate W28 source closes the strong remaining
actual-cycle theorem. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_outerBoundaryCoreSource
    (S : OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  (outerBoundaryCoreSource_with_length_iff_remainingActualOuterBoundaryCycleTheorem
    C).1 (Exists.intro S hcycle)

/--
Finite-noncrossing actual outer-boundary theorem surface for the canonical
unit-distance graph.

The finite vertex type and pairwise noncrossing edge theorem are already built
into `CanonicalGraph C`; this source records only the remaining topology
payload: face-boundary data, a selected outer face, a nondegenerate selected
boundary cycle, and enclosure predicates for that same dependent face.
-/
def FiniteNoncrossingActualOuterBoundaryCycleSource
    (C : _root_.UDConfig n) : Prop :=
  Exists fun H :
      FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (CanonicalGraph C) =>
    Exists fun F : H.Face =>
      H.IsOuterFace F /\
        3 <= H.boundaryLength F /\
          Nonempty
            (OuterBoundaryInterface.OuterBoundaryEnclosure
              (CanonicalGraph C) H F)

/-- Direct constructor from the exact finite face-boundary fields exposed by
`FaceReduction`: selected outer face, nondegenerate boundary length, and
enclosure predicates for that same dependent face. -/
theorem finiteNoncrossingActualOuterBoundaryCycleSource_of_faceBoundaryFields
    {C : _root_.UDConfig n}
    {H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (CanonicalGraph C)}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hlen : 3 <= H.boundaryLength F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    FiniteNoncrossingActualOuterBoundaryCycleSource C := by
  exact
    Exists.intro H
      (Exists.intro F
        (And.intro hF
          (And.intro hlen (Nonempty.intro E))))

/-- A concrete extracted simple cyclic outer-boundary row supplies the
finite-noncrossing actual-cycle source once the matching enclosure predicates
are attached to the same row. -/
theorem finiteNoncrossingActualOuterBoundaryCycleSource_of_extractedSimpleCyclicOuterBoundaryRow_enclosure
    {C : _root_.UDConfig n}
    (R : OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryRow C)
    (insideOrOn : PlanarInterface.Point -> Prop)
    (onBoundary : Fin n -> Prop)
    (boundary_vertex_onBoundary :
      forall k : Fin R.length, onBoundary (R.vertex k))
    (boundary_point_insideOrOn :
      forall k : Fin R.length, insideOrOn ((CanonicalGraph C).point (R.vertex k)))
    (all_vertices_insideOrOn :
      forall v : Fin n, insideOrOn ((CanonicalGraph C).point v))
    (onBoundary_iff_outer_cycle :
      forall v : Fin n, onBoundary v <->
        Exists fun k : Fin R.length => R.vertex k = v) :
    FiniteNoncrossingActualOuterBoundaryCycleSource C := by
  let H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (CanonicalGraph C) :=
    R.toFaceBoundaryHypotheses
  let E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H PUnit.unit := {
    insideOrOn := insideOrOn
    onBoundary := onBoundary
    boundary_vertex_onBoundary := boundary_vertex_onBoundary
    boundary_point_insideOrOn := boundary_point_insideOrOn
    all_vertices_insideOrOn := all_vertices_insideOrOn
    onBoundary_iff_outer_cycle := onBoundary_iff_outer_cycle }
  exact
    finiteNoncrossingActualOuterBoundaryCycleSource_of_faceBoundaryFields
      (C := C) (H := H) (F := PUnit.unit)
      (OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryRow.toFaceBoundaryHypotheses_isOuterFace R)
      (OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryRow.toFaceBoundaryHypotheses_boundaryLength_ge_three R)
      E

theorem finiteNoncrossingActualOuterBoundaryCycleSource_iff_faceBoundaryFields
    (C : _root_.UDConfig n) :
    FiniteNoncrossingActualOuterBoundaryCycleSource C <->
      Exists fun H :
          FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
            (CanonicalGraph C) =>
        Exists fun F : H.Face =>
          H.IsOuterFace F /\
            3 <= H.boundaryLength F /\
              Nonempty
                (OuterBoundaryInterface.OuterBoundaryEnclosure
                  (CanonicalGraph C) H F) := by
  rfl

/-- Concrete inhabited source for the strong S2 lane: a W28 core source plus
the nondegenerate selected outer-cycle length proof. -/
structure OuterBoundaryCoreSourceWithLength
    (C : _root_.UDConfig n) where
  source : OuterBoundaryCoreSource C
  outerCycle_length_ge_three : 3 <= source.core.outerCycle.length

namespace OuterBoundaryCoreSourceWithLength

variable {C : _root_.UDConfig n}

/-- Build the concrete source-with-length package from an already supplied
outer-boundary core and a nondegenerate selected-cycle proof. -/
def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C))
    (hcycle : 3 <= P.outerCycle.length) :
    OuterBoundaryCoreSourceWithLength C where
  source := OuterBoundaryCoreSource.ofOuterBoundaryCore P
  outerCycle_length_ge_three := by
    change 3 <= P.outerCycle.length
    exact hcycle

/-- Build the concrete source-with-length package from the stronger actual
outer-boundary-cycle data. -/
def ofActualOuterBoundaryCycleData
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) :
    OuterBoundaryCoreSourceWithLength C :=
  ofOuterBoundaryCore D.core D.outerCycle_length_ge_three

/-- Build the concrete source-with-length package directly from the finite
noncrossing theorem fields for the canonical unit-distance graph. -/
def ofFiniteNoncrossingFields
    {H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (CanonicalGraph C)}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hlen : 3 <= H.boundaryLength F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    OuterBoundaryCoreSourceWithLength C where
  source :=
    OuterBoundaryCoreSource.ofOuterBoundaryCore
      { faceBoundary := H
        outerFace := F
        outerFace_isOuter := hF
        outerEnclosure := E }
  outerCycle_length_ge_three := by
    change 3 <= H.boundaryLength F
    exact hlen

/-- Forget the concrete package wrapper into the existing existential
source-with-length surface. -/
theorem exists_source_with_length
    (S : OuterBoundaryCoreSourceWithLength C) :
    Exists fun W : OuterBoundaryCoreSource C =>
      3 <= W.core.outerCycle.length :=
  Exists.intro S.source S.outerCycle_length_ge_three

/-- The recorded face-boundary length is the same nondegenerate length carried
by the selected outer cycle. -/
theorem boundaryLength_ge_three
    (S : OuterBoundaryCoreSourceWithLength C) :
    3 <= S.source.core.faceBoundary.boundaryLength S.source.core.outerFace := by
  change 3 <= S.source.core.outerCycle.length
  exact S.outerCycle_length_ge_three

/-- The nondegenerate W28 source-with-length package supplies the concrete
endpoint-neighbour interval at every selected boundary index. -/
def endpointNeighborInterval
    (S : OuterBoundaryCoreSourceWithLength C)
    (k : Fin S.source.core.outerCycle.length) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      S.source.core.outerCycle k :=
  S.source.endpointNeighborInterval S.outerCycle_length_ge_three k

/-- The concrete nondegenerate W28 source-with-length package supplies
endpoint-compatible ordered unit-neighbor rows at every selected boundary
index. -/
def orderedUnitNeighborData
    (S : OuterBoundaryCoreSourceWithLength C)
    (k : Fin S.source.core.outerCycle.length) :
    BoundaryIndexOrderedUnitNeighborData S.source.core.outerCycle k
      (S.endpointNeighborInterval k) :=
  S.source.orderedUnitNeighborData S.outerCycle_length_ge_three k

@[simp]
theorem endpointNeighborInterval_gapCount
    (S : OuterBoundaryCoreSourceWithLength C)
    (k : Fin S.source.core.outerCycle.length) :
    (S.endpointNeighborInterval k).gapCount = 1 :=
  rfl

@[simp]
theorem orderedUnitNeighborData_gapCount
    (S : OuterBoundaryCoreSourceWithLength C)
    (k : Fin S.source.core.outerCycle.length) :
    (S.orderedUnitNeighborData k).gapCount = 1 :=
  rfl

/-- The dependent enclosure field is part of the same core whose length is
recorded by the source-with-length package. -/
theorem outerEnclosure_nonempty
    (S : OuterBoundaryCoreSourceWithLength C) :
    Nonempty
      (OuterBoundaryInterface.OuterBoundaryEnclosure
        (CanonicalGraph C) S.source.core.faceBoundary S.source.core.outerFace) :=
  Nonempty.intro S.source.core.outerEnclosure

/-- Forget the concrete package to the exact finite-noncrossing field source:
the selected face, nondegenerate length, and enclosure all come from the same
outer-boundary core. -/
theorem toFiniteNoncrossingActualOuterBoundaryCycleSource
    (S : OuterBoundaryCoreSourceWithLength C) :
    FiniteNoncrossingActualOuterBoundaryCycleSource C :=
  Exists.intro S.source.core.faceBoundary
    (Exists.intro S.source.core.outerFace
      (And.intro S.source.core.outerFace_isOuter
        (And.intro S.boundaryLength_ge_three S.outerEnclosure_nonempty)))

/-- The concrete source-with-length package directly supplies the strong
actual boundary-cycle data. -/
def toActualOuterBoundaryCycleData
    (S : OuterBoundaryCoreSourceWithLength C) :
    JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C :=
  S.source.toActualOuterBoundaryCycleData S.outerCycle_length_ge_three

/-- The concrete source-with-length package directly closes the strong
remaining actual-cycle target. -/
theorem remainingActualOuterBoundaryCycleTheorem
    (S : OuterBoundaryCoreSourceWithLength C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  Nonempty.intro S.toActualOuterBoundaryCycleData

end OuterBoundaryCoreSourceWithLength

/-- Strong actual outer-boundary-cycle data supplies the endpoint-neighbour
intervals from its real selected cycle. -/
def endpointNeighborIntervalOfActualOuterBoundaryCycleData
    {C : _root_.UDConfig n}
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{u} C)
    (k : Fin D.outerCycle.length) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      D.outerCycle k :=
  endpointNeighborIntervalOfBoundaryCycle
    D.outerCycle D.three_le_outerCycle_length k

/-- Strong actual outer-boundary-cycle data supplies endpoint-compatible
ordered unit-neighbor rows from the real selected cycle. -/
def orderedUnitNeighborDataOfActualOuterBoundaryCycleData
    {C : _root_.UDConfig n}
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{u} C)
    (k : Fin D.outerCycle.length) :
    BoundaryIndexOrderedUnitNeighborData D.outerCycle k
      (endpointNeighborIntervalOfActualOuterBoundaryCycleData D k) :=
  BoundaryIndexOrderedUnitNeighborData.ofEndpointNeighborInterval
    (endpointNeighborIntervalOfActualOuterBoundaryCycleData D k)

@[simp]
theorem endpointNeighborIntervalOfActualOuterBoundaryCycleData_gapCount
    {C : _root_.UDConfig n}
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{u} C)
    (k : Fin D.outerCycle.length) :
    (endpointNeighborIntervalOfActualOuterBoundaryCycleData D k).gapCount = 1 :=
  rfl

@[simp]
theorem orderedUnitNeighborDataOfActualOuterBoundaryCycleData_gapCount
    {C : _root_.UDConfig n}
    (D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{u} C)
    (k : Fin D.outerCycle.length) :
    (orderedUnitNeighborDataOfActualOuterBoundaryCycleData D k).gapCount = 1 :=
  rfl

/-- A chosen Jordan outer-component cycle supplies the same endpoint-neighbour
intervals before it is repackaged as face-boundary data. -/
def endpointNeighborIntervalOfChosenJordanOuterComponentRow
    {C : _root_.UDConfig n}
    (row : JordanBoundaryConcrete.ChosenJordanOuterComponentRow C)
    (k : Fin row.boundary.toBoundaryCycle.length) :
    OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval
      row.boundary.toBoundaryCycle k :=
  endpointNeighborIntervalOfBoundaryCycle row.boundary.toBoundaryCycle
    (by
      change 3 <= row.boundary.length
      exact row.boundary.length_ge_three)
    k

/-- A chosen Jordan outer-component cycle supplies endpoint-compatible ordered
unit-neighbor rows before it is repackaged as face-boundary data. -/
def orderedUnitNeighborDataOfChosenJordanOuterComponentRow
    {C : _root_.UDConfig n}
    (row : JordanBoundaryConcrete.ChosenJordanOuterComponentRow C)
    (k : Fin row.boundary.toBoundaryCycle.length) :
    BoundaryIndexOrderedUnitNeighborData row.boundary.toBoundaryCycle k
      (endpointNeighborIntervalOfChosenJordanOuterComponentRow row k) :=
  BoundaryIndexOrderedUnitNeighborData.ofEndpointNeighborInterval
    (endpointNeighborIntervalOfChosenJordanOuterComponentRow row k)

@[simp]
theorem endpointNeighborIntervalOfChosenJordanOuterComponentRow_gapCount
    {C : _root_.UDConfig n}
    (row : JordanBoundaryConcrete.ChosenJordanOuterComponentRow C)
    (k : Fin row.boundary.toBoundaryCycle.length) :
    (endpointNeighborIntervalOfChosenJordanOuterComponentRow row k).gapCount =
      1 :=
  rfl

@[simp]
theorem orderedUnitNeighborDataOfChosenJordanOuterComponentRow_gapCount
    {C : _root_.UDConfig n}
    (row : JordanBoundaryConcrete.ChosenJordanOuterComponentRow C)
    (k : Fin row.boundary.toBoundaryCycle.length) :
    (orderedUnitNeighborDataOfChosenJordanOuterComponentRow row k).gapCount =
      1 :=
  rfl

/-- The existential source-with-length surface is the nonemptiness of the
concrete source-with-length package. -/
theorem outerBoundaryCoreSource_with_length_iff_nonempty_outerBoundaryCoreSourceWithLength :
    (Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length) <->
      Nonempty (OuterBoundaryCoreSourceWithLength C) := by
  constructor
  · rintro ⟨S, hS⟩
    exact
      Nonempty.intro
        { source := S
          outerCycle_length_ge_three := hS }
  · rintro ⟨S⟩
    exact S.exists_source_with_length

/-- Nonempty concrete source-with-length packages are exactly the existing
existential source-with-length surface. -/
theorem nonempty_outerBoundaryCoreSourceWithLength_iff_outerBoundaryCoreSource_with_length :
    Nonempty (OuterBoundaryCoreSourceWithLength C) <->
      Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length :=
  (outerBoundaryCoreSource_with_length_iff_nonempty_outerBoundaryCoreSourceWithLength
    C).symm

theorem nonempty_actualOuterBoundaryCycleData_iff_nonempty_outerBoundaryCoreSourceWithLength :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) <->
      Nonempty (OuterBoundaryCoreSourceWithLength C) :=
  Iff.trans
    (nonempty_actualOuterBoundaryCycleData_iff_outerBoundaryCoreSource_with_length
      C)
    (outerBoundaryCoreSource_with_length_iff_nonempty_outerBoundaryCoreSourceWithLength
      C)

/-- The finite-noncrossing field source inhabits the concrete W28
source-with-length package. -/
theorem nonempty_outerBoundaryCoreSourceWithLength_of_finiteNoncrossingActualOuterBoundaryCycleSource
    (h : FiniteNoncrossingActualOuterBoundaryCycleSource C) :
    Nonempty (OuterBoundaryCoreSourceWithLength C) := by
  rcases h with ⟨H, F, hF, hlen, ⟨E⟩⟩
  exact
    Nonempty.intro
      (OuterBoundaryCoreSourceWithLength.ofFiniteNoncrossingFields
        (C := C) (H := H) (F := F) hF hlen E)

theorem finiteNoncrossingActualOuterBoundaryCycleSource_of_outerBoundaryCoreSourceWithLength
    (S : OuterBoundaryCoreSourceWithLength C) :
    FiniteNoncrossingActualOuterBoundaryCycleSource C :=
  S.toFiniteNoncrossingActualOuterBoundaryCycleSource

theorem finiteNoncrossingActualOuterBoundaryCycleSource_iff_nonempty_outerBoundaryCoreSourceWithLength :
    FiniteNoncrossingActualOuterBoundaryCycleSource C <->
      Nonempty (OuterBoundaryCoreSourceWithLength C) := by
  constructor
  · exact
      nonempty_outerBoundaryCoreSourceWithLength_of_finiteNoncrossingActualOuterBoundaryCycleSource
        C
  · rintro ⟨S⟩
    exact S.toFiniteNoncrossingActualOuterBoundaryCycleSource

/-- Concrete finite-noncrossing fields close the strong remaining actual-cycle
target through the W28 source-with-length package. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_finiteNoncrossingFields
    {H : FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0} (CanonicalGraph C)}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hlen : 3 <= H.boundaryLength F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  (OuterBoundaryCoreSourceWithLength.ofFiniteNoncrossingFields
    (C := C) (H := H) (F := F) hF hlen E).remainingActualOuterBoundaryCycleTheorem

/-- The finite-noncrossing source gives the W28 source-with-length package. -/
theorem outerBoundaryCoreSource_with_length_of_finiteNoncrossingActualOuterBoundaryCycleSource
    (h : FiniteNoncrossingActualOuterBoundaryCycleSource C) :
    Exists fun S : OuterBoundaryCoreSource C =>
      3 <= S.core.outerCycle.length := by
  rcases
      nonempty_outerBoundaryCoreSourceWithLength_of_finiteNoncrossingActualOuterBoundaryCycleSource
        (C := C) h with
    ⟨S⟩
  exact S.exists_source_with_length

/-- A W28 source-with-length package is exactly the finite-noncrossing source
fields with the automatic graph facts removed. -/
theorem finiteNoncrossingActualOuterBoundaryCycleSource_of_outerBoundaryCoreSource_with_length
    (h :
      Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length) :
    FiniteNoncrossingActualOuterBoundaryCycleSource C := by
  rcases h with ⟨S, hS⟩
  exact
    ⟨S.core.faceBoundary, S.core.outerFace, S.core.outerFace_isOuter,
      by
        change 3 <= S.core.outerCycle.length
        exact hS,
      ⟨S.core.outerEnclosure⟩⟩

theorem finiteNoncrossingActualOuterBoundaryCycleSource_iff_outerBoundaryCoreSource_with_length :
    FiniteNoncrossingActualOuterBoundaryCycleSource C <->
      Exists fun S : OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length := by
  constructor
  · exact
      outerBoundaryCoreSource_with_length_of_finiteNoncrossingActualOuterBoundaryCycleSource
        C
  · exact
      finiteNoncrossingActualOuterBoundaryCycleSource_of_outerBoundaryCoreSource_with_length
        C

/-- The strong remaining actual-cycle target reduces exactly to the
finite-noncrossing outer-boundary theorem surface above. -/
theorem remainingActualOuterBoundaryCycleTheorem_iff_finiteNoncrossingActualOuterBoundaryCycleSource :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C <->
      FiniteNoncrossingActualOuterBoundaryCycleSource C :=
  Iff.trans
    (remainingActualOuterBoundaryCycleTheorem_iff_outerBoundaryCoreSource_with_length
      C)
    (finiteNoncrossingActualOuterBoundaryCycleSource_iff_outerBoundaryCoreSource_with_length
      C).symm

theorem finiteNoncrossingActualOuterBoundaryCycleSource_iff_remainingActualOuterBoundaryCycleTheorem :
    FiniteNoncrossingActualOuterBoundaryCycleSource C <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C :=
  (remainingActualOuterBoundaryCycleTheorem_iff_finiteNoncrossingActualOuterBoundaryCycleSource
    C).symm

theorem remainingActualOuterBoundaryCycleTheorem_iff_nonempty_outerBoundaryCoreSourceWithLength :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C <->
      Nonempty (OuterBoundaryCoreSourceWithLength C) :=
  Iff.trans
    (remainingActualOuterBoundaryCycleTheorem_iff_outerBoundaryCoreSource_with_length
      C)
    (outerBoundaryCoreSource_with_length_iff_nonempty_outerBoundaryCoreSourceWithLength
      C)

theorem nonempty_outerBoundaryCoreSourceWithLength_iff_remainingActualOuterBoundaryCycleTheorem :
    Nonempty (OuterBoundaryCoreSourceWithLength C) <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C :=
  (remainingActualOuterBoundaryCycleTheorem_iff_nonempty_outerBoundaryCoreSourceWithLength
    C).symm

theorem remainingActualOuterBoundaryCycleTheorem_of_outerBoundaryCoreSourceWithLength
    (S : OuterBoundaryCoreSourceWithLength C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  S.remainingActualOuterBoundaryCycleTheorem

/-- The empty configuration is a checked obstruction to any global
source-with-length theorem stated for arbitrary `UDConfig`s. -/
def emptyUDConfig : _root_.UDConfig 0 where
  pts := fun i => Fin.elim0 i
  sep := by
    intro i
    exact Fin.elim0 i

theorem not_nonempty_outerBoundaryCoreSourceWithLength_emptyUDConfig :
    ¬ Nonempty (OuterBoundaryCoreSourceWithLength emptyUDConfig) := by
  rintro ⟨S⟩
  have hpos : 0 < S.source.core.outerCycle.length :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3)
      S.outerCycle_length_ge_three
  exact Fin.elim0 (S.source.core.outerCycle.vertex ⟨0, hpos⟩)

/-- Concrete feeder: a finite-noncrossing nondegenerate outer-boundary cycle
source closes `JordanBoundaryConcrete`'s strong remaining actual-cycle target. -/
theorem remainingActualOuterBoundaryCycleTheorem_of_finiteNoncrossingActualOuterBoundaryCycleSource
    (h : FiniteNoncrossingActualOuterBoundaryCycleSource C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  (finiteNoncrossingActualOuterBoundaryCycleSource_iff_remainingActualOuterBoundaryCycleTheorem
    C).1 h

/-- The W28 source is exactly the W27 actual selected-topology datum. -/
theorem nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (ActualSelectedTopologyData C) :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_outerBoundaryCore C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_outerBoundaryCore
      C).symm

/-- The W28 source is exactly the split selected-face/enclosure payload. -/
theorem nonempty_outerBoundaryCoreSource_iff_splitExactTopologyFields :
    Nonempty (OuterBoundaryCoreSource C) <->
      SplitExactTopologyFields C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (PlanarTopologyActualExtractionW26.nonempty_actualSelectedTopologyData_iff_splitExactTopologyFields
      C)

/-- The W28 source is exactly the raw exact topology field list. -/
theorem nonempty_outerBoundaryCoreSource_iff_exactTopologyFields :
    Nonempty (OuterBoundaryCoreSource C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_exactTopologyFields
      C)

/-- The W28 source is exactly the old missing-topology wrapper. -/
theorem nonempty_outerBoundaryCoreSource_iff_missingTopologyFacts :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_missingTopologyFacts
      C)

/-- The W28 source is exactly the concrete topology-facts wrapper. -/
theorem nonempty_outerBoundaryCoreSource_iff_concreteTopologyFacts :
    Nonempty (OuterBoundaryCoreSource C) <->
      Nonempty (JordanTopologyFactsConcrete.TopologyFacts.{0} C) :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_concreteTopologyFacts
      C)

/-- The W28 source is exactly the remaining core-topology target. -/
theorem nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology :
    Nonempty (OuterBoundaryCoreSource C) <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_remainingCoreTopology
      C)

/-- The W28 source is exactly the noncrossing-to-topology frontier. -/
theorem nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier :
    Nonempty (OuterBoundaryCoreSource C) <->
      ConcreteNoncrossingTopologyFrontier C :=
  Iff.trans
    (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_noncrossingFrontier
      C)

/-- The frontier is the automatic graph facts plus the W28 core source. -/
theorem noncrossingFrontier_iff_graphFacts_and_outerBoundaryCoreSource :
    ConcreteNoncrossingTopologyFrontier C <->
      OuterBoundaryExistenceConcrete.ConcreteGraphFacts C /\
        Nonempty (OuterBoundaryCoreSource C) := by
  constructor
  case mp =>
    intro h
    exact
      And.intro h.1
        ((nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).2 h)
  case mpr =>
    intro h
    exact
      (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).1 h.2

/-- Full planar-boundary data contains the W28 core source by forgetting
angle and subpolygon fields. -/
theorem nonempty_outerBoundaryCoreSource_of_planarBoundaryData
    (P : PlanarBoundaryClosure.PlanarBoundaryData.{u, 0}
      (CanonicalGraph C)) :
    Nonempty (OuterBoundaryCoreSource C) :=
  Nonempty.intro (OuterBoundaryCoreSource.ofPlanarBoundaryData P)

/-- Concrete topology facts provide the W28 core source. -/
theorem nonempty_outerBoundaryCoreSource_of_concreteTopologyFacts
    (T : JordanTopologyFactsConcrete.TopologyFacts.{0} C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  Nonempty.intro (OuterBoundaryCoreSource.ofConcreteTopologyFacts T)

/-- Missing-topology facts provide the W28 core source. -/
theorem nonempty_outerBoundaryCoreSource_of_missingTopologyFacts
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  Nonempty.intro (OuterBoundaryCoreSource.ofMissingTopologyFacts T)

/-- Exact topology fields provide the W28 source, with graph facts still
coming from the canonical unit-distance theorem. -/
theorem nonempty_outerBoundaryCoreSource_of_exactTopologyFields
    (h : OuterBoundaryExistenceConcrete.ExactTopologyFields C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  (nonempty_outerBoundaryCoreSource_iff_exactTopologyFields C).2 h

/-- The concrete frontier provides the W28 source. -/
theorem nonempty_outerBoundaryCoreSource_of_noncrossingFrontier
    (h : ConcreteNoncrossingTopologyFrontier C) :
    Nonempty (OuterBoundaryCoreSource C) :=
  (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).2 h

def GlobalOuterBoundaryCoreSourceTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (OuterBoundaryCoreSource C)

/-- The global W28 source target is the same as the W26 selected-topology
extraction target. -/
theorem globalOuterBoundaryCoreSourceTarget_iff_actualSelectedTopology :
    GlobalOuterBoundaryCoreSourceTarget <->
      PlanarTopologyActualExtractionW26.GlobalActualSelectedTopologyExtractionTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData C).2
      (h n C)

/-- The global W28 source target is the same as the W10/W26 outer-boundary
core construction target. -/
theorem globalOuterBoundaryCoreSourceTarget_iff_outerBoundaryCoreTarget :
    GlobalOuterBoundaryCoreSourceTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_remainingCoreTopology C).2
      (h n C)

/-- The global W28 source target is also exactly the concrete noncrossing
frontier target; the graph half of that frontier is already automatic. -/
theorem globalOuterBoundaryCoreSourceTarget_iff_noncrossingFrontier :
    GlobalOuterBoundaryCoreSourceTarget <->
      forall (n : Nat) (C : _root_.UDConfig n),
        ConcreteNoncrossingTopologyFrontier C := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier C).2
      (h n C)

end

end OuterBoundaryCoreConstructionW28

namespace Verified

open Swanepoel.OuterBoundaryCoreConstructionW28

abbrev SwanepoelW28OuterBoundaryCoreSource
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource C

abbrev SwanepoelW28FiniteNoncrossingActualOuterBoundaryCycleSource
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.OuterBoundaryCoreConstructionW28.FiniteNoncrossingActualOuterBoundaryCycleSource
    C

theorem swanepoelW28_outerBoundaryCoreSource_exactly_actualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW28OuterBoundaryCoreSource C) <->
      Nonempty
        (Swanepoel.ActualSelectedTopologyDataW27.ActualSelectedTopologyData
          C) :=
  Swanepoel.OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_actualSelectedTopologyData
    C

theorem swanepoelW28_outerBoundaryCoreSource_exactly_concreteFrontier
    {n : Nat} (C : _root_.UDConfig n) :
      Nonempty (SwanepoelW28OuterBoundaryCoreSource C) <->
      Swanepoel.TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier
        C :=
  Swanepoel.OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSource_iff_noncrossingFrontier
    C

theorem swanepoelW28_remainingActualOuterBoundaryCycle_exactly_finiteNoncrossingActualOuterBoundaryCycleSource
    {n : Nat} (C : _root_.UDConfig n) :
    Swanepoel.JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C <->
      SwanepoelW28FiniteNoncrossingActualOuterBoundaryCycleSource C :=
  Swanepoel.OuterBoundaryCoreConstructionW28.remainingActualOuterBoundaryCycleTheorem_iff_finiteNoncrossingActualOuterBoundaryCycleSource
    C

theorem swanepoelW28_remainingActualOuterBoundaryCycle_of_finiteNoncrossingActualOuterBoundaryCycleSource
    {n : Nat} {C : _root_.UDConfig n}
    (h : SwanepoelW28FiniteNoncrossingActualOuterBoundaryCycleSource C) :
    Swanepoel.JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  Swanepoel.OuterBoundaryCoreConstructionW28.remainingActualOuterBoundaryCycleTheorem_of_finiteNoncrossingActualOuterBoundaryCycleSource
    C h

theorem swanepoelW28_globalSource_exactly_globalCoreTarget :
    Swanepoel.OuterBoundaryCoreConstructionW28.GlobalOuterBoundaryCoreSourceTarget <->
      Swanepoel.OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Swanepoel.OuterBoundaryCoreConstructionW28.globalOuterBoundaryCoreSourceTarget_iff_outerBoundaryCoreTarget

end Verified
end Swanepoel
end ErdosProblems1066
