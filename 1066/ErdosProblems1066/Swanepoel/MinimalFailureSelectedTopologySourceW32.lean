import ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
import ErdosProblems1066.Swanepoel.JordanBoundaryConcreteInhabitationW24
import ErdosProblems1066.Swanepoel.MinimalFailureConcreteDataMatrix
import ErdosProblems1066.Swanepoel.SelectedFaceEnclosureBridgeW32

set_option autoImplicit false

/-!
# W32 minimal-failure selected topology source

The W32 selected-face/enclosure route is a topology source: it is exactly the
checked face-boundary/enclosure payload, or equivalently concrete topology
facts / an `OuterBoundaryCore`. Minimality supplies the positive-cardinality
field needed by the graph route, but it does not by itself manufacture the
selected outer face and enclosure.

This file records that honest boundary. For a fixed minimal cleared failure,
the strongest checked source is indexed by `hmin` and reduces precisely to the
remaining concrete topology field. The global all-configuration source target
is also marked as false, with the empty configuration as witness.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureSelectedTopologySourceW32

universe u

noncomputable section

open JordanTopologyFactsConcrete.MinimalFailureTopology

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureBridgeW32.CanonicalGraph C

abbrev SelectedFaceEnclosureRoute (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureBridgeW32.SelectedFaceEnclosureRoute C

abbrev SelectedOuterFaceSource (C : _root_.UDConfig n) :=
  SelectedFaceEnclosureBridgeW32.SelectedOuterFaceSource C

abbrev JordanSourceFields (C : _root_.UDConfig n) :=
  FaceBoundaryTopologySourceW32.JordanSourceFields C

abbrev MissingOuterFaceData (C : _root_.UDConfig n) :=
  JordanBoundaryConcrete.MissingOuterFaceData.{0} C

abbrev TopologyBoundary (C : _root_.UDConfig n) :=
  OuterBoundaryCore.{0} (CanonicalGraph C)

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  JordanTopologyFactsConcrete.TopologyFacts.{0} C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

abbrev MissingTopologyFacts (C : _root_.UDConfig n) :=
  JordanBoundaryConcrete.MissingTopologyFacts.{0} C

abbrev MinimalExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  JordanTopologyFactsConcrete.MinimalFailureTopology.ExactOuterBoundaryTopologyFields C

abbrev RemainingCoreTopology (C : _root_.UDConfig n) : Prop :=
  OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C

abbrev ExactTopologyFields (C : _root_.UDConfig n) : Prop :=
  OuterBoundaryExistenceConcrete.ExactTopologyFields C

abbrev MinimalBoundaryTopologyWitnessFamily : Type (u + 1) :=
  JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologyWitnessFamily.{u}

theorem positiveCard_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    0 < n :=
  MinimalFailureConcreteDataMatrix.positiveCard_of_minimalClearedFailure
    hmin

/-! ## Concrete selected outer-face payload from minimality -/

/-- A minimal cleared failure contains an actual unit-distance edge. -/
theorem exists_unitDistanceAdj_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Exists fun u : Fin n =>
      Exists fun v : Fin n =>
        GraphBridge.UnitDistanceAdj C u v := by
  let u : Fin n :=
    ⟨0, positiveCard_of_minimalClearedFailure (C := C) hmin⟩
  have hdeg :
      3 <= (DegreePipeline.unitDistanceNeighborSet C u).card :=
    CutVertexFinal.minimumDegree_of_minimalFailure hmin u
  have hpos :
      0 < (DegreePipeline.unitDistanceNeighborSet C u).card :=
    Nat.lt_of_lt_of_le (by decide) hdeg
  rcases Finset.card_pos.mp hpos with ⟨v, hv⟩
  have hvprop :
      v != u /\ _root_.eucDist (C.pts v) (C.pts u) = 1 :=
    (DegreePipeline.mem_unitDistanceNeighborSet C u v).1 hv
  have hdist : _root_.eucDist (C.pts u) (C.pts v) = 1 := by
    simpa [_root_.eucDist_comm] using hvprop.2
  exact ⟨u, v, (GraphBridge.unitDistanceAdj_iff C u v).2 hdist⟩

/-- Package one oriented unit edge as selected outer-face data for the current
face-boundary interface. -/
def missingOuterFaceDataOfUnitDistanceAdj
    {C : _root_.UDConfig n} {u v : Fin n}
    (hAdj : GraphBridge.UnitDistanceAdj C u v) :
    MissingOuterFaceData C where
  faceBoundary :=
    FaceReduction.UnitDistanceFaceBoundaryHypotheses.ofAdjacentPair
      (CanonicalGraph C) (((CanonicalGraph C).adj_iff_unitDistanceAdj u v).2 hAdj)
  outerFace := PUnit.unit
  outerFace_isOuter := trivial

/-- Minimality supplies the selected outer-face payload requested by W32. -/
def missingOuterFaceDataOfMinimalClearedFailure
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MissingOuterFaceData C := by
  let u : Fin n :=
    ⟨0, positiveCard_of_minimalClearedFailure (C := C) hmin⟩
  let neighbors := DegreePipeline.unitDistanceNeighborSet C u
  have hdeg : 3 <= neighbors.card :=
    CutVertexFinal.minimumDegree_of_minimalFailure hmin u
  have hpos : 0 < neighbors.card :=
    Nat.lt_of_lt_of_le (by decide) hdeg
  have hne : neighbors.Nonempty :=
    Finset.card_pos.mp hpos
  let v : Fin n := neighbors.min' hne
  have hv : v ∈ neighbors :=
    neighbors.min'_mem hne
  have hvprop :
      v != u /\ _root_.eucDist (C.pts v) (C.pts u) = 1 :=
    (DegreePipeline.mem_unitDistanceNeighborSet C u v).1 hv
  have hdist : _root_.eucDist (C.pts u) (C.pts v) = 1 := by
    simpa [_root_.eucDist_comm] using hvprop.2
  have hAdj : GraphBridge.UnitDistanceAdj C u v :=
    (GraphBridge.unitDistanceAdj_iff C u v).2 hdist
  exact missingOuterFaceDataOfUnitDistanceAdj
    (C := C) (u := u) (v := v) hAdj

/-- Exact remaining selected topology payload: every minimal cleared failure
has selected outer-face/boundary data in the `MissingOuterFaceData` interface. -/
theorem nonempty_missingOuterFaceData_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (MissingOuterFaceData C) :=
  ⟨missingOuterFaceDataOfMinimalClearedFailure C hmin⟩

theorem route_nonempty_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (TopologyBoundary C) :=
  SelectedFaceEnclosureBridgeW32.nonempty_route_iff_outerBoundaryCore C

theorem route_nonempty_iff_jordanSourceFields
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (JordanSourceFields C) :=
  Iff.trans (route_nonempty_iff_outerBoundaryCore C)
    (FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_outerBoundaryCore
      C).symm

theorem route_nonempty_iff_selectedOuterFaceSource
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (SelectedOuterFaceSource C) :=
  SelectedFaceEnclosureBridgeW32.nonempty_route_iff_selectedOuterFaceSource
    C

theorem route_nonempty_iff_missingOuterFaceData
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (MissingOuterFaceData C) := by
  constructor
  case mp =>
    intro h
    rcases (route_nonempty_iff_selectedOuterFaceSource C).1 h with ⟨S⟩
    exact
      ⟨{
        faceBoundary := S.faceBoundary
        outerFace := S.outerFace
        outerFace_isOuter := S.outerFace_isOuter }⟩
  case mpr =>
    intro h
    rcases h with ⟨D⟩
    exact
      (route_nonempty_iff_selectedOuterFaceSource C).2
        ⟨SelectedOuterFaceConstructionW31.SelectedOuterFaceSource.ofRaw
          D.faceBoundary D.outerFace D.outerFace_isOuter⟩

theorem route_nonempty_iff_minimalExactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      MinimalExactTopologyFields C :=
  Iff.trans (route_nonempty_iff_outerBoundaryCore C)
    (exactOuterBoundaryTopologyFields_iff_outerBoundaryCore C).symm

theorem route_nonempty_iff_concreteTopologyFacts
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (ConcreteTopologyFacts C) :=
  Iff.trans (route_nonempty_iff_minimalExactTopologyFields C)
    (exactOuterBoundaryTopologyFields_iff_topologyFacts C)

theorem route_nonempty_iff_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (ActualSelectedTopologyData C) :=
  SelectedFaceEnclosureBridgeW32.nonempty_route_iff_actualSelectedTopologyData
    C

theorem route_nonempty_iff_missingTopologyFacts
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      Nonempty (MissingTopologyFacts C) :=
  Iff.trans (route_nonempty_iff_minimalExactTopologyFields C)
    (exactOuterBoundaryTopologyFields_iff_missingTopologyFacts C)

theorem route_nonempty_iff_remainingCoreTopology
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      RemainingCoreTopology C :=
  Iff.trans (route_nonempty_iff_jordanSourceFields C)
    (FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_remainingCoreTopology
      C)

theorem route_nonempty_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      ExactTopologyFields C :=
  Iff.trans (route_nonempty_iff_jordanSourceFields C)
    (FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_exactTopologyFields
      C)

def routeOfOuterBoundaryCore
    {C : _root_.UDConfig n}
    (P : TopologyBoundary C) :
    SelectedFaceEnclosureRoute C :=
  SelectedFaceEnclosureBridgeW32.ofOuterBoundaryCore P

def routeOfConcreteTopologyFacts
    {C : _root_.UDConfig n}
    (T : ConcreteTopologyFacts C) :
    SelectedFaceEnclosureRoute C :=
  routeOfOuterBoundaryCore T.toCore

theorem nonempty_route_of_concreteTopologyFacts
    {C : _root_.UDConfig n}
    (T : ConcreteTopologyFacts C) :
    Nonempty (SelectedFaceEnclosureRoute C) :=
  Nonempty.intro (routeOfConcreteTopologyFacts T)

/-- A selected-face/enclosure route directly supplies the exact dependent
outer-boundary topology payload. -/
theorem minimalExactTopologyFields_of_route
    {C : _root_.UDConfig n}
    (R : SelectedFaceEnclosureRoute C) :
    MinimalExactTopologyFields C :=
  ⟨R.selectedOuterFace.faceBoundary,
    R.selectedOuterFace.outerFace,
    R.selectedOuterFace.outerFace_isOuter,
    ⟨R.outerEnclosure⟩⟩

/-- Direct form of the route/exact-field equivalence, spelling out the raw
face-boundary, selected outer face, and enclosure payload. -/
theorem route_nonempty_iff_minimalExactTopologyFields_direct
    (C : _root_.UDConfig n) :
    Nonempty (SelectedFaceEnclosureRoute C) <->
      MinimalExactTopologyFields C := by
  constructor
  case mp =>
    rintro ⟨R⟩
    exact minimalExactTopologyFields_of_route R
  case mpr =>
    rintro ⟨H, F, hF, ⟨E⟩⟩
    exact
      Nonempty.intro
        (SelectedFaceEnclosureBridgeW32.ofRawSelectedFaceAndEnclosure
          H F hF E)

/-- Minimality contributes the positive-cardinality field; the selected
topology source remains exactly the concrete topology payload. -/
structure MinimalFailureSelectedTopologySource
    (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop where
  positiveCard : 0 < n
  route : Nonempty (SelectedFaceEnclosureRoute C)

theorem minimalFailureSelectedTopologySource_iff_route
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C} :
    MinimalFailureSelectedTopologySource C hmin <->
      Nonempty (SelectedFaceEnclosureRoute C) := by
  constructor
  case mp =>
    intro S
    exact S.route
  case mpr =>
    intro hroute
    exact
      { positiveCard := positiveCard_of_minimalClearedFailure hmin
        route := hroute }

theorem minimalFailureSelectedTopologySource_iff_concreteTopologyFacts
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalFailureSelectedTopologySource C hmin <->
      Nonempty (ConcreteTopologyFacts C) :=
  Iff.trans minimalFailureSelectedTopologySource_iff_route
    (route_nonempty_iff_concreteTopologyFacts C)

theorem minimalFailureSelectedTopologySource_iff_actualSelectedTopologyData
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalFailureSelectedTopologySource C hmin <->
      Nonempty (ActualSelectedTopologyData C) :=
  Iff.trans minimalFailureSelectedTopologySource_iff_route
    (route_nonempty_iff_actualSelectedTopologyData C)

theorem minimalFailureSelectedTopologySource_iff_outerBoundaryCore
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalFailureSelectedTopologySource C hmin <->
      Nonempty (TopologyBoundary C) :=
  Iff.trans minimalFailureSelectedTopologySource_iff_route
    (route_nonempty_iff_outerBoundaryCore C)

theorem minimalFailureSelectedTopologySource_iff_minimalExactTopologyFields
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalFailureSelectedTopologySource C hmin <->
      MinimalExactTopologyFields C :=
  Iff.trans minimalFailureSelectedTopologySource_iff_route
    (route_nonempty_iff_minimalExactTopologyFields C)

theorem minimalFailureSelectedTopologySource_iff_remainingCoreTopology
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalFailureSelectedTopologySource C hmin <->
      RemainingCoreTopology C :=
  Iff.trans minimalFailureSelectedTopologySource_iff_route
    (route_nonempty_iff_remainingCoreTopology C)

theorem minimalFailureSelectedTopologySource_of_concreteTopologyFacts
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (T : ConcreteTopologyFacts C) :
    MinimalFailureSelectedTopologySource C hmin :=
  (minimalFailureSelectedTopologySource_iff_concreteTopologyFacts
    hmin).2 (Nonempty.intro T)

theorem minimalFailureSelectedTopologySource_of_actualSelectedTopologyData
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (A : ActualSelectedTopologyData C) :
    MinimalFailureSelectedTopologySource C hmin :=
  (minimalFailureSelectedTopologySource_iff_actualSelectedTopologyData
    hmin).2 (Nonempty.intro A)

theorem minimalFailureSelectedTopologySource_of_minimalExactTopologyFields
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (T : MinimalExactTopologyFields C) :
    MinimalFailureSelectedTopologySource C hmin :=
  (minimalFailureSelectedTopologySource_iff_minimalExactTopologyFields
    hmin).2 T

theorem minimalExactTopologyFields_of_minimalFailureSelectedTopologySource
    {C : _root_.UDConfig n}
    {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}
    (S : MinimalFailureSelectedTopologySource C hmin) :
    MinimalExactTopologyFields C :=
  (minimalFailureSelectedTopologySource_iff_minimalExactTopologyFields
    hmin).1 S

theorem positive_route_iff_concreteTopologyFacts_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (0 < n /\ Nonempty (SelectedFaceEnclosureRoute C)) <->
      Nonempty (ConcreteTopologyFacts C) := by
  constructor
  case mp =>
    intro h
    exact (route_nonempty_iff_concreteTopologyFacts C).1 h.2
  case mpr =>
    intro hT
    exact
      And.intro (positiveCard_of_minimalClearedFailure hmin)
        ((route_nonempty_iff_concreteTopologyFacts C).2 hT)

theorem positive_route_iff_remainingCoreTopology_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (0 < n /\ Nonempty (SelectedFaceEnclosureRoute C)) <->
      RemainingCoreTopology C := by
  constructor
  case mp =>
    intro h
    exact (route_nonempty_iff_remainingCoreTopology C).1 h.2
  case mpr =>
    intro hT
    exact
      And.intro (positiveCard_of_minimalClearedFailure hmin)
        ((route_nonempty_iff_remainingCoreTopology C).2 hT)

def MinimalFailureSelectedFaceRouteTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      Nonempty (SelectedFaceEnclosureRoute C)

def MinimalFailureSelectedTopologySourceTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      MinimalFailureSelectedTopologySource C hmin

def MinimalFailureConcreteTopologyFactsTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      Nonempty (ConcreteTopologyFacts C)

def MinimalFailureSelectedOuterFaceSourceTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      Nonempty (SelectedOuterFaceSource C)

def MinimalFailureMissingOuterFaceDataTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      Nonempty (MissingOuterFaceData C)

def MinimalFailureExactOuterBoundaryTopologyFieldsTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      MinimalExactTopologyFields C

def MinimalFailureActualSelectedTopologyDataTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      Nonempty (ActualSelectedTopologyData C)

def MinimalFailureActualSelectedTopologyRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ActualSelectedTopologyData C

def MinimalFailureConcreteTopologyFactsRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ConcreteTopologyFacts C

def MinimalFailureMissingOuterFaceDataRows : Type 1 :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      MissingOuterFaceData C

def MinimalFailureRemainingCoreTopologyTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      RemainingCoreTopology C

def actualSelectedTopologyDataTargetOfRows
    (rows : MinimalFailureActualSelectedTopologyRows) :
    MinimalFailureActualSelectedTopologyDataTarget :=
  fun C hmin => Nonempty.intro (rows C hmin)

def actualSelectedTopologyRowsOfActualSelectedTopologyDataTarget
    (target : MinimalFailureActualSelectedTopologyDataTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => Classical.choice (target C hmin)

def concreteTopologyFactsTargetOfMinimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureConcreteTopologyFactsTarget :=
  fun C hmin => Nonempty.intro (F.row C hmin).topology

def concreteTopologyFactsRowsOfMinimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureConcreteTopologyFactsRows :=
  fun C hmin => (F.row C hmin).topology

def exactOuterBoundaryTopologyFieldsTargetOfConcreteTopologyFactsRows
    (rows : MinimalFailureConcreteTopologyFactsRows) :
    MinimalFailureExactOuterBoundaryTopologyFieldsTarget :=
  fun C hmin =>
    let T := rows C hmin
    ⟨T.faceBoundary, T.outerFace, T.outerFace_isOuter,
      ⟨T.outerEnclosure⟩⟩

def concreteTopologyFactsTargetOfMissingOuterFaceDataRows
    (rows : MinimalFailureMissingOuterFaceDataRows) :
    MinimalFailureConcreteTopologyFactsTarget :=
  fun C hmin =>
    (route_nonempty_iff_concreteTopologyFacts C).1
      ((route_nonempty_iff_missingOuterFaceData C).2
        (Nonempty.intro (rows C hmin)))

theorem nonempty_actualSelectedTopologyRows_iff_actualSelectedTopologyDataTarget :
    Nonempty MinimalFailureActualSelectedTopologyRows <->
      MinimalFailureActualSelectedTopologyDataTarget := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro rows =>
        exact actualSelectedTopologyDataTargetOfRows rows
  case mpr =>
    intro h
    exact
      Nonempty.intro
        (actualSelectedTopologyRowsOfActualSelectedTopologyDataTarget h)

theorem minimalFailureSelectedTopologySourceTarget_iff_routeTarget :
    MinimalFailureSelectedTopologySourceTarget <->
      MinimalFailureSelectedFaceRouteTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact (h C hmin).route
  case mpr =>
    intro h n C hmin
    exact
      (minimalFailureSelectedTopologySource_iff_route
        (C := C) (hmin := hmin)).2 (h C hmin)

theorem minimalFailureSelectedFaceRouteTarget_iff_concreteTopologyFactsTarget :
    MinimalFailureSelectedFaceRouteTarget <->
      MinimalFailureConcreteTopologyFactsTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact (route_nonempty_iff_concreteTopologyFacts C).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact (route_nonempty_iff_concreteTopologyFacts C).2 (h C hmin)

theorem minimalFailureSelectedFaceRouteTarget_iff_selectedOuterFaceSourceTarget :
    MinimalFailureSelectedFaceRouteTarget <->
      MinimalFailureSelectedOuterFaceSourceTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact (route_nonempty_iff_selectedOuterFaceSource C).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact (route_nonempty_iff_selectedOuterFaceSource C).2 (h C hmin)

theorem minimalFailureSelectedFaceRouteTarget_iff_missingOuterFaceDataTarget :
    MinimalFailureSelectedFaceRouteTarget <->
      MinimalFailureMissingOuterFaceDataTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact (route_nonempty_iff_missingOuterFaceData C).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact (route_nonempty_iff_missingOuterFaceData C).2 (h C hmin)

theorem minimalFailureMissingOuterFaceDataTarget :
    MinimalFailureMissingOuterFaceDataTarget :=
  fun _ hmin => nonempty_missingOuterFaceData_of_minimalClearedFailure hmin

theorem minimalFailureSelectedFaceRouteTarget_of_missingOuterFaceData :
    MinimalFailureSelectedFaceRouteTarget :=
  minimalFailureSelectedFaceRouteTarget_iff_missingOuterFaceDataTarget.2
    minimalFailureMissingOuterFaceDataTarget

theorem minimalFailureSelectedTopologySourceTarget_of_missingOuterFaceData :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_iff_routeTarget.2
    minimalFailureSelectedFaceRouteTarget_of_missingOuterFaceData

theorem minimalFailureSelectedTopologySourceTarget_iff_concreteTopologyFactsTarget :
    MinimalFailureSelectedTopologySourceTarget <->
      MinimalFailureConcreteTopologyFactsTarget :=
  Iff.trans minimalFailureSelectedTopologySourceTarget_iff_routeTarget
    minimalFailureSelectedFaceRouteTarget_iff_concreteTopologyFactsTarget

theorem minimalFailureConcreteTopologyFactsTarget_iff_selectedOuterFaceSourceTarget :
    MinimalFailureConcreteTopologyFactsTarget <->
      MinimalFailureSelectedOuterFaceSourceTarget :=
  Iff.trans
    minimalFailureSelectedFaceRouteTarget_iff_concreteTopologyFactsTarget.symm
    minimalFailureSelectedFaceRouteTarget_iff_selectedOuterFaceSourceTarget

theorem minimalFailureConcreteTopologyFactsTarget_iff_missingOuterFaceDataTarget :
    MinimalFailureConcreteTopologyFactsTarget <->
      MinimalFailureMissingOuterFaceDataTarget :=
  Iff.trans
    minimalFailureSelectedFaceRouteTarget_iff_concreteTopologyFactsTarget.symm
    minimalFailureSelectedFaceRouteTarget_iff_missingOuterFaceDataTarget

theorem concreteTopologyFactsTarget_of_selectedOuterFaceSourceTarget
    (h : MinimalFailureSelectedOuterFaceSourceTarget) :
    MinimalFailureConcreteTopologyFactsTarget :=
  minimalFailureConcreteTopologyFactsTarget_iff_selectedOuterFaceSourceTarget.2
    h

theorem concreteTopologyFactsTarget_of_missingOuterFaceDataTarget
    (h : MinimalFailureMissingOuterFaceDataTarget) :
    MinimalFailureConcreteTopologyFactsTarget :=
  minimalFailureConcreteTopologyFactsTarget_iff_missingOuterFaceDataTarget.2
    h

theorem selectedOuterFaceSourceTarget_of_concreteTopologyFactsTarget
    (h : MinimalFailureConcreteTopologyFactsTarget) :
    MinimalFailureSelectedOuterFaceSourceTarget :=
  minimalFailureConcreteTopologyFactsTarget_iff_selectedOuterFaceSourceTarget.1
    h

theorem missingOuterFaceDataTarget_of_concreteTopologyFactsTarget
    (h : MinimalFailureConcreteTopologyFactsTarget) :
    MinimalFailureMissingOuterFaceDataTarget :=
  minimalFailureConcreteTopologyFactsTarget_iff_missingOuterFaceDataTarget.1
    h

theorem minimalFailureSelectedTopologySourceTarget_iff_exactOuterBoundaryTopologyFieldsTarget :
    MinimalFailureSelectedTopologySourceTarget <->
      MinimalFailureExactOuterBoundaryTopologyFieldsTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact
      minimalExactTopologyFields_of_minimalFailureSelectedTopologySource
        (h C hmin)
  case mpr =>
    intro h n C hmin
    exact
      minimalFailureSelectedTopologySource_of_minimalExactTopologyFields
        (h C hmin)

theorem minimalFailureSelectedTopologySourceTarget_of_exactOuterBoundaryTopologyFieldsTarget
    (h : MinimalFailureExactOuterBoundaryTopologyFieldsTarget) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_iff_exactOuterBoundaryTopologyFieldsTarget.2
    h

theorem exactOuterBoundaryTopologyFieldsTarget_of_minimalFailureSelectedTopologySourceTarget
    (h : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureExactOuterBoundaryTopologyFieldsTarget :=
  minimalFailureSelectedTopologySourceTarget_iff_exactOuterBoundaryTopologyFieldsTarget.1
    h

theorem minimalFailureExactOuterBoundaryTopologyFieldsTarget_iff_concreteTopologyFactsTarget :
    MinimalFailureExactOuterBoundaryTopologyFieldsTarget <->
      MinimalFailureConcreteTopologyFactsTarget :=
  Iff.trans
    minimalFailureSelectedTopologySourceTarget_iff_exactOuterBoundaryTopologyFieldsTarget.symm
    minimalFailureSelectedTopologySourceTarget_iff_concreteTopologyFactsTarget

theorem exactOuterBoundaryTopologyFieldsTarget_of_concreteTopologyFactsTarget
    (h : MinimalFailureConcreteTopologyFactsTarget) :
    MinimalFailureExactOuterBoundaryTopologyFieldsTarget :=
  minimalFailureExactOuterBoundaryTopologyFieldsTarget_iff_concreteTopologyFactsTarget.2
    h

theorem concreteTopologyFactsTarget_of_exactOuterBoundaryTopologyFieldsTarget
    (h : MinimalFailureExactOuterBoundaryTopologyFieldsTarget) :
    MinimalFailureConcreteTopologyFactsTarget :=
  minimalFailureExactOuterBoundaryTopologyFieldsTarget_iff_concreteTopologyFactsTarget.1
    h

theorem minimalFailureSelectedTopologySourceTarget_of_minimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_iff_concreteTopologyFactsTarget.2
    (concreteTopologyFactsTargetOfMinimalBoundaryTopologyWitnessFamily F)

theorem minimalFailureSelectedTopologySourceTarget_of_nonempty_minimalBoundaryTopologyWitnessFamily
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureSelectedTopologySourceTarget := by
  cases h with
  | intro F =>
      exact
        minimalFailureSelectedTopologySourceTarget_of_minimalBoundaryTopologyWitnessFamily
          F

theorem exactOuterBoundaryTopologyFieldsTarget_of_minimalBoundaryTopologyWitnessFamily
    (F : MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureExactOuterBoundaryTopologyFieldsTarget :=
  exactOuterBoundaryTopologyFieldsTargetOfConcreteTopologyFactsRows
    (concreteTopologyFactsRowsOfMinimalBoundaryTopologyWitnessFamily F)

theorem exactOuterBoundaryTopologyFieldsTarget_of_nonempty_minimalBoundaryTopologyWitnessFamily
    (h : Nonempty MinimalBoundaryTopologyWitnessFamily.{u}) :
    MinimalFailureExactOuterBoundaryTopologyFieldsTarget := by
  cases h with
  | intro F =>
      exact exactOuterBoundaryTopologyFieldsTarget_of_minimalBoundaryTopologyWitnessFamily F

theorem minimalFailureSelectedFaceRouteTarget_iff_actualSelectedTopologyDataTarget :
    MinimalFailureSelectedFaceRouteTarget <->
      MinimalFailureActualSelectedTopologyDataTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact (route_nonempty_iff_actualSelectedTopologyData C).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact (route_nonempty_iff_actualSelectedTopologyData C).2 (h C hmin)

theorem minimalFailureSelectedTopologySourceTarget_iff_actualSelectedTopologyDataTarget :
    MinimalFailureSelectedTopologySourceTarget <->
      MinimalFailureActualSelectedTopologyDataTarget :=
  Iff.trans minimalFailureSelectedTopologySourceTarget_iff_routeTarget
    minimalFailureSelectedFaceRouteTarget_iff_actualSelectedTopologyDataTarget

theorem minimalFailureSelectedTopologySourceTarget_of_actualSelectedTopologyDataTarget
    (h : MinimalFailureActualSelectedTopologyDataTarget) :
    MinimalFailureSelectedTopologySourceTarget :=
  minimalFailureSelectedTopologySourceTarget_iff_actualSelectedTopologyDataTarget.2
    h

theorem actualSelectedTopologyDataTarget_of_minimalFailureSelectedTopologySourceTarget
    (h : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureActualSelectedTopologyDataTarget :=
  minimalFailureSelectedTopologySourceTarget_iff_actualSelectedTopologyDataTarget.1
    h

def actualSelectedTopologyRowsOfMinimalFailureSelectedTopologySourceTarget
    (h : MinimalFailureSelectedTopologySourceTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  actualSelectedTopologyRowsOfActualSelectedTopologyDataTarget
    (actualSelectedTopologyDataTarget_of_minimalFailureSelectedTopologySourceTarget
      h)

theorem minimalFailureSelectedTopologySourceTarget_of_actualSelectedTopologyRows
    (topology : MinimalFailureActualSelectedTopologyRows) :
    MinimalFailureSelectedTopologySourceTarget := by
  apply minimalFailureSelectedTopologySourceTarget_of_actualSelectedTopologyDataTarget
  exact actualSelectedTopologyDataTargetOfRows topology

theorem minimalFailureSelectedTopologySourceTarget_iff_nonempty_actualSelectedTopologyRows :
    MinimalFailureSelectedTopologySourceTarget <->
      Nonempty MinimalFailureActualSelectedTopologyRows := by
  constructor
  case mp =>
    intro h
    exact
      Nonempty.intro
        (actualSelectedTopologyRowsOfMinimalFailureSelectedTopologySourceTarget
          h)
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact
          minimalFailureSelectedTopologySourceTarget_of_actualSelectedTopologyRows
            rows

theorem minimalFailureSelectedFaceRouteTarget_iff_remainingCoreTopologyTarget :
    MinimalFailureSelectedFaceRouteTarget <->
      MinimalFailureRemainingCoreTopologyTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact (route_nonempty_iff_remainingCoreTopology C).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact (route_nonempty_iff_remainingCoreTopology C).2 (h C hmin)

theorem minimalFailureSelectedTopologySourceTarget_iff_remainingCoreTopologyTarget :
    MinimalFailureSelectedTopologySourceTarget <->
      MinimalFailureRemainingCoreTopologyTarget :=
  Iff.trans minimalFailureSelectedTopologySourceTarget_iff_routeTarget
    minimalFailureSelectedFaceRouteTarget_iff_remainingCoreTopologyTarget

def GlobalSelectedFaceRouteTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (SelectedFaceEnclosureRoute C)

def emptyUDConfig : _root_.UDConfig 0 where
  pts := fun i => nomatch i
  sep := by
    intro i
    exact Fin.elim0 i

theorem empty_selectedFaceRoute_false :
    Not (Nonempty (SelectedFaceEnclosureRoute emptyUDConfig)) := by
  intro h
  cases h with
  | intro R =>
      have k :
          Fin
            (R.selectedOuterFace.faceBoundary.boundaryLength
              R.selectedOuterFace.outerFace) :=
        { val := 0
          isLt :=
            R.selectedOuterFace.faceBoundary.boundaryLength_pos
              R.selectedOuterFace.outerFace }
      exact
        Fin.elim0
          (R.selectedOuterFace.faceBoundary.boundaryVertex
            R.selectedOuterFace.outerFace k)

theorem empty_concreteTopologyFacts_false :
    Not (Nonempty (ConcreteTopologyFacts emptyUDConfig)) := by
  intro h
  exact empty_selectedFaceRoute_false
    ((route_nonempty_iff_concreteTopologyFacts emptyUDConfig).2 h)

theorem not_globalSelectedFaceRouteTarget :
    Not GlobalSelectedFaceRouteTarget := by
  intro h
  exact empty_selectedFaceRoute_false (h 0 emptyUDConfig)

theorem globalSelectedFaceRouteTarget_iff_globalConcreteTopologyFacts :
    GlobalSelectedFaceRouteTarget <->
      (forall (n : Nat) (C : _root_.UDConfig n),
        Nonempty (ConcreteTopologyFacts C)) := by
  constructor
  case mp =>
    intro h n C
    exact (route_nonempty_iff_concreteTopologyFacts C).1 (h n C)
  case mpr =>
    intro h n C
    exact (route_nonempty_iff_concreteTopologyFacts C).2 (h n C)

theorem globalSelectedFaceRouteTarget_iff_globalActualSelectedTopologyData :
    GlobalSelectedFaceRouteTarget <->
      (forall (n : Nat) (C : _root_.UDConfig n),
        Nonempty (ActualSelectedTopologyData C)) := by
  constructor
  case mp =>
    intro h n C
    exact (route_nonempty_iff_actualSelectedTopologyData C).1 (h n C)
  case mpr =>
    intro h n C
    exact (route_nonempty_iff_actualSelectedTopologyData C).2 (h n C)

end

end MinimalFailureSelectedTopologySourceW32
end Swanepoel

namespace Verified

open Swanepoel.MinimalFailureSelectedTopologySourceW32

abbrev SwanepoelW32MinimalFailureSelectedFaceRouteTarget : Prop :=
  Swanepoel.MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedFaceRouteTarget

abbrev SwanepoelW32MinimalFailureConcreteTopologyFactsTarget : Prop :=
  Swanepoel.MinimalFailureSelectedTopologySourceW32.MinimalFailureConcreteTopologyFactsTarget

abbrev SwanepoelW32MinimalFailureExactOuterBoundaryTopologyFieldsTarget : Prop :=
  Swanepoel.MinimalFailureSelectedTopologySourceW32.MinimalFailureExactOuterBoundaryTopologyFieldsTarget

abbrev SwanepoelW32MinimalFailureActualSelectedTopologyDataTarget : Prop :=
  Swanepoel.MinimalFailureSelectedTopologySourceW32.MinimalFailureActualSelectedTopologyDataTarget

theorem swanepoelW32_minimalFailureSelectedFaceRoute_exactly_concreteTopologyFacts :
    SwanepoelW32MinimalFailureSelectedFaceRouteTarget <->
      SwanepoelW32MinimalFailureConcreteTopologyFactsTarget :=
  minimalFailureSelectedFaceRouteTarget_iff_concreteTopologyFactsTarget

theorem swanepoelW32_minimalFailureSelectedFaceRoute_exactly_actualSelectedTopologyData :
    SwanepoelW32MinimalFailureSelectedFaceRouteTarget <->
      SwanepoelW32MinimalFailureActualSelectedTopologyDataTarget :=
  minimalFailureSelectedFaceRouteTarget_iff_actualSelectedTopologyDataTarget

theorem swanepoelW32_minimalFailureSelectedTopologySource_exactly_exactOuterBoundaryTopologyFields :
    Swanepoel.MinimalFailureSelectedTopologySourceW32.MinimalFailureSelectedTopologySourceTarget <->
      SwanepoelW32MinimalFailureExactOuterBoundaryTopologyFieldsTarget :=
  minimalFailureSelectedTopologySourceTarget_iff_exactOuterBoundaryTopologyFieldsTarget

theorem swanepoelW32_not_globalSelectedFaceRouteTarget :
    Not
      Swanepoel.MinimalFailureSelectedTopologySourceW32.GlobalSelectedFaceRouteTarget :=
  Swanepoel.MinimalFailureSelectedTopologySourceW32.not_globalSelectedFaceRouteTarget

end Verified
end ErdosProblems1066
