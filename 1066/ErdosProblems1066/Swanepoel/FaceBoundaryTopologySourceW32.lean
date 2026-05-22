import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Geometry.Polygon.Basic
import ErdosProblems1066.Swanepoel.CutVertexFinal
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.JordanTopologyExteriorEnclosure
import ErdosProblems1066.Swanepoel.ExteriorComponentTopology
import ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource
import ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
import ErdosProblems1066.Swanepoel.S2BoundaryFreeRawSource
import ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
import ErdosProblems1066.Swanepoel.S2CarrierLocalSource
import ErdosProblems1066.Swanepoel.S2TopologySource
import ErdosProblems1066.Swanepoel.EnclosureAndFaceBoundaryW31
import ErdosProblems1066.Swanepoel.OuterBoundaryCoreConstructionW28
import ErdosProblems1066.Swanepoel.BoundaryWalkBridge
import ErdosProblems1066.Swanepoel.FaceCountingBridge
import ErdosProblems1066.Swanepoel.MinimalFailureConcreteDataMatrix

set_option autoImplicit false

/-!
# W32 explicit face-boundary topology source

W31 packages the remaining outer-boundary input as a selected face-boundary
surface together with enclosure data.  This file splits that same payload into
three source-facing layers:

* topology fields: canonical unit-distance face-boundary data and a selected
  outer face;
* Jordan fields: the same selected face plus the enclosure predicates for that
  dependent face;
* boundary-counting fields: Jordan fields plus the explicit angle-count lower
  bound consumed by `BoundaryCounting`.

All constructors are conditional projections from supplied data.  The exact
blocker theorems below identify the missing planar boundary data with the W31
and W30 target surfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace FaceBoundaryTopologySourceW32

open BoundaryCounting
open _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology
open _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
open _root_.ErdosProblems1066.Swanepoel.JordanTopologyExteriorEnclosure
open _root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.MinimalFailureTopology

noncomputable section

universe u

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.CanonicalGraph C

abbrev FaceBoundaryHypotheses (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.FaceBoundaryHypotheses C

abbrev W31Source (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.FaceBoundaryEnclosureSource C

abbrev SelectedFaceEnclosureFields (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.SelectedFaceEnclosureFields C

abbrev ExactSelectedFaceEnclosureBlocker (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.ExactSelectedFaceEnclosureBlocker C

abbrev OuterBoundarySourceFields (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.OuterBoundarySourceFields C

abbrev ConcreteTopologyFacts (C : _root_.UDConfig n) :=
  EnclosureAndFaceBoundaryW31.ConcreteTopologyFacts C

abbrev ActualSelectedTopologyData (C : _root_.UDConfig n) :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData C

abbrev UnitDistanceSimpleGraph (C : _root_.UDConfig n) :
    SimpleGraph (Fin n) :=
  GraphBridge.unitDistanceSimpleGraph C

/-! ## Topology-only selected outer-face fields -/

/-- The topology part of the W31 payload: face-boundary data and a selected
outer face on that data. -/
structure TopologySourceFields (C : _root_.UDConfig n) where
  faceBoundary : FaceBoundaryHypotheses C
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace

namespace TopologySourceFields

variable {C : _root_.UDConfig n}

def ofRaw
    (H : FaceBoundaryHypotheses C)
    (F : H.Face)
    (hF : H.IsOuterFace F) :
    TopologySourceFields C where
  faceBoundary := H
  outerFace := F
  outerFace_isOuter := hF

def ofW31Source (S : W31Source C) :
    TopologySourceFields C :=
  ofRaw S.faceBoundary S.outerFace S.outerFace_isOuter

def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    TopologySourceFields C :=
  ofRaw P.faceBoundary P.outerFace P.outerFace_isOuter

def toMissingOuterFaceData
    (T : TopologySourceFields C) :
    JordanBoundaryConcrete.MissingOuterFaceData.{0} C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter

def ofMissingOuterFaceData
    (D : JordanBoundaryConcrete.MissingOuterFaceData.{0} C) :
    TopologySourceFields C where
  faceBoundary := D.faceBoundary
  outerFace := D.outerFace
  outerFace_isOuter := D.outerFace_isOuter

def planarFaceBoundary (T : TopologySourceFields C) :
    PlanarInterface.FaceBoundaryHypotheses
      (CanonicalGraph C).toStraightLine :=
  T.faceBoundary.toFaceBoundaryHypotheses

def outerCycle (T : TopologySourceFields C) :
    OuterBoundaryInterface.BoundaryCycle (CanonicalGraph C) :=
  OuterBoundaryInterface.BoundaryCycle.ofFaceBoundary
    T.faceBoundary T.outerFace

def outerSimplePolygon (T : TopologySourceFields C) :
    OuterBoundaryInterface.SimplePolygon
      (CanonicalGraph C) T.outerCycle :=
  OuterBoundaryReduction.BoundaryCycle.simplePolygonOfFaceBoundary
    T.faceBoundary T.outerFace

def outerPolygon (T : TopologySourceFields C) :
    Polygon PlanarInterface.Point T.outerCycle.length :=
  T.outerCycle.toPolygon

/-- The enclosure predicates canonically determined by the selected boundary
cycle.  All vertices are inside-or-on, while boundary membership is exactly
membership in the selected boundary walk. -/
def boundarySetEnclosure (T : TopologySourceFields C) :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) T.faceBoundary T.outerFace where
  insideOrOn := fun _ => True
  onBoundary := fun v =>
    Exists fun k : Fin (T.faceBoundary.boundaryLength T.outerFace) =>
      T.faceBoundary.boundaryVertex T.outerFace k = v
  boundary_vertex_onBoundary := fun k => Exists.intro k rfl
  boundary_point_insideOrOn := fun _ => trivial
  all_vertices_insideOrOn := fun _ => trivial
  onBoundary_iff_outer_cycle := fun _ => Iff.rfl

def unitDistanceSimpleGraph (_T : TopologySourceFields C) :
    SimpleGraph (Fin n) :=
  UnitDistanceSimpleGraph C

theorem pairwiseNoncrossing (_T : TopologySourceFields C) :
    PlanarInterface.PairwiseNoncrossing
      (CanonicalGraph C).config (CanonicalGraph C).edgeSet :=
  (CanonicalGraph C).pairwiseNoncrossing

theorem planarFaceBoundary_noncrossing
    (T : TopologySourceFields C) :
    T.planarFaceBoundary.noncrossing =
      (CanonicalGraph C).pairwiseNoncrossing := by
  rfl

@[simp]
theorem outerCycle_length (T : TopologySourceFields C) :
    T.outerCycle.length =
      T.faceBoundary.boundaryLength T.outerFace :=
  rfl

theorem outerCycle_vertex_injective
    (T : TopologySourceFields C) :
    Function.Injective T.outerCycle.vertex :=
  T.faceBoundary.boundarySimple T.outerFace

theorem outerCycle_adjacent_unitDistanceAdj
    (T : TopologySourceFields C) (k : Fin T.outerCycle.length) :
    GraphBridge.UnitDistanceAdj (CanonicalGraph C).config
      (T.outerCycle.vertex k)
      (T.outerCycle.vertex
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) :=
  T.outerCycle.adjacent_unitDistanceAdj k

theorem outerCycle_edge_geometry_dist_eq_one
    (T : TopologySourceFields C) (k : Fin T.outerCycle.length) :
    Geometry.Distance.eucDist (T.outerCycle.point k)
      (T.outerCycle.point
        (PlanarInterface.cyclicSucc T.outerCycle.length_pos k)) = 1 :=
  T.outerCycle.edge_geometry_dist_eq_one k

theorem outerPolygon_apply_finRotate
    (T : TopologySourceFields C) (k : Fin T.outerCycle.length) :
    T.outerPolygon (finRotate T.outerCycle.length k) =
      T.outerCycle.nextPoint k :=
  T.outerCycle.toPolygon_apply_finRotate k

end TopologySourceFields

def ExactTopologySourceBlocker (C : _root_.UDConfig n) : Prop :=
  Exists fun H : FaceBoundaryHypotheses C =>
    Exists fun F : H.Face =>
      H.IsOuterFace F

theorem nonempty_topologySourceFields_iff_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (TopologySourceFields C) <->
      ExactTopologySourceBlocker C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
        exact Exists.intro T.faceBoundary
          (Exists.intro T.outerFace T.outerFace_isOuter)
  case mpr =>
    intro h
    cases h with
    | intro H hH =>
        cases hH with
        | intro F hF =>
            exact Nonempty.intro (TopologySourceFields.ofRaw H F hF)

theorem nonempty_topologySourceFields_iff_missingOuterFaceData
    (C : _root_.UDConfig n) :
    Nonempty (TopologySourceFields C) <->
      Nonempty (JordanBoundaryConcrete.MissingOuterFaceData.{0} C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T =>
        exact Nonempty.intro T.toMissingOuterFaceData
  case mpr =>
    intro h
    cases h with
    | intro D =>
        exact Nonempty.intro
          (TopologySourceFields.ofMissingOuterFaceData D)

theorem nonempty_missingOuterFaceData_iff_topologySourceFields
    (C : _root_.UDConfig n) :
    Nonempty (JordanBoundaryConcrete.MissingOuterFaceData.{0} C) <->
      Nonempty (TopologySourceFields C) :=
  (nonempty_topologySourceFields_iff_missingOuterFaceData C).symm

theorem nonempty_missingOuterFaceData_iff_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (JordanBoundaryConcrete.MissingOuterFaceData.{0} C) <->
      ExactTopologySourceBlocker C :=
  Iff.trans
    (nonempty_missingOuterFaceData_iff_topologySourceFields C)
    (nonempty_topologySourceFields_iff_exactBlocker C)

theorem w31Source_implies_topologySourceFields
    {C : _root_.UDConfig n}
    (h : Nonempty (W31Source C)) :
    Nonempty (TopologySourceFields C) := by
  cases h with
  | intro S =>
      exact Nonempty.intro (TopologySourceFields.ofW31Source S)

theorem topologySourceFields_nonempty_of_unitDistanceAdj
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : GraphBridge.UnitDistanceAdj C i j) :
    Nonempty (TopologySourceFields C) :=
  (nonempty_topologySourceFields_iff_missingOuterFaceData C).2
    ⟨JordanBoundaryConcrete.MissingOuterFaceData.ofUnitDistanceAdj
      (C := C) hAdj⟩

theorem missingOuterFaceData_nonempty_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (JordanBoundaryConcrete.MissingOuterFaceData.{0} C) :=
  JordanBoundaryConcrete.MissingOuterFaceData.nonempty_of_minimalClearedFailure
    (C := C) hmin

theorem topologySourceFields_nonempty_of_minimalClearedFailure
    {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (TopologySourceFields C) :=
  (nonempty_topologySourceFields_iff_missingOuterFaceData C).2
    (missingOuterFaceData_nonempty_of_minimalClearedFailure
      (C := C) hmin)

/-! ## Jordan/enclosure fields -/

/-- The W31 payload with each dependent topology and Jordan/enclosure field
spelled out. -/
structure JordanSourceFields (C : _root_.UDConfig n) extends
    TopologySourceFields C where
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) faceBoundary outerFace

namespace JordanSourceFields

variable {C : _root_.UDConfig n}

def ofRaw
    (H : FaceBoundaryHypotheses C)
    (F : H.Face)
    (hF : H.IsOuterFace F)
    (E :
      OuterBoundaryInterface.OuterBoundaryEnclosure
        (CanonicalGraph C) H F) :
    JordanSourceFields C where
  faceBoundary := H
  outerFace := F
  outerFace_isOuter := hF
  outerEnclosure := E

def ofW31Source (S : W31Source C) :
    JordanSourceFields C :=
  ofRaw S.faceBoundary S.outerFace
    S.outerFace_isOuter S.outerEnclosure

def ofTopology (T : TopologySourceFields C) :
    JordanSourceFields C :=
  ofRaw T.faceBoundary T.outerFace
    T.outerFace_isOuter T.boundarySetEnclosure

def toW31Source (J : JordanSourceFields C) :
    W31Source C where
  faceBoundary := J.faceBoundary
  outerFace := J.outerFace
  outerFace_isOuter := J.outerFace_isOuter
  outerEnclosure := J.outerEnclosure

def ofOuterBoundaryCore
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    JordanSourceFields C :=
  ofRaw P.faceBoundary P.outerFace
    P.outerFace_isOuter P.outerEnclosure

def ofOuterBoundarySourceFields
    (S : OuterBoundarySourceFields C) :
    JordanSourceFields C :=
  ofRaw S.faceBoundary S.outerFace
    S.outerFace_isOuter S.outerEnclosure

def ofConcreteTopologyFacts
    (T : ConcreteTopologyFacts C) :
    JordanSourceFields C :=
  ofRaw T.faceBoundary T.outerFace
    T.outerFace_isOuter T.outerEnclosure

def ofActualSelectedTopologyData
    (A : ActualSelectedTopologyData C) :
    JordanSourceFields C :=
  ofOuterBoundaryCore
    (ActualSelectedTopologyDataW27.ActualSelectedTopologyData.toOuterBoundaryCore
      A)

def toOuterBoundaryCore
    (J : JordanSourceFields C) :
    OuterBoundaryCore.{0} (CanonicalGraph C) :=
  J.toW31Source.toOuterBoundaryCore

/-- Strengthen a Jordan source to the nondegenerate actual boundary-cycle
payload once the selected outer cycle has length at least three. -/
def toActualOuterBoundaryCycleData
    (J : JordanSourceFields C)
    (hcycle : 3 <= J.toOuterBoundaryCore.outerCycle.length) :
    JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C :=
  JordanBoundaryConcrete.ActualOuterBoundaryCycleData.ofCore
    J.toOuterBoundaryCore hcycle

def actualSelectedTopologyData
    (J : JordanSourceFields C) :
    ActualSelectedTopologyData C :=
  ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
    J.toOuterBoundaryCore

def toOuterBoundarySourceFields
    (J : JordanSourceFields C) :
    OuterBoundarySourceFields C :=
  J.toW31Source.toOuterBoundarySourceFields

def toConcreteTopologyFacts
    (J : JordanSourceFields C) :
    ConcreteTopologyFacts C :=
  J.toW31Source.toConcreteTopologyFacts

def toExtractionOuterFaceData
    (J : JordanSourceFields C) :
    JordanBoundaryExtraction.OuterFaceData (CanonicalGraph C) where
  faceBoundary := J.faceBoundary
  outerFace := J.outerFace
  outerFace_isOuter := J.outerFace_isOuter

def toExtractionEnclosureData
    (J : JordanSourceFields C) :
    JordanBoundaryExtraction.EnclosureData
      J.toExtractionOuterFaceData where
  outerEnclosure := J.outerEnclosure

def toExtractionData
    (J : JordanSourceFields C) :
    JordanBoundaryExtraction.Data (CanonicalGraph C) where
  faceBoundary := J.faceBoundary
  outerFace := J.outerFace
  outerFace_isOuter := J.outerFace_isOuter
  outerEnclosure := J.outerEnclosure

def selectedFaceEnclosureFields
    (J : JordanSourceFields C) :
    SelectedFaceEnclosureFields C :=
  J.toW31Source.toSelectedFaceEnclosureFields

theorem all_vertices_insideOrOn
    (J : JordanSourceFields C) (v : Fin n) :
    J.outerEnclosure.insideOrOn ((CanonicalGraph C).point v) :=
  J.outerEnclosure.all_vertices_insideOrOn v

theorem boundary_vertex_onBoundary
    (J : JordanSourceFields C)
    (k : Fin (J.faceBoundary.boundaryLength J.outerFace)) :
    J.outerEnclosure.onBoundary
      (J.faceBoundary.boundaryVertex J.outerFace k) :=
  J.outerEnclosure.boundary_vertex_onBoundary k

theorem onBoundary_iff_outerCycle
    (J : JordanSourceFields C) (v : Fin n) :
    J.outerEnclosure.onBoundary v <->
      Exists fun k : Fin J.toTopologySourceFields.outerCycle.length =>
        J.toTopologySourceFields.outerCycle.vertex k = v :=
  J.toW31Source.onBoundary_iff_outerCycle v

@[simp]
theorem toW31Source_faceBoundary (J : JordanSourceFields C) :
    J.toW31Source.faceBoundary = J.faceBoundary :=
  rfl

@[simp]
theorem toOuterBoundaryCore_faceBoundary (J : JordanSourceFields C) :
    J.toOuterBoundaryCore.faceBoundary = J.faceBoundary :=
  rfl

@[simp]
theorem toOuterBoundaryCore_outerEnclosure (J : JordanSourceFields C) :
    J.toOuterBoundaryCore.outerEnclosure = J.outerEnclosure :=
  rfl

end JordanSourceFields

def ofExactSelectedFaceEnclosureBlocker
    {C : _root_.UDConfig n}
    (h : ExactSelectedFaceEnclosureBlocker C) :
    Nonempty (JordanSourceFields C) := by
  cases h with
  | intro H hH =>
      cases hH with
      | intro F hFPair =>
          cases hFPair with
          | intro hF hE =>
              cases hE with
              | intro E =>
                  exact
                    Nonempty.intro
                      (JordanSourceFields.ofRaw H F hF E)

theorem nonempty_jordanSourceFields_iff_w31Source
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      Nonempty (W31Source C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro J =>
        exact Nonempty.intro J.toW31Source
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro (JordanSourceFields.ofW31Source S)

theorem topologySourceFields_implies_jordanSourceFields
    {C : _root_.UDConfig n}
    (h : Nonempty (TopologySourceFields C)) :
    Nonempty (JordanSourceFields C) := by
  cases h with
  | intro T =>
      exact Nonempty.intro (JordanSourceFields.ofTopology T)

theorem nonempty_jordanSourceFields_iff_topologySourceFields
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      Nonempty (TopologySourceFields C) := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro J =>
        exact Nonempty.intro J.toTopologySourceFields
  case mpr =>
    exact topologySourceFields_implies_jordanSourceFields

theorem nonempty_jordanSourceFields_iff_missingOuterFaceData
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      Nonempty (JordanBoundaryConcrete.MissingOuterFaceData.{0} C) :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_topologySourceFields C)
    (nonempty_topologySourceFields_iff_missingOuterFaceData C)

theorem nonempty_jordanSourceFields_iff_topologySourceBlocker
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      ExactTopologySourceBlocker C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_topologySourceFields C)
    (nonempty_topologySourceFields_iff_exactBlocker C)

theorem nonempty_jordanSourceFields_iff_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      SelectedFaceEnclosureFields C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_w31Source C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_selectedFaceEnclosureFields
      C)

theorem nonempty_topologySourceFields_iff_selectedFaceEnclosureFields
    (C : _root_.UDConfig n) :
    Nonempty (TopologySourceFields C) <->
      SelectedFaceEnclosureFields C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_topologySourceFields C).symm
    (nonempty_jordanSourceFields_iff_selectedFaceEnclosureFields C)

theorem nonempty_jordanSourceFields_iff_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      ExactSelectedFaceEnclosureBlocker C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_w31Source C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_exactBlocker C)

theorem nonempty_jordanSourceFields_iff_exactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_w31Source C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_exactTopologyFields C)

theorem nonempty_jordanSourceFields_iff_splitExactTopologyFields
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      TopologyExtractionFromNoncrossing.SplitExactTopologyFields C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_w31Source C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_splitExactTopologyFields
      C)

theorem nonempty_jordanSourceFields_iff_outerBoundaryCore
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      Nonempty (OuterBoundaryCore.{0} (CanonicalGraph C)) :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_w31Source C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_outerBoundaryCore C)

/-! ## Mathlib cycle extraction from a recorded nondegenerate boundary -/

namespace ListChainWalk

variable {V : Type u} {G : SimpleGraph V}

/-- Turn a nonempty chained list of graph vertices into the corresponding
Mathlib walk. -/
def ofChain :
    (l : List V) -> (hne : l ≠ []) -> l.IsChain G.Adj ->
      G.Walk (l.head hne) (l.getLast hne)
  | [], hne, _ => False.elim (hne rfl)
  | [_x], _hne, _hchain => SimpleGraph.Walk.nil
  | x :: y :: xs, _hne, hchain => by
      have hxy : G.Adj x y := (List.isChain_cons_cons.mp hchain).1
      have htail : (y :: xs).IsChain G.Adj :=
        (List.isChain_cons_cons.mp hchain).2
      exact
        SimpleGraph.Walk.cons hxy
          (ofChain (y :: xs) (List.cons_ne_nil y xs) htail)

@[simp]
theorem ofChain_support :
    forall (l : List V) (hne : l ≠ []) (hchain : l.IsChain G.Adj),
      (ofChain l hne hchain).support = l
  | [], hne, _ => False.elim (hne rfl)
  | [_x], _hne, _hchain => rfl
  | x :: y :: xs, _hne, hchain => by
      have htail : (y :: xs).IsChain G.Adj :=
        (List.isChain_cons_cons.mp hchain).2
      change
        x :: (ofChain (y :: xs) (List.cons_ne_nil y xs) htail).support =
          x :: y :: xs
      rw [ofChain_support (y :: xs) (List.cons_ne_nil y xs) htail]

end ListChainWalk

/--
A Mathlib graph-cycle certificate for the selected boundary of an
`OuterBoundaryCore`.

This is the stronger nondegenerate lane: the selected boundary is tied to an
honest `SimpleGraph.Walk.IsCycle` on the unit-distance graph, with the same
length and the same vertex support as the recorded outer cycle.  Mathlib then
rules out the accepted two-endpoint adjacent-pair witness automatically.
-/
structure ActualOuterBoundaryCoreCycleWitness
    {C : _root_.UDConfig n}
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) where
  base : Fin n
  walk : (UnitDistanceSimpleGraph C).Walk base base
  isCycle : walk.IsCycle
  length_eq_outerCycle_length : walk.length = P.outerCycle.length
  support_iff_outerCycle :
    forall v : Fin n, v ∈ walk.support <->
      Exists fun k : Fin P.outerCycle.length => P.outerCycle.vertex k = v

namespace ActualOuterBoundaryCoreCycleWitness

variable {C : _root_.UDConfig n}
variable {P : OuterBoundaryCore.{0} (CanonicalGraph C)}

def rotatedBoundaryList
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    List (Fin n) :=
  List.ofFn fun k : Fin P.outerCycle.length =>
    P.outerCycle.vertex (finRotate P.outerCycle.length k)

theorem rotatedBoundaryList_ne_nil
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    rotatedBoundaryList P ≠ [] := by
  intro h
  have hlen : P.outerCycle.length = 0 := by
    have hlen' := congrArg List.length h
    simp only [rotatedBoundaryList, List.length_ofFn, List.length_nil] at hlen'
    exact hlen'
  exact Nat.ne_of_gt P.outerCycle.length_pos hlen

theorem rotatedBoundaryList_head
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (rotatedBoundaryList P).head (rotatedBoundaryList_ne_nil P) =
      P.outerCycle.vertex
        (finRotate P.outerCycle.length
          (Fin.mk 0 P.outerCycle.length_pos)) := by
  unfold rotatedBoundaryList
  rw [List.head_ofFn]

theorem rotatedBoundaryList_getLast
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (rotatedBoundaryList P).getLast (rotatedBoundaryList_ne_nil P) =
      P.outerCycle.vertex (Fin.mk 0 P.outerCycle.length_pos) := by
  unfold rotatedBoundaryList
  rw [List.getLast_ofFn]
  congr 1
  have hrot :=
    OuterBoundaryInterface.finRotate_eq_cyclicSucc
      P.outerCycle.length_pos
      (Fin.mk (P.outerCycle.length - 1)
        (Nat.sub_lt P.outerCycle.length_pos Nat.one_pos))
  rw [hrot]
  ext
  change ((P.outerCycle.length - 1) + 1) % P.outerCycle.length = 0
  have hpred :
      P.outerCycle.length - 1 + 1 = P.outerCycle.length :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt P.outerCycle.length_pos)
  rw [hpred, Nat.mod_self]

theorem rotatedBoundaryList_chain
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (rotatedBoundaryList P).IsChain (UnitDistanceSimpleGraph C).Adj := by
  rw [rotatedBoundaryList, List.isChain_ofFn]
  intro i hi
  let a : Fin P.outerCycle.length :=
    Fin.mk i (Nat.lt_of_succ_lt hi)
  let b : Fin P.outerCycle.length := Fin.mk (i + 1) hi
  have hsucc_a :
      PlanarInterface.cyclicSucc P.outerCycle.length_pos a = b := by
    ext
    change (i + 1) % P.outerCycle.length = i + 1
    exact Nat.mod_eq_of_lt hi
  have hnext :
      finRotate P.outerCycle.length b =
        PlanarInterface.cyclicSucc P.outerCycle.length_pos
          (finRotate P.outerCycle.length a) := by
    calc
      finRotate P.outerCycle.length b =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos b :=
        OuterBoundaryInterface.finRotate_eq_cyclicSucc
          P.outerCycle.length_pos b
      _ =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (PlanarInterface.cyclicSucc P.outerCycle.length_pos a) := by
        rw [hsucc_a]
      _ =
          PlanarInterface.cyclicSucc P.outerCycle.length_pos
            (finRotate P.outerCycle.length a) := by
        rw [OuterBoundaryInterface.finRotate_eq_cyclicSucc
          P.outerCycle.length_pos a]
  have hadj :
      (CanonicalGraph C).Adj
        (P.outerCycle.vertex (finRotate P.outerCycle.length a))
        (P.outerCycle.vertex (finRotate P.outerCycle.length b)) := by
    rw [hnext]
    exact P.outerCycle.adjacent (finRotate P.outerCycle.length a)
  exact (GraphBridge.unitDistanceSimpleGraph_adj C _ _).2
    (((CanonicalGraph C).adj_iff_unitDistanceAdj _ _).1 hadj)

theorem rotatedBoundaryList_nodup
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (rotatedBoundaryList P).Nodup := by
  rw [rotatedBoundaryList]
  exact
    List.nodup_ofFn_ofInjective
      (P.outerCycle.simple.comp
        (finRotate P.outerCycle.length).injective)

theorem mathlib_first_adj
    (P : OuterBoundaryCore.{0} (CanonicalGraph C)) :
    (UnitDistanceSimpleGraph C).Adj
      (P.outerCycle.vertex (Fin.mk 0 P.outerCycle.length_pos))
      ((rotatedBoundaryList P).head (rotatedBoundaryList_ne_nil P)) := by
  rw [rotatedBoundaryList_head]
  have hcanonical :
      (CanonicalGraph C).Adj
        (P.outerCycle.vertex (Fin.mk 0 P.outerCycle.length_pos))
        (P.outerCycle.vertex
          (finRotate P.outerCycle.length
            (Fin.mk 0 P.outerCycle.length_pos))) := by
    have hrot :=
      OuterBoundaryInterface.finRotate_eq_cyclicSucc
        P.outerCycle.length_pos (Fin.mk 0 P.outerCycle.length_pos)
    rw [hrot]
    exact P.outerCycle.adjacent (Fin.mk 0 P.outerCycle.length_pos)
  exact (GraphBridge.unitDistanceSimpleGraph_adj C _ _).2
    (((CanonicalGraph C).adj_iff_unitDistanceAdj _ _).1 hcanonical)

/-- A recorded boundary cycle of length at least three carries a Mathlib
`Walk.IsCycle` certificate on the canonical unit-distance graph. -/
def ofOuterBoundaryCoreWithLength
    (P : OuterBoundaryCore.{0} (CanonicalGraph C))
    (hcycle : 3 <= P.outerCycle.length) :
    ActualOuterBoundaryCoreCycleWitness P := by
  let L := rotatedBoundaryList P
  have hLne : L ≠ [] := rotatedBoundaryList_ne_nil P
  have hchain : L.IsChain (UnitDistanceSimpleGraph C).Adj := by
    exact rotatedBoundaryList_chain (C := C) P
  let tailWalk :=
    ListChainWalk.ofChain L hLne hchain
  have htailStart :
      tailWalk.support = L := by
    dsimp only [tailWalk]
    exact ListChainWalk.ofChain_support L hLne hchain
  have htailEnd :
      L.getLast hLne =
        P.outerCycle.vertex (Fin.mk 0 P.outerCycle.length_pos) := by
    exact rotatedBoundaryList_getLast (C := C) P
  let tailWalk' :=
    tailWalk.copy rfl htailEnd
  have htailWalk'_support :
      tailWalk'.support = L := by
    dsimp only [tailWalk']
    rw [SimpleGraph.Walk.support_copy]
    exact htailStart
  have htailWalk'_path :
      tailWalk'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    rw [htailWalk'_support]
    exact rotatedBoundaryList_nodup (C := C) P
  have hfirst :
      (UnitDistanceSimpleGraph C).Adj
        (P.outerCycle.vertex (Fin.mk 0 P.outerCycle.length_pos))
        ((rotatedBoundaryList P).head
          (rotatedBoundaryList_ne_nil P)) :=
    mathlib_first_adj (C := C) P
  let walk :=
    SimpleGraph.Walk.cons hfirst tailWalk'
  have hwalk_tail_path : walk.tail.IsPath := by
    dsimp only [walk]
    rw [SimpleGraph.Walk.tail_cons, SimpleGraph.Walk.isPath_copy]
    exact htailWalk'_path
  have htail_length :
      tailWalk'.length + 1 = P.outerCycle.length := by
    have hsupp_len : tailWalk'.support.length = tailWalk'.length + 1 :=
      tailWalk'.length_support
    rw [htailWalk'_support] at hsupp_len
    have hLlength : L.length = P.outerCycle.length := by
      dsimp only [L, rotatedBoundaryList]
      rw [List.length_ofFn]
    rw [hLlength] at hsupp_len
    exact hsupp_len.symm
  have hwalk_length : walk.length = P.outerCycle.length := by
    dsimp only [walk]
    rw [SimpleGraph.Walk.length_cons]
    exact htail_length
  have hwalk_support :
      walk.support =
        P.outerCycle.vertex (Fin.mk 0 P.outerCycle.length_pos) :: L := by
    dsimp only [walk]
    rw [SimpleGraph.Walk.support_cons, htailWalk'_support]
  refine
    { base := P.outerCycle.vertex (Fin.mk 0 P.outerCycle.length_pos)
      walk := walk
      isCycle := ?_
      length_eq_outerCycle_length := hwalk_length
      support_iff_outerCycle := ?_ }
  · rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨hwalk_tail_path, by rw [hwalk_length]; exact hcycle⟩
  · intro v
    constructor
    · intro hv
      rw [hwalk_support] at hv
      rw [List.mem_cons] at hv
      rcases hv with hv | hv
      · exact
          ⟨Fin.mk 0 P.outerCycle.length_pos, hv.symm⟩
      · have hv' :
            Exists fun k : Fin P.outerCycle.length =>
              P.outerCycle.vertex (finRotate P.outerCycle.length k) = v := by
          simpa only [L, rotatedBoundaryList, List.mem_ofFn] using hv
        rcases hv' with ⟨k, hk⟩
        exact ⟨finRotate P.outerCycle.length k, hk⟩
    · rintro ⟨k, hk⟩
      rw [hwalk_support]
      right
      change v ∈ L
      dsimp only [L, rotatedBoundaryList]
      rw [List.mem_ofFn]
      refine ⟨(finRotate P.outerCycle.length).symm k, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hk

/-- A Mathlib cycle certificate forces the selected outer cycle to have length
at least three. -/
theorem three_le_outerCycle_length
    (W : ActualOuterBoundaryCoreCycleWitness P) :
    3 <= P.outerCycle.length := by
  rw [<- W.length_eq_outerCycle_length]
  exact SimpleGraph.Walk.IsCycle.three_le_length W.isCycle

/-- The Mathlib-cycle source directly inhabits the stronger actual boundary
cycle payload. -/
def toActualOuterBoundaryCycleData
    (W : ActualOuterBoundaryCoreCycleWitness P) :
    JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C :=
  JordanBoundaryConcrete.ActualOuterBoundaryCycleData.ofCore
    P W.three_le_outerCycle_length

/-- The fake two-endpoint selected-face boundary cannot carry a Mathlib cycle
certificate. -/
theorem false_of_outerCycle_length_eq_two
    (W : ActualOuterBoundaryCoreCycleWitness P)
    (hlen : P.outerCycle.length = 2) :
    False := by
  have hthree := W.three_le_outerCycle_length
  rw [hlen] at hthree
  norm_num at hthree

end ActualOuterBoundaryCoreCycleWitness

/-- No selected boundary of length two can satisfy the stronger Mathlib-cycle
source. -/
theorem not_nonempty_actualOuterBoundaryCoreCycleWitness_of_outerCycle_length_eq_two
    {C : _root_.UDConfig n}
    {P : OuterBoundaryCore.{0} (CanonicalGraph C)}
    (hlen : P.outerCycle.length = 2) :
    Not (Nonempty (ActualOuterBoundaryCoreCycleWitness P)) := by
  rintro ⟨W⟩
  exact W.false_of_outerCycle_length_eq_two hlen

/-- The accepted adjacent-pair weak topology witness is rejected by the
stronger Mathlib-cycle source. -/
theorem not_nonempty_actualOuterBoundaryCoreCycleWitness_of_adjacentPair
    {C : _root_.UDConfig n} {i j : Fin n}
    (hAdj : GraphBridge.UnitDistanceAdj C i j) :
    Not
      (Nonempty
        (ActualOuterBoundaryCoreCycleWitness
          (JordanSourceFields.ofTopology
            (TopologySourceFields.ofMissingOuterFaceData
              (JordanBoundaryConcrete.MissingOuterFaceData.ofUnitDistanceAdj
                (C := C) hAdj))).toOuterBoundaryCore)) := by
  apply not_nonempty_actualOuterBoundaryCoreCycleWitness_of_outerCycle_length_eq_two
  rfl

/-- The stronger S2 cycle blocker: an actual outer-boundary core together with
a nondegenerate selected outer cycle.  This is intentionally stronger than the
current weak `MissingOuterFaceData` lane inhabited from one adjacent pair. -/
def ExactActualOuterBoundaryCycleSourceBlocker
    (C : _root_.UDConfig n) : Prop :=
  Exists fun P : OuterBoundaryCore.{0} (CanonicalGraph C) =>
    3 <= P.outerCycle.length

/-- Sharper S2 source: an outer-boundary core whose selected boundary is an
honest Mathlib simple graph cycle, not merely a recorded face boundary. -/
def ExactMathlibActualOuterBoundaryCycleSourceBlocker
    (C : _root_.UDConfig n) : Prop :=
  Exists fun P : OuterBoundaryCore.{0} (CanonicalGraph C) =>
    Nonempty (ActualOuterBoundaryCoreCycleWitness P)

/--
Precise finite-noncrossing planar theorem still needed upstream.

For the canonical unit-distance graph the vertex type is finite and
pairwise-noncrossing is already proved by `CanonicalGraph.pairwiseNoncrossing`.
What remains for the strong S2 lane is exactly: construct face-boundary data,
select the actual outer face, prove its boundary has length at least three,
and attach the outer-enclosure predicates.  The length field excludes the weak
adjacent-pair face-boundary witness.
-/
def ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem
    (C : _root_.UDConfig n) : Prop :=
  Exists fun H : FaceBoundaryHypotheses C =>
    Exists fun F : H.Face =>
      H.IsOuterFace F /\
        3 <= H.boundaryLength F /\
          Nonempty
            (OuterBoundaryInterface.OuterBoundaryEnclosure
              (CanonicalGraph C) H F)

/-- Direct constructor from the exact face-boundary fields exposed by
`FaceReduction`, with no adjacent-pair or graph-cycle synthesis. -/
theorem exactFiniteNoncrossingActualOuterBoundaryCycleTheorem_of_faceBoundaryFields
    {C : _root_.UDConfig n}
    {H : FaceBoundaryHypotheses C}
    {F : H.Face}
    (hF : H.IsOuterFace F)
    (hlen : 3 <= H.boundaryLength F)
    (E : OuterBoundaryInterface.OuterBoundaryEnclosure
      (CanonicalGraph C) H F) :
    ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C := by
  exact
    Exists.intro H
      (Exists.intro F
        (And.intro hF
          (And.intro hlen (Nonempty.intro E))))

theorem w28FiniteNoncrossingActualOuterBoundaryCycleSource_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem
    {C : _root_.UDConfig n}
    (h : ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C) :
    OuterBoundaryCoreConstructionW28.FiniteNoncrossingActualOuterBoundaryCycleSource
      C := by
  rcases h with ⟨H, F, hF, hlen, ⟨E⟩⟩
  exact
    Exists.intro H
      (Exists.intro F
        (And.intro hF
          (And.intro hlen (Nonempty.intro E))))

theorem exactFiniteNoncrossingActualOuterBoundaryCycleTheorem_of_w28FiniteNoncrossingActualOuterBoundaryCycleSource
    {C : _root_.UDConfig n}
    (h :
      OuterBoundaryCoreConstructionW28.FiniteNoncrossingActualOuterBoundaryCycleSource
        C) :
    ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C := by
  rcases h with ⟨H, F, hF, hlen, ⟨E⟩⟩
  exact
    exactFiniteNoncrossingActualOuterBoundaryCycleTheorem_of_faceBoundaryFields
      (C := C) (H := H) (F := F) hF hlen E

/-- Exact finite-noncrossing face-boundary fields inhabit the concrete W28
source-with-length package. -/
theorem nonempty_outerBoundaryCoreSourceWithLength_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem
    {C : _root_.UDConfig n}
    (h : ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C) :
    Nonempty
      (OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength C) :=
  OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSourceWithLength_of_finiteNoncrossingActualOuterBoundaryCycleSource
    (C := C)
    (w28FiniteNoncrossingActualOuterBoundaryCycleSource_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem
      h)

theorem remainingActualOuterBoundaryCycleTheorem_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem
    {C : _root_.UDConfig n}
    (h : ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C) :
    JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
      C :=
  OuterBoundaryCoreConstructionW28.remainingActualOuterBoundaryCycleTheorem_of_finiteNoncrossingActualOuterBoundaryCycleSource
    (C := C)
    (w28FiniteNoncrossingActualOuterBoundaryCycleSource_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem
      h)

def ExactActualBoundaryCycleDataWithMathlibWitnessSource
    (C : _root_.UDConfig n) : Prop :=
  Exists fun D : JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C =>
    Nonempty (ActualOuterBoundaryCoreCycleWitness D.core)

/-- The same strong S2 source stated directly on the concrete topology package:
construct the selected topology facts and prove that their selected boundary
is nondegenerate. -/
def ExactNondegenerateMissingTopologyFactsSource
    (C : _root_.UDConfig n) : Prop :=
  Exists fun T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C =>
    3 <= T.outerCycle.length

theorem nonempty_actualOuterBoundaryCycleData_iff_exactCycleBlocker
    (C : _root_.UDConfig n) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) <->
      ExactActualOuterBoundaryCycleSourceBlocker C :=
  JordanBoundaryConcrete.ActualOuterBoundaryCycleData.nonempty_iff_outerBoundaryCore_with_length_ge_three
    (C := C)

theorem exactNondegenerateMissingTopologyFactsSource_iff_exactCycleBlocker
    (C : _root_.UDConfig n) :
    ExactNondegenerateMissingTopologyFactsSource C <->
      ExactActualOuterBoundaryCycleSourceBlocker C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro T hT =>
        exact Exists.intro T.toCore (by
          change 3 <= T.outerCycle.length
          exact hT)
  case mpr =>
    intro h
    cases h with
    | intro P hP =>
        exact
          Exists.intro
            (JordanBoundaryConcrete.MissingTopologyFacts.ofCore P) (by
              change 3 <= P.outerCycle.length
              exact hP)

/-- A W28 outer-boundary core source closes the strong W32 source exactly when
its recorded outer cycle is nondegenerate. -/
theorem exactNondegenerateMissingTopologyFactsSource_of_w28OuterBoundaryCoreSource
    {C : _root_.UDConfig n}
    (S : OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource C)
    (hcycle : 3 <= S.core.outerCycle.length) :
    ExactNondegenerateMissingTopologyFactsSource C :=
  (exactNondegenerateMissingTopologyFactsSource_iff_exactCycleBlocker C).2
    (Exists.intro S.core hcycle)

theorem exactNondegenerateMissingTopologyFactsSource_iff_w28OuterBoundaryCoreSource_with_length
    (C : _root_.UDConfig n) :
    ExactNondegenerateMissingTopologyFactsSource C <->
      Exists fun S : OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource C =>
        3 <= S.core.outerCycle.length := by
  constructor
  case mp =>
    intro h
    cases
        (exactNondegenerateMissingTopologyFactsSource_iff_exactCycleBlocker
          C).1 h with
    | intro P hP =>
        exact
          Exists.intro
            (OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource.ofOuterBoundaryCore
              P)
            (by
              rw [OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSource.ofOuterBoundaryCore_core]
              exact hP)
  case mpr =>
    intro h
    cases h with
    | intro S hS =>
        exact
          exactNondegenerateMissingTopologyFactsSource_of_w28OuterBoundaryCoreSource
            S hS

/-- A W31 face-boundary/enclosure source closes the strong W32 source exactly
when its selected outer cycle is nondegenerate. -/
theorem exactNondegenerateMissingTopologyFactsSource_of_w31FaceBoundaryEnclosureSource
    {C : _root_.UDConfig n}
    (S : W31Source C)
    (hcycle : 3 <= S.toOuterBoundaryCore.outerCycle.length) :
    ExactNondegenerateMissingTopologyFactsSource C :=
  (exactNondegenerateMissingTopologyFactsSource_iff_exactCycleBlocker C).2
    (Exists.intro S.toOuterBoundaryCore hcycle)

theorem exactNondegenerateMissingTopologyFactsSource_iff_w31FaceBoundaryEnclosureSource_with_length
    (C : _root_.UDConfig n) :
    ExactNondegenerateMissingTopologyFactsSource C <->
      Exists fun S : W31Source C =>
        3 <= S.toOuterBoundaryCore.outerCycle.length := by
  constructor
  case mp =>
    intro h
    cases
        (exactNondegenerateMissingTopologyFactsSource_iff_exactCycleBlocker
          C).1 h with
    | intro P hP =>
        exact
          Exists.intro
            (EnclosureAndFaceBoundaryW31.ofOuterBoundaryCore P)
            (by
              rw [EnclosureAndFaceBoundaryW31.ofOuterBoundaryCore_toOuterBoundaryCore]
              exact hP)
  case mpr =>
    intro h
    cases h with
    | intro S hS =>
        exact
          exactNondegenerateMissingTopologyFactsSource_of_w31FaceBoundaryEnclosureSource
            S hS

theorem exactMathlibCycleBlocker_iff_actualCycleDataWithWitness
    (C : _root_.UDConfig n) :
    ExactMathlibActualOuterBoundaryCycleSourceBlocker C <->
      ExactActualBoundaryCycleDataWithMathlibWitnessSource C := by
  constructor
  case mp =>
    intro h
    rcases h with ⟨P, hP⟩
    rcases hP with ⟨W⟩
    refine Exists.intro W.toActualOuterBoundaryCycleData ?_
    exact Nonempty.intro W
  case mpr =>
    intro h
    rcases h with ⟨D, hD⟩
    exact Exists.intro D.core hD

theorem actualCycleDataWithWitnessSource_iff_exactMathlibCycleBlocker
    (C : _root_.UDConfig n) :
    ExactActualBoundaryCycleDataWithMathlibWitnessSource C <->
      ExactMathlibActualOuterBoundaryCycleSourceBlocker C :=
  (exactMathlibCycleBlocker_iff_actualCycleDataWithWitness C).symm

theorem actualCycleDataWithWitnessSource_implies_actualCycleData
    {C : _root_.UDConfig n}
    (h : ExactActualBoundaryCycleDataWithMathlibWitnessSource C) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) := by
  rcases h with ⟨D, _hW⟩
  exact Nonempty.intro D

/-- The finite-noncrossing theorem-shaped source gives the raw
nondegenerate outer-boundary core. -/
theorem exactCycleBlocker_of_finiteNoncrossingActualOuterBoundaryCycle
    {C : _root_.UDConfig n}
    (h : ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C) :
    ExactActualOuterBoundaryCycleSourceBlocker C := by
  rcases h with ⟨H, F, hF, hlen, ⟨E⟩⟩
  let P : OuterBoundaryCore.{0} (CanonicalGraph C) := {
    faceBoundary := H
    outerFace := F
    outerFace_isOuter := hF
    outerEnclosure := E }
  exact ⟨P, hlen⟩

/-- Conversely, any Mathlib-cycle source supplies exactly the nondegenerate
finite-noncrossing outer-face theorem fields. -/
theorem finiteNoncrossingActualOuterBoundaryCycle_of_mathlibCycleBlocker
    {C : _root_.UDConfig n}
    (h : ExactMathlibActualOuterBoundaryCycleSourceBlocker C) :
    ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C := by
  rcases h with ⟨P, ⟨W⟩⟩
  exact
    ⟨P.faceBoundary, P.outerFace, P.outerFace_isOuter,
      W.three_le_outerCycle_length, ⟨P.outerEnclosure⟩⟩

/-- The sharper Mathlib-cycle source implies the raw nondegenerate-cycle
blocker. -/
theorem exactCycleBlocker_of_mathlibCycleBlocker
    {C : _root_.UDConfig n}
    (h : ExactMathlibActualOuterBoundaryCycleSourceBlocker C) :
    ExactActualOuterBoundaryCycleSourceBlocker C := by
  rcases h with ⟨P, ⟨W⟩⟩
  exact ⟨P, W.three_le_outerCycle_length⟩

/-- The Mathlib-cycle source is exactly the nondegenerate recorded
outer-boundary-core source: once the selected boundary has length at least
three, its cyclic adjacency and injective vertex record build the Mathlib
`Walk.IsCycle` certificate. -/
theorem mathlibCycleBlocker_of_exactCycleBlocker
    {C : _root_.UDConfig n}
    (h : ExactActualOuterBoundaryCycleSourceBlocker C) :
    ExactMathlibActualOuterBoundaryCycleSourceBlocker C := by
  rcases h with ⟨P, hP⟩
  exact ⟨P, ⟨ActualOuterBoundaryCoreCycleWitness.ofOuterBoundaryCoreWithLength
    (C := C) P hP⟩⟩

theorem exactMathlibCycleBlocker_iff_exactCycleBlocker
    (C : _root_.UDConfig n) :
    ExactMathlibActualOuterBoundaryCycleSourceBlocker C <->
      ExactActualOuterBoundaryCycleSourceBlocker C := by
  constructor
  · exact exactCycleBlocker_of_mathlibCycleBlocker
  · exact mathlibCycleBlocker_of_exactCycleBlocker

theorem exactCycleBlocker_iff_exactMathlibCycleBlocker
    (C : _root_.UDConfig n) :
    ExactActualOuterBoundaryCycleSourceBlocker C <->
      ExactMathlibActualOuterBoundaryCycleSourceBlocker C :=
  (exactMathlibCycleBlocker_iff_exactCycleBlocker C).symm

theorem exactNondegenerateMissingTopologyFactsSource_iff_exactMathlibCycleBlocker
    (C : _root_.UDConfig n) :
    ExactNondegenerateMissingTopologyFactsSource C <->
      ExactMathlibActualOuterBoundaryCycleSourceBlocker C :=
  Iff.trans
    (exactNondegenerateMissingTopologyFactsSource_iff_exactCycleBlocker C)
    (exactCycleBlocker_iff_exactMathlibCycleBlocker C)

theorem exactMathlibCycleBlocker_iff_nonDegenerateMissingTopologyFactsSource
    (C : _root_.UDConfig n) :
    ExactMathlibActualOuterBoundaryCycleSourceBlocker C <->
      ExactNondegenerateMissingTopologyFactsSource C :=
  (exactNondegenerateMissingTopologyFactsSource_iff_exactMathlibCycleBlocker
    C).symm

/-- A nondegenerate concrete topology package is enough for the strong Mathlib
outer-cycle source. -/
theorem mathlibCycleBlocker_of_nonDegenerateMissingTopologyFacts
    {C : _root_.UDConfig n}
    (T : JordanBoundaryConcrete.MissingTopologyFacts.{0} C)
    (hT : 3 <= T.outerCycle.length) :
    ExactMathlibActualOuterBoundaryCycleSourceBlocker C :=
  (exactMathlibCycleBlocker_iff_nonDegenerateMissingTopologyFactsSource C).2
    (Exists.intro T hT)

theorem exactMathlibCycleBlocker_iff_finiteNoncrossingActualOuterBoundaryCycle
    (C : _root_.UDConfig n) :
    ExactMathlibActualOuterBoundaryCycleSourceBlocker C <->
      ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C := by
  constructor
  · exact finiteNoncrossingActualOuterBoundaryCycle_of_mathlibCycleBlocker
  · intro h
    exact mathlibCycleBlocker_of_exactCycleBlocker
      (exactCycleBlocker_of_finiteNoncrossingActualOuterBoundaryCycle h)

theorem finiteNoncrossingActualOuterBoundaryCycle_iff_exactMathlibCycleBlocker
    (C : _root_.UDConfig n) :
    ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C <->
      ExactMathlibActualOuterBoundaryCycleSourceBlocker C :=
  (exactMathlibCycleBlocker_iff_finiteNoncrossingActualOuterBoundaryCycle C).symm

theorem exactNondegenerateMissingTopologyFactsSource_iff_finiteNoncrossingActualOuterBoundaryCycle
    (C : _root_.UDConfig n) :
    ExactNondegenerateMissingTopologyFactsSource C <->
      ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C :=
  Iff.trans
    (exactNondegenerateMissingTopologyFactsSource_iff_exactMathlibCycleBlocker
      C)
    (exactMathlibCycleBlocker_iff_finiteNoncrossingActualOuterBoundaryCycle
      C)

/-- The S2 nondegenerate missing-topology source is exactly the honest
nondegenerate outer-boundary construction theorem recorded in
`JordanBoundaryConcrete`. -/
theorem exactNondegenerateMissingTopologyFactsSource_iff_remainingActualOuterBoundaryCycleTheorem
    (C : _root_.UDConfig n) :
    ExactNondegenerateMissingTopologyFactsSource C <->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C :=
  (JordanBoundaryConcrete.MissingTopologyFacts.remainingActualOuterBoundaryCycleTheorem_iff_missingTopologyFacts_with_length_ge_three
    C).symm

/-- Reduction of the S2 source to the honest nondegenerate outer-boundary
construction theorem. -/
theorem exactNondegenerateMissingTopologyFactsSource_of_remainingActualOuterBoundaryCycleTheorem
    {C : _root_.UDConfig n}
    (h :
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C) :
    ExactNondegenerateMissingTopologyFactsSource C :=
  (exactNondegenerateMissingTopologyFactsSource_iff_remainingActualOuterBoundaryCycleTheorem
    C).2 h

theorem nonempty_actualOuterBoundaryCycleData_iff_exactMathlibCycleBlocker
    (C : _root_.UDConfig n) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) <->
      ExactMathlibActualOuterBoundaryCycleSourceBlocker C := by
  exact
    Iff.trans
      (nonempty_actualOuterBoundaryCycleData_iff_exactCycleBlocker C)
      (exactCycleBlocker_iff_exactMathlibCycleBlocker C)

/-- The sharper Mathlib-cycle source inhabits the stronger actual outer
boundary-cycle payload. -/
theorem nonempty_actualOuterBoundaryCycleData_of_mathlibCycleBlocker
    {C : _root_.UDConfig n}
    (h : ExactMathlibActualOuterBoundaryCycleSourceBlocker C) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) := by
  rcases h with ⟨P, ⟨W⟩⟩
  exact ⟨W.toActualOuterBoundaryCycleData⟩

theorem actualOuterBoundaryCycleData_of_jordanSourceFields
    {C : _root_.UDConfig n}
    (J : JordanSourceFields C)
    (hcycle : 3 <= J.toOuterBoundaryCore.outerCycle.length) :
    Nonempty (JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C) :=
  Nonempty.intro (J.toActualOuterBoundaryCycleData hcycle)

theorem nonempty_jordanSourceFields_iff_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      Nonempty (ActualSelectedTopologyData C) :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_outerBoundaryCore C)
    (ActualSelectedTopologyDataW27.nonempty_actualSelectedTopologyData_iff_outerBoundaryCore
      C).symm

theorem nonempty_actualSelectedTopologyData_iff_jordanSourceFields
    (C : _root_.UDConfig n) :
    Nonempty (ActualSelectedTopologyData C) <->
      Nonempty (JordanSourceFields C) :=
  (nonempty_jordanSourceFields_iff_actualSelectedTopologyData C).symm

theorem jordanSourceFields_nonempty_of_actualSelectedTopologyData
    {C : _root_.UDConfig n}
    (A : ActualSelectedTopologyData C) :
    Nonempty (JordanSourceFields C) :=
  Nonempty.intro (JordanSourceFields.ofActualSelectedTopologyData A)

theorem actualSelectedTopologyData_nonempty_of_jordanSourceFields
    {C : _root_.UDConfig n}
    (J : JordanSourceFields C) :
    Nonempty (ActualSelectedTopologyData C) :=
  Nonempty.intro J.actualSelectedTopologyData

theorem nonempty_jordanSourceFields_iff_remainingCoreTopology
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      OuterBoundaryCoreConstruction.RemainingCoreTopologyRequirements C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_w31Source C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_remainingCoreTopology C)

theorem nonempty_jordanSourceFields_iff_noncrossingFrontier
    (C : _root_.UDConfig n) :
    Nonempty (JordanSourceFields C) <->
      TopologyExtractionFromNoncrossing.ConcreteNoncrossingTopologyFrontier C :=
  Iff.trans
    (nonempty_jordanSourceFields_iff_w31Source C)
    (EnclosureAndFaceBoundaryW31.nonempty_source_iff_noncrossingFrontier C)

theorem jordanSource_missing_iff_no_exactBlocker
    (C : _root_.UDConfig n) :
    Not (Nonempty (JordanSourceFields C)) <->
      Not (ExactSelectedFaceEnclosureBlocker C) :=
  not_congr (nonempty_jordanSourceFields_iff_exactBlocker C)

theorem jordanSource_missing_iff_no_actualSelectedTopologyData
    (C : _root_.UDConfig n) :
    Not (Nonempty (JordanSourceFields C)) <->
      Not (Nonempty (ActualSelectedTopologyData C)) :=
  not_congr (nonempty_jordanSourceFields_iff_actualSelectedTopologyData C)

def actualSelectedTopologyDataOfJordanSource
    {C : _root_.UDConfig n}
    (J : JordanSourceFields C) :
    ActualSelectedTopologyData C :=
  J.actualSelectedTopologyData

theorem nonempty_actualSelectedTopologyData_of_jordanSource
    {C : _root_.UDConfig n}
    (h : Nonempty (JordanSourceFields C)) :
    Nonempty (ActualSelectedTopologyData C) := by
  cases h with
  | intro J =>
      exact Nonempty.intro J.actualSelectedTopologyData

abbrev MinimalFailureJordanSourceRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      JordanSourceFields C

abbrev MinimalFailureActualSelectedTopologyRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ActualSelectedTopologyData C

abbrev MinimalFailureActualOuterBoundaryCycleDataRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0} C

abbrev MinimalFailureSimpleCyclicOuterBoundaryEnclosureRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows C

abbrev MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength C

abbrev MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows
        C

theorem unitDistanceSimpleGraph_degree_eq_neighborSet_card
    {n : Nat} (C : _root_.UDConfig n) (v : Fin n) :
    ((UnitDistanceSimpleGraph C).neighborFinset v).card =
      (DegreePipeline.unitDistanceNeighborSet C v).card := by
  classical
  congr 1
  ext w
  rw [SimpleGraph.neighborFinset_def]
  simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet]
  rw [DegreePipeline.mem_unitDistanceNeighborSet C v w]
  constructor
  · intro h
    have hpair :=
      (GraphBridge.unitDistanceSimpleGraph_adj_iff_ne_and_dist C v w).1 h
    exact
      And.intro
        ((bne_iff_ne (a := w) (b := v)).2
          (fun hwv => hpair.1 hwv.symm))
        (by simpa [_root_.eucDist_comm] using hpair.2)
  · intro h
    exact
      (GraphBridge.unitDistanceSimpleGraph_adj C v w).2
        (by simpa [_root_.eucDist_comm] using h.2)

theorem unitDistanceSimpleGraph_not_acyclic_of_minimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Not (UnitDistanceSimpleGraph C).IsAcyclic := by
  classical
  let G : SimpleGraph (Fin n) := UnitDistanceSimpleGraph C
  have hn : 0 < n :=
    MinimalFailureConcreteDataMatrix.positiveCard_of_minimalClearedFailure
      hmin
  haveI : Nonempty (Fin n) := Nonempty.intro ⟨0, hn⟩
  have hdegree_two : forall v : Fin n, 2 <= G.degree v := by
    intro v
    have hthree :
        3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
      CutVertexFinal.minimumDegree_of_minimalFailure hmin v
    have hdeg_card :
        (G.neighborFinset v).card =
          (DegreePipeline.unitDistanceNeighborSet C v).card := by
      congr 1
      ext w
      rw [SimpleGraph.neighborFinset_def]
      simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet]
      rw [DegreePipeline.mem_unitDistanceNeighborSet C v w]
      constructor
      · intro h
        have hunit : (UnitDistanceSimpleGraph C).Adj v w := by
          simpa [G] using h
        have hpair :=
          (GraphBridge.unitDistanceSimpleGraph_adj_iff_ne_and_dist C v w).1
            hunit
        exact
          And.intro
            ((bne_iff_ne (a := w) (b := v)).2
              (fun hwv => hpair.1 hwv.symm))
            (by simpa [_root_.eucDist_comm] using hpair.2)
      · intro h
        have hunit : (UnitDistanceSimpleGraph C).Adj v w :=
          (GraphBridge.unitDistanceSimpleGraph_adj C v w).2
            (by simpa [_root_.eucDist_comm] using h.2)
        simpa [G] using hunit
    have hcard_bound : 2 <= (G.neighborFinset v).card := by
      rw [hdeg_card]
      exact Nat.le_trans (by decide : 2 <= 3) hthree
    have hdeg_eq :
        (G.neighborFinset v).card = G.degree v :=
      SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v)
    exact hdeg_eq ▸ hcard_bound
  have hminDegree_two : 2 <= G.minDegree :=
    SimpleGraph.le_minDegree_of_forall_le_degree (G := G) 2 hdegree_two
  have hcard_gt_one : 1 < Fintype.card (Fin n) := by
    let v : Fin n := ⟨0, hn⟩
    have hvdeg : 2 <= G.degree v := hdegree_two v
    have hvlt : G.degree v < Fintype.card (Fin n) :=
      SimpleGraph.degree_lt_card_verts (G := G) v
    exact Nat.lt_trans (by decide : 1 < 2) (Nat.lt_of_le_of_lt hvdeg hvlt)
  haveI : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp hcard_gt_one
  intro hacyclic
  have hconnected : G.Connected := by
    simpa [G] using
      CutVertexFinal.connected_of_minimalFailure
        (C := C) hn hmin
  have htree : G.IsTree := ⟨hconnected, hacyclic⟩
  have hminDegree_one : G.minDegree = 1 :=
    SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial
      (G := G) htree
  rw [hminDegree_one] at hminDegree_two
  exact Nat.not_succ_le_self 1 hminDegree_two

theorem outerBoundaryExistenceCanonicalGraph_adj_of_unitDistanceSimpleGraph_adj
    {n : Nat} {C : _root_.UDConfig n} {i j : Fin n}
    (h : (UnitDistanceSimpleGraph C).Adj i j) :
    (OuterBoundaryExistenceConcrete.canonicalGraph C).Adj i j :=
  ((OuterBoundaryExistenceConcrete.canonicalGraph C).adj_iff_unitDistanceAdj
    i j).2
    ((GraphBridge.unitDistanceAdj_iff C i j).2
      ((GraphBridge.unitDistanceSimpleGraph_adj C i j).1 h))

def extractedSimpleCyclicOuterBoundaryEnclosureRowsOfWalkCycle
    {n : Nat} {C : _root_.UDConfig n} {base : Fin n}
    (walk : (UnitDistanceSimpleGraph C).Walk base base)
    (hcycle : walk.IsCycle) :
    OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows
      C where
  boundary := {
    length := walk.length
    length_pos :=
      Nat.lt_of_lt_of_le (by decide : 0 < 3)
        (SimpleGraph.Walk.IsCycle.three_le_length hcycle)
    vertex := fun k => walk.getVert k.val
    adjacent := by
      intro k
      let hpos : 0 < walk.length :=
        Nat.lt_of_lt_of_le (by decide : 0 < 3)
          (SimpleGraph.Walk.IsCycle.three_le_length hcycle)
      by_cases hk : k.val + 1 < walk.length
      · have hsucc_val :
            (PlanarInterface.cyclicSucc hpos k).val = k.val + 1 := by
          simp [PlanarInterface.cyclicSucc, Nat.mod_eq_of_lt hk]
        have hadj :
            (UnitDistanceSimpleGraph C).Adj
              (walk.getVert k.val) (walk.getVert (k.val + 1)) :=
          walk.adj_getVert_succ k.isLt
        have hadj_canon :
            (OuterBoundaryExistenceConcrete.canonicalGraph C).Adj
              (walk.getVert k.val) (walk.getVert (k.val + 1)) :=
          outerBoundaryExistenceCanonicalGraph_adj_of_unitDistanceSimpleGraph_adj
            (C := C) hadj
        change
          (OuterBoundaryExistenceConcrete.canonicalGraph C).Adj
            (walk.getVert k.val)
            (walk.getVert (PlanarInterface.cyclicSucc hpos k).val)
        rw [hsucc_val]
        exact hadj_canon
      · have hlast : k.val + 1 = walk.length :=
          eq_of_le_of_not_lt (Nat.succ_le_of_lt k.isLt) hk
        have hsucc_val :
            (PlanarInterface.cyclicSucc hpos k).val = 0 := by
          simp [PlanarInterface.cyclicSucc, hlast]
        have hadj :
            (UnitDistanceSimpleGraph C).Adj
              (walk.getVert k.val) (walk.getVert (k.val + 1)) :=
          walk.adj_getVert_succ k.isLt
        have hend : walk.getVert (k.val + 1) = walk.getVert 0 := by
          rw [hlast, SimpleGraph.Walk.getVert_length,
            SimpleGraph.Walk.getVert_zero]
        have hadj_zero :
            (UnitDistanceSimpleGraph C).Adj
              (walk.getVert k.val) (walk.getVert 0) := by
          simpa [hend] using hadj
        have hadj_canon :
            (OuterBoundaryExistenceConcrete.canonicalGraph C).Adj
              (walk.getVert k.val) (walk.getVert 0) :=
          outerBoundaryExistenceCanonicalGraph_adj_of_unitDistanceSimpleGraph_adj
            (C := C) hadj_zero
        change
          (OuterBoundaryExistenceConcrete.canonicalGraph C).Adj
            (walk.getVert k.val)
            (walk.getVert (PlanarInterface.cyclicSucc hpos k).val)
        rw [hsucc_val]
        exact hadj_canon
    simple := by
      intro a b h
      apply Fin.ext
      exact
        SimpleGraph.Walk.IsCycle.getVert_injOn' hcycle
          (Nat.le_sub_one_of_lt a.isLt)
          (Nat.le_sub_one_of_lt b.isLt)
          h
    length_ge_three := SimpleGraph.Walk.IsCycle.three_le_length hcycle
  }
  insideOrOn := fun _ => True
  onBoundary := fun v =>
    Exists fun k : Fin walk.length => walk.getVert k.val = v
  boundary_vertex_onBoundary := fun k => Exists.intro k rfl
  boundary_point_insideOrOn := fun _ => trivial
  all_vertices_insideOrOn := fun _ => trivial
  onBoundary_iff_outer_cycle := fun _ => Iff.rfl

noncomputable def extractedSimpleCyclicOuterBoundaryEnclosureRowsOfMinimalClearedFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows
      C := by
  classical
  let G : SimpleGraph (Fin n) := UnitDistanceSimpleGraph C
  have hnotAcyclic :
      Not G.IsAcyclic := by
    simpa [G] using
      unitDistanceSimpleGraph_not_acyclic_of_minimalClearedFailure
        (C := C) hmin
  let hexists := (SimpleGraph.exists_girth_eq_length (G := G)).2 hnotAcyclic
  let base : Fin n := Classical.choose hexists
  let hwalkExists := Classical.choose_spec hexists
  let walk : G.Walk base base := Classical.choose hwalkExists
  have hcycle : walk.IsCycle := (Classical.choose_spec hwalkExists).1
  exact
    extractedSimpleCyclicOuterBoundaryEnclosureRowsOfWalkCycle
      (C := C) walk hcycle

noncomputable def minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :
    MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  fun C hmin =>
    extractedSimpleCyclicOuterBoundaryEnclosureRowsOfMinimalClearedFailure
      (C := C) hmin

def MinimalFailureNondegenerateMissingTopologyFactsTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ExactNondegenerateMissingTopologyFactsSource C

def MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      JordanBoundaryConcrete.MissingTopologyFacts.RemainingActualOuterBoundaryCycleTheorem
        C

def MinimalFailureExactMathlibActualOuterBoundaryCycleSourceTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ExactMathlibActualOuterBoundaryCycleSourceBlocker C

def MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      OuterBoundaryCoreConstructionW28.FiniteNoncrossingActualOuterBoundaryCycleSource
        C

def MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget :
    Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem C

def MinimalFailureOuterBoundaryCoreSourceWithLengthTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      Nonempty
        (OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength C)

def MinimalFailureExactActualTopologyFieldsTarget : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C ->
      OuterBoundaryExistenceConcrete.ExactActualTopologyFields C

/-- Rowwise constructor for the S2 actual topology target from an extracted
simple cyclic outer-boundary row and the matching enclosure predicates.  The
selected `H/F/outer/length` rows are supplied by the
`FaceReduction.ofOuterBoundaryCycle` bridge; this theorem only attaches the
separate enclosure rows to the same extracted boundary. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_extractedOuterBoundaryCycle_enclosureRows
    (R :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryRow C)
    (insideOrOn :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          PlanarInterface.Point -> Prop)
    (onBoundary :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          Fin n -> Prop)
    (boundary_vertex_onBoundary :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          forall k : Fin ((R C hmin).length),
            onBoundary C hmin ((R C hmin).vertex k))
    (boundary_point_insideOrOn :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          forall k : Fin ((R C hmin).length),
            insideOrOn C hmin
              ((CanonicalGraph C).point ((R C hmin).vertex k)))
    (all_vertices_insideOrOn :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          forall v : Fin n,
            insideOrOn C hmin ((CanonicalGraph C).point v))
    (onBoundary_iff_outer_cycle :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          forall v : Fin n,
            onBoundary C hmin v <->
              Exists fun k : Fin ((R C hmin).length) =>
                (R C hmin).vertex k = v) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  intro n C hmin
  exact
    OuterBoundaryExistenceConcrete.exactActualTopologyFields_of_extractedSimpleCyclicOuterBoundaryRow_enclosure
      (C := C) (R := R C hmin)
      (insideOrOn := insideOrOn C hmin)
      (onBoundary := onBoundary C hmin)
      (boundary_vertex_onBoundary := boundary_vertex_onBoundary C hmin)
      (boundary_point_insideOrOn := boundary_point_insideOrOn C hmin)
      (all_vertices_insideOrOn := all_vertices_insideOrOn C hmin)
      (onBoundary_iff_outer_cycle := onBoundary_iff_outer_cycle C hmin)

/-- The compact positive S2 row package closes the exact actual topology
target rowwise.  Its remaining obligation is the honest construction of those
minimal-failure rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_extractedSimpleCyclicOuterBoundaryEnclosureRows
    (rows : MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  intro n C hmin
  exact
    OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows.toExactActualTopologyFields
      (rows (n := n) C hmin)

/-- The extracted cyclic boundary/enclosure rows carry an honest
nondegenerate face-boundary length proof.  The proof is the row's
`length_ge_three`, transported through `FaceReduction.ofOuterBoundaryCycle`;
it does not use the adjacent-pair selected-face witness. -/
theorem extractedSimpleCyclicOuterBoundaryEnclosureRows_boundaryLength_ge_three
    {n : Nat} {C : _root_.UDConfig n}
    (rows :
      OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows
        C) :
    3 <= rows.boundary.toFaceBoundaryHypotheses.boundaryLength PUnit.unit :=
  OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryRow.toFaceBoundaryHypotheses_boundaryLength_ge_three
    rows.boundary

/-- The concrete extracted minimal-failure rows expose the honest
nondegenerate face-boundary length row. -/
  theorem minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows_boundaryLength_ge_three
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    3 <=
      (minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows
        (n := n) C hmin).boundary.toFaceBoundaryHypotheses.boundaryLength
        PUnit.unit :=
  extractedSimpleCyclicOuterBoundaryEnclosureRows_boundaryLength_ge_three
    (minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows
      (n := n) C hmin)

/-- Bookkeeping-only S2 topology/length row from a graph cycle.

This theorem deliberately keeps the synthetic-cycle route out of the live
`minimalFailureExactActualTopologyFieldsTarget` name.  Its enclosure predicates
come from `extractedSimpleCyclicOuterBoundaryEnclosureRowsOfWalkCycle`, whose
`insideOrOn` field is a compatibility shim, not a Jordan/outer-face
construction.  Use the strong constructors from
`MinimalFailureOuterBoundaryCoreSourceWithLengthRows`,
`MinimalFailureActualOuterBoundaryCycleDataRows`, or
`SimpleCyclicOuterBoundaryEnclosureRows` for the live S2 route. -/
theorem bookkeeping_minimalFailureExactActualTopologyFieldsTarget_of_syntheticCycleEnclosure :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_extractedSimpleCyclicOuterBoundaryEnclosureRows
    minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows

theorem minimalFailureExactActualTopologyFieldsTarget_iff_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget :
    MinimalFailureExactActualTopologyFieldsTarget <->
      MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget := by
  constructor
  case mp =>
    intro h n C hmin
    rcases h C hmin with ⟨H, F, hF, hlen, hE⟩
    exact ⟨H, F, hF, hlen, hE⟩
  case mpr =>
    intro h n C hmin
    rcases h C hmin with ⟨H, F, hF, hlen, hE⟩
    exact ⟨H, F, hF, hlen, hE⟩

theorem minimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget_of_exactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget) :
    MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget :=
  minimalFailureExactActualTopologyFieldsTarget_iff_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget.1
    h

theorem minimalFailureExactActualTopologyFieldsTarget_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_iff_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget.2
    h

theorem minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget := by
  intro n C hmin
  exact
    OuterBoundaryExistenceConcrete.remainingActualOuterBoundaryCycleTheorem_of_exactActualTopologyFields
      (h C hmin)

theorem minimalFailureExactActualTopologyFieldsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget :
    MinimalFailureExactActualTopologyFieldsTarget <->
      MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget := by
  constructor
  case mp =>
    exact minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
  case mpr =>
    intro h n C hmin
    have hiff :=
      OuterBoundaryExistenceConcrete.exactActualTopologyFields_iff_remainingActualOuterBoundaryCycleTheorem
        C
    exact hiff.2 (h C hmin)

theorem minimalFailureExactActualTopologyFieldsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget.2
    h

/-- W31/Jordan selected face-enclosure rows, together with the honest
nondegenerate boundary-length row, inhabit the concrete W28
source-with-length rows.  The length proof is carried over the definitional
identity between the selected face-boundary length and the core outer-cycle
length. -/
def minimalFailureOuterBoundaryCoreSourceWithLengthRowsOfJordanSourceRowsWithLength
    (rows : MinimalFailureJordanSourceRows)
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <=
            (rows C hmin).faceBoundary.boundaryLength
              (rows C hmin).outerFace) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  fun {n} C hmin =>
    OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength.ofOuterBoundaryCore
      (rows (n := n) C hmin).toOuterBoundaryCore
      (by
        change
          3 <=
            (rows (n := n) C hmin).faceBoundary.boundaryLength
              (rows (n := n) C hmin).outerFace
        exact hlen C hmin)

theorem nonempty_minimalFailureOuterBoundaryCoreSourceWithLengthRows_of_jordanSourceRows_with_length
    (rows : MinimalFailureJordanSourceRows)
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <=
            (rows C hmin).faceBoundary.boundaryLength
              (rows C hmin).outerFace) :
    Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  Nonempty.intro
    (minimalFailureOuterBoundaryCoreSourceWithLengthRowsOfJordanSourceRowsWithLength
      rows hlen)

/-- The same W31/Jordan rows with a real nondegenerate boundary-length proof
also inhabit the extracted simple cyclic boundary/enclosure row package.  The
boundary cycle and enclosure predicates are projected from the same
outer-boundary core. -/
def minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfJordanSourceRowsWithLength
    (rows : MinimalFailureJordanSourceRows)
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <=
            (rows C hmin).faceBoundary.boundaryLength
              (rows C hmin).outerFace) :
    MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  fun {n} C hmin =>
    OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows.ofOuterBoundaryCoreWithLength
      (rows (n := n) C hmin).toOuterBoundaryCore
      (by
        change
          3 <=
            (rows (n := n) C hmin).faceBoundary.boundaryLength
              (rows (n := n) C hmin).outerFace
        exact hlen C hmin)

theorem nonempty_minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows_of_jordanSourceRows_with_length
    (rows : MinimalFailureJordanSourceRows)
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <=
            (rows C hmin).faceBoundary.boundaryLength
              (rows C hmin).outerFace) :
    Nonempty MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  Nonempty.intro
    (minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfJordanSourceRowsWithLength
      rows hlen)

/-- W31 selected face/enclosure rows close the exact actual topology target
once the selected boundary length is separately known to be nondegenerate.
This projects the actual `ExactActualTopologyFields` row from the W31 source;
the nondegenerate length row is the precise extra fact not present in the
plain enclosure source. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_w31JordanSourceRows_with_length
    (rows : MinimalFailureJordanSourceRows)
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <=
            (rows C hmin).faceBoundary.boundaryLength
              (rows C hmin).outerFace) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  exact
    minimalFailureExactActualTopologyFieldsTarget_of_extractedSimpleCyclicOuterBoundaryEnclosureRows
      (minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfJordanSourceRowsWithLength
        rows hlen)

/-- W28 source-with-length rows already contain the selected face, enclosure,
and nondegenerate length in one dependent package, hence project directly to
`ExactActualTopologyFields`. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_outerBoundaryCoreSourceWithLengthRows
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  intro n C hmin
  exact
    OuterBoundaryExistenceConcrete.exactActualTopologyFields_of_outerBoundaryCoreWithLength
      (C := C) (rows C hmin).source.core
      (rows C hmin).outerCycle_length_ge_three

/-- Project W28 source-with-length rows into the exact S2 extracted
boundary/enclosure row package. -/
def minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfOuterBoundaryCoreSourceWithLengthRows
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows) :
    MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  fun {n} C hmin =>
    OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows.ofOuterBoundaryCoreWithLength
      (rows (n := n) C hmin).source.core
      (rows (n := n) C hmin).outerCycle_length_ge_three

theorem nonempty_minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows_of_outerBoundaryCoreSourceWithLengthRows
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows) :
    Nonempty MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  Nonempty.intro
    (minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfOuterBoundaryCoreSourceWithLengthRows
      rows)

/-- Strong actual-cycle rows are already the exact S2 extracted
boundary/enclosure rows after forgetting the wrapper. -/
def minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfActualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  fun {n} C hmin =>
    OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows.ofActualOuterBoundaryCycleData
      (rows (n := n) C hmin)

/-- Strong actual outer-boundary-cycle rows directly close the live exact S2
target by projecting their core and enclosure to `ExactActualTopologyFields`. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_actualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  fun {n} C hmin =>
    OuterBoundaryExistenceConcrete.exactActualTopologyFields_of_actualOuterBoundaryCycleData
      (C := C) (rows (n := n) C hmin)

/-- Simple cyclic boundary/enclosure rows are the shortest honest S2 source
once supplied for each minimal failure: they project to strong actual
outer-boundary-cycle data, and then to the exact actual topology fields. -/
def minimalFailureActualOuterBoundaryCycleDataRowsOfSimpleCyclicOuterBoundaryEnclosureRows
    (rows : MinimalFailureSimpleCyclicOuterBoundaryEnclosureRows) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  fun {n} C hmin =>
    (rows (n := n) C hmin).toActualOuterBoundaryCycleData

theorem minimalFailureExactActualTopologyFieldsTarget_of_simpleCyclicOuterBoundaryEnclosureRows
    (rows : MinimalFailureSimpleCyclicOuterBoundaryEnclosureRows) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_actualOuterBoundaryCycleDataRows
    (minimalFailureActualOuterBoundaryCycleDataRowsOfSimpleCyclicOuterBoundaryEnclosureRows
      rows)

/-- Jordan outer-component rows are the precise S2 source package: they start
from an actual unit-distance graph cycle and attach enclosure predicates for
that same cycle. -/
def minimalFailureSimpleCyclicOuterBoundaryEnclosureRowsOfJordanOuterComponentSourceRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows) :
    MinimalFailureSimpleCyclicOuterBoundaryEnclosureRows :=
  JordanBoundaryConcrete.simpleCyclicOuterBoundaryEnclosureRowsOfJordanOuterComponentSourceRows
    rows

/-- Flexible Jordan outer-component rows project directly to the strong
actual outer-boundary-cycle rows used by W33.  This keeps the live S2 bridge
independent of the canonical girth cycle being the outer cycle. -/
def minimalFailureActualOuterBoundaryCycleDataRowsOfJordanOuterComponentSourceRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  minimalFailureActualOuterBoundaryCycleDataRowsOfSimpleCyclicOuterBoundaryEnclosureRows
    (minimalFailureSimpleCyclicOuterBoundaryEnclosureRowsOfJordanOuterComponentSourceRows
      rows)

/-- The flexible Jordan outer-component source supplies the remaining
actual-cycle target without using the synthetic extracted-cycle enclosure
shim. -/
theorem minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_jordanOuterComponentSourceRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  fun C hmin =>
    Nonempty.intro
      ((minimalFailureActualOuterBoundaryCycleDataRowsOfJordanOuterComponentSourceRows
        rows) C hmin)

/-- A supplied Jordan outer-component theorem closes the live exact S2 target
through the strong simple cyclic boundary/enclosure row path. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_jordanOuterComponentSourceRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_simpleCyclicOuterBoundaryEnclosureRows
    (minimalFailureSimpleCyclicOuterBoundaryEnclosureRowsOfJordanOuterComponentSourceRows
      rows)

/-- Nonempty flexible Jordan outer-component source rows give the exact W33 S2
target.  This is the downstream-ready form of the live S2 bridge. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_nonempty_jordanOuterComponentSourceRows
    (h :
      Nonempty
        JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  cases h with
  | intro rows =>
      exact
        minimalFailureExactActualTopologyFieldsTarget_of_jordanOuterComponentSourceRows
          rows

/-- Nonempty flexible Jordan outer-component source rows also give W33 the
actual outer-boundary-cycle row family explicitly. -/
theorem nonempty_minimalFailureActualOuterBoundaryCycleDataRows_of_jordanOuterComponentSourceRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows) :
    Nonempty MinimalFailureActualOuterBoundaryCycleDataRows :=
  Nonempty.intro
    (minimalFailureActualOuterBoundaryCycleDataRowsOfJordanOuterComponentSourceRows
      rows)

/-- Chosen Jordan outer-component rows are the flexible positive S2 source:
the cycle may be chosen per configuration, but the enclosure predicates still
belong to that same chosen cycle. -/
def minimalFailureJordanOuterComponentSourceRowsOfChosenJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows) :
    JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows :=
  JordanBoundaryConcrete.minimalFailureJordanOuterComponentSourceRowsOfChosen
    rows

/-- Chosen-cycle rows project to the strong simple cyclic boundary/enclosure
rows without passing through the synthetic extracted-cycle enclosure. -/
def minimalFailureSimpleCyclicOuterBoundaryEnclosureRowsOfChosenJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows) :
    MinimalFailureSimpleCyclicOuterBoundaryEnclosureRows :=
  JordanBoundaryConcrete.simpleCyclicOuterBoundaryEnclosureRowsOfChosenJordanOuterComponentRows
    rows

/-- Chosen-cycle rows project all the way to the strong actual
outer-boundary-cycle rows, preserving the real enclosure attached to the
chosen cycle. -/
def minimalFailureActualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  JordanBoundaryConcrete.actualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows
    rows

/-- Chosen-cycle rows give W33 the actual outer-boundary-cycle row family
explicitly. -/
theorem nonempty_minimalFailureActualOuterBoundaryCycleDataRows_of_chosenJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows) :
    Nonempty MinimalFailureActualOuterBoundaryCycleDataRows :=
  Nonempty.intro
    (minimalFailureActualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows
      rows)

/-- A chosen Jordan outer-component row family supplies the remaining
actual-cycle target directly through its real enclosure data. -/
theorem minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_chosenJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  fun C hmin =>
    Nonempty.intro
      ((minimalFailureActualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows
        rows) C hmin)

/-- Chosen Jordan outer-component rows close the live exact S2 target through
strong actual outer-boundary-cycle data, not through the synthetic extracted
cycle shim. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_chosenJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_actualOuterBoundaryCycleDataRows
    (minimalFailureActualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows
      rows)

/-- Nonempty chosen-cycle rows are enough to close the exact W32 S2 target. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_nonempty_chosenJordanOuterComponentRows
    (h :
      Nonempty
        JordanBoundaryConcrete.MinimalFailureChosenJordanOuterComponentRows) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  cases h with
  | intro rows =>
      exact
        minimalFailureExactActualTopologyFieldsTarget_of_chosenJordanOuterComponentRows
          rows

/-- The finite planar straight-line outer-component theorem feeds the live S2
exact target through the chosen-row constructor, with no-cut rows kept as the
graph-side minimal-failure input. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (outerComponent :
      JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarStraightLineOuterComponentTheorem)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_chosenJordanOuterComponentRows
    (JordanTopologyFactsConcrete.MinimalFailureTopology.minimalFailureChosenRows_of_finitePlanarOuterComponentTheorem
      outerComponent noCutRows)

/-- Exterior-frontier rows with off-orbit vertices outside the exterior close
the live S2 exact topology target through the chosen outer-component theorem. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_exterior_frontier_not_mem
    (frontierRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
          C ->
          Exists fun R :
            JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem
              C =>
            Exists fun O :
              JordanTopologyFactsConcrete.MinimalFailureTopology.FaceDartOrbit
                C R =>
              Exists fun exterior : Set PlanarInterface.Point =>
                (forall v : Fin n,
                  (¬ Exists fun k : Fin O.boundary.length =>
                    O.boundary.vertex k = v) ->
                    (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∉
                      exterior) /\
                (forall v : Fin n,
                  (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                      frontier exterior <->
                    Exists fun k : Fin O.boundary.length =>
                      O.boundary.vertex k = v))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_exterior_frontier_not_mem
      frontierRows)
    noCutRows

/-- The current sharp S2 source surface: once the constructed unbounded
component of the finite drawing complement has a simple unit-distance frontier
cycle on graph vertices, the live exact topology target follows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedExteriorFrontierCycleRows
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
        rows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current S2 actual-sector source surface.

The source proof must still construct the actual exterior boundary cycle,
prove exact graph-vertex frontier coverage for that cycle, and provide the
same-boundary actual exterior-sector rows.  This theorem only records the
short checked route from that source package to the existing W32 target. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_actualExteriorSectorInputSourceRows
    (source :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                  frontier
                    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                      C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            _root_.Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualExteriorSectorInputSourceRows
                inputs B))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_unboundedExteriorFrontierCycleRows_family_of_actualExteriorSectorInputSourceRows
      source)
    noCutRows

set_option linter.style.longLine false in
/-- Actual-sector source family after the checked q18 lowerings.

The displayed leaves are exactly the ones not erased by q16/q17/q18 here:
the q18 relative-clopen topology source, actual local-sector rows, one-step
geometric face-successor frontier propagation, and repeated-tail/orientation
callbacks for the selected raw orbit.  The proof first uses the q16/q15
topology route to get component rows, then q17 and q18 to build the raw-orbit
package consumed by `S2_q3_exterior_boundary_source_assembler`; the final
actual-sector package is produced through
`actualExteriorSectorInputSourceRows_of_inputs`, not a W32 facade. -/
noncomputable def
    actualExteriorSectorInputSourceRows_family_of_q18_remaining_leaves_20260522
    (nontrivial_side :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
    (faceSucc_preserves_openSegment_frontier :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        (d : UnitDistanceDart C),
          (forall q : PlanarInterface.Point,
            PlanarInterface.InOpenSegment q
              ((JordanTopologyFactsConcrete.canonicalGraph C).point d.tail)
              ((JordanTopologyFactsConcrete.canonicalGraph C).point d.head) ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
          forall q : PlanarInterface.Point,
            PlanarInterface.InOpenSegment q
              ((JordanTopologyFactsConcrete.canonicalGraph C).point
                ((GeometricRotationSystem.geometricUnitDistanceRotationSystem C).faceSucc d).tail)
              ((JordanTopologyFactsConcrete.canonicalGraph C).point
                ((GeometricRotationSystem.geometricUnitDistanceRotationSystem C).faceSucc d).head) ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (repeated_tail_rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        {e : PlanarInterface.Edge m} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
          start.head = e.2 ->
          forall O :
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).RawFaceSuccOrbit
              start,
            forall {i j : Fin O.period},
              i ≠ j ->
              (O.dart i).tail = (O.dart j).tail ->
                RepeatedExteriorBoundarySeparationRows C
                  (fun k : Fin O.period => (O.dart k).tail) i j)
    (raw_orientation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        {e : PlanarInterface.Edge m} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
          start.head = e.2 ->
          forall O :
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).RawFaceSuccOrbit
              start,
            forall k : Fin O.period,
              GeometricRotationSystem.graphDartArg
                  (GeometricRotationSystem.canonicalGeometricGraph C)
                  (O.dart k).tail
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
                GeometricRotationSystem.graphDartArg
                  (GeometricRotationSystem.canonicalGeometricGraph C)
                  (O.dart k).tail
                  (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  S2_q3_exterior_boundary_source_assembler
    (fun C inputs => by
      classical
      let topologyRows :=
        S2_q15_finiteDrawing_noClosed_noOpen_componentTopology_family_of_noCompactConnectedKCrossing_localSectorRows_20260522
          (S2_q16_noCompactConnectedKCrossing_source_of_nontrivialRelativeClopenKSide_20260522
            nontrivial_side)
          localSectorRows
      let componentRows :
          UnboundedExteriorFrontierComponentTopologySourceRows inputs :=
        (topologyRows.2.2 C inputs).2
      let localRows :
          forall a : {v : Fin _ // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        localSectorRows C inputs
      let dart_edge_openSegment_frontier :
          forall {e : PlanarInterface.Edge _} {p : PlanarInterface.Point}
              {start : UnitDistanceDart C},
            UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
              start.tail = e.1 ->
                start.head = e.2 ->
                  forall O :
                    (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).RawFaceSuccOrbit
                      start,
                    forall k : Fin O.period,
                      forall q : PlanarInterface.Point,
                        PlanarInterface.InOpenSegment q
                          ((JordanTopologyFactsConcrete.canonicalGraph C).point
                            (O.dart k).tail)
                          ((JordanTopologyFactsConcrete.canonicalGraph C).point
                            (O.dart k).head) ->
                        q ∈ frontier
                          (unboundedExteriorComponentRows C inputs).exterior := by
        intro e p start edgeRows htail hhead O
        exact
          S2_q18_dart_edge_openSegment_frontier_of_selectedEdgeLocalRows_faceSuccPropagation
            (C := C) (inputs := inputs) edgeRows htail hhead O
            (faceSucc_preserves_openSegment_frontier C inputs)
      let rawSource :=
          S2_q17_selected_seed_rawCoverage_boundaryFreeLocalRawOrbitSourceRows_of_inputs_componentTopology_localSectorRows_dartEdgeFrontier_20260522
            (C := C) inputs componentRows localRows
            dart_edge_openSegment_frontier
      let seed := Classical.choose rawSource
      let rawSource₁ := Classical.choose_spec rawSource
      let e := Classical.choose rawSource₁
      let rawSource₂ := Classical.choose_spec rawSource₁
      let p := Classical.choose rawSource₂
      let rawSource₃ := Classical.choose_spec rawSource₂
      let start := Classical.choose rawSource₃
      let rawSource₄ := Classical.choose_spec rawSource₃
      let edgeRows :
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p :=
        rawSource₄.2.1
      let htail : start.tail = e.1 := rawSource₄.2.2.1
      let hhead : start.head = e.2 := rawSource₄.2.2.2.1
      let orbitSource := rawSource₄.2.2.2.2
      let O := Classical.choose orbitSource
      let dartFrontier :
          forall k : Fin O.period,
            forall q : PlanarInterface.Point,
              PlanarInterface.InOpenSegment q
                ((JordanTopologyFactsConcrete.canonicalGraph C).point
                  (O.dart k).tail)
                ((JordanTopologyFactsConcrete.canonicalGraph C).point
                  (O.dart k).head) ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior :=
        dart_edge_openSegment_frontier edgeRows htail hhead O
      refine
        ⟨localRows,
          unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
            inputs componentRows,
          start, O, dartFrontier, ?_, ?_⟩
      · intro i j hij htail_eq
        exact
          repeated_tail_rows C inputs edgeRows htail hhead O hij htail_eq
      · intro k
        exact
          raw_orientation C inputs edgeRows htail hhead O k)

set_option linter.style.longLine false in
/-- Actual-sector source family after the q19 topology/local lowerings.

Compared with `actualExteriorSectorInputSourceRows_family_of_q18_remaining_leaves_20260522`,
this erases the topology leaf to the whole-frontier no-subcontinuum obstruction
and the local-sector leaf to the r30 deleted-neighbour local-separation
primitive plus the matching selected angular/no-between row. -/
noncomputable def
    actualExteriorSectorInputSourceRows_family_of_q19_remaining_leaves_20260522
    (no_subcontinuum :
      PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction)
    (r30_source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs)
    (selected_angular_rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
              (C := C) (inputs := inputs) (r30_source C inputs))
    (faceSucc_preserves_openSegment_frontier :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        (d : UnitDistanceDart C),
          (forall q : PlanarInterface.Point,
            PlanarInterface.InOpenSegment q
              ((JordanTopologyFactsConcrete.canonicalGraph C).point d.tail)
              ((JordanTopologyFactsConcrete.canonicalGraph C).point d.head) ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
          forall q : PlanarInterface.Point,
            PlanarInterface.InOpenSegment q
              ((JordanTopologyFactsConcrete.canonicalGraph C).point
                ((GeometricRotationSystem.geometricUnitDistanceRotationSystem C).faceSucc d).tail)
              ((JordanTopologyFactsConcrete.canonicalGraph C).point
                ((GeometricRotationSystem.geometricUnitDistanceRotationSystem C).faceSucc d).head) ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (repeated_tail_rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        {e : PlanarInterface.Edge m} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
          start.head = e.2 ->
          forall O :
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).RawFaceSuccOrbit
              start,
            forall {i j : Fin O.period},
              i ≠ j ->
              (O.dart i).tail = (O.dart j).tail ->
                RepeatedExteriorBoundarySeparationRows C
                  (fun k : Fin O.period => (O.dart k).tail) i j)
    (raw_orientation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        {e : PlanarInterface.Edge m} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
          start.head = e.2 ->
          forall O :
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).RawFaceSuccOrbit
              start,
            forall k : Fin O.period,
              GeometricRotationSystem.graphDartArg
                  (GeometricRotationSystem.canonicalGeometricGraph C)
                  (O.dart k).tail
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
                GeometricRotationSystem.graphDartArg
                  (GeometricRotationSystem.canonicalGeometricGraph C)
                  (O.dart k).tail
                  (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  actualExteriorSectorInputSourceRows_family_of_q18_remaining_leaves_20260522
    (S2_q19_nontrivialRelativeClopenKSide_source_of_noSubcontinuumObstruction_20260522
      no_subcontinuum)
    (_root_.ErdosProblems1066.Swanepoel.S2CarrierLocalSource.S2_q19_localSectorRows_family_of_r30_selectedAngularNoBetweenRows
        r30_source selected_angular_rows)
    faceSucc_preserves_openSegment_frontier
    repeated_tail_rows
    raw_orientation

set_option linter.style.longLine false in
/-- Actual-sector source family after the q20 topology lowering.

This is the same source-facing spine as
`actualExteriorSectorInputSourceRows_family_of_q19_remaining_leaves_20260522`,
with the topology leaf lowered one step further to the same-`K`
Janiszewski point-between primitive.  The local, raw `faceSucc`,
repeated-tail, and orientation leaves stay unchanged and remain input-facing. -/
noncomputable def
    actualExteriorSectorInputSourceRows_family_of_q20_remaining_leaves_20260522
    (points_between :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween)
    (r30_source :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
            (C := C) inputs)
    (selected_angular_rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
              (C := C) (inputs := inputs) (r30_source C inputs))
    (faceSucc_preserves_openSegment_frontier :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        (d : UnitDistanceDart C),
          (forall q : PlanarInterface.Point,
            PlanarInterface.InOpenSegment q
              ((JordanTopologyFactsConcrete.canonicalGraph C).point d.tail)
              ((JordanTopologyFactsConcrete.canonicalGraph C).point d.head) ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior) ->
          forall q : PlanarInterface.Point,
            PlanarInterface.InOpenSegment q
              ((JordanTopologyFactsConcrete.canonicalGraph C).point
                ((GeometricRotationSystem.geometricUnitDistanceRotationSystem C).faceSucc d).tail)
              ((JordanTopologyFactsConcrete.canonicalGraph C).point
                ((GeometricRotationSystem.geometricUnitDistanceRotationSystem C).faceSucc d).head) ->
            q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior)
    (repeated_tail_rows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        {e : PlanarInterface.Edge m} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
          start.head = e.2 ->
          forall O :
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).RawFaceSuccOrbit
              start,
            forall {i j : Fin O.period},
              i ≠ j ->
              (O.dart i).tail = (O.dart j).tail ->
                RepeatedExteriorBoundarySeparationRows C
                  (fun k : Fin O.period => (O.dart k).tail) i j)
    (raw_orientation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C)
        {e : PlanarInterface.Edge m} {p : PlanarInterface.Point}
        {start : UnitDistanceDart C},
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
          start.head = e.2 ->
          forall O :
            (GeometricRotationSystem.geometricUnitDistanceRotationSystem C).RawFaceSuccOrbit
              start,
            forall k : Fin O.period,
              GeometricRotationSystem.graphDartArg
                  (GeometricRotationSystem.canonicalGeometricGraph C)
                  (O.dart k).tail
                  (O.dart (PlanarInterface.cyclicPred O.period_pos k)).tail <
                GeometricRotationSystem.graphDartArg
                  (GeometricRotationSystem.canonicalGeometricGraph C)
                  (O.dart k).tail
                  (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  actualExteriorSectorInputSourceRows_family_of_q19_remaining_leaves_20260522
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q20_no_subcontinuum_obstruction_source_of_kComponentPointsBetween_20260522
      points_between)
    r30_source
    selected_angular_rows
    faceSucc_preserves_openSegment_frontier
    repeated_tail_rows
    raw_orientation

set_option linter.style.longLine false in
/-- Claim `S2-q22-source-composer`.

Actual exterior-sector source family after the checked q21 cyclic-successor
cut lowering.  This is only the eraser/composer layer: q21 supplies the honest
face-dart exterior carrier plus same-boundary angular rows from component
topology, selected neighbour geometry, selected incident germs, strict selected
successor order, cyclic-successor deleted-tail cut partitions on the same
selected raw orbit, and selected raw orientation rows.  The final step is the
existing non-W32 actual-sector eraser from the face-dart/angular package. -/
noncomputable def
    actualExteriorSectorInputSourceRows_family_of_q21_remaining_leaves_20260522
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (strictSuccessorOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (selectedNeighborGeometricCarrierLeft
              (C := C) (inputs := inputs) selectedRows.toGeometricSelectionInputSource)
            (selectedNeighborGeometricCarrierRight
              (C := C) (inputs := inputs) selectedRows.toGeometricSelectionInputSource))
    (cyclicSuccCutPartitions :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
            (S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              (strictSuccessorOrder C inputs)))
    (rawOrientationRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          SelectedRawOrbitOrientationRows
            (S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              (strictSuccessorOrder C inputs))) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  actualExteriorSectorInputSourceRows_of_faceDartOrbitExteriorCarrierRows_family
    (S2_q21_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentInput_geometricSelection_incidentGerm_strictSuccessor_cyclicSuccCutPartitions_orientation
      componentTopology geometricSelection incidentGermFrontierEdgeRows
      strictSuccessorOrder cyclicSuccCutPartitions rawOrientationRows)

set_option linter.style.longLine false in
/-- Claim `S2-q23-source-composer`, q22 reduced actual-sector source family.

This is the current smallest actual-sector producer in this file: component
topology, selected neighbour geometry, and selected incident germs are combined
with actual selected `faceSucc` angle rows, cyclic-successor deleted-tail
nonreachability, and raw `faceSucc` turn rows.  The theorem only composes
checked source reducers and does not add a W-facing facade or synthetic
enclosure row. -/
noncomputable def
    actualExteriorSectorInputSourceRows_family_of_q22_remaining_leaves_20260522
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (cyclicSuccDeletedTail :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            selectedRawRows)
    (rawFaceSuccTurnRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitGeometricFaceSuccTurnRows selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) :=
  actualExteriorSectorInputSourceRows_of_faceDartOrbitExteriorCarrierRows_family
    (S2_q22_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn
      componentTopology geometricSelection incidentGermFrontierEdgeRows
      angleRows cyclicSuccDeletedTail rawFaceSuccTurnRows)

set_option linter.style.longLine false in
/-- Cycle-row family eraser for the q22 reduced actual-sector source. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_family_of_q22_remaining_leaves_20260522
    (componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (cyclicSuccDeletedTail :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            selectedRawRows)
    (rawFaceSuccTurnRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitGeometricFaceSuccTurnRows selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_family_of_actualExteriorSectorInputSourceRows
    (actualExteriorSectorInputSourceRows_family_of_q22_remaining_leaves_20260522
      componentTopology geometricSelection incidentGermFrontierEdgeRows
      angleRows cyclicSuccDeletedTail rawFaceSuccTurnRows)

set_option linter.style.longLine false in
/-- Claim `S2-q23-source-composer`, topology-collapsed q22 actual-sector
source family.

The component-topology premise in the q22 actual-sector producer is sourced
from the Janiszewski relative-clopen boundary-bumping row and the same selected
local incident-germ rows used by the carrier source.  This removes a separate
component-topology family premise while keeping the remaining leaves on the
actual selected exterior face-successor walk. -/
noncomputable def
    actualExteriorSectorInputSourceRows_family_of_boundaryBumping_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn_20260522q23
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (cyclicSuccDeletedTail :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        S2LocalTwoGermAssembly.localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          geometricSelection
      let outside_accumulation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
                C inputs :=
        S2_outsideAccumulationSource_family_of_localSectorRows_20260522
          localSectorRows
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
          boundary_bumping outside_accumulation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            selectedRawRows)
    (rawFaceSuccTurnRows :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        S2LocalTwoGermAssembly.localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          geometricSelection
      let outside_accumulation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
                C inputs :=
        S2_outsideAccumulationSource_family_of_localSectorRows_20260522
          localSectorRows
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
          boundary_bumping outside_accumulation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitGeometricFaceSuccTurnRows selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
          (forall v : Fin m,
            (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ↔
              Exists fun k : Fin B.length => B.vertex k = v) ∧
          _root_.Nonempty (ActualExteriorSectorInputSourceRows inputs B) := by
  let localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
    S2LocalTwoGermAssembly.localSectorRowsFamily_of_geometricSelection_localIncident_20260520
      geometricSelection
  let outside_accumulation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
            C inputs :=
    S2_outsideAccumulationSource_family_of_localSectorRows_20260522
      localSectorRows
  let componentTopology :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
      boundary_bumping outside_accumulation
  exact
    fun {m} C inputs =>
      actualExteriorSectorInputSourceRows_family_of_q22_remaining_leaves_20260522
        componentTopology geometricSelection incidentGermFrontierEdgeRows
        angleRows
        (by
          intro m C inputs
          exact cyclicSuccDeletedTail C inputs)
        (by
          intro m C inputs
          exact rawFaceSuccTurnRows C inputs)
        C inputs

set_option linter.style.longLine false in
/-- Cycle-row eraser for the topology-collapsed q23 actual-sector source. -/
noncomputable def
    unboundedExteriorFrontierCycleRows_family_of_boundaryBumping_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn_20260522q23
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (cyclicSuccDeletedTail :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        S2LocalTwoGermAssembly.localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          geometricSelection
      let outside_accumulation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
                C inputs :=
        S2_outsideAccumulationSource_family_of_localSectorRows_20260522
          localSectorRows
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
          boundary_bumping outside_accumulation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            selectedRawRows)
    (rawFaceSuccTurnRows :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        S2LocalTwoGermAssembly.localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          geometricSelection
      let outside_accumulation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
                C inputs :=
        S2_outsideAccumulationSource_family_of_localSectorRows_20260522
          localSectorRows
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
          boundary_bumping outside_accumulation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitGeometricFaceSuccTurnRows selectedRawRows) :
    forall {m : Nat} (C : _root_.UDConfig m)
      (inputs : FinitePlanarOuterComponentInputs C),
        UnboundedExteriorFrontierCycleRows C inputs :=
  S2_unboundedExteriorFrontierCycleRows_family_of_actualExteriorSectorInputSourceRows
    (actualExteriorSectorInputSourceRows_family_of_boundaryBumping_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn_20260522q23
      boundary_bumping geometricSelection incidentGermFrontierEdgeRows
      angleRows cyclicSuccDeletedTail rawFaceSuccTurnRows)

set_option linter.style.longLine false in
/-- W32 target from the topology-collapsed q23 actual-sector source. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_boundaryBumping_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn_20260522q23
    (boundary_bumping :
      PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (incidentGermFrontierEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (angleRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
            inputs selectedRows)
    (cyclicSuccDeletedTail :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        S2LocalTwoGermAssembly.localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          geometricSelection
      let outside_accumulation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
                C inputs :=
        S2_outsideAccumulationSource_family_of_localSectorRows_20260522
          localSectorRows
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
          boundary_bumping outside_accumulation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
            selectedRawRows)
    (rawFaceSuccTurnRows :
      let localSectorRows :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
                UnboundedFrontierCarrierLocalSectorRowsAt inputs a :=
        S2LocalTwoGermAssembly.localSectorRowsFamily_of_geometricSelection_localIncident_20260520
          geometricSelection
      let outside_accumulation :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier
                C inputs :=
        S2_outsideAccumulationSource_family_of_localSectorRows_20260522
          localSectorRows
      let componentTopology :
          forall {m : Nat} (C : _root_.UDConfig m)
            (inputs : FinitePlanarOuterComponentInputs C),
              UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs :=
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_q23_component_topology_input_source_family_of_janiszewskiBoundaryBumping_outsideAccumulation_20260522
          boundary_bumping outside_accumulation
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs : FinitePlanarOuterComponentInputs C),
          let selectedRows :
              S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
                inputs :=
            S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
              (C := C) (inputs := inputs) (geometricSelection C inputs)
          let strictSuccessorOrder :
              RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
                inputs
                (selectedNeighborGeometricCarrierLeft
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource)
                (selectedNeighborGeometricCarrierRight
                  (C := C) (inputs := inputs)
                  selectedRows.toGeometricSelectionInputSource) :=
            S2_selected_faceSucc_local_strict_order_source_of_selectedActualCarrierFaceSuccAngles
              (C := C) (inputs := inputs) (geometricSelection C inputs)
              (angleRows C inputs)
          let selectedRawRows : SelectedRawTailCoverageSourceRows inputs :=
            S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
              (C := C) (inputs := inputs)
              (componentTopology C inputs) (geometricSelection C inputs)
              (incidentGermFrontierEdgeRows C inputs)
              strictSuccessorOrder
          SelectedRawOrbitGeometricFaceSuccTurnRows selectedRawRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (unboundedExteriorFrontierCycleRows_family_of_boundaryBumping_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn_20260522q23
      boundary_bumping geometricSelection incidentGermFrontierEdgeRows
      angleRows cyclicSuccDeletedTail rawFaceSuccTurnRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the CT selected raw-orbit endgame route.

The remaining S2 source obligations are displayed as the connected raw-orbit
package, selected repeated-tail cut partitions on the internally selected
raw orbit, and selected raw predecessor/successor orientation rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260520
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows
            inputs)
    (cut_partitions :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitRepeatedTailCutPartitions
            selectedRows)
    (raw_orientation :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitOrientationRows
            selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260520
      rows cut_partitions raw_orientation)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current selected raw-orbit endgame with the
orientation row reduced to genuine geometric angular-neighbour selection.

The remaining S2 source obligations are the connected raw-orbit package,
selected repeated-tail exterior cut witnesses for the internally selected raw
orbit, and the concrete nonwrap neighbour-selection rows in the sorted
`geometricOutgoingDartList`. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricAngularNeighborSelection_20260520
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows
            inputs)
    (deleted_tail_witnesses :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          forall {i j : Fin selectedRows.O.period},
            i ≠ j ->
            (selectedRows.O.dart i).tail = (selectedRows.O.dart j).tail ->
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2RepeatedTailExteriorCutWitnessSource
                (inputs := inputs) selectedRows.O i j)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitGeometricAngularNeighborSelectionRows
            selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricAngularNeighborSelection_20260520
      rows deleted_tail_witnesses selectionRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for claim
`S2-agent-20260520-unconditional-cycle-composer`.

This is the direct boundary-sector version of the connected raw-orbit route:
the internally selected raw orbit is consumed with repeated-tail separation
rows and selected raw predecessor/successor orientation rows to produce
`UnboundedExteriorFrontierCycleRows`, then the existing W32 handoff consumes
those rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation_20260520
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows
            inputs)
    (repeated_tail_rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          forall {i j : Fin selectedRows.O.period},
            i ≠ j ->
            (selectedRows.O.dart i).tail = (selectedRows.O.dart j).tail ->
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RepeatedExteriorBoundarySeparationRows
                C
                (fun k : Fin selectedRows.O.period =>
                  (selectedRows.O.dart k).tail) i j)
    (raw_orientation :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitOrientationRows
            selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation_20260520
      rows repeated_tail_rows raw_orientation)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the deleted-tail-witness version of the current raw-orbit
boundary-sector route.

This keeps the same direct `UnboundedExteriorFrontierCycleRows` handoff as
`minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation_20260520`,
but exposes the repeated-tail source in the primitive
`S2RepeatedTailExteriorCutWitnessSource` form. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_rawOrientation_20260520
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows
            inputs)
    (deleted_tail_witnesses :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          forall {i j : Fin selectedRows.O.period},
            i ≠ j ->
            (selectedRows.O.dart i).tail = (selectedRows.O.dart j).tail ->
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2RepeatedTailExteriorCutWitnessSource
                (inputs := inputs) selectedRows.O i j)
    (raw_orientation :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitOrientationRows
            selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_rawOrientation_20260520
      rows deleted_tail_witnesses raw_orientation)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the deleted-tail-witness route with orientation reduced
to concrete nonwrap successor rows in the selected raw orbit's geometric
outgoing-dart lists. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricSuccessorNonwrap_20260520
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows
            inputs)
    (deleted_tail_witnesses :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          forall {i j : Fin selectedRows.O.period},
            i ≠ j ->
            (selectedRows.O.dart i).tail = (selectedRows.O.dart j).tail ->
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2RepeatedTailExteriorCutWitnessSource
                (inputs := inputs) selectedRows.O i j)
    (successorRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let selectedRows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
              (C := C) (inputs := inputs) (rows C inputs)
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitGeometricSuccessorNonwrapRows
            selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricSuccessorNonwrap_20260520
      rows deleted_tail_witnesses successorRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the preferred incident-edge primitive route.

This keeps endpoint closure selected-edge gated: the adjacent endpoint source
must first identify the edge as an actual `unboundedFrontierEdgeSet` edge, and
the closed-segment endpoint closure is derived inside the S2 route. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_incidentEdgePrimitiveSources_20260520af
    (localAngularSource :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a :
              {v : Fin n //
                v ∈ unboundedFrontierVertexSet C inputs},
            Exists fun left : Fin n =>
              Exists fun right : Fin n =>
                ((a.1, left) ∈ unboundedFrontierEdgeSet C inputs ∨
                  (left, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
                ((a.1, right) ∈ unboundedFrontierEdgeSet C inputs ∨
                  (right, a.1) ∈ unboundedFrontierEdgeSet C inputs) ∧
                left ≠ right ∧
                BoundaryFreeGraphVertexAngularNoBetweenRows
                  C a.1 left right ∧
                forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
                  q ∈ Metric.ball
                      ((JordanTopologyFactsConcrete.canonicalGraph C).point
                        a.1)
                      ε ->
                    q ∈
                        frontier
                          (unboundedExteriorComponentRows C inputs).exterior ->
                      (JordanTopologyFactsConcrete.canonicalGraph C).Adj
                          a.1 x ->
                        q ∈
                            _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.vertexIncidentGermW3
                              C a.1 x ε ->
                          q ≠
                              ((JordanTopologyFactsConcrete.canonicalGraph C).point
                                a.1) ->
                            x ≠ left ->
                              x ≠ right ->
                                BoundaryFreeGraphVertexAngularBetween
                                  C a.1 left right x)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (componentTopologyRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (successorSource :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_incidentEdgePrimitiveSources_20260520af
      localAngularSource incident_edge componentTopologyRows successorSource)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for claim `S2-dyn-20260520-input-premise-composer`.

This is only the downstream eraser from the checked S2 cycle-row composer:
boundary-free input reduction, planar-continuum frontier preconnectedness,
and local-angular head-between rows produce
`UnboundedExteriorFrontierCycleRows`; the existing W32 theorem then consumes
those rows together with the explicit minimal-failure no-cut family. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_inputPremiseComposer_20260520
    (boundaryFree :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeInputSourceReduction
            inputs)
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierPreconnected)
    (localAngularSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
            inputs)
    (headBetween :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitIteratedFaceSuccHeadBetweenLocalAngularNoOrbitSource
            inputs (localAngularSource C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_inputPremiseComposer_20260520
      boundaryFree frontier_preconnected localAngularSource headBetween)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current shortest CO S2 source surface.

The S2 side first builds `UnboundedExteriorFrontierCycleRows` from raw
face-successor orbit source rows, pointwise local two-germ rows, adjacent
endpoint selected-edge incidence, and selected successor-edge propagation.
W32 then consumes those cycle rows through the existing finite outer-component
theorem bridge, with the minimal-failure no-cut rows still explicit. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_rawFaceSuccOrbitSourceRows_localTwoGerm_incident_selectedSuccessorEdge_20260520co
    (source :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun R :
            JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem
              C =>
            Exists fun start :
              JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceDart
                C =>
              Exists fun O :
                JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem.RawFaceSuccOrbit
                  R start =>
                Nonempty
                  (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawFaceSuccOrbitSourceRows
                    (inputs := inputs) O))
    (localTwoGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalTwoGermRowsAt
              inputs a)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (selectedSuccessorEdge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_rawFaceSuccOrbitSourceRows_localTwoGerm_incident_selectedSuccessorEdge_20260520co
      source localTwoGermRows incident_edge selectedSuccessorEdge)
    noCutRows

/-- W32 S2 target from actual unbounded-exterior boundary-cycle rows.

This is the shortest current eraser for the source theorem: it still requires
the honest construction of `ActualBoundaryCycleFrontierEquivalenceRows` for
each finite planar input package. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_actualBoundaryCycleFrontierEquivalenceRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualBoundaryCycleFrontierEquivalenceRows
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_actualBoundaryCycleFrontierEquivalenceRows
      rows)
    noCutRows

/-- W32 S2 target from the current edge-chain plus boundary-free local
two-germ source surface.

This is the compact consumer for the non-circular carrier route: the source
rows prove connectedness of the actual unbounded-frontier edge carrier and
degree two of the actual frontier carrier graph, then the checked S2 eraser
produces the exact outer-boundary topology target. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
    (edge_segment_chain :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeCarrierSegmentChainConnected
            inputs)
    (source :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            Exists fun left : Fin n =>
              Exists fun right : Fin n =>
                ((a.1, left) ∈
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                      C inputs ∨
                  (left, a.1) ∈
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                      C inputs) ∧
                ((a.1, right) ∈
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                      C inputs ∨
                  (right, a.1) ∈
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                      C inputs) ∧
                left ≠ right ∧
                forall (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
                  q ∈ Metric.ball
                      ((_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1)
                      ε ->
                    q ∈ frontier
                        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                          C inputs).exterior ->
                      (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
                        q ∈
                            _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.vertexIncidentGermW3
                              C a.1 x ε ->
                          q ≠
                              (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point
                                a.1 ->
                            x ≠ left ->
                              x ≠ right ->
                                False)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_unboundedExteriorFrontierCycleRows_of_edgeChain_boundaryFree_noThirdGerm_fixedSide
          inputs (edge_segment_chain C inputs) (source C inputs))
    noCutRows

/-- W32 S2 target from concrete carrier connectedness plus the boundary-free
local two-germ/no-third-germ source.

This is the compact workboard endpoint for the current carrier route: the
selected-edge chain is derived from graph connectedness of the actual
unbounded-frontier carrier, and the local source supplies degree two through
the checked local-sector eraser. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_carrierGraphConnected_boundaryFreeSource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
              C inputs).Connected ∧
            Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeNoThirdGermSource
                inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_carrierGraphConnected_boundaryFreeSource
      rows)
    noCutRows

/-- W32 S2 target from frontier preconnectedness of the actual unbounded
exterior component plus the boundary-free local two-germ/no-third-germ source.
-/
theorem minimalFailureExactActualTopologyFieldsTarget_of_frontierPreconnected_boundaryFreeSource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          IsPreconnected
              (frontier
                (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                  C inputs).exterior) ∧
            Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeNoThirdGermSource
                inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_frontierPreconnected_boundaryFreeSource
      rows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the actual exterior-sector package plus the remaining
closed-segment residual rows.

This is the displayed consumer for the current actual-sector route: the
actual-sector package supplies pointwise local sectors, closed-segment
relative openness supplies endpoint incidence, frontier preconnectedness gives
the selected edge chain, and the raw iterated-successor row supplies the
geometric orbit propagation. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_actualSector_closedSegmentSources_20260520bq
    (actualSector :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            _root_.Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualExteriorSectorInputSourceRows
                inputs B))
    (closure_locus_relative_open :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.AdjacentFrontierEndpointsClosedSegmentClosureLocusRelativeOpenSource
            C inputs)
    (frontier_preconnected :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          IsPreconnected
            (frontier
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                C inputs).exterior))
    (successorSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_actualSector_closedSegmentSources_20260520bq
      actualSector closure_locus_relative_open frontier_preconnected
      successorSource)
    noCutRows

/-- W32 S2 target from honest exterior-frontier carrier rows alone.

The carrier package already includes connectedness, two-regularity, exact
frontier-vertex coverage, and actual edge-frontier rows, so no separate
boundary-free local source is needed on this route. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_exteriorFrontierCarrierRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (ExteriorFrontierCarrierRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_exteriorFrontierCarrierRows
      rows)
    noCutRows

/-- W32 S2 target from the current non-circular concrete-carrier route:
actual exterior-frontier preconnectedness plus pointwise local-sector rows
first build the honest exterior-frontier carrier, then erase it through the
checked finite planar outer-component theorem. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_frontierPreconnected_localSectorRows
    (frontier_preconnected :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          IsPreconnected
              (frontier
                (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                  C inputs).exterior))
    (localSectorRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
            (forall a :
              {v : Fin n // v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
                  inputs a))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_exteriorFrontierCarrierRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_exterior_carrier_source_20260520t
        inputs (frontier_preconnected C inputs) (localSectorRows C inputs))
    noCutRows

/-- W32 S2 target from the planar-continuum no-closed-separation theorem plus
the honest local-radius no-third-germ source.

This is the non-circular decomposition currently below S2: the global
topology row gives preconnectedness of the actual unbounded exterior frontier,
while the local source gives the two selected carrier edges and local
no-third-germ row at each frontier vertex. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_planarContinuumNoClosedSeparation_localNoThirdGermSource
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierNoClosedSeparation)
    (localSourceRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeLocalNoThirdGermSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_frontierPreconnected_localSectorRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_planar_continuum_frontier_no_closed_separation
        (C := C) inputs frontier_noClosedSeparation)
    (fun C inputs =>
      (localSourceRows C inputs).toLocalSectorRows)
    noCutRows

/-- W32 S2 target from the seeded raw-orbit one-step source package.

This is the current narrowest displayed route: boundary-free local two-germ
rows, actual-frontier preconnectedness, and the exterior-oriented
start/successor `faceSucc` row select the geometric raw face-successor orbit
and erase it through the checked S2 reducers. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_frontierPreconnectedStepSourceRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeFrontierPreconnectedStepSourceRows
              inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_frontierPreconnectedStepSourceRows
      rows)
    noCutRows

/-- W32 S2 target from the orientation-aware seeded raw-orbit source package.

This is the corrected selected-orbit variant of the one-step route: it follows
only iterates of the exterior-oriented start dart instead of demanding a
global orientation-free `faceSucc` preservation theorem. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_frontierPreconnectedIteratedStepSourceRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (BoundaryFreeFrontierPreconnectedIteratedStepSourceRows
              inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_frontierPreconnectedIteratedStepSourceRows
      rows)
    noCutRows

/-- W32 S2 target from a genuine exterior carrier plus boundary-free local
no-third-germ rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_exteriorCarrier_boundaryFreeSource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ExteriorFrontierCarrierRows.{0}
                C inputs) ∧
            Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeNoThirdGermSource
                inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_exteriorCarrier_boundaryFreeSource
      rows)
    noCutRows

/-- W32 S2 target from a genuine exterior carrier plus incident-only local
source rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_exteriorCarrier_incidentOnlySource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ExteriorFrontierCarrierRows.{0}
                C inputs) ∧
            Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeIncidentOnlySourceRows
                inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_exteriorCarrier_incidentOnlySource
      rows)
    noCutRows

/-- W32 S2 target from a genuine exterior carrier plus endpoint-incident local
source rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_exteriorCarrier_endpointIncidentSource
    (carrierRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ExteriorFrontierCarrierRows.{0}
              C inputs))
    (endpointRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeEndpointIncidentSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_exteriorCarrier_endpointIncidentSource
      carrierRows endpointRows)
    noCutRows

/-- W32 S2 target from the strongest checked input-facing edge-chain route.

The exact residual source rows are selected-edge chain connectedness, the
pointwise local-sector rows, and endpoint-frontier incident-edge closure.  The
open-segment incident case is discharged inside the S2 reducer by the
definition of the actual unbounded-frontier edge set. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_localSector_endpointIncidentRows
    (edgeChainRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeCarrierSegmentChainConnected
            inputs)
    (localSectorRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
              inputs a)
    (endpointRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall (a :
              {v : Fin n //
                v ∈
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                    C inputs})
            (x : Fin n),
            (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
              (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point x ∈
                  frontier
                    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                      C inputs).exterior ->
                (a.1, x) ∈
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                      C inputs ∨
                  (x, a.1) ∈
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                      C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_localSector_endpointIncidentRows
      edgeChainRows localSectorRows endpointRows)
    noCutRows

/-- W32 S2 target from selected-edge chain connectedness plus endpoint-incident
local source rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_endpointIncidentSource
    (edgeChainRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeCarrierSegmentChainConnected
            inputs)
    (endpointRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeEndpointIncidentSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_localSector_endpointIncidentRows
    edgeChainRows
    (fun C inputs => (endpointRows C inputs).localSectorRows)
    (fun C inputs => (endpointRows C inputs).endpoint_frontier_edge)
    noCutRows

/-- W32 S2 target from raw-orbit coverage plus endpoint-incident local source
rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_rawCoverage_endpointIncidentRows
    (rawRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun R :
              JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem
                C =>
            Exists fun start :
                JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceDart
                  C =>
              Exists fun O :
                JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem.RawFaceSuccOrbit
                  R start =>
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitCoverageSourceRows
                  (inputs := inputs) O)
    (endpointRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeEndpointIncidentSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_endpointIncidentRows
      rawRows endpointRows)
    noCutRows

/-- W32 S2 target from the current non-circular raw-coverage/deleted-neighbour
source split.

The raw rows supply the selected exterior raw face-orbit coverage, and the
deleted-neighbour source supplies the no-cut local two-neighbour data for the
actual unbounded-frontier carrier.  This route avoids the invalid universal
adjacent-frontier-endpoint incident-edge premise. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_rawCoverage_unreachableAfterDeleteInputSource
    (rawRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun R :
              JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem
                C =>
            Exists fun start :
                JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceDart
                  C =>
              Exists fun O :
                JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem.RawFaceSuccOrbit
                  R start =>
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitCoverageSourceRows
                  (inputs := inputs) O)
    (source :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_unreachableAfterDeleteInputSource
      rawRows source)
    noCutRows

/-- W32 S2 target from the compact boundary-free connected raw-orbit package.

This is the direct no-orientation handoff: the package already contains the
boundary-free local source, connectedness of the actual unbounded-frontier
carrier, and selected raw-orbit dart-edge frontier coverage. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows
              inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows
      rows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the current compact selected-neighbour strict-order
leaf split.

The connected raw-orbit package is assembled in the S2 owner file from:
boundary-free local rows, planar-continuum frontier preconnectedness, selected
neighbour/cut/geometric-order input rows, and the strict selected raw
`faceSucc` angular-order row.  This theorem is only the W32 handoff through
the existing connected raw-orbit consumer. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_boundaryFreeInput_preconnected_selectedNeighborInput_strictOrder_20260520
    (boundaryFree :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeInputSourceReduction
            inputs)
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (strictOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_dependentSource
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.selectedNeighborCutPartitionGeometricOrderSource_of_inputSource
              (C := C) (inputs := inputs) (selectedInput C inputs))
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
          inputs
          (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.selectedNeighborGeometricCarrierLeft
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource)
          (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.selectedNeighborGeometricCarrierRight
            (C := C) (inputs := inputs)
            selectedRows.toGeometricSelectionInputSource))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.boundaryFreeConnectedRawOrbitSourceRows_family_of_boundaryFreeInput_preconnected_selectedNeighborInput_strictOrder_20260520
      boundaryFree frontier_preconnected selectedInput strictOrder)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the current no-orientation raw-orbit source split.

This is the direct consumer for the three owner-file source obligations:
boundary-free no-third-germ local rows, component-topology rows for the actual
unbounded exterior frontier, and selected successor local two-germ rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_componentTopology_boundaryFree_selectedSuccessorLocalTwoGerm
    (localSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          BoundaryFreeNoThirdGermSource inputs)
    (componentTopology :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (selectedSuccessorLocalTwoGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccSuccessorLocalTwoGermRowsNoOrbitSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_family_of_componentTopology_boundaryFree_selectedSuccessorLocalTwoGerm_20260520bp
      localSource componentTopology selectedSuccessorLocalTwoGermRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the direct selected-edge no-orientation raw-orbit
source split.

This is the selected-edge version of
`minimalFailureExactActualTopologyFieldsTarget_of_componentTopology_boundaryFree_selectedSuccessorLocalTwoGerm`:
when the Nat-indexed geometric `faceSucc` edge row is already available, the
local-two-germ successor source is not kept as a separate W32 premise. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_componentTopology_boundaryFree_selectedSuccessorEdge
    (localSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          BoundaryFreeNoThirdGermSource inputs)
    (componentTopology :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (selectedSuccessorEdge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_family_of_componentTopology_boundaryFree_selectedSuccessorEdge_20260520bv
      localSource componentTopology selectedSuccessorEdge)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the direct selected-edge chain route.

This is the current compact displayed route: boundary-free local rows and the
selected edge-chain source build the component-topology package internally,
while the selected Nat-indexed geometric `faceSucc` edge row supplies raw
orbit propagation. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_boundaryFree_selectedSuccessorEdge_20260520ce
    (localSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          BoundaryFreeNoThirdGermSource inputs)
    (edge_segment_chain :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (selectedSuccessorEdge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_boundaryFree_selectedSuccessorEdge_20260520ce
      localSource edge_segment_chain selectedSuccessorEdge)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the current CH-composed source surface.

This is the shortest displayed route after the recent CH reducers: endpoint-only
neighbor rows build the boundary-free no-third-germ source, component-topology
rows build the selected edge-carrier chain, and local-angular/head-between rows
build the selected `faceSucc` frontier-edge source. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_ch_endpointOnly_componentTopology_faceSuccEdge_20260520ci
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (endpoint_only :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C)
        (a :
          {v : Fin n //
            v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
          (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
            (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point x ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ->
              x = ((neighborRows C inputs) a).left.1 ∨
                x = ((neighborRows C inputs) a).right.1)
    (componentTopology :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (localAngularSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
            inputs)
    (headBetween :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccHeadBetweenLocalAngularNoOrbitSource
            inputs (localAngularSource C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_boundaryFree_selectedSuccessorEdge_20260520ce
    (fun C inputs =>
      boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointOnly
        (C := C) (inputs := inputs)
        (neighborRows C inputs) (endpoint_only C inputs))
    (S2_agent_ch_carrier_connectedness_source_family componentTopology)
    (S2_agent_ch_selected_faceSucc_edge_source_family_20260520ch
      localAngularSource headBetween)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the current four concrete source families.

The boundary-free and component-topology packages are constructed internally
from local-sector rows, adjacent endpoint incidence, and selected edge-chain
connectivity; the selected-successor package is constructed from pointwise
local two-germ rows plus the selected no-orbit geometric `faceSucc` edge row.
-/
theorem minimalFailureExactActualTopologyFieldsTarget_of_localTwoGerm_edgeChain_incident_selectedSuccessorEdge
    (localTwoGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (edge_segment_chain :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (selectedSuccessorEdge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_localTwoGerm_edgeChain_incident_selectedSuccessorEdge_20260520bv
      localTwoGermRows incident_edge edge_segment_chain selectedSuccessorEdge)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the direct raw-coverage cycle reducer.

The raw coverage rows are erased internally to selected edge-chain
connectedness by the checked raw-coverage consumer, while the local two-germ,
incident-edge, and selected successor-edge rows remain the explicit source
families. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_rawCoverage_localTwoGerm_incident_selectedSuccessorEdge
    (rawRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          Exists fun R =>
            Exists fun start :
              JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceDart C =>
              Exists fun O :
                JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem.RawFaceSuccOrbit
                  R start =>
                RawOrbitCoverageSourceRows (inputs := inputs) O)
    (localTwoGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (selectedSuccessorEdge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_localTwoGerm_incident_selectedSuccessorEdge_20260520co
      rawRows localTwoGermRows incident_edge selectedSuccessorEdge)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the current strict residual source packages.

This composes the local geometric-angular source and the frontier-topology
selected-edge source into the four concrete rows consumed by
`minimalFailureExactActualTopologyFieldsTarget_of_localTwoGerm_edgeChain_incident_selectedSuccessorEdge`.
-/
theorem minimalFailureExactActualTopologyFieldsTarget_of_geometricAngular_frontierTopology_selectedSuccessorEdge
    (localAngular :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
            inputs)
    (frontierTopology :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          EdgeChainIncidentFrontierTopologySourceRows inputs)
    (selectedSuccessorEdge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_localSector_edgeChain_incident_selectedSuccessorLocalTwoGerm_20260520bn
      (fun C inputs =>
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.localSectorRows_of_boundaryFree_geometricAngularSource
          (C := C) (inputs := inputs) (localAngular C inputs))
      (fun C inputs =>
        (frontierTopology C inputs).adjacentEndpointIncidentSource)
      (fun C inputs =>
        (frontierTopology C inputs).edgeCarrierSegmentChainConnected)
      (fun C inputs =>
        let localSectorRows :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.localSectorRows_of_boundaryFree_geometricAngularSource
            (C := C) (inputs := inputs) (localAngular C inputs)
        let localSource : BoundaryFreeNoThirdGermSource inputs :=
          S2_agent_boundary_free_no_third_input_source_20260520bu
            (C := C) (inputs := inputs)
            localSectorRows
            (frontierTopology C inputs).adjacentEndpointIncidentSource
        S2_agent_selected_successor_local_two_germ_source_20260520bu
          (C := C) (inputs := inputs)
          localSource.toLocalTwoGermRows
          (selectedSuccessorEdge C inputs))
    )
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the strict local/frontier topology source families and
the orbit-free selected successor point row.

The selected successor point row is promoted internally to selected
`unboundedFrontierEdgeSet` membership by
`S2_agent_selected_edge_noorbit_source_20260520av`, then the existing
selected-edge W32 consumer takes over. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_geometricAngular_frontierTopology_successorPoint
    (localAngular :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
            inputs)
    (frontierTopology :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          EdgeChainIncidentFrontierTopologySourceRows inputs)
    (successorSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_geometricAngular_frontierTopology_selectedSuccessorEdge
    localAngular
    frontierTopology
    (fun C inputs =>
      S2_agent_selected_edge_noorbit_source_20260520av
        (C := C) (inputs := inputs) (successorSource C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the current strict BX residual source tracks.

This is the composition handoff for the active workboard claims: component
frontier topology, adjacent endpoint local component-interval closure,
pointwise local angular/third-germ rows, and the selected raw `faceSucc`
local-sector transition row. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_bx_residualSources
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (thirdGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall (a :
              {v : Fin n //
                v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball
                ((_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
                  q ∈
                    _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.vertexIncidentGermW3
                      C a.1 x ε ->
                    q ≠ (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1 ->
                      x ≠ ((neighborRows C inputs) a).left.1 ->
                        x ≠ ((neighborRows C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexAngularBetween C a.1
                            ((neighborRows C inputs) a).left.1
                            ((neighborRows C inputs) a).right.1 x)
    (component_topology :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologySourceRows inputs)
    (local_component_interval :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsLocalComponentIntervalClosureSource
            C inputs)
    (transitionRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccLocalSectorTransitionNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_geometricAngular_frontierTopology_selectedSuccessorEdge
    (S2_agent_local_angular_source_of_neighborPair_selection_thirdGerm_20260520bw
      neighborRows selectionRows thirdGermRows)
    (S2_agent_frontier_topology_source_20260520bw
      component_topology local_component_interval)
    (S2_agent_selected_faceSucc_edge_source_family_20260520bw
      transitionRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target after the component-topology and endpoint-interval BX
reducers have been erased to their input-facing source rows. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_bx_inputSourceRows
    (componentRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (thirdGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall (a :
              {v : Fin n //
                v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball
                ((_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
                  q ∈
                    _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.vertexIncidentGermW3
                      C a.1 x ε ->
                    q ≠ (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1 ->
                      x ≠ ((neighborRows C inputs) a).left.1 ->
                        x ≠ ((neighborRows C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexAngularBetween C a.1
                            ((neighborRows C inputs) a).left.1
                            ((neighborRows C inputs) a).right.1 x)
    (transitionRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccLocalSectorTransitionNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_bx_residualSources
    neighborRows
    selectionRows
    thirdGermRows
    (S2_agent_component_topology_input_source_20260520bx componentRows)
    (S2_agent_local_component_interval_source_20260520bx incident_edge)
    transitionRows
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the compressed BY source surface.

The geometric-selection input source supplies both the concrete carrier
neighbour-pair rows and the genuine sorted outgoing-dart selection rows.  With
the adjacent-endpoint incident-edge source, it also gives the point-ray
third-germ row, so the live W32 route only carries component topology,
incident edges, geometric selection, and the selected local-transition row. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_by_geometricSelection_localTransition_20260520bz
    (componentRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (transitionRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccLocalSectorTransitionNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_geometricAngular_frontierTopology_selectedSuccessorEdge
    (S2_main_local_angular_source_of_geometricSelection_incidentEdge_20260520bz
      incident_edge geometricSelection)
    (S2_agent_frontier_topology_source_20260520bw
      (S2_agent_component_topology_input_source_20260520bx componentRows)
      (S2_agent_local_component_interval_source_20260520bx incident_edge))
      (S2_agent_selected_faceSucc_edge_source_family_20260520bw transitionRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target using the non-circular selected-successor local two-germ
source.

The local-two-germ source is erased to the strict local transition row in
`S2SeededRawOrbitSource`; this avoids routing the transition through the
successor-point source that is itself a consequence of the transition. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_ca_geometricSelection_successorLocalTwoGerm_20260520ca
    (componentRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (successorLocalTwoGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccSuccessorLocalTwoGermRowsNoOrbitSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_by_geometricSelection_localTransition_20260520bz
    componentRows
    incident_edge
    geometricSelection
    (S2_agent_local_transition_source_from_successor_localTwoGerm_20260520ca
      successorLocalTwoGermRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target after erasing the component-topology input row through the
checked CI finite-drawing reducer.

The residual source surface is now the selected edge-chain row, adjacent
endpoint selected-edge incidence, geometric neighbour selection, and selected
successor local two-germ rows.  The component-topology input package is built
internally from the selected edge chain and the local-sector rows obtained from
the geometric-selection source. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_ci_edgeChain_geometricSelection_successorLocalTwoGerm_20260520cj
    (edge_segment_chain :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (successorLocalTwoGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccSuccessorLocalTwoGermRowsNoOrbitSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_ca_geometricSelection_successorLocalTwoGerm_20260520ca
    (fun C inputs =>
      let localAngular :
          BoundaryFreeLocalSectorGeometricAngularSource inputs :=
        S2_main_local_angular_source_of_geometricSelection_incidentEdge_20260520bz
          incident_edge geometricSelection C inputs
      S2_agent_ci_frontier_component_topology_source_args_20260520ci
        inputs
        (edge_segment_chain C inputs)
        (localSectorRows_of_boundaryFree_geometricAngularSource
          (C := C) (inputs := inputs) localAngular))
    incident_edge
    geometricSelection
    successorLocalTwoGermRows
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target after composing the CI local-angular and face-successor
reducers.

The remaining source surface is the selected edge-chain row, adjacent endpoint
selected-edge incidence, geometric neighbour selection, the selected successor
interior-frontier point row, and the non-local-carrier row for the geometric
`faceSucc` head.  The local angular source, boundary-free local source, and
selected successor edge source are all constructed internally by checked S2
reducers. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_cj_edgeChain_incident_geometricSelection_successorPoint_notLocalCarrier
    (edge_segment_chain :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (successorPoint :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs)
    (notLocalCarrier :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccHeadNotLocalAngularCarrierNoOrbitSource
            inputs
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_ci_local_angular_neighbor_source_family
              incident_edge geometricSelection C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  intro n C hmin
  let localAngularSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
            inputs :=
    _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_ci_local_angular_neighbor_source_family
      incident_edge geometricSelection
  exact
    (minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_boundaryFree_selectedSuccessorEdge_20260520ce
      (fun C inputs =>
        let localAngular := localAngularSource C inputs
        let localSectorRows :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.localSectorRows_of_boundaryFree_geometricAngularSource
            (C := C) (inputs := inputs) localAngular
        S2_agent_boundary_free_no_third_input_source_20260520bu
          (C := C) (inputs := inputs)
          localSectorRows (incident_edge C inputs))
      edge_segment_chain
      (fun C inputs =>
        S2_agent_ci_selected_faceSucc_edge_source_20260520ci
          (C := C) (inputs := inputs)
          (localAngularSource C inputs)
          (successorPoint C inputs)
          (notLocalCarrier C inputs))
      noCutRows) C hmin

set_option linter.style.longLine false in
/-- W32 S2 target with the local-angular route using only the endpoint-only
no-chord row.

Compared with
`minimalFailureExactActualTopologyFieldsTarget_of_cj_edgeChain_incident_geometricSelection_successorPoint_notLocalCarrier`,
this removes the too-strong adjacent-frontier-endpoint incident-edge source
from the local-angular construction.  The boundary-free source and the
local-angular source are both rebuilt from the same selected carrier-neighbour
geometric-selection package and the endpoint-only row, so the residual says
only that an adjacent frontier endpoint is one of the two selected carrier
neighbours. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_ck_edgeChain_endpointOnly_geometricSelection_successorPoint_notLocalCarrier
    (edge_segment_chain :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierEdgeCarrierSegmentChainConnected inputs)
    (geometricSelection :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (endpoint_only :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C)
        (a :
          {v : Fin n //
            v ∈ unboundedFrontierVertexSet C inputs})
        (x : Fin n),
          (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
            (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point x ∈
                frontier (unboundedExteriorComponentRows C inputs).exterior ->
              x =
                  (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                    (geometricSelection C inputs) a).left.1 ∨
                x =
                  (unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                    (geometricSelection C inputs) a).right.1)
    (successorPoint :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs)
    (notLocalCarrier :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccHeadNotLocalAngularCarrierNoOrbitSource
            inputs
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_cj_local_angular_neighbor_source_endpointOnly
              (C := C) (inputs := inputs)
              (geometricSelection C inputs) (endpoint_only C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  intro n C hmin
  let localAngularSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
            inputs :=
    fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_cj_local_angular_neighbor_source_endpointOnly
        (C := C) (inputs := inputs)
        (geometricSelection C inputs) (endpoint_only C inputs)
  exact
    (minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_boundaryFree_selectedSuccessorEdge_20260520ce
      (fun C inputs =>
        let neighborRows :=
          unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
            (geometricSelection C inputs)
        boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointOnly
          (C := C) (inputs := inputs) neighborRows
          (by
            intro a x hadj hxfrontier
            simpa [neighborRows] using endpoint_only C inputs a x hadj hxfrontier))
      edge_segment_chain
      (fun C inputs =>
        S2_agent_ci_selected_faceSucc_edge_source_20260520ci
          (C := C) (inputs := inputs)
          (localAngularSource C inputs)
          (successorPoint C inputs)
          (notLocalCarrier C inputs))
      noCutRows) C hmin

set_option linter.style.longLine false in
/-- W32 S2 target after replacing the selected local-transition source by the
successor interior-frontier point source. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_bx_inputSourceRows_successorPoint
    (componentRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (thirdGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall (a :
              {v : Fin n //
                v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball
                ((_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
                  q ∈
                    _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.vertexIncidentGermW3
                      C a.1 x ε ->
                    q ≠ (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1 ->
                      x ≠ ((neighborRows C inputs) a).left.1 ->
                        x ≠ ((neighborRows C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexAngularBetween C a.1
                            ((neighborRows C inputs) a).left.1
                            ((neighborRows C inputs) a).right.1 x)
    (successorPoint :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_bx_inputSourceRows
    componentRows
    incident_edge
    neighborRows
    selectionRows
    thirdGermRows
    (S2_agent_faceSucc_local_transition_source_family_20260520bx
      (fun C inputs =>
        S2_agent_local_angular_source_of_neighborPair_selection_thirdGerm_20260520bw
          neighborRows selectionRows thirdGermRows C inputs)
      successorPoint)
    noCutRows

set_option linter.style.longLine false in
/-- Same successor-point W32 handoff with third-germ geometry supplied in the
point-ray sector form before converting to graph-dart angles. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_bx_pointThirdGerm_successorPoint
    (componentRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs)
    (incident_edge :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource
            C inputs)
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            UnboundedFrontierCarrierNeighborPairAt inputs a)
    (selectionRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall a :
            {v : Fin n //
              v ∈ unboundedFrontierVertexSet C inputs},
            Nonempty
              (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
                C a.1 ((neighborRows C inputs) a).left.1
                ((neighborRows C inputs) a).right.1))
    (pointThirdGermRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          forall (a :
              {v : Fin n //
                v ∈ unboundedFrontierVertexSet C inputs})
              (ε : Real) (q : PlanarInterface.Point) (x : Fin n),
            q ∈ Metric.ball
                ((_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1) ε ->
              q ∈ frontier (unboundedExteriorComponentRows C inputs).exterior ->
                (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
                  q ∈
                    _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.vertexIncidentGermW3
                      C a.1 x ε ->
                    q ≠ (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1 ->
                      x ≠ ((neighborRows C inputs) a).left.1 ->
                        x ≠ ((neighborRows C inputs) a).right.1 ->
                          BoundaryFreeGraphVertexPointAngularBetween C a.1
                            ((neighborRows C inputs) a).left.1
                            ((neighborRows C inputs) a).right.1 q)
    (successorPoint :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
    minimalFailureExactActualTopologyFieldsTarget_of_bx_inputSourceRows_successorPoint
      componentRows
      incident_edge
      neighborRows
      selectionRows
      (fun C inputs =>
        boundaryFreeThirdGermAngularRows_of_pointAngularRows
          (C := C) (inputs := inputs)
          (left := fun a => ((neighborRows C inputs) a).left.1)
          (right := fun a => ((neighborRows C inputs) a).right.1)
          (pointThirdGermRows C inputs))
      successorPoint
      noCutRows

/-- W32 S2 target from connected carrier rows plus the seeded raw-orbit
one-step source package. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedStepSourceRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedStepSourceRows
              inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_connectedStepSourceRows
      rows)
    noCutRows

/-- W32 S2 target from connected carrier rows plus the orientation-aware
seeded raw-orbit source package. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedIteratedStepSourceRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (BoundaryFreeConnectedIteratedStepSourceRows
              inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_connectedIteratedStepSourceRows
      rows)
    noCutRows

/-- W32 S2 target from direct boundary-free local rows, connected carrier rows,
and the selected raw-orbit iterated successor source. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_connectedIteratedSuccessorSource
    (localSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          BoundaryFreeNoThirdGermSource inputs)
    (carrier_connected :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          (unboundedFrontierCarrierGraph C inputs).Connected)
    (start_and_iterated_successor_frontier :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitStartAndIteratedSuccessorFrontierSource inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (finitePlanarStraightLineOuterComponentTheorem_of_connectedIteratedSuccessorSource
      localSource carrier_connected start_and_iterated_successor_frontier)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from boundary-free local rows, connected carrier rows, the
raw dart-edge frontier source, and repeated-tail actual exterior-arc rows.

This is the selected actual-arc route after the selected-edge membership row
has been erased from `RawOrbitDartEdgeFrontierSource`; the only orbit-specific
residual is the repeated-tail actual-arc callback. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_selectedActualArcRows_dartFrontier_boundaryFree_connected
    (localSource :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          BoundaryFreeNoThirdGermSource inputs)
    (carrier_connected :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          (unboundedFrontierCarrierGraph C inputs).Connected)
    (dart_edge_frontier_source :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          RawOrbitDartEdgeFrontierSource inputs)
    (repeated_tail_arcRows_source :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C)
        {e : PlanarInterface.Edge n} {p : PlanarInterface.Point}
        {start :
          JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceDart C},
          UnboundedExteriorFrontierEdgeLocalRows C inputs e p ->
          start.tail = e.1 ->
          start.head = e.2 ->
          forall O :
            JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem.RawFaceSuccOrbit
              (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.geometricUnitDistanceRotationSystem C) start,
            forall {i j : Fin O.period},
              i ≠ j ->
              (O.dart i).tail = (O.dart j).tail ->
                RawFaceSuccOrbitRepeatedTailActualExteriorArcRows
                  (inputs := inputs) O i j)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_selectedActualArcRows_dartFrontier_boundaryFree_connected
      localSource carrier_connected dart_edge_frontier_source
      repeated_tail_arcRows_source)
    noCutRows

/-- W32 S2 target from endpoint rows, carrier connectedness, and the
orientation-aware iterated `faceSucc` selected-edge source. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_endpointIncident_iteratedFaceSuccEdgeSource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeEndpointIncidentSourceRows
              inputs) ∧
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
              C inputs).Connected ∧
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitIteratedFaceSuccFrontierEdgeSource
                inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_endpointIncident_iteratedFaceSuccEdgeSource
      (fun C inputs => (rows C inputs).1)
      (fun C inputs => (rows C inputs).2.1)
      (fun C inputs => (rows C inputs).2.2))
    noCutRows

/-- W32 S2 target from the direct same-`B` raw face-successor boundary handoff.

This consumer only needs the raw orbit tied to a concrete boundary cycle by
period/tail rows plus raw-tail frontier exactness. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_rawFaceSuccOrbitBoundaryRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun R :
              JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem
                C =>
            Exists fun start :
                JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceDart
                  C =>
              Exists fun O :
                  JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceRotationSystem.RawFaceSuccOrbit
                    R start =>
                Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
                  Exists fun hperiod : B.length = O.period =>
                    (forall k : Fin B.length,
                      (O.dart (Fin.cast hperiod k)).tail = B.vertex k) ∧
                    (forall v : Fin n,
                      (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                          frontier
                            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                              C inputs).exterior ↔
                        Exists fun k : Fin O.period =>
                          (O.dart k).tail = v))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_rawFaceSuccOrbitBoundaryRows
      rows)
    noCutRows

/-- W32 S2 target from the complete exterior boundary-cycle source shape.

This is a consumer route only: the proof-owning source theorem still has to
construct the boundary cycle and prove frontier exactness, selected boundary
sides, and incident-edge completeness from
`FinitePlanarOuterComponentInputs`. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_exists_boundaryCycle_complete
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                  frontier
                    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                      C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              (B.vertex k,
                  B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                    C inputs ∨
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k),
                  B.vertex k) ∈
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                    C inputs) ∧
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryCycleIncidentFrontierEdgeCompleteness
              inputs B)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_exists_boundaryCycle_complete
      rows)
    noCutRows

/-- W32 S2 target from the primitive local-sector source shape.

This is the direct consumer for the repaired S2 route.  The source theorem
still has to construct the actual exterior boundary cycle and prove the local
sector rows; this wrapper only erases those rows through the checked finite
planar outer-component theorem. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_boundaryVertexExteriorSectorRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                  frontier
                    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                      C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryVertexExteriorSectorRowsAt
                inputs B k))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_boundaryVertexExteriorSectorRows
      rows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 S2 target from the compact boundary-cycle edge-membership, angular,
and incident-completeness handoff. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_boundaryCycleEdgeMem_angular_complete
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C) ->
          Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
            (forall v : Fin n,
              (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
                  frontier
                    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows
                      C inputs).exterior ↔
                Exists fun k : Fin B.length => B.vertex k = v) ∧
            (forall k : Fin B.length,
              (B.vertex k,
                  B.vertex (PlanarInterface.cyclicSucc B.length_pos k)) ∈
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                    C inputs ∨
                (B.vertex (PlanarInterface.cyclicSucc B.length_pos k),
                  B.vertex k) ∈
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierEdgeSet
                    C inputs) ∧
            (forall k : Fin B.length,
              _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
                C B k) ∧
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryCycleIncidentFrontierEdgeCompleteness
              inputs B)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_boundaryCycleEdgeMem_angular_complete
      rows)
    noCutRows

/-- Concrete-carrier version of the S2 endpoint handoff.  It leaves exactly
the finite plane-graph rows for the actual unbounded-frontier carrier:
decidability, connectedness, degree two, and whole-edge-frontier. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_frontierCarrierGraph_wholeRows
    (hdec :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          DecidableRel
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
              C inputs).Adj)
    (hconn :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          letI : DecidableRel
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                C inputs).Adj :=
            hdec C inputs
          (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
            C inputs).Connected)
    (hdegree_two :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          letI : DecidableRel
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                C inputs).Adj :=
            hdec C inputs
          forall v :
            {v : Fin n //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
              @SimpleGraph.degree _
                (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                  C inputs) v
                ((_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                  C inputs).neighborSetFintype v) =
                  2)
    (hwhole :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeSetWholeOpenSegmentFrontier
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_frontierCarrierGraph_wholeRows
      hdec hconn hdegree_two hwhole)
    noCutRows

/-- Concrete-carrier S2 endpoint handoff with decidability discharged by the
canonical finite frontier carrier.  The remaining rows are exactly the
geometric/topological connectedness, degree-two, and whole-edge-frontier facts. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_frontierCarrierGraph_geometricRows
    (hconn :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          letI : DecidableRel
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                C inputs).Adj :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph_decidableAdj
              C inputs
          (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
            C inputs).Connected)
    (hdegree_two :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          letI : DecidableRel
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                C inputs).Adj :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph_decidableAdj
              C inputs
          forall v :
            {v : Fin n //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
              @SimpleGraph.degree _
                (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                  C inputs) v
                ((_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                  C inputs).neighborSetFintype v) =
                  2)
    (hwhole :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeSetWholeOpenSegmentFrontier
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_frontierCarrierGraph_geometricRows
      hconn hdegree_two hwhole)
    noCutRows

/-- S2 endpoint handoff from cyclic coverage of the concrete carrier plus
local dart-pair rows.  These rows give connectedness and degree two; whole-edge
frontier is built into the concrete carrier definition. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_cyclicCoverageDartPairRows
    (hcycle :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierCyclicCoverageRows
            C inputs)
    (hdart :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a :
            {v : Fin n //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierDartPairAt
                inputs a)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_cyclicCoverageDartPairRows
      hcycle hdart)
    noCutRows

/-- S2 endpoint handoff from the compact concrete-carrier source rows:
cyclic coverage of the actual unbounded-frontier carrier plus local sector
rows at every selected carrier vertex. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_cyclicCoverageLocalSectorRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierCyclicCoverageRows
                C inputs ×
              (forall a :
                {v : Fin n //
                  v ∈
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                      C inputs},
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
                    inputs a)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_cyclicCoverageLocalSectorRows
      rows)
    noCutRows

/-- S2 endpoint handoff from the current concrete-carrier source split:
selected frontier-edge chain connectivity plus the pointwise neighbour-pair
rows for the actual unbounded-frontier carrier.

This wrapper does not add another target surface; it only displays the
smallest remaining carrier obligations that erase to the existing finite
planar outer-component theorem. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_neighborPairRows
    (edgeChainRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeCarrierSegmentChainConnected
            inputs)
    (neighborRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a :
            {v : Fin n //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairAt
                inputs a)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_neighborPairRows
      edgeChainRows neighborRows)
    noCutRows

/-- S2 endpoint handoff from selected frontier-edge chain connectivity plus
the honest local-radius no-third-germ source.

This is the current compact route after the neighbour-pair reduction: the
local source names the two selected `unboundedFrontierEdgeSet` carrier edges
at each actual frontier vertex and proves the local no-third-germ row.  It
does not use the false all-adjacent endpoint source or the global closed-germ
source as a bare input. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_localNoThirdGermSource
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeCarrierSegmentChainConnected
              inputs ∧
            Nonempty
              (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeLocalNoThirdGermSourceRows
                inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_localNoThirdGermSource
      rows)
    noCutRows

/-- Split-family version of
`minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_localNoThirdGermSource`.

This is the workboard-facing form: S2 now decomposes into selected carrier
edge-chain connectivity and the pointwise selected local no-third-germ source,
plus the separate S1 no-cut family. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_localNoThirdGermSourceRows
    (edgeChainRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierEdgeCarrierSegmentChainConnected
            inputs)
    (localSourceRows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeLocalNoThirdGermSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_edgeChain_localNoThirdGermSource
    (fun C inputs => ⟨edgeChainRows C inputs, ⟨localSourceRows C inputs⟩⟩)
    noCutRows

/-- S2 endpoint handoff from the orbit-first exterior face-dart carrier
package.  The package erases to cyclic coverage and local dart-pair rows inside
`ExteriorComponentTopology`; the compact displayed route is
`minimalFailureExactActualTopologyFieldsTarget_of_cyclicCoverageLocalSectorRows`.
-/
theorem minimalFailureExactActualTopologyFieldsTarget_of_faceDartOrbitExteriorCarrierRows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FaceDartOrbitExteriorCarrierRows
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finitePlanarStraightLineOuterComponentTheorem_of_faceDartOrbitExteriorCarrierRows
      rows)
    noCutRows

/-- Minimal-failure exterior cycle/frontier rows close the live exact S2
target directly: the Jordan enclosure is derived from the exterior frontier,
then consumed through the concrete boundary/enclosure adapter. -/
structure ExteriorCycleFrontierNotMemRow (C : _root_.UDConfig n) where
  boundary : JordanBoundaryConcrete.UnitDistanceCycleBoundary C
  exterior : Set PlanarInterface.Point
  off_cycle_vertices_not_mem_exterior :
    forall v : Fin n,
      (¬ Exists fun k : Fin boundary.length => boundary.vertex k = v) ->
        (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∉ exterior
  frontier_iff_cycle_vertex :
    forall v : Fin n,
      (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
          frontier exterior <->
        Exists fun k : Fin boundary.length => boundary.vertex k = v

def exteriorCycleFrontierNotMemRowOfUnboundedExteriorFrontierCycleRows
    {C : _root_.UDConfig n}
    {inputs :
      JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
        C}
    (rows :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedExteriorFrontierCycleRows
        C inputs) :
    ExteriorCycleFrontierNotMemRow C where
  boundary := rows.boundary
  exterior := rows.unbounded.exterior
  off_cycle_vertices_not_mem_exterior := fun v _ =>
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedExteriorFrontierCycleRows.graph_vertex_not_mem_exterior
      rows v
  frontier_iff_cycle_vertex := rows.frontier_iff_cycle_vertex

theorem minimalFailureExactActualTopologyFieldsTarget_of_exterior_cycle_frontier_not_mem_rows
    (rows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          ExteriorCycleFrontierNotMemRow C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_chosenJordanOuterComponentRows
    (JordanBoundaryConcrete.minimalFailureChosenJordanOuterComponentRowsOfBoundaryEnclosureRows
      (fun {n} C hmin => by
        let row := rows (n := n) C hmin
        exact
          ⟨row.boundary,
            jordanOuterComponentEnclosure_of_exterior_frontier_not_mem
              row.boundary row.exterior
              row.off_cycle_vertices_not_mem_exterior
              row.frontier_iff_cycle_vertex⟩))

/-- Nonempty flexible Jordan outer-component source rows imply the remaining
actual-cycle target, again without choosing the canonical cycle as outer. -/
theorem minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_nonempty_jordanOuterComponentSourceRows
    (h :
      Nonempty
        JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget := by
  cases h with
  | intro rows =>
      exact
        minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_jordanOuterComponentSourceRows
          rows

/-- The canonical form of the same source: prove Jordan enclosure predicates
for the canonical simple cycle extracted from each minimal failure. -/
noncomputable def minimalFailureSimpleCyclicOuterBoundaryEnclosureRowsOfCanonicalJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureCanonicalJordanOuterComponentRows) :
    MinimalFailureSimpleCyclicOuterBoundaryEnclosureRows :=
  minimalFailureSimpleCyclicOuterBoundaryEnclosureRowsOfJordanOuterComponentSourceRows
    (JordanBoundaryConcrete.minimalFailureJordanOuterComponentSourceRowsOfCanonical
      rows)

/-- The canonical Jordan outer-component theorem is now the sharpest S2
source: it combines the checked graph-cycle extraction with real enclosure
predicates for that selected cycle. -/
theorem minimalFailureExactActualTopologyFieldsTarget_of_canonicalJordanOuterComponentRows
    (rows :
      JordanBoundaryConcrete.MinimalFailureCanonicalJordanOuterComponentRows) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_simpleCyclicOuterBoundaryEnclosureRows
    (minimalFailureSimpleCyclicOuterBoundaryEnclosureRowsOfCanonicalJordanOuterComponentRows
      rows)

theorem minimalFailureExactActualTopologyFieldsTarget_of_nonempty_outerBoundaryCoreSourceWithLengthRows
    (h : Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  cases h with
  | intro rows =>
      exact
        minimalFailureExactActualTopologyFieldsTarget_of_outerBoundaryCoreSourceWithLengthRows
          rows

theorem minimalFailureExactActualTopologyFieldsTarget_of_nonempty_actualOuterBoundaryCycleDataRows
    (h : Nonempty MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  cases h with
  | intro rows =>
      exact minimalFailureExactActualTopologyFieldsTarget_of_actualOuterBoundaryCycleDataRows rows

/--
The minimal field package for the W28 finite-noncrossing source is rowwise
face-boundary data, a selected outer face, nondegenerate boundary length, and
enclosure for that same dependent face.
-/
theorem minimalFailureFiniteNoncrossingSourceTarget_iff_minimalFaceBoundaryFieldPackage :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget <->
      (forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          Exists fun H :
              FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
                (CanonicalGraph C) =>
            Exists fun F : H.Face =>
              H.IsOuterFace F /\
                3 <= H.boundaryLength F /\
                  Nonempty
                    (OuterBoundaryInterface.OuterBoundaryEnclosure
                      (CanonicalGraph C) H F)) := by
  constructor
  case mp =>
    intro h n C hmin
    exact h C hmin
  case mpr =>
    intro h n C hmin
    exact h C hmin

theorem minimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget_iff_minimalFaceBoundaryFieldPackage :
    MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget <->
      (forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          Exists fun H :
              FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
                (CanonicalGraph C) =>
            Exists fun F : H.Face =>
              H.IsOuterFace F /\
                3 <= H.boundaryLength F /\
                  Nonempty
                    (OuterBoundaryInterface.OuterBoundaryEnclosure
                      (CanonicalGraph C) H F)) := by
  constructor
  case mp =>
    intro h n C hmin
    exact h C hmin
  case mpr =>
    intro h n C hmin
    exact h C hmin

/--
Direct row constructor for the actual W28 finite-noncrossing source target.
It assumes only the dependent face-boundary rows named in the source: the
unit-distance face-boundary hypotheses, selected outer face, outer-face proof,
length at least three, and enclosure.
-/
theorem minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_of_faceBoundaryFieldRows
    (H :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
            (CanonicalGraph C))
    (F :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).Face)
    (hF :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).IsOuterFace (F C hmin))
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (H C hmin).boundaryLength (F C hmin))
    (E :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          OuterBoundaryInterface.OuterBoundaryEnclosure
            (CanonicalGraph C) (H C hmin) (F C hmin)) :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget := by
  intro n C hmin
  exact
    ⟨H C hmin, F C hmin, hF C hmin, hlen C hmin,
      ⟨E C hmin⟩⟩

/-- The same honest dependent face-boundary fields also produce the concrete
W28 source-with-length rows. -/
def minimalFailureOuterBoundaryCoreSourceWithLengthRowsOfFaceBoundaryFieldRows
    (H :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
            (CanonicalGraph C))
    (F :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).Face)
    (hF :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).IsOuterFace (F C hmin))
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (H C hmin).boundaryLength (F C hmin))
    (E :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          OuterBoundaryInterface.OuterBoundaryEnclosure
            (CanonicalGraph C) (H C hmin) (F C hmin)) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  fun C hmin =>
    OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength.ofFiniteNoncrossingFields
      (C := C) (H := H C hmin) (F := F C hmin)
      (hF C hmin) (hlen C hmin) (E C hmin)

theorem minimalFailureOuterBoundaryCoreSourceWithLengthTarget_of_faceBoundaryFieldRows
    (H :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
            (CanonicalGraph C))
    (F :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).Face)
    (hF :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).IsOuterFace (F C hmin))
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (H C hmin).boundaryLength (F C hmin))
    (E :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          OuterBoundaryInterface.OuterBoundaryEnclosure
            (CanonicalGraph C) (H C hmin) (F C hmin)) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthTarget := by
  intro n C hmin
  exact
    Nonempty.intro
      (minimalFailureOuterBoundaryCoreSourceWithLengthRowsOfFaceBoundaryFieldRows
        H F hF hlen E C hmin)

theorem minimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget_of_faceBoundaryFieldRows
    (H :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
            (CanonicalGraph C))
    (F :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).Face)
    (hF :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).IsOuterFace (F C hmin))
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (H C hmin).boundaryLength (F C hmin))
    (hE :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Nonempty
            (OuterBoundaryInterface.OuterBoundaryEnclosure
              (CanonicalGraph C) (H C hmin) (F C hmin))) :
    MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget := by
  intro n C hmin
  exact
    ⟨H C hmin, F C hmin, hF C hmin, hlen C hmin,
      hE C hmin⟩

theorem minimalFailureExactActualTopologyFieldsTarget_of_faceBoundaryFieldRows
    (H :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          FaceReduction.UnitDistanceFaceBoundaryHypotheses.{0}
            (CanonicalGraph C))
    (F :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).Face)
    (hF :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          (H C hmin).IsOuterFace (F C hmin))
    (hlen :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          3 <= (H C hmin).boundaryLength (F C hmin))
    (hE :
      forall {n : Nat} (C : _root_.UDConfig n)
        (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
          Nonempty
            (OuterBoundaryInterface.OuterBoundaryEnclosure
              (CanonicalGraph C) (H C hmin) (F C hmin))) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget
    (minimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget_of_faceBoundaryFieldRows
      H F hF hlen hE)

theorem minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_iff_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget <->
      MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact
      exactFiniteNoncrossingActualOuterBoundaryCycleTheorem_of_w28FiniteNoncrossingActualOuterBoundaryCycleSource
        (h C hmin)
  case mpr =>
    intro h n C hmin
    exact
      w28FiniteNoncrossingActualOuterBoundaryCycleSource_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem
        (h C hmin)

theorem minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget :=
  minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_iff_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget.2
    h

def actualOuterBoundaryCycleDataRowsOfOuterBoundaryCoreSourceWithLengthRows
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  fun C hmin => (rows C hmin).toActualOuterBoundaryCycleData

def outerBoundaryCoreSourceWithLengthRowsOfActualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  fun C hmin =>
    OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength.ofActualOuterBoundaryCycleData
      (rows C hmin)

theorem minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_of_outerBoundaryCoreSourceWithLengthRows
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows) :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget := by
  intro n C hmin
  exact (rows C hmin).toFiniteNoncrossingActualOuterBoundaryCycleSource

theorem minimalFailureOuterBoundaryCoreSourceWithLengthTarget_of_rows
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthTarget := by
  intro n C hmin
  exact Nonempty.intro (rows C hmin)

/-- Choose concrete W28 source-with-length rows from the rowwise nonempty
target. -/
def minimalFailureOuterBoundaryCoreSourceWithLengthRowsOfTarget
    (h : MinimalFailureOuterBoundaryCoreSourceWithLengthTarget) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  fun C hmin => Classical.choice (h C hmin)

theorem nonempty_minimalFailureOuterBoundaryCoreSourceWithLengthRows_of_target
    (h : MinimalFailureOuterBoundaryCoreSourceWithLengthTarget) :
    Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  Nonempty.intro (minimalFailureOuterBoundaryCoreSourceWithLengthRowsOfTarget h)

theorem minimalFailureOuterBoundaryCoreSourceWithLengthTarget_iff_nonempty_rows :
    MinimalFailureOuterBoundaryCoreSourceWithLengthTarget <->
      Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows := by
  constructor
  case mp =>
    exact nonempty_minimalFailureOuterBoundaryCoreSourceWithLengthRows_of_target
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact minimalFailureOuterBoundaryCoreSourceWithLengthTarget_of_rows rows

/-- Rowwise length projection from the concrete W28 source-with-length package:
the selected face boundary is nondegenerate in the same row that carries the
outer-boundary core. -/
theorem minimalFailureOuterBoundaryCoreSourceWithLengthRows_boundaryLength_ge_three
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    3 <=
      (rows C hmin).source.core.faceBoundary.boundaryLength
        (rows C hmin).source.core.outerFace :=
  OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength.boundaryLength_ge_three
    (rows C hmin)

/-- Rowwise enclosure projection from the same concrete W28 package used for
the nondegenerate length proof. -/
theorem minimalFailureOuterBoundaryCoreSourceWithLengthRows_outerEnclosure_nonempty
    (rows : MinimalFailureOuterBoundaryCoreSourceWithLengthRows)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty
      (OuterBoundaryInterface.OuterBoundaryEnclosure
        (CanonicalGraph C)
        (rows C hmin).source.core.faceBoundary
        (rows C hmin).source.core.outerFace) :=
  OuterBoundaryCoreConstructionW28.OuterBoundaryCoreSourceWithLength.outerEnclosure_nonempty
    (rows C hmin)

theorem minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_iff_nonempty_outerBoundaryCoreSourceWithLengthRows :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget <->
      Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows := by
  constructor
  case mp =>
    intro h
    refine Nonempty.intro ?_
    intro n C hmin
    exact
      Classical.choice
        (OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSourceWithLength_of_finiteNoncrossingActualOuterBoundaryCycleSource
          (C := C) (h C hmin))
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact
          minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_of_outerBoundaryCoreSourceWithLengthRows
            rows

theorem minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_iff_outerBoundaryCoreSourceWithLengthTarget :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget <->
      MinimalFailureOuterBoundaryCoreSourceWithLengthTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact
      OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSourceWithLength_of_finiteNoncrossingActualOuterBoundaryCycleSource
        (C := C) (h C hmin)
  case mpr =>
    intro h n C hmin
    rcases h C hmin with ⟨S⟩
    exact S.toFiniteNoncrossingActualOuterBoundaryCycleSource

theorem minimalFailureOuterBoundaryCoreSourceWithLengthTarget_of_finiteNoncrossingActualOuterBoundaryCycleSourceTarget
    (h : MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthTarget :=
  minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_iff_outerBoundaryCoreSourceWithLengthTarget.1
    h

theorem minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_of_outerBoundaryCoreSourceWithLengthTarget
    (h : MinimalFailureOuterBoundaryCoreSourceWithLengthTarget) :
    MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget :=
  minimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget_iff_outerBoundaryCoreSourceWithLengthTarget.2
    h

theorem minimalFailureNondegenerateMissingTopologyFactsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget :
    MinimalFailureNondegenerateMissingTopologyFactsTarget <->
      MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact
      (exactNondegenerateMissingTopologyFactsSource_iff_remainingActualOuterBoundaryCycleTheorem
        C).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact
      exactNondegenerateMissingTopologyFactsSource_of_remainingActualOuterBoundaryCycleTheorem
        (h C hmin)

theorem minimalFailureNondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureNondegenerateMissingTopologyFactsTarget :=
  minimalFailureNondegenerateMissingTopologyFactsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget.2
    h

theorem minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_nonDegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  minimalFailureNondegenerateMissingTopologyFactsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget.1
    h

def actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  fun C hmin => Classical.choice (h C hmin)

/-- Choose strong actual-cycle rows from the exact nondegenerate topology
target.  This is just the rowwise form of the existing equivalence between
`ExactActualTopologyFields` and the remaining actual-cycle theorem. -/
def actualOuterBoundaryCycleDataRowsOfExactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
      h)

/-- Choose strong actual-cycle rows from the nondegenerate missing-topology
target, keeping the nondegenerate length proof in the selected core. -/
def actualOuterBoundaryCycleDataRowsOfNondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureActualOuterBoundaryCycleDataRows :=
  actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_nonDegenerateMissingTopologyFactsTarget
      h)

/-- Choose W28 source-with-length rows from the strong actual-cycle target by
projecting each actual-cycle datum to the matching source-with-length package. -/
def outerBoundaryCoreSourceWithLengthRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  outerBoundaryCoreSourceWithLengthRowsOfActualOuterBoundaryCycleDataRows
    (actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)

/-- Choose W28 source-with-length rows from the exact nondegenerate topology
target. -/
def outerBoundaryCoreSourceWithLengthRowsOfExactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  outerBoundaryCoreSourceWithLengthRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
      h)

/-- Choose W28 source-with-length rows from nondegenerate missing-topology
facts. -/
def outerBoundaryCoreSourceWithLengthRowsOfNondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  outerBoundaryCoreSourceWithLengthRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_nonDegenerateMissingTopologyFactsTarget
      h)

theorem remainingActualOuterBoundaryCycleTheoremTargetOfActualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  fun C hmin => Nonempty.intro (rows C hmin)

theorem minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_actualOuterBoundaryCycleDataRows :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget <->
      Nonempty MinimalFailureActualOuterBoundaryCycleDataRows := by
  constructor
  case mp =>
    intro h
    exact
      Nonempty.intro
        (actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
          h)
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact
          remainingActualOuterBoundaryCycleTheoremTargetOfActualOuterBoundaryCycleDataRows
            rows

theorem nonempty_minimalFailureActualOuterBoundaryCycleDataRows_of_exactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget) :
    Nonempty MinimalFailureActualOuterBoundaryCycleDataRows :=
  Nonempty.intro
    (actualOuterBoundaryCycleDataRowsOfExactActualTopologyFieldsTarget h)

theorem nonempty_minimalFailureActualOuterBoundaryCycleDataRows_of_nondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    Nonempty MinimalFailureActualOuterBoundaryCycleDataRows :=
  Nonempty.intro
    (actualOuterBoundaryCycleDataRowsOfNondegenerateMissingTopologyFactsTarget
      h)

theorem minimalFailureExactActualTopologyFieldsTarget_iff_nonempty_actualOuterBoundaryCycleDataRows :
    MinimalFailureExactActualTopologyFieldsTarget <->
      Nonempty MinimalFailureActualOuterBoundaryCycleDataRows :=
  Iff.trans
    minimalFailureExactActualTopologyFieldsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget
    minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_actualOuterBoundaryCycleDataRows

theorem minimalFailureNondegenerateMissingTopologyFactsTarget_iff_nonempty_actualOuterBoundaryCycleDataRows :
    MinimalFailureNondegenerateMissingTopologyFactsTarget <->
      Nonempty MinimalFailureActualOuterBoundaryCycleDataRows :=
  Iff.trans
    minimalFailureNondegenerateMissingTopologyFactsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget
    minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_actualOuterBoundaryCycleDataRows

theorem minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_outerBoundaryCoreSourceWithLengthRows :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget <->
      Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows := by
  constructor
  case mp =>
    intro h
    exact
      Nonempty.intro
        (outerBoundaryCoreSourceWithLengthRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
          h)
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact
          remainingActualOuterBoundaryCycleTheoremTargetOfActualOuterBoundaryCycleDataRows
            (actualOuterBoundaryCycleDataRowsOfOuterBoundaryCoreSourceWithLengthRows
              rows)

theorem nonempty_minimalFailureOuterBoundaryCoreSourceWithLengthRows_of_exactActualTopologyFieldsTarget
    (h : MinimalFailureExactActualTopologyFieldsTarget) :
    Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  Nonempty.intro
    (outerBoundaryCoreSourceWithLengthRowsOfExactActualTopologyFieldsTarget
      h)

theorem nonempty_minimalFailureOuterBoundaryCoreSourceWithLengthRows_of_nondegenerateMissingTopologyFactsTarget
    (h : MinimalFailureNondegenerateMissingTopologyFactsTarget) :
    Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  Nonempty.intro
    (outerBoundaryCoreSourceWithLengthRowsOfNondegenerateMissingTopologyFactsTarget
      h)

theorem minimalFailureExactActualTopologyFieldsTarget_iff_nonempty_outerBoundaryCoreSourceWithLengthRows :
    MinimalFailureExactActualTopologyFieldsTarget <->
      Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  Iff.trans
    minimalFailureExactActualTopologyFieldsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget
    minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_outerBoundaryCoreSourceWithLengthRows

theorem minimalFailureNondegenerateMissingTopologyFactsTarget_iff_nonempty_outerBoundaryCoreSourceWithLengthRows :
    MinimalFailureNondegenerateMissingTopologyFactsTarget <->
      Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows :=
  Iff.trans
    minimalFailureNondegenerateMissingTopologyFactsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget
    minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_outerBoundaryCoreSourceWithLengthRows

/-- Choose exact S2 extracted boundary/enclosure rows from the strong
remaining actual-cycle target. -/
def minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfActualOuterBoundaryCycleDataRows
    (actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)

theorem minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_extractedSimpleCyclicOuterBoundaryEnclosureRows :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget <->
      Nonempty MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows := by
  constructor
  case mp =>
    intro h
    exact
      Nonempty.intro
        (minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
          h)
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact
          minimalFailureRemainingActualCycleTarget_of_exactActualTopologyFieldsTarget
            (minimalFailureExactActualTopologyFieldsTarget_of_extractedSimpleCyclicOuterBoundaryEnclosureRows
              rows)

theorem nonempty_minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows_iff_outerBoundaryCoreSourceWithLengthRows :
    Nonempty MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows <->
      Nonempty MinimalFailureOuterBoundaryCoreSourceWithLengthRows := by
  constructor
  case mp =>
    intro h
    have htarget :
        MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
      minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_extractedSimpleCyclicOuterBoundaryEnclosureRows.2
        h
    exact
      minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_iff_nonempty_outerBoundaryCoreSourceWithLengthRows.1
        htarget
  case mpr =>
    intro h
    cases h with
    | intro rows =>
        exact
          Nonempty.intro
            (minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRowsOfOuterBoundaryCoreSourceWithLengthRows
              rows)

theorem nonempty_minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows_of_outerBoundaryCoreSourceWithLengthTarget
    (h : MinimalFailureOuterBoundaryCoreSourceWithLengthTarget) :
    Nonempty MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows :=
  nonempty_minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows_iff_outerBoundaryCoreSourceWithLengthRows.2
    (nonempty_minimalFailureOuterBoundaryCoreSourceWithLengthRows_of_target h)

theorem minimalFailureOuterBoundaryCoreSourceWithLengthTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget :
    MinimalFailureOuterBoundaryCoreSourceWithLengthTarget <->
      MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact
      (OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSourceWithLength_iff_remainingActualOuterBoundaryCycleTheorem
        (C := C)).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact
      (OuterBoundaryCoreConstructionW28.nonempty_outerBoundaryCoreSourceWithLength_iff_remainingActualOuterBoundaryCycleTheorem
        (C := C)).2 (h C hmin)

theorem minimalFailureRemainingActualCycleTarget_of_outerBoundaryCoreSourceWithLengthTarget
    (h : MinimalFailureOuterBoundaryCoreSourceWithLengthTarget) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  minimalFailureOuterBoundaryCoreSourceWithLengthTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget.1
    h

theorem minimalFailureOuterBoundaryCoreSourceWithLengthTarget_of_remainingActualCycleTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureOuterBoundaryCoreSourceWithLengthTarget :=
  minimalFailureOuterBoundaryCoreSourceWithLengthTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget.2
    h

def actualSelectedTopologyRowsOfActualOuterBoundaryCycleDataRows
    (rows : MinimalFailureActualOuterBoundaryCycleDataRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin =>
    ActualSelectedTopologyDataW27.ActualSelectedTopologyData.ofOuterBoundaryCore
      (rows C hmin).core

def actualSelectedTopologyRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureActualSelectedTopologyRows :=
  actualSelectedTopologyRowsOfActualOuterBoundaryCycleDataRows
    (actualOuterBoundaryCycleDataRowsOfRemainingActualOuterBoundaryCycleTheoremTarget
      h)

theorem minimalFailureExactMathlibActualOuterBoundaryCycleSourceTarget_iff_nonDegenerateMissingTopologyFactsTarget :
    MinimalFailureExactMathlibActualOuterBoundaryCycleSourceTarget <->
      MinimalFailureNondegenerateMissingTopologyFactsTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact
      (exactMathlibCycleBlocker_iff_nonDegenerateMissingTopologyFactsSource
        C).1 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact
      (exactMathlibCycleBlocker_iff_nonDegenerateMissingTopologyFactsSource
        C).2 (h C hmin)

theorem minimalFailureRemainingActualCycleTarget_iff_w28FiniteNoncrossingSourceTarget :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget <->
      MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget := by
  constructor
  case mp =>
    intro h n C hmin
    exact
      (OuterBoundaryCoreConstructionW28.finiteNoncrossingActualOuterBoundaryCycleSource_iff_remainingActualOuterBoundaryCycleTheorem
        C).2 (h C hmin)
  case mpr =>
    intro h n C hmin
    exact
      (OuterBoundaryCoreConstructionW28.finiteNoncrossingActualOuterBoundaryCycleSource_iff_remainingActualOuterBoundaryCycleTheorem
        C).1 (h C hmin)

theorem minimalFailureRemainingActualCycleTarget_of_w28FiniteNoncrossingSourceTarget
    (h : MinimalFailureFiniteNoncrossingActualOuterBoundaryCycleSourceTarget) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget :=
  minimalFailureRemainingActualCycleTarget_iff_w28FiniteNoncrossingSourceTarget.2
    h

theorem minimalFailureRemainingActualCycleTarget_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget := by
  intro n C hmin
  exact
    remainingActualOuterBoundaryCycleTheorem_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem
      (h C hmin)

theorem minimalFailureNondegenerateMissingTopologyFactsTarget_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget
    (h : MinimalFailureExactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget) :
    MinimalFailureNondegenerateMissingTopologyFactsTarget :=
  minimalFailureNondegenerateMissingTopologyFactsTarget_of_remainingActualOuterBoundaryCycleTheoremTarget
    (minimalFailureRemainingActualCycleTarget_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget
      h)

def actualSelectedTopologyRowsOfJordanSourceRows
    (rows : MinimalFailureJordanSourceRows) :
    MinimalFailureActualSelectedTopologyRows :=
  fun C hmin => (rows C hmin).actualSelectedTopologyData

/-! ## Boundary-counting source fields -/

/-- Outer-boundary counting data over an explicit Jordan source. -/
structure BoundaryCountingSourceFields (C : _root_.UDConfig n) extends
    JordanSourceFields C where
  boundaryCounts : BoundaryCounting.BoundaryCounts
  boundaryAngleLowerBound : boundaryCounts.AngleLowerBound

namespace BoundaryCountingSourceFields

variable {C : _root_.UDConfig n}

def ofJordan
    (J : JordanSourceFields C)
    (counts : BoundaryCounting.BoundaryCounts)
    (hangle : counts.AngleLowerBound) :
    BoundaryCountingSourceFields C where
  faceBoundary := J.faceBoundary
  outerFace := J.outerFace
  outerFace_isOuter := J.outerFace_isOuter
  outerEnclosure := J.outerEnclosure
  boundaryCounts := counts
  boundaryAngleLowerBound := hangle

def ofW31Source
    (S : W31Source C)
    (counts : BoundaryCounting.BoundaryCounts)
    (hangle : counts.AngleLowerBound) :
    BoundaryCountingSourceFields C :=
  ofJordan (JordanSourceFields.ofW31Source S) counts hangle

def toCanonicalBoundaryCountHypotheses
    (B : BoundaryCountingSourceFields C) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses
      (CanonicalGraph C) where
  faceBoundary := B.faceBoundary
  counts := B.boundaryCounts
  angleLowerBound := B.boundaryAngleLowerBound

theorem boundaryAngleCountInequality
    (B : BoundaryCountingSourceFields C) :
    B.boundaryCounts.d5 + 2 * B.boundaryCounts.d6 +
        B.boundaryCounts.b + B.boundaryCounts.B + 6 <=
      B.boundaryCounts.d3 :=
  B.toCanonicalBoundaryCountHypotheses.boundaryAngleCountInequality

theorem boundaryAngleCountInequality_direct
    (B : BoundaryCountingSourceFields C) :
    B.boundaryCounts.d5 + 2 * B.boundaryCounts.d6 +
        B.boundaryCounts.b + B.boundaryCounts.B + 6 <=
      B.boundaryCounts.d3 :=
  BoundaryCounting.BoundaryCounts.boundary_angle_count_inequality
    B.boundaryCounts B.boundaryAngleLowerBound

theorem boundaryNegativeCountInequality
    (B : BoundaryCountingSourceFields C) :
    B.boundaryCounts.negativeCount + B.boundaryCounts.B + 6 <=
      B.boundaryCounts.d3 :=
  B.toCanonicalBoundaryCountHypotheses.boundaryNegativeCountInequality

theorem boundaryNegativeCountInequality_direct
    (B : BoundaryCountingSourceFields C) :
    B.boundaryCounts.negativeCount + B.boundaryCounts.B + 6 <=
      B.boundaryCounts.d3 :=
  BoundaryCounting.BoundaryCounts.boundary_negative_count_inequality
    B.boundaryCounts B.boundaryAngleLowerBound

end BoundaryCountingSourceFields

def ExactBoundaryCountingSourceBlocker
    (C : _root_.UDConfig n) : Prop :=
  Exists fun _ : JordanSourceFields C =>
    Exists fun counts : BoundaryCounting.BoundaryCounts =>
      counts.AngleLowerBound

theorem nonempty_boundaryCountingSourceFields_iff_exactBlocker
    (C : _root_.UDConfig n) :
    Nonempty (BoundaryCountingSourceFields C) <->
      ExactBoundaryCountingSourceBlocker C := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro B =>
        exact Exists.intro B.toJordanSourceFields
          (Exists.intro B.boundaryCounts B.boundaryAngleLowerBound)
  case mpr =>
    intro h
    cases h with
    | intro J hJ =>
        cases hJ with
        | intro counts hangle =>
            exact
              Nonempty.intro
                (BoundaryCountingSourceFields.ofJordan J counts hangle)

theorem boundaryCountingSource_implies_jordanSource
    {C : _root_.UDConfig n}
    (h : Nonempty (BoundaryCountingSourceFields C)) :
    Nonempty (JordanSourceFields C) := by
  cases h with
  | intro B =>
      exact Nonempty.intro B.toJordanSourceFields

theorem boundaryCountingSource_missing_if_no_planarBoundary
    (C : _root_.UDConfig n) :
    Not (Nonempty (JordanSourceFields C)) ->
      Not (Nonempty (BoundaryCountingSourceFields C)) := by
  intro hNoJordan hBoundary
  exact hNoJordan (boundaryCountingSource_implies_jordanSource hBoundary)

set_option linter.style.longLine false in
/-- W32 consumer for the compact strict-angular selected-neighbour S2 route.

The S2 cycle rows are supplied by the checked composer in
`S2SeededRawOrbitSource`: aligned K-split topology, selected carrier-neighbour
geometric rows, endpoint-only no-chord rows, and the local strict angular-order
row.  This theorem adds no new source premise beyond those rows and the
minimal-failure no-cut family. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_alignedK_geometricSelection_endpointOnly_strictOrder_20260520
    (aligned_K_split :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (endpoint_only :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall (a :
              {v : Fin m //
                v ∈
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                    C inputs})
            (x : Fin m),
            (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
              (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point x ∈
                  frontier (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows C inputs).exterior ->
                x =
                    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                      (geometricSelection C inputs) a).left.1 ∨
                  x =
                    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                      (geometricSelection C inputs) a).right.1)
    (strictOrder :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
            inputs
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.localAngularCarrierLeft
              (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_local_angular_source_of_inputs
                (C := C) (inputs := inputs)
                (geometricSelection C inputs) (endpoint_only C inputs)))
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.localAngularCarrierRight
              (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_local_angular_source_of_inputs
                (C := C) (inputs := inputs)
                (geometricSelection C inputs) (endpoint_only C inputs))))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_alignedK_geometricSelection_endpointOnly_strictOrder_20260520
      aligned_K_split geometricSelection endpoint_only strictOrder)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the endpoint-free finite-drawing aligned K-split route.

This is the compact source-facing surface after pruning the all-adjacent
endpoint shortcut: finite-drawing aligned K-split, selected carrier-neighbour
geometric rows, and the local point-third-germ row produce S2 cycle rows via
fixed-side local-sector rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingAlignedK_geometricSelection_pointThirdGerm_20260520
    (aligned_K_split :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (pointThirdGermRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall (a :
              {v : Fin m //
                v ∈
                  _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                    C inputs})
            (ε : Real) (q : PlanarInterface.Point) (x : Fin m),
            q ∈ Metric.ball
                ((_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1) ε ->
              q ∈ frontier
                  (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorComponentRows C inputs).exterior ->
                (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).Adj a.1 x ->
                  q ∈
                    _root_.ErdosProblems1066.Swanepoel.FinitePlaneDrawing.vertexIncidentGermW3
                      C a.1 x ε ->
                    q ≠
                        (_root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.canonicalGraph C).point a.1 ->
                      x ≠
                          (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                            (geometricSelection C inputs) a).left.1 ->
                        x ≠
                            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              (geometricSelection C inputs) a).right.1 ->
                          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeGraphVertexPointAngularBetween C a.1
                            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              (geometricSelection C inputs) a).left.1
                            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.unboundedFrontierCarrierNeighborPairRows_of_geometricSelectionInputSource
                              (geometricSelection C inputs) a).right.1 q)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_finiteDrawingAlignedK_geometricSelection_pointThirdGerm_20260520
      aligned_K_split geometricSelection pointThirdGermRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the trace-free finite-drawing aligned K-split plus
pointwise selected-neighbour input route.

The topology branch supplies a whole-frontier aligned K-split row, and the
local branch supplies the dependent selected-neighbour/cut/geometric row for
each actual exterior frontier vertex.  This avoids the compatibility-only
arbitrary trace-connected surfaces. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingAlignedK_selectedNeighborInput_localIncident_20260520
    (aligned_K_split :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_finiteDrawingAlignedK_selectedNeighborInput_localIncident_20260520
      aligned_K_split selectedInput)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the currently shortest finite-drawing selected-neighbour
source surface.

The topology residual is the finite-drawing nontrivial relative-clopen side
source, which strictly reduces to aligned K-split.  The local source residual is
the selected-neighbour exterior point-sector row, which strictly reduces to the
point-third-germ row consumed by the checked endpoint-free cycle-row composer.
This theorem adds no final boundary-cycle premise, endpoint-only/no-chord row,
induced frontier graph, arbitrary carrier/cycle, convex hull shortcut, or
synthetic enclosure. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNontrivialRelativeClopen_geometricSelection_localPointSector_20260520
    (nontrivial_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (pointSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborLocalExteriorPointSectorRows
            (C := C) (inputs := inputs) (geometricSelection C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingAlignedK_geometricSelection_pointThirdGerm_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finiteDrawingUnboundedComplementFrontierAlignedKSplit_of_finiteDrawing_nontrivialRelativeClopenKSide
      nontrivial_side)
    geometricSelection
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_pointThirdGerm_source_of_selectedNeighbor_localPointSector
      (C := C) (inputs := inputs)
        (geometricSelection C inputs) (pointSectorRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer using the current named S2 source leaves.

This theorem composes only checked strict reductions: the finite-drawing
topology source is supplied from the Janiszewski/boundary-bumping leaf, and the
geometric-selection input source is supplied from selected carrier-neighbour
geometric-order rows.  The remaining local source is the selected-neighbour
point-sector row. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_selectedNeighborOrder_localPointSector_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (selectedOrderRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (pointSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborLocalExteriorPointSectorRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_selected_neighbor_geometric_source_replacement
              (C := C) (inputs := inputs) (selectedOrderRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNontrivialRelativeClopen_geometricSelection_localPointSector_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_20260520_finite_nontrivial_relative_clopen_side_source
      janiszewski)
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_selected_neighbor_geometric_source_replacement_family
      selectedOrderRows)
    pointSectorRows
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the safe selected-neighbour dependent source route.

This is the current non-chord S2 surface after the selected-neighbour source is
kept as one dependent package: selected carrier-neighbour rows and their
genuine sorted outgoing-dart order are produced together, and the local-radius
incident-germ theorem supplies the local sector rows internally. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_selectedNeighborDependent_safeLocalIncident_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (selectedSource :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderSource
            (C := C) inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_finiteDrawingNontrivialRelativeClopen_selectedNeighborGeometricOrder_localIncident_20260520
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_20260520_finite_nontrivial_relative_clopen_side_source
        janiszewski)
      (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_family_of_dependentSource
        selectedSource))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the pointwise selected-neighbour input source form.

This exposes the current smallest local S2 source surface to W32: for each
frontier carrier vertex, the proof must select the two actual frontier-carrier
edges, the third-neighbour cut residual, and their adjacent genuine geometric
outgoing-list positions in one pointwise row. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_selectedNeighborInput_safeLocalIncident_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_finiteDrawingNontrivialRelativeClopen_selectedNeighborInput_localIncident_20260520
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_20260520_finite_nontrivial_relative_clopen_side_source
        janiszewski)
      selectedInput)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the relative-clopen planar-continuum form of the
pointwise selected-neighbour input source.

This is the current compact S2 work surface: the topology branch supplies the
one-sided relative-clopen source, and the local branch supplies one dependent
row per unbounded-frontier vertex containing the selected frontier incidences,
third-neighbour cut residual, and genuine sorted outgoing-list adjacent index
row for the same selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedNeighborInput_localIncident_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_selectedNeighborInput_localIncident_20260520
      relative_side selectedInput)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the boundary-free geometric-angular local source form.

This is the local-source version of the current support route: the S2 side
provides actual selected frontier germs, their genuine sorted outgoing-list
consecutive row, and the local third-germ exclusion; the selected-neighbour
input rows are then obtained by the checked eraser in
`S2LocalTwoGermAssembly`. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_boundaryFreeGeometricAngular_safeLocalIncident_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (boundaryFree :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.BoundaryFreeLocalSectorGeometricAngularSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_finiteDrawingNontrivialRelativeClopen_boundaryFreeGeometricAngular_localIncident_20260520
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_20260520_finite_nontrivial_relative_clopen_side_source
        janiszewski)
      boundaryFree)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer with the selected-neighbour geometric source split into its
two current leaves: selected cut-partition rows and genuine sorted outgoing-dart
geometric order rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_selectedNeighborSplit_localPointSector_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
            (selectedRows C inputs))
    (pointSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborLocalExteriorPointSectorRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_selected_neighbor_geometric_source_replacement
              (C := C) (inputs := inputs)
              (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_codex_20260520_selected_neighbor_geometric_order_source_split
                (C := C) (inputs := inputs)
                (selectedRows C inputs) (geometricRows C inputs))))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_selectedNeighborOrder_localPointSector_20260520
    janiszewski
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_codex_20260520_selected_neighbor_geometric_order_source_split_family
      selectedRows geometricRows)
    pointSectorRows
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer using the safe local-radius selected-neighbour S2 route.

This is the current preferred consumer over the older `localPointSector`
surface: the S2 side gets its local sectors from
`SelectedNeighborThirdGermLocalExteriorPointSectorRows`, internally supplied by
the checked local-radius selected incident-germ theorem.  No arbitrary-radius
point-sector premise, all-adjacent endpoint/no-chord row, final boundary-cycle
row, induced frontier graph, arbitrary carrier/cycle, or synthetic enclosure is
introduced. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNontrivialRelativeClopen_selectedNeighborOrder_safeLocalThirdGerm_20260520
    (nontrivial_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide)
    (selectedOrderRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_finiteDrawingNontrivialRelativeClopen_selectedNeighborOrder_safeLocalThirdGerm_20260520
      nontrivial_side selectedOrderRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the planar-continuum preconnected frontier form of the
safe selected-neighbour route.

The topology side is the direct standard theorem that the unbounded complement
frontier of a compact connected planar drawing is preconnected; the checked
finite-drawing adapter turns that into the aligned-split source consumed by
the selected-neighbour S2 composer. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_preconnected_selectedNeighborOrder_safeLocalThirdGerm_20260520
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedOrderRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_preconnected_selectedNeighborOrder_safeLocalThirdGerm_20260520
      frontier_preconnected selectedOrderRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the actual boundary-sector selected-neighbour route.

The source rows stay tied to the same endpoint-free actual boundary cycle:
frontier equivalence, genuine boundary geometric rotation order, and actual
exterior-sector rows are erased by Carson's selected-geometric source-row
adapter, then consumed by the checked preconnected selected-neighbour
safe-local-third-germ route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_preconnected_actualBoundarySector_selectedOrder_safeLocalThirdGerm_20260520
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierPreconnected)
    (actualRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualBoundaryCycleFrontierEquivalenceRows
            C inputs)
    (geometric_order :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall k : Fin (actualRows C inputs).boundary.length,
            _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow
              C (actualRows C inputs).boundary k)
    (sectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall k : Fin (actualRows C inputs).boundary.length,
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryVertexExteriorSectorRowsAt
              inputs (actualRows C inputs).boundary k)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_preconnected_selectedNeighborOrder_safeLocalThirdGerm_20260520
    frontier_preconnected
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows
        (C := C) (inputs := inputs) (actualRows C inputs)
        (geometric_order C inputs) (sectorRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the compact valid S2 handoff below the selected-neighbour
route.

The two remaining source branches are explicit: planar-continuum
preconnectedness of the unbounded complement frontier, and actual carrier
neighbour/geometric-selection rows for the same selected frontier edges. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_preconnected_geometricNeighborSelection_20260520
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierPreconnected)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_preconnected_geometricNeighborSelection_20260520
      frontier_preconnected geometricRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the direct preconnected topology leaf and the bundled
actual carrier/geometric-selection input source.

This is the compact two-leaf S2 handoff after the preconnected reducer: the
topology branch supplies preconnectedness of the actual unbounded exterior
frontier, and the local branch supplies selected carrier neighbour pairs plus
their genuine geometric selection rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_preconnected_geometricSelectionInputSource_20260520
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierPreconnected)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_geometricSelectionInputSource_20260520
        (C := C) inputs frontier_preconnected
        (geometricSelection C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer with the selected-neighbour geometric source split into selected
cut-partition rows and genuine sorted outgoing-dart geometric order, routed
through the safe local-radius third-germ S2 composer. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_selectedNeighborSplit_safeLocalThirdGerm_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
            (selectedRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNontrivialRelativeClopen_selectedNeighborOrder_safeLocalThirdGerm_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_20260520_finite_nontrivial_relative_clopen_side_source
      janiszewski)
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_codex_20260520_selected_neighbor_geometric_order_source_split_family
      selectedRows geometricRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current strict split of both live S2 leaves.

The topology branch is the bounded-subcontinuum form below Janiszewski, and
the local branch is selected exterior-neighbour cut-partition rows together
with genuine sorted outgoing-dart index rows for the same selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumForcesBounded_selectedNeighborCutPartitionIndex_localIncident_20260520
    (subcontinuum_forces_bounded :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
            (selectedRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_subcontinuumForcesBounded_selectedNeighborCutPartitionIndex_localIncident_20260520
      subcontinuum_forces_bounded selectedRows indexRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the relative-clopen planar-continuum form of the current
strict S2 split.

This is the post-boundedness topology surface: the planar branch supplies the
one-sided relative-clopen `K`-side theorem, and the local branch supplies
selected cut-partition rows plus genuine sorted outgoing-list index rows for
the same selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedNeighborCutPartitionIndex_localIncident_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
            (selectedRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_selectedNeighborCutPartitionIndex_localIncident_20260520
      relative_side selectedRows indexRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer exposing the selected-edge-pair local source over the live
relative-clopen topology branch.

This avoids the compatibility-only frontier-trace surface: the topology branch
is the one-sided relative-clopen planar-continuum theorem, while the local
branch is the selected incident-edge pair source plus genuine sorted-list
index rows for the selected heads derived from that same source. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let cutSource :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
      relative_side selectedEdgeRows indexRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the selected-edge/index route from actual carrier
neighbour-pair rows.

The local branch starts with the concrete unbounded-frontier carrier
neighbour-pair row at each frontier vertex.  These rows determine the selected
incident-edge pair source, and the matching input is the genuine selected
geometric-order/index row for the selected heads produced by that same route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_neighborPairRows_indexRows_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a :
            {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairAt
              inputs a)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedEdgeRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
            (C := C) inputs (neighborRows C inputs)
        let cutSource :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedEdgeRows
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
    relative_side
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_local_selected_edge_pair_source_family_of_neighborPairRows
      neighborRows)
    (fun C inputs => by
      simpa using indexRows C inputs)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current sharp residual split.

The topology branch is the Janiszewski/boundary-bumping relative-clopen source.
The local branch is the actual selected-edge/no-third-germ source, which
erases to selected incident edge-pair rows.  The geometric branch is the
pointwise genuine selected-head geometric-order source for the exact selected
heads produced by that local branch. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_localSelectedNoThird_graphVertexGeometricOrder_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (localSource :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSelectedNoThirdGermSource
            C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_edge_pair_source
              (C := C) (inputs := inputs) (localSource C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_relative_clopen_topology_source
      janiszewski)
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_edge_pair_source_family
      localSource)
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_index_geometric_source
      (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_edge_pair_source_family
        localSource)
      (fun C inputs => by
        simpa [
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_edge_pair_source_family]
          using geometricRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current reduced S2 source split.

The topology source is the Janiszewski/boundary-bumping relative-clopen side.
The local source is the actual selected-edge/no-third-germ row, which erases to
neighbour-pair rows and then selected incident-edge pairs.  The angular source
is genuine selected geometric-order rows for those same selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_localSelectedNoThird_geometricOrderRows_20260520
    (janiszewski :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide)
    (localSource :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSelectedNoThirdGermSource
            C inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let neighborRows :
            forall {k : Nat} (D : _root_.UDConfig k)
              (inputsD :
                JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
                  D),
                forall a :
                  {v : Fin k //
                    v ∈
                      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                        D inputsD},
                    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairAt
                      inputsD a :=
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_carrier_neighbor_pair_source_family
            localSource
        let selectedEdgeRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
            (C := C) inputs (neighborRows C inputs)
        let cutSource :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedEdgeRows
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
          selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  intro n C hmin
  let relativeSide :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierRelativeClopenKSide_of_nontrivialRelativeClopenKSide
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_nontrivial_relative_clopen_source
        janiszewski)
  let neighborRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a :
            {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairAt
                inputs a :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_carrier_neighbor_pair_source_family
      localSource
  let selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs :=
    _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_local_selected_edge_pair_source_family_of_neighborPairRows
      neighborRows
  exact
    (minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
      relativeSide selectedEdgeRows
      (fun {m} D inputs =>
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometricOrderRows
          (C := D) (inputs := inputs) (selectedEdgeRows D inputs)
          (by
            simpa [neighborRows, selectedEdgeRows] using
              geometricRows D inputs))
      noCutRows) C hmin

set_option linter.style.longLine false in
/-- W32 reducer for the currently lowered S2 leaves.

This wrapper composes the live Janiszewski relative-clopen source, the local
selected/no-third source, and the selected-head geometric-order source into
the existing W32 handoff.  The S1 no-cut rows remain the only graph-minimality
input at this layer. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiRelativeClopen_localSelectedNoThird_selectedHeadGeometricOrder_20260520
    (no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a : {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
              inputs a)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_local_selected_no_third_source
              (C := C) (inputs := inputs) (localSectorRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_localSelectedNoThird_graphVertexGeometricOrder_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_janiszewski_relative_clopen_source
      no_subcontinuum)
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_local_selected_no_third_source
        (C := C) (inputs := inputs) (localSectorRows C inputs))
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_order_source
        (C := C) (inputs := inputs)
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_local_selected_no_third_source
          (C := C) (inputs := inputs) (localSectorRows C inputs))
        (angularRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the lower selected-head geometric-order residual on the
local selected/no-third route.

The local-sector rows produce the selected/no-third source, and the geometric
rows are already stated for the exact selected heads of that route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiRelativeClopen_localSector_selectedHeadGeometricRows_20260520
    (no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a : {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
              inputs a)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_order_row_source_for_localSelectedNoThirdGermRoute
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_local_selected_no_third_source
              (C := C) (inputs := inputs) (localSectorRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiRelativeClopen_localSelectedNoThird_selectedHeadGeometricOrder_20260520
    no_subcontinuum localSectorRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute_of_graph_vertex_geometric_order_rows
        (C := C) (inputs := inputs)
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_local_selected_no_third_source
          (C := C) (inputs := inputs) (localSectorRows C inputs))
        (geometricRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the route-specific selected-head angular residual.

The local selected-edge pair rows determine the selected cut rows; the
route-specific angular no-between source then produces the genuine sorted-list
index rows for those exact selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_angularNoBetween_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
    relative_side selectedEdgeRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute
      (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
      (angularRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the smallest current selected-edge angular residual.

The local branch supplies selected incident-edge pairs and proves that no
outgoing unit-distance dart lies strictly between the exact selected heads in
the genuine geometric order.  That residual is erased internally to the
selected-head angular rows and then to the sorted-list index rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_noInterveningOutgoing_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (outgoingRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
    relative_side selectedEdgeRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_no_intervening_outgoing_dart
        (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        (outgoingRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the selected-edge route with the topology leaf already
lowered to the whole-frontier no-subcontinuum obstruction.

The local source names the selected exterior-edge pair at each unbounded
frontier vertex, and the angular source is the genuine outgoing-list
no-between row for exactly those selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_noSubcontinuum_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    (no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_noInterveningOutgoing_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_whole_frontier_relative_clopen_source
      no_subcontinuum)
    selectedEdgeRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
        (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        (listRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current live S2 split.

The topology branch is the whole-frontier crossing-subcontinuum boundedness
source.  The local carrier branch is the ambient deleted-graph unreachable
selected-neighbour source.  The angular branch is the no-intervening
outgoing-dart source for the exact heads selected by that local branch. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_crossingBounded_unreachable_noIntervening_20260520
    (crossing_forces_bounded :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (unreachableRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
            C inputs)
    (outgoingRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute
          (C := C) (inputs := inputs)
          (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
            (C := C) inputs
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierNeighborPairRows_of_unreachableAfterDeleteInputSource
              (C := C) (inputs := inputs) (unreachableRows C inputs))))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_noInterveningOutgoing_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_whole_frontier_relative_clopen_source
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_whole_frontier_no_subcontinuum_worker
        crossing_forces_bounded))
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
        (C := C) inputs
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierNeighborPairRows_of_unreachableAfterDeleteInputSource
          (C := C) (inputs := inputs) (unreachableRows C inputs)))
    outgoingRows
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current post-reduction S2 leaves.

This composes Nash's crossing relative-clopen reduction, Dirac's
local-sector-to-unreachable reduction, and Kierkegaard's genuine outgoing-list
no-between reduction into the existing W32 handoff.  The selected heads remain
those produced by the local-sector rows through the deleted-neighbour route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_crossingRelativeClopen_localSector_geometricOutgoingListNoBetween_20260520
    (relative_crossing_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumRelativeClopenKSide)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        forall a : {v : Fin m //
            v ∈
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                C inputs},
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
            inputs a)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute
          (C := C) (inputs := inputs)
          (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_unreachable_neighbor_source_worker
            (C := C) (inputs := inputs) (localSectorRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_crossingBounded_unreachable_noIntervening_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_crossing_bounded_source_worker
      relative_crossing_side)
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_unreachable_neighbor_source_worker
        (C := C) (inputs := inputs) (localSectorRows C inputs))
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_unreachableAfterDeleteRoute_of_geometric_outgoing_list_no_between_source
        (C := C) (inputs := inputs)
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_unreachable_neighbor_source_worker
          (C := C) (inputs := inputs) (localSectorRows C inputs))
        (listRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current sharpest checked S2 leaf split.

The topology branch is the Janiszewski/boundary-bumping boundedness theorem.
The local branch is the selected incident exterior-edge pair source, and the
angular branch is the genuine sorted outgoing-list consecutive-index row for
the same selected heads.  The proof only composes the checked reducers above;
it introduces no new facade, final-cycle row, induced-frontier graph, or
endpoint shortcut. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumForcesBounded_selectedEdgePair_indexRows_20260520
    (subcontinuum_forces_bounded :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedEdgeRowsHere :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
              inputs :=
          selectedEdgeRows C inputs
        let cutSource :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedEdgeRowsHere
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_crossingRelativeClopen_localSector_geometricOutgoingListNoBetween_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_crossing_relative_clopen_worker
      subcontinuum_forces_bounded)
    (fun C inputs =>
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_boundaryFreeLocalNoThirdGermSource_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) (selectedEdgeRows C inputs)).toLocalSectorRows)
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute_of_selected_index_rows
        (C := C) (inputs := inputs)
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_unreachable_neighbor_source_worker
          (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_boundaryFreeLocalNoThirdGermSource_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)).toLocalSectorRows)
        (by
          simpa using indexRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the frontier-trace-connected topology reduction and the
strict selected-neighbour cut/index local split.

The topology branch is the smaller trace-connected source now feeding the
relative-clopen K-side theorem; the local branch keeps selected carrier
cut-partition rows separate from genuine sorted outgoing-list index rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedNeighborCutPartitionIndex_localIncident_20260520
    (frontier_trace_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceConnected)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
            (selectedRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedNeighborCutPartitionIndex_localIncident_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_agent_20260520_planar_continuum_boundary_relativeClopenKSide
      frontier_trace_connected)
    selectedRows indexRows noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the frontier-trace-connected topology reduction and the
pointwise selected-neighbour/cut/geometric local input source.

This is the compact current source surface after the latest reductions:
frontier trace connectedness for the planar topology branch, and one
dependent selected-neighbour row per unbounded-frontier vertex carrying both
the selected cut data and the genuine sorted-list index data. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedNeighborInput_localIncident_20260520
    (frontier_trace_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceConnected)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedNeighborCutPartitionIndex_localIncident_20260520
    frontier_trace_connected
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
        (C := C) (inputs := inputs) (selectedInput C inputs))
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
        (C := C) (inputs := inputs) (selectedInput C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer exposing the current selected-edge-pair local source.

The local selected incident-edge pair row supplies the carrier cut-partition
input source through the checked local-radius reducer.  The only separate
angular input is the genuine sorted outgoing-list index row for the selected
heads produced from that same source. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedEdgePair_indexRows_20260520
    (frontier_trace_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceConnected)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (indexRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let cutSource :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
          selectedRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  refine
    minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedNeighborCutPartitionIndex_localIncident_20260520
      frontier_trace_connected ?_ ?_ noCutRows
  · intro m C inputs
    let cutSource :
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs :=
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
    exact
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
  · intro m C inputs
    let cutSource :
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
          C inputs :=
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
    let selectedRows :
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
          inputs :=
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    change
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows
    simpa [cutSource, selectedRows] using indexRows C inputs

set_option linter.style.longLine false in
/-- W32 consumer for the current input-facing S2 split.

The topology branch is the one-sided relative-clopen planar-continuum source.
The local branch is the actual carrier cut-partition input source plus honest
selected-head angular no-between rows, erased internally to the checked
selected-neighbour cycle-row route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_neighborPairCutPartition_angularNoBetween_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (cutSource :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
            C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) (cutSource C inputs))
        forall a : {v : Fin m //
            v ∈
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                C inputs},
          _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.GraphVertexAngularNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_neighborPairCutPartition_angularNoBetween_20260520
      relative_side cutSource angularRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the bundled selected-carrier/geometric-selection local
source.

The topology branch is the one-sided relative-clopen planar-continuum source.
The local branch gives, at each actual unbounded-frontier carrier vertex, the
two selected frontier incidences and their genuine consecutive positions in
the geometric outgoing-dart list. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_geometricSelectionInputSource_20260520
    (relative_side :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_geometricSelectionInputSource_20260520
      relative_side geometricSelection)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current two-leaf S2 source split.

The topology leaf is the component-indexed Janiszewski no-subcontinuum
obstruction.  The local/geometric leaf is the bundled actual carrier
geometric-selection input source, which supplies the selected carrier
neighbour pairs and genuine geometric order rows together. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_geometricSelectionInputSource_20260520
    (janiszewski_no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiNoSubcontinuum_geometricSelectionInputSource_20260520
      janiszewski_no_subcontinuum geometricSelection)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current shortest safe S2 route with the local leaf
strictly reduced to compact actual carrier/geometric-neighbour rows.

The compact row carries the selected `unboundedFrontierEdgeSet` heads and the
genuine consecutive sorted outgoing-dart indices together; the existing eraser
then supplies the bundled geometric-selection input source without introducing a
second selected-head family. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_geometricNeighborSelectionRows_20260520
    (janiszewski_no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_geometricSelectionInputSource_20260520
    janiszewski_no_subcontinuum
    (fun C inputs =>
      (geometricRows C inputs).toGeometricSelectionInputSource)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current boundary/sector S2 source split.

The topology branch is reduced to the component-avoidance Janiszewski row.
The local branch keeps the honest actual boundary rows, geometric `faceSucc`
rows, boundary orientation, and independent local-sector rows; incident
frontier-edge completeness is supplied by the checked local-sector bridge
before erasing to the compact geometric-selection input source. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_actualBoundary_faceSucc_localSectorRows_20260520
    (component_avoidance :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance)
    (actualRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualBoundaryCycleFrontierEquivalenceRows
            C inputs)
    (faceSuccRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceCycleFaceSuccRows C
            (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.geometricUnitDistanceRotationSystem
              C)
            (actualRows C inputs).boundary)
    (boundary_orientation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        forall k : Fin (actualRows C inputs).boundary.length,
          _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
              (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
                C)
              ((actualRows C inputs).boundary.vertex k)
              ((actualRows C inputs).boundary.vertex
                (_root_.ErdosProblems1066.Swanepoel.PlanarInterface.cyclicPred
                  (actualRows C inputs).boundary.length_pos k)) <
            _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
              (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
                C)
              ((actualRows C inputs).boundary.vertex k)
              ((actualRows C inputs).boundary.vertex
                (_root_.ErdosProblems1066.Swanepoel.PlanarInterface.cyclicSucc
                  (actualRows C inputs).boundary.length_pos k)))
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a : {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
              inputs a)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_geometricSelectionInputSource_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_dyn_20260520_topology_janiszewski_leaf
      component_avoidance)
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_geometricSelectionInputSource_of_actualBoundaryRows_faceSucc_localSectorRows_20260520
        (C := C) (inputs := inputs) (actualRows C inputs)
        (faceSuccRows C inputs) (boundary_orientation C inputs)
        (localSectorRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the actual-boundary/local-sector route with the standard
planar-continuum connected-frontier topology source.

This is the sharper finite-topology handoff: connectedness of unbounded
complement frontiers supplies the preconnected topology branch, while the
same actual boundary, genuine `faceSucc` rows, boundary orientation, and
pointwise local-sector rows supply the compact geometric-selection source. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_actualBoundary_faceSucc_localSectorRows_20260520
    (frontier_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierConnected)
    (actualRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualBoundaryCycleFrontierEquivalenceRows
            C inputs)
    (faceSuccRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete.MinimalFailureTopology.UnitDistanceCycleFaceSuccRows C
            (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.geometricUnitDistanceRotationSystem
              C)
            (actualRows C inputs).boundary)
    (boundary_orientation :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        forall k : Fin (actualRows C inputs).boundary.length,
          _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
              (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
                C)
              ((actualRows C inputs).boundary.vertex k)
              ((actualRows C inputs).boundary.vertex
                (_root_.ErdosProblems1066.Swanepoel.PlanarInterface.cyclicPred
                  (actualRows C inputs).boundary.length_pos k)) <
            _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphDartArg
              (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.canonicalGeometricGraph
                C)
              ((actualRows C inputs).boundary.vertex k)
              ((actualRows C inputs).boundary.vertex
                (_root_.ErdosProblems1066.Swanepoel.PlanarInterface.cyclicSucc
                  (actualRows C inputs).boundary.length_pos k)))
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a : {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
              inputs a)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_preconnected_geometricSelectionInputSource_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierPreconnected_of_connected
      frontier_connected)
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_geometricSelectionInputSource_of_actualBoundaryRows_faceSucc_localSectorRows_20260520
        (C := C) (inputs := inputs) (actualRows C inputs)
        (faceSuccRows C inputs) (boundary_orientation C inputs)
        (localSectorRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- Package-form W32 consumer for the current actual-boundary S2 source.

The local S2 work now packages the actual boundary rows, genuine geometric
`faceSucc` rows, boundary orientation, and pointwise local-sector rows in
`ActualBoundaryFaceSuccLocalSectorRows`.  This wrapper exposes the true
remaining leaves without duplicating those four dependent arguments at every
call site. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_actualBoundaryPackage_20260520
    (frontier_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierConnected)
    (actualPackageRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualBoundaryFaceSuccLocalSectorRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_actualBoundary_faceSucc_localSectorRows_20260520
    frontier_connected
    (fun C inputs => (actualPackageRows C inputs).actualRows)
    (fun C inputs => (actualPackageRows C inputs).faceSuccRows)
    (fun C inputs => (actualPackageRows C inputs).boundary_orientation)
    (fun C inputs => (actualPackageRows C inputs).localSectorRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the connected-frontier plus pointwise local-sector route.

The concrete carrier route in `S2ExteriorBoundarySource` constructs the actual
boundary cycle from the connected frontier and the local two-sector rows, so
this wrapper exposes those two proof-owning leaves directly to W32. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_localSectorRows_20260520
    (frontier_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierConnected)
    (localSectorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          forall a : {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierLocalSectorRowsAt
              inputs a)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      S2_codex_20260520_unboundedExteriorFrontierCycleRows_of_connectedFrontier_localSectorRows
        (C := C) inputs frontier_connected (localSectorRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- Package-form W32 consumer with the topology leaf reduced to the current
Janiszewski no-subcontinuum source.

This is the live compact S2 handoff after the connected-frontier theorem was
strictly reduced to `PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction`. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_actualBoundaryPackage_20260520
    (no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction)
    (actualPackageRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.ActualBoundaryFaceSuccLocalSectorRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_actualBoundaryPackage_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierConnected_of_janiszewskiNoSubcontinuumObstruction
      no_subcontinuum)
    actualPackageRows noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the selected raw-tail route through the
`ActualBoundaryFaceSuccLocalSectorRows` package.

This is the shortest package-form handoff from the selected/raw-orbit source
lane to the current connected-frontier W32 route.  The residuals stay honest:
connected frontier, selected raw-tail coverage, primitive repeated-tail cut
witnesses for that same selected orbit, nonwrap geometric successor rows, and
the standard no-cut rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_selectedRawTailCoverage_repeatedTailWitnesses_geometricSuccessorNonwrap_20260520
    (frontier_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierConnected)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
            inputs)
    (deleted_tail_witnesses :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let rows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            selectedRows C inputs
          forall {i j : Fin rows.O.period},
            i ≠ j ->
            (rows.O.dart i).tail = (rows.O.dart j).tail ->
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2RepeatedTailExteriorCutWitnessSource
                (inputs := inputs) rows.O i j)
    (successorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let rows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            selectedRows C inputs
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitGeometricSuccessorNonwrapRows
            rows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_actualBoundaryPackage_20260520
    frontier_connected
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.actualBoundaryFaceSuccLocalSectorRows_family_of_selectedRawTailCoverage_repeatedTailWitnesses_geometricSuccessorNonwrap_20260520
      selectedRows deleted_tail_witnesses successorRows)
    noCutRows

set_option linter.style.longLine false in
/-- Selected raw-tail package route with the topology leaf reduced to the
Janiszewski no-subcontinuum source.

The residuals are now exactly: the Janiszewski no-subcontinuum topology row,
selected raw-tail coverage, primitive repeated-tail witnesses for that same
selected orbit, nonwrap geometric successor rows, and S1 no-cut rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_selectedRawTailCoverage_repeatedTailWitnesses_geometricSuccessorNonwrap_20260520
    (no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
            inputs)
    (deleted_tail_witnesses :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let rows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            selectedRows C inputs
          forall {i j : Fin rows.O.period},
            i ≠ j ->
            (rows.O.dart i).tail = (rows.O.dart j).tail ->
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2RepeatedTailExteriorCutWitnessSource
                (inputs := inputs) rows.O i j)
    (successorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let rows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            selectedRows C inputs
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitGeometricSuccessorNonwrapRows
            rows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_selectedRawTailCoverage_repeatedTailWitnesses_geometricSuccessorNonwrap_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierConnected_of_janiszewskiNoSubcontinuumObstruction
      no_subcontinuum)
    selectedRows deleted_tail_witnesses successorRows noCutRows

set_option linter.style.longLine false in
/-- Selected raw-tail package route with the topology leaf exposed as the
crossing-subcontinuum boundedness source.

This is the current shortest honest S2 composer: the topology source is lowered
through the checked Janiszewski component-avoidance/connected-frontier reducers,
and the boundary source is the selected raw-tail package with repeated-tail
deleted-tail witnesses and genuine nonwrap successor rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_crossingSubcontinuumForcesBounded_selectedRawTailCoverage_repeatedTailWitnesses_geometricSuccessorNonwrap_20260520
    (crossing_forces_bounded :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
            inputs)
    (deleted_tail_witnesses :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let rows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            selectedRows C inputs
          forall {i j : Fin rows.O.period},
            i ≠ j ->
            (rows.O.dart i).tail = (rows.O.dart j).tail ->
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2RepeatedTailExteriorCutWitnessSource
                (inputs := inputs) rows.O i j)
    (successorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          let rows :
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
                inputs :=
            selectedRows C inputs
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitGeometricSuccessorNonwrapRows
            rows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_selectedRawTailCoverage_repeatedTailWitnesses_geometricSuccessorNonwrap_20260520
    ((_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_main_20260520_connected_frontier_source_leaf
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_janiszewski_component_avoidance_leaf
        crossing_forces_bounded)).1)
    selectedRows deleted_tail_witnesses successorRows noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the preconnected topology source and the selected-edge
outgoing-list local route.

This is the direct reduced form of the no-closed-separation handoff below:
the topology branch is the standard planar-continuum frontier preconnectedness
surface, and the local branch is the selected incident-edge pair route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_preconnected_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierPreconnected)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localSectorRows
        (C := C) inputs frontier_preconnected
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.localSectorRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520
          (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
          (listRows C inputs)))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the direct no-closed-separation topology leaf and the
selected-edge/outgoing-list local route.

This compatibility handoff first lowers the topology branch to the
preconnectedness surface above; the local branch then produces pointwise
local-sector rows from the selected incident frontier edges and genuine
outgoing-list no-between data for those same selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_planarNoClosedSeparation_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierNoClosedSeparation)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_preconnected_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierPreconnected_of_noClosedSeparation
      frontier_noClosedSeparation)
    selectedEdgeRows listRows
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the finite no-closed-separation topology leaf and the
selected-edge/outgoing-list local route.

This is the finite-drawing version of the selected-edge handoff above: the
topology branch stays on the actual embedded unit-edge drawing, while the
local branch is the selected `unboundedFrontierEdgeSet` carrier plus genuine
outgoing-list no-between data for those selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_localSectorRows
        (C := C) inputs frontier_noClosedSeparation
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.localSectorRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520
          (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
          (listRows C inputs)))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the finite no-closed-separation topology leaf and the
honest face-dart exterior carrier package.

This is the selected-carrier specialization of the previous theorem:
`FaceDartOrbitExteriorCarrierRows` supplies the actual selected
`unboundedFrontierEdgeSet` neighbour pair rows, while the list premise only
asserts genuine outgoing-list no-between rows for those selected heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_faceDartOrbitCarrier_geometricOutgoingListNoBetween_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (faceRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FaceDartOrbitExteriorCarrierRows
            C inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_selected_carrier_source
              (C := C) (inputs := inputs) (faceRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedEdgePair_geometricOutgoingListNoBetween_20260520
    frontier_noClosedSeparation
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_selected_carrier_source
        (C := C) (inputs := inputs) (faceRows C inputs))
    listRows noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the finite frontier-preconnectedness topology leaf and
the honest face-dart exterior carrier package.

This is the current reduced topology surface: preconnectedness of the actual
finite drawing unbounded-component frontier is first erased to the closed-piece
no-separation row, then the existing selected face-dart carrier route supplies
the S2 topology target. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingPreconnected_faceDartOrbitCarrier_geometricOutgoingListNoBetween_20260520
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierPreconnected)
    (faceRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FaceDartOrbitExteriorCarrierRows
            C inputs)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_selected_carrier_source
              (C := C) (inputs := inputs) (faceRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_faceDartOrbitCarrier_geometricOutgoingListNoBetween_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_frontierPreconnected
      frontier_preconnected)
    faceRows listRows noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the finite no-closed-separation topology leaf and the
face-dart carrier package with selected-head angular no-between rows.

This is parallel to the outgoing-list handoff, but accepts the lower geometric
source in angular no-between form.  The local assembly then packages those
same selected carrier heads as compact geometric-neighbour rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_faceDartOrbitCarrier_angularNoBetween_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (faceRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FaceDartOrbitExteriorCarrierRows
            C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_selected_carrier_source
              (C := C) (inputs := inputs) (faceRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRowsFamily_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
      frontier_noClosedSeparation
      (fun C inputs =>
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_codex_current_20260520_local_geometric_assembly_of_selectedEdgePairRoute_angularNoBetween
          (C := C) (inputs := inputs)
          (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_selected_carrier_source
            (C := C) (inputs := inputs) (faceRows C inputs))
          (angularRows C inputs)))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the finite frontier-preconnectedness topology leaf and the
face-dart carrier package with selected-head angular no-between rows.

This is the angular no-between analogue of the outgoing-list preconnected
handoff: preconnectedness is first lowered to finite drawing
no-closed-separation, then the selected face-dart carrier angular route
supplies the S2 topology target. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingPreconnected_faceDartOrbitCarrier_angularNoBetween_20260520
    (frontier_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierPreconnected)
    (faceRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FaceDartOrbitExteriorCarrierRows
            C inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_selected_carrier_source
              (C := C) (inputs := inputs) (faceRows C inputs)))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_faceDartOrbitCarrier_angularNoBetween_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_frontierPreconnected
      frontier_preconnected)
    faceRows angularRows noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the direct no-closed-separation topology leaf and the
bundled actual carrier/geometric-selection local source. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_planarNoClosedSeparation_geometricSelectionInputSource_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierNoClosedSeparation)
    (geometricSelection :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
            C inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumNoClosedSeparation_geometricSelectionInputSource_20260520
      frontier_noClosedSeparation geometricSelection)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the direct no-closed-separation topology leaf and compact
selected-carrier geometric-neighbour source rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_planarNoClosedSeparation_geometricNeighborSelectionRows_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierNoClosedSeparation)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumNoClosedSeparation_geometricNeighborSelectionRows_20260520
      frontier_noClosedSeparation geometricRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the finite no-closed-separation topology leaf and compact
selected-carrier geometric-neighbour source rows.

This is the narrow finite-topology S2 route: the topology branch is the actual
finite drawing no-closed-separation source, and the local branch is the compact
geometric-neighbour row family for the same `FinitePlanarOuterComponentInputs`.
-/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedExteriorFrontierCycleRowsFamily_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
      frontier_noClosedSeparation geometricRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for claim
`S2-codex-current-20260520-w32-selected-cut-angular-integration`.

The finite topology branch is the actual no-closed-separation source.  The
local branch keeps the selected cut-partition rows and pointwise genuine
selected-head angular no-between rows, then uses the compact geometric-neighbour
leaf to enter the existing short W32 route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_angularNoBetween_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (angularRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedRowsHere :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          selectedRows C inputs
        forall a : {v : Fin m //
            v ∈
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                C inputs},
          _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.GraphVertexAngularNoBetweenRows
            C a.1 (selectedRowsHere.selectedNeighborRows a).left
              (selectedRowsHere.selectedNeighborRows a).right)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
    frontier_noClosedSeparation
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_codex_current_20260520_compact_geometric_neighbor_source_leaf
        (C := C) (inputs := inputs) (selectedRows C inputs)
        (angularRows C inputs))
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer after the selected-head angular-order final reducer.

The local source keeps the selected cut-partition rows and asks only for the
genuine nonwrap adjacent selected-head rows in the real
`geometricOutgoingDartList`.  These rows are erased to graph-vertex angular
no-between rows, then the existing selected cut/angular W32 route applies. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_geometricAngularSelection_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedRowsHere :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          selectedRows C inputs
        forall a : {v : Fin m //
            v ∈
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                C inputs},
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1 (selectedRowsHere.selectedNeighborRows a).left
                (selectedRowsHere.selectedNeighborRows a).right))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_angularNoBetween_20260520
    frontier_noClosedSeparation
    selectedRows
    (fun C inputs =>
      let selectedRowsHere :
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs :=
        selectedRows C inputs
      fun a =>
        let row :
            _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1 (selectedRowsHere.selectedNeighborRows a).left
                (selectedRowsHere.selectedNeighborRows a).right :=
          Classical.choice (geometricRows C inputs a)
        _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.graphVertexAngularNoBetweenRows_of_geometricAngularNeighborSelectionRow
          row)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current topology hard case and the sharp selected
geometric-angular local source.

The topology residual is the aligned hard-case source for a nontrivial closed
separation of the unbounded-component frontier.  It feeds the checked
connected-frontier reducer and then the finite no-closed-separation route.
The local residual stays at actual selected cut-partition rows plus genuine
nonwrap geometric neighbour-selection rows in `geometricOutgoingDartList`. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_alignedKSplit_selectedCutPartition_geometricAngularSelection_20260520
    (alignedKSplit :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit)
    (selectedRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedRowsHere :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          selectedRows C inputs
        forall a : {v : Fin m //
            v ∈
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                C inputs},
          Nonempty
            (_root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
              C a.1 (selectedRowsHere.selectedNeighborRows a).left
                (selectedRowsHere.selectedNeighborRows a).right))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  let frontier_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierConnected :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_main_20260520_planar_connected_frontier_of_janiszewski_closed_split_source
      alignedKSplit
  let finite_noClosed :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_finite_no_closed_separation_source
      frontier_connected
  intro m C hmin
  exact
    (minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_geometricAngularSelection_20260520
      finite_noClosed selectedRows geometricRows noCutRows) (C := C) hmin

set_option linter.style.longLine false in
/-- W32 consumer for the finite no-closed-separation topology leaf and the
bundled selected-neighbour/cut/geometric input source.

This is the same finite S2 route as
`minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_angularNoBetween_20260520`,
but it consumes the smaller same-input local source: each frontier vertex row
carries the two selected `unboundedFrontierEdgeSet` incidences, the
third-neighbour cut residual, and the genuine adjacent
`geometricOutgoingDartList` indices for those same heads. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedNeighborInput_20260520
    (frontier_noClosedSeparation :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_angularNoBetween_20260520
    frontier_noClosedSeparation
    (fun C inputs =>
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
        (C := C) (inputs := inputs) (selectedInput C inputs))
    (fun C inputs =>
      let source :
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs :=
        selectedInput C inputs
      let selectedRows :
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
            inputs :=
        _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
          (C := C) (inputs := inputs) source
      let indexRows :
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
            selectedRows :=
        by
          simpa [selectedRows] using
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
              (C := C) (inputs := inputs) source
      _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_head_angular_no_between_of_indexRows
        (C := C) (inputs := inputs) indexRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current two-source S2 split.

The topology source is the planar crossing-subcontinuum boundedness theorem;
the local source is the bundled selected-neighbour cut/geometric-order input.
The theorem composes both through the checked finite no-closed-separation and
selected-neighbour W32 route. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_crossingBounded_selectedNeighborInput_20260520
    (crossing_forces_bounded :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  let planar_nontrivial :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_nontrivial_relative_clopen_side_leaf
      crossing_forces_bounded
  let finite_nontrivial :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finiteDrawingUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_planarContinuum
      planar_nontrivial
  let finite_noClosed :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_finiteDrawing_nontrivialRelativeClopenKSide
      finite_nontrivial
  intro m C hmin
  exact
    (minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedNeighborInput_20260520
      (frontier_noClosedSeparation := finite_noClosed)
      (selectedInput := selectedInput)
      (noCutRows := noCutRows)) (C := C) hmin

set_option linter.style.longLine false in
/-- W32 consumer for the current non-circular finite-topology residual and the
bundled selected-neighbour/cut/geometric input source.

The topology branch is the pairwise subcontinuum-between theorem for the
frontier of each unbounded complement component.  It feeds the finite
frontier-preconnected source, then the finite no-closed-separation route, and
finally the bundled selected-neighbour W32 consumer above. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumBetween_selectedNeighborInput_20260520
    (subcontinuum_between :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  let finite_preconnected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierPreconnected :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_finite_frontier_preconnected_acyclic_source
      subcontinuum_between
  let finite_noClosed :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_frontierPreconnected
      finite_preconnected
  intro m C hmin
  exact
    (minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedNeighborInput_20260520
      (frontier_noClosedSeparation := finite_noClosed)
      (selectedInput := selectedInput)
      (noCutRows := noCutRows)) (C := C) hmin

set_option linter.style.longLine false in
/-- W32 consumer for the standard connected-frontier planar-continuum residual
and the bundled selected-neighbour/cut/geometric input source.

The topology branch first gives the pairwise subcontinuum-between residual by
taking the whole unbounded-complement frontier as the connecting subcontinuum,
then uses the checked `SubcontinuumBetween` handoff above. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_selectedNeighborInput_20260520
    (frontier_connected :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierConnected)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumBetween_selectedNeighborInput_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_current_20260520_subcontinuum_between_source
      frontier_connected)
    selectedInput
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the shortest current S2 split.

The topology branch is the Janiszewski/boundary-bumping component-avoidance
source specialized by the finite-drawing no-closed-separation reducer.  The
local branch is the bundled selected-neighbour/cut/geometric input source.
The S1 no-cut family remains an explicit input here, avoiding any downstream
W34 circularity. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedNeighborInput_20260520
    (component_avoidance :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedNeighborInput_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_codex_cont_20260520_finite_no_closed_separation_source
      component_avoidance)
    selectedInput
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the no-subcontinuum Janiszewski topology leaf plus the
selected-neighbour input source.

This is the same finite S2 spine as the component-avoidance consumer, but it
uses the direct no-subcontinuum-to-no-closed-separation topology reducer. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_selectedNeighborInput_20260520
    (no_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedNeighborInput_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiNoSubcontinuumObstruction
      no_subcontinuum)
    selectedInput
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current no-subcontinuum topology reduction.

The topology source is the exact remaining crossing-subcontinuum frontier
witness theorem.  It feeds the checked no-subcontinuum reducer, then the
finite no-closed-separation S2 spine. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_crossingSubcontinuum_selectedNeighborInput_20260520
    (frontier_subcontinuum :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum)
    (selectedInput :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.SelectedNeighborCutPartitionGeometricOrderInputSource
            inputs)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_selectedNeighborInput_20260520
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_no_subcontinuum_source_20260520b
      frontier_subcontinuum)
    selectedInput
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for component avoidance plus the selected-edge/geometric-order
local source family.

The local source is reduced to actual selected `unboundedFrontierEdgeSet`
incidences and genuine selected-head order in
`GeometricRotationSystem.geometricOutgoingDartList`. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedIncidentEdgeRows_geometricOrderRows_20260520
    (component_avoidance :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (geometricRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedNeighborInput_20260520
    component_avoidance
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_current_selected_neighbor_input_source_20260520a_family_of_selectedIncidentEdgeRows_geometricOrderRows
      selectedEdgeRows geometricRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the actual-carrier degree-two specialization of the current
selected-neighbour route.

This leaves the geometric local order as the genuine
`GraphVertexGeometricOutgoingListNoBetweenRows` family for the selected heads
coming from actual carrier degree two. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_actualCarrierDegreeTwo_geometricOutgoingListNoBetweenRows_20260520
    (component_avoidance :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance)
    (hdegree :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          letI : DecidableRel
            (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
              C inputs).Adj :=
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph_decidableAdj
              C inputs
          forall a : {v : Fin m //
              v ∈
                _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                  C inputs},
            ((_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierCarrierGraph
                C inputs).neighborFinset a).card =
              2)
    (listRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let selectedEdgeRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_codex_current_20260520_actual_carrier_degree_two_source
            (C := C) (inputs := inputs) (hdegree C inputs)
        let cutSource :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) selectedEdgeRows
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        forall a : {v : Fin m //
            v ∈
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.unboundedFrontierVertexSet
                C inputs},
          _root_.ErdosProblems1066.Swanepoel.GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
            C a.1 (selectedRows.selectedNeighborRows a).left
              (selectedRows.selectedNeighborRows a).right)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedNeighborInput_20260520
    component_avoidance
    (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_current_selected_neighbor_input_source_20260520a_family_of_actualCarrierDegreeTwo_geometricOutgoingListNoBetweenRows
      hdegree listRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the raw-orbit selected-order route.

This is a route composer only.  The source rows remain explicit: actual
selected frontier-edge incidences, selected raw-tail coverage, the selected
head/raw-orbit match, raw orientation, component avoidance, and no-cut rows. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedIncidentEdgeRows_rawOrbitHeadMatch_rawOrientation_20260520
    (component_avoidance :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (rawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
            inputs)
    (headRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let cutSource :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairCutPartitionInputSource
              C inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
            (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
        let selectedRows :
            _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
            (C := C) (inputs := inputs)
            (_root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
              (C := C) (inputs := inputs) cutSource)
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitHeadMatchSource
          selectedRows (rawRows C inputs))
    (orientationRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitOrientationRows
            (rawRows C inputs))
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget :=
  minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedNeighborInput_20260520
    component_avoidance
    (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_raw_orbit_selected_order_source_family_20260520a
      selectedEdgeRows rawRows headRows orientationRows)
    noCutRows

set_option linter.style.longLine false in
/-- W32 consumer for the current selected raw-orbit source split.

The raw-tail package is built from connected raw-orbit rows by the 20260520b
selected raw-tail reducer; the selected-head match is reduced to the one-sided
left-predecessor leaf; and raw orientation is reduced to genuine nonwrap rows
in the selected raw orbit's sorted outgoing geometric lists. -/
theorem
    minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedIncidentEdgeRows_connectedRawOrbit_leftPred_geometricSuccessorNonwrap_20260520b
    (component_avoidance :
      _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance)
    (selectedEdgeRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows
            inputs)
    (connectedRawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows
            inputs)
    (leftPredRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let rawRows :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520b
            (C := C) (inputs := inputs) (connectedRawRows C inputs)
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_selected_raw_left_pred_head_match_source_20260520b
          (C := C) (inputs := inputs) (selectedEdgeRows C inputs) rawRows)
    (successorRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
        let rawRows :
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
              inputs :=
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520b
            (C := C) (inputs := inputs) (connectedRawRows C inputs)
        _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitGeometricSuccessorNonwrapRows
          rawRows)
    (noCutRows :
      forall {n : Nat} (C : _root_.UDConfig n),
        MinimalGraphFacts.IsMinimalClearedFailure C ->
          CutVertexInterface.NoCutVertex C) :
    MinimalFailureExactActualTopologyFieldsTarget := by
  intro n C hmin
  let rawRows :
      forall {m : Nat} (C : _root_.UDConfig m)
        (inputs :
          JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs
            C),
          _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawTailCoverageSourceRows
            inputs :=
    _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_selectedRawTailCoverageSourceRows_family_of_connectedRawOrbitSourceRows_20260520b
      connectedRawRows
  exact
    minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedNeighborInput_20260520
      component_avoidance
      (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_raw_orbit_selected_order_source_family_20260520b
        selectedEdgeRows rawRows
        (by
          intro m C inputs
          change
            _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_selected_raw_left_pred_head_match_source_20260520b
              (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
              (rawRows C inputs)
          exact leftPredRows C inputs)
        (_root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.S2_current_raw_orbit_orientation_source_family_20260520b
          rawRows
          (by
            intro m C inputs
            change
              _root_.ErdosProblems1066.Swanepoel.ExteriorComponentTopology.SelectedRawOrbitGeometricSuccessorNonwrapRows
                (rawRows C inputs)
            exact successorRows C inputs)))
      noCutRows C hmin

/-! ## Subpolygon count fields -/

/-- Subpolygon counting data over the face-boundary topology layer. -/
structure SubpolygonCountingSourceFields (C : _root_.UDConfig n) extends
    TopologySourceFields C where
  counts : BoundaryCounting.SubpolygonDegreeCounts
  angleLowerBound : counts.AngleLowerBound

namespace SubpolygonCountingSourceFields

variable {C : _root_.UDConfig n}

def ofTopology
    (T : TopologySourceFields C)
    (counts : BoundaryCounting.SubpolygonDegreeCounts)
    (hangle : counts.AngleLowerBound) :
    SubpolygonCountingSourceFields C where
  faceBoundary := T.faceBoundary
  outerFace := T.outerFace
  outerFace_isOuter := T.outerFace_isOuter
  counts := counts
  angleLowerBound := hangle

def toCanonicalSubpolygonCountHypotheses
    (S : SubpolygonCountingSourceFields C) :
    FaceCountingBridge.CanonicalSubpolygonCountHypotheses
      (CanonicalGraph C) where
  faceBoundary := S.faceBoundary
  counts := S.counts
  angleLowerBound := S.angleLowerBound

theorem lowDegreeWithHighDegreeSlack
    (S : SubpolygonCountingSourceFields C) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 :=
  S.toCanonicalSubpolygonCountHypotheses.subpolygonLowDegreeWithHighDegreeSlack

theorem lowDegreeWithHighDegreeSlack_direct
    (S : SubpolygonCountingSourceFields C) :
    S.counts.D5 + 2 * S.counts.D6 + 6 <=
      2 * S.counts.D2 + S.counts.D3 :=
  BoundaryCounting.SubpolygonDegreeCounts.subpolygon_low_degree_with_high_degree_slack
    S.counts S.angleLowerBound

theorem lowDegreeInequality
    (S : SubpolygonCountingSourceFields C) :
    6 <= 2 * S.counts.D2 + S.counts.D3 :=
  S.toCanonicalSubpolygonCountHypotheses.subpolygonLowDegreeInequality

theorem lowDegreeInequality_direct
    (S : SubpolygonCountingSourceFields C) :
    6 <= 2 * S.counts.D2 + S.counts.D3 :=
  BoundaryCounting.SubpolygonDegreeCounts.subpolygon_low_degree_inequality
    S.counts S.angleLowerBound

end SubpolygonCountingSourceFields

def GlobalJordanSourceTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (JordanSourceFields C)

def GlobalTopologySourceTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (TopologySourceFields C)

def GlobalMissingOuterFaceDataTarget : Prop :=
  forall (n : Nat) (C : _root_.UDConfig n),
    Nonempty (JordanBoundaryConcrete.MissingOuterFaceData.{0} C)

theorem globalTopologySourceTarget_iff_missingOuterFaceDataTarget :
    GlobalTopologySourceTarget <-> GlobalMissingOuterFaceDataTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_topologySourceFields_iff_missingOuterFaceData C).1
      (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_topologySourceFields_iff_missingOuterFaceData C).2
      (h n C)

theorem globalJordanSourceTarget_iff_w31SourceTarget :
    GlobalJordanSourceTarget <->
      EnclosureAndFaceBoundaryW31.GlobalFaceBoundaryEnclosureSourceTarget := by
  constructor
  case mp =>
    intro h n C
    exact (nonempty_jordanSourceFields_iff_w31Source C).1 (h n C)
  case mpr =>
    intro h n C
    exact (nonempty_jordanSourceFields_iff_w31Source C).2 (h n C)

theorem globalJordanSourceTarget_iff_outerBoundaryCoreTarget :
    GlobalJordanSourceTarget <->
      OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Iff.trans
    globalJordanSourceTarget_iff_w31SourceTarget
    EnclosureAndFaceBoundaryW31.globalFaceBoundaryEnclosureSourceTarget_iff_outerBoundaryCoreTarget

end

end FaceBoundaryTopologySourceW32

namespace Verified

abbrev SwanepoelW32TopologySourceFields
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.FaceBoundaryTopologySourceW32.TopologySourceFields C

abbrev SwanepoelW32JordanSourceFields
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.FaceBoundaryTopologySourceW32.JordanSourceFields C

abbrev SwanepoelW32BoundaryCountingSourceFields
    {n : Nat} (C : _root_.UDConfig n) :=
  Swanepoel.FaceBoundaryTopologySourceW32.BoundaryCountingSourceFields C

theorem swanepoelW32_jordanSource_exactly_w31Source
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32JordanSourceFields C) <->
      Nonempty
        (Swanepoel.EnclosureAndFaceBoundaryW31.FaceBoundaryEnclosureSource
          C) :=
  Swanepoel.FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_w31Source
    C

theorem swanepoelW32_jordanSource_exactly_exactTopologyFields
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32JordanSourceFields C) <->
      Swanepoel.OuterBoundaryExistenceConcrete.ExactTopologyFields C :=
  Swanepoel.FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_exactTopologyFields
    C

theorem swanepoelW32_jordanSource_exactly_actualSelectedTopologyData
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32JordanSourceFields C) <->
      Nonempty
        (Swanepoel.FaceBoundaryTopologySourceW32.ActualSelectedTopologyData
          C) :=
  Swanepoel.FaceBoundaryTopologySourceW32.nonempty_jordanSourceFields_iff_actualSelectedTopologyData
    C

theorem swanepoelW32_actualOuterBoundaryCycle_exactly_mathlibCycleBlocker
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty
        (Swanepoel.JordanBoundaryConcrete.ActualOuterBoundaryCycleData.{0}
          C) <->
      Swanepoel.FaceBoundaryTopologySourceW32.ExactMathlibActualOuterBoundaryCycleSourceBlocker
        C :=
  Swanepoel.FaceBoundaryTopologySourceW32.nonempty_actualOuterBoundaryCycleData_iff_exactMathlibCycleBlocker
    C

theorem swanepoelW32_mathlibCycleBlocker_exactly_finiteNoncrossingActualOuterBoundaryCycle
    {n : Nat} (C : _root_.UDConfig n) :
    Swanepoel.FaceBoundaryTopologySourceW32.ExactMathlibActualOuterBoundaryCycleSourceBlocker
        C <->
      Swanepoel.FaceBoundaryTopologySourceW32.ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem
        C :=
  Swanepoel.FaceBoundaryTopologySourceW32.exactMathlibCycleBlocker_iff_finiteNoncrossingActualOuterBoundaryCycle
    C

theorem swanepoelW32_nonDegenerateTopology_exactly_finiteNoncrossingActualOuterBoundaryCycle
    {n : Nat} (C : _root_.UDConfig n) :
    Swanepoel.FaceBoundaryTopologySourceW32.ExactNondegenerateMissingTopologyFactsSource
        C <->
      Swanepoel.FaceBoundaryTopologySourceW32.ExactFiniteNoncrossingActualOuterBoundaryCycleTheorem
        C :=
  Swanepoel.FaceBoundaryTopologySourceW32.exactNondegenerateMissingTopologyFactsSource_iff_finiteNoncrossingActualOuterBoundaryCycle
    C

theorem swanepoelW32_topologySource_exactly_missingOuterFaceData
    {n : Nat} (C : _root_.UDConfig n) :
    Nonempty (SwanepoelW32TopologySourceFields C) <->
      Nonempty
        (Swanepoel.JordanBoundaryConcrete.MissingOuterFaceData.{0} C) :=
  Swanepoel.FaceBoundaryTopologySourceW32.nonempty_topologySourceFields_iff_missingOuterFaceData
    C

theorem swanepoelW32_globalTopologySource_exactly_missingOuterFaceData :
    Swanepoel.FaceBoundaryTopologySourceW32.GlobalTopologySourceTarget <->
      Swanepoel.FaceBoundaryTopologySourceW32.GlobalMissingOuterFaceDataTarget :=
  Swanepoel.FaceBoundaryTopologySourceW32.globalTopologySourceTarget_iff_missingOuterFaceDataTarget

theorem swanepoelW32_missing_jordanSource_exactly_no_planarBoundaryBlocker
    {n : Nat} (C : _root_.UDConfig n) :
    Not (Nonempty (SwanepoelW32JordanSourceFields C)) <->
      Not
        (Swanepoel.EnclosureAndFaceBoundaryW31.ExactSelectedFaceEnclosureBlocker
          C) :=
  Swanepoel.FaceBoundaryTopologySourceW32.jordanSource_missing_iff_no_exactBlocker
    C

theorem swanepoelW32_globalJordanSource_exactly_outerBoundaryCoreTarget :
    Swanepoel.FaceBoundaryTopologySourceW32.GlobalJordanSourceTarget <->
      Swanepoel.OuterBoundaryCoreConstruction.GlobalOuterBoundaryCoreConstructionTarget :=
  Swanepoel.FaceBoundaryTopologySourceW32.globalJordanSourceTarget_iff_outerBoundaryCoreTarget

end Verified
end Swanepoel
end ErdosProblems1066
