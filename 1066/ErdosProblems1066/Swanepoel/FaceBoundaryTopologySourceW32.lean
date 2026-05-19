import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Geometry.Polygon.Basic
import ErdosProblems1066.Swanepoel.CutVertexFinal
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.JordanTopologyExteriorEnclosure
import ErdosProblems1066.Swanepoel.ExteriorComponentTopology
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
open _root_.ErdosProblems1066.Swanepoel.JordanTopologyExteriorEnclosure

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
                    (JordanTopologyFactsConcrete.canonicalGraph C).point v ∉
                      exterior) /\
                (forall v : Fin n,
                  (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
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
                      (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
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
              (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
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
              (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
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
        (JordanTopologyFactsConcrete.canonicalGraph C).point v ∉ exterior
  frontier_iff_cycle_vertex :
    forall v : Fin n,
      (JordanTopologyFactsConcrete.canonicalGraph C).point v ∈
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
