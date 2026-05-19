import ErdosProblems1066.Swanepoel.PlanarBoundaryFinal
import ErdosProblems1066.Swanepoel.LocalExclusions

set_option autoImplicit false

/-!
# Concrete boundary-walk classifications

This module specializes the generic boundary-walk bookkeeping interface to the
canonical unit-distance graph attached to an `OuterBoundaryCore`.

The triangle/nontriangle edge split is constructed directly from the local
unit-distance graph: every certified boundary edge is adjacent, so it is either
a triangle edge with a common-neighbor witness or a nontriangle edge with no
such witness.  Boundary vertex degree classes use the concrete ambient
unit-distance degree.  The only still-explicit input needed to classify
vertices into the paper's `3..6` classes is the lower bound `3 <= degree`; the
upper bound is the checked unit-distance kissing-number bound.

No minimality, no-cut, or global Swanepoel assumptions are introduced here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryWalkClassificationConcrete

open BoundaryClassification
open BoundaryCounting
open BoundaryWalkConstruction
open FaceReduction
open PlanarInterface

noncomputable section

universe u

variable {n : Nat}

/-! ## Concrete predicates -/

/-- The local unit-distance graph of a canonical straight-line graph. -/
abbrev unitLocalGraph
    (G : CanonicalStraightLineUnitDistanceGraph n) :
    LocalConfigurations.LocalGraph (Fin n) :=
  GraphBridge.unitDistanceLocalGraph G.config

/-- A concrete boundary edge is triangular when its endpoints have a common
unit-distance neighbor. -/
def IsTriangleEdge
    (G : CanonicalStraightLineUnitDistanceGraph n) (e : Edge n) : Prop :=
  (unitLocalGraph G).IsTriangleEdge e.1 e.2

/-- A concrete boundary edge is nontriangular when it is adjacent and has no
common unit-distance neighbor. -/
def IsNontriangleEdge
    (G : CanonicalStraightLineUnitDistanceGraph n) (e : Edge n) : Prop :=
  (unitLocalGraph G).IsNontriangleEdge e.1 e.2

/-- Ambient unit-distance degree of a vertex in the canonical graph. -/
def ambientDegree
    (G : CanonicalStraightLineUnitDistanceGraph n) (v : Fin n) : Nat :=
  LocalExclusions.LocalGraph.degree (unitLocalGraph G) v

/-- Concrete degree-`d` predicate for boundary vertices. -/
def IsDegree
    (G : CanonicalStraightLineUnitDistanceGraph n) (d : Nat)
    (v : Fin n) : Prop :=
  ambientDegree G v = d

/-- Concrete degree-three predicate. -/
abbrev IsDegree3
    (G : CanonicalStraightLineUnitDistanceGraph n) (v : Fin n) : Prop :=
  IsDegree G 3 v

/-- Concrete degree-four predicate. -/
abbrev IsDegree4
    (G : CanonicalStraightLineUnitDistanceGraph n) (v : Fin n) : Prop :=
  IsDegree G 4 v

/-- Concrete degree-five predicate. -/
abbrev IsDegree5
    (G : CanonicalStraightLineUnitDistanceGraph n) (v : Fin n) : Prop :=
  IsDegree G 5 v

/-- Concrete degree-six predicate. -/
abbrev IsDegree6
    (G : CanonicalStraightLineUnitDistanceGraph n) (v : Fin n) : Prop :=
  IsDegree G 6 v

/-- The checked ambient degree upper bound for unit-distance graphs. -/
theorem ambientDegree_le_six
    (G : CanonicalStraightLineUnitDistanceGraph n) (v : Fin n) :
    ambientDegree G v <= 6 := by
  simpa [ambientDegree, unitLocalGraph] using
    LocalExclusions.UnitDistance.unitDistanceLocalGraph_degree_le_six
      G.config v

/-! ## Boundary-edge classification from the outer core -/

/-- A selected outer-boundary edge is adjacent in the concrete local graph. -/
theorem outerBoundary_edge_adj
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    (unitLocalGraph G).Adj
      (P.outerCycle.edge k).1 (P.outerCycle.edge k).2 :=
  P.outerCycle.edge_unitDistanceAdj k

/-- A common-neighbor witness turns a selected outer-boundary edge into a
concrete triangle edge. -/
theorem isTriangleEdge_of_outerBoundary_commonNeighbor
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length)
    {x : Fin n}
    (hx :
      (unitLocalGraph G).CommonNeighbor
        (P.outerCycle.edge k).1 (P.outerCycle.edge k).2 x) :
    IsTriangleEdge G (P.outerCycle.edge k) :=
  ⟨outerBoundary_edge_adj P k, ⟨x, hx⟩⟩

/-- If a selected outer-boundary edge has no common-neighbor witness, it is a
concrete nontriangle edge. -/
theorem isNontriangleEdge_of_not_isTriangleEdge
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length)
    (hnot : Not (IsTriangleEdge G (P.outerCycle.edge k))) :
    IsNontriangleEdge G (P.outerCycle.edge k) := by
  refine ⟨outerBoundary_edge_adj P k, ?_⟩
  intro x hx
  exact hnot (isTriangleEdge_of_outerBoundary_commonNeighbor P k hx)

/-- On selected outer-boundary edges, nontriangle is the complement of
triangle. -/
theorem isNontriangleEdge_iff_not_isTriangleEdge
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    IsNontriangleEdge G (P.outerCycle.edge k) <->
      Not (IsTriangleEdge G (P.outerCycle.edge k)) := by
  constructor
  · intro hnon htri
    rcases htri.2 with ⟨x, hx⟩
    exact hnon.2 x hx
  · exact isNontriangleEdge_of_not_isTriangleEdge P k

/-- Concrete triangle/nontriangle class for a selected outer-boundary edge. -/
def edgeKind
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    BoundaryEdgeClass := by
  classical
  exact
    if IsTriangleEdge G (P.outerCycle.edge k) then
      BoundaryEdgeClass.triangle
    else
      BoundaryEdgeClass.nontriangle

@[simp]
theorem edgeKind_eq_triangle_iff
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    edgeKind P k = BoundaryEdgeClass.triangle <->
      IsTriangleEdge G (P.outerCycle.edge k) := by
  classical
  unfold edgeKind
  by_cases h : IsTriangleEdge G (P.outerCycle.edge k)
  · simp [h]
  · simp [h]

@[simp]
theorem edgeKind_eq_nontriangle_iff
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    edgeKind P k = BoundaryEdgeClass.nontriangle <->
      IsNontriangleEdge G (P.outerCycle.edge k) := by
  classical
  unfold edgeKind
  by_cases h : IsTriangleEdge G (P.outerCycle.edge k)
  · constructor
    · intro hclass
      simp [h] at hclass
    · intro hnon
      exact False.elim ((isNontriangleEdge_iff_not_isTriangleEdge P k).1 hnon h)
  · constructor
    · intro _hclass
      exact isNontriangleEdge_of_not_isTriangleEdge P k h
    · intro _hnon
      simp [h]

theorem edgeKind_triangleEvidence
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length)
    (hclass : edgeKind P k = BoundaryEdgeClass.triangle) :
    IsTriangleEdge G (P.outerCycle.edge k) :=
  (edgeKind_eq_triangle_iff P k).1 hclass

theorem edgeKind_nontriangleEvidence
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length)
    (hclass : edgeKind P k = BoundaryEdgeClass.nontriangle) :
    IsNontriangleEdge G (P.outerCycle.edge k) :=
  (edgeKind_eq_nontriangle_iff P k).1 hclass

/-! ## Boundary-degree classification -/

/-- Degree class chosen from a natural number.  The evidence lemmas below use
the explicit range hypotheses to prove that the fallback case is degree six. -/
def degreeKindOfNat (d : Nat) : BoundaryDegreeClass := by
  classical
  exact
    if d = 3 then
      BoundaryDegreeClass.degree3
    else if d = 4 then
      BoundaryDegreeClass.degree4
    else if d = 5 then
      BoundaryDegreeClass.degree5
    else
      BoundaryDegreeClass.degree6

@[simp]
theorem degreeKindOfNat_eq_degree3_iff
    {d : Nat} :
    degreeKindOfNat d = BoundaryDegreeClass.degree3 <-> d = 3 := by
  classical
  unfold degreeKindOfNat
  by_cases h3 : d = 3
  · simp [h3]
  · by_cases h4 : d = 4
    · simp [h4]
    · by_cases h5 : d = 5
      · simp [h5]
      · simp [h3, h4, h5]

@[simp]
theorem degreeKindOfNat_eq_degree4_iff
    {d : Nat} :
    degreeKindOfNat d = BoundaryDegreeClass.degree4 <-> d = 4 := by
  classical
  unfold degreeKindOfNat
  by_cases h3 : d = 3
  · simp [h3]
  · by_cases h4 : d = 4
    · simp [h4]
    · by_cases h5 : d = 5
      · simp [h5]
      · simp [h3, h4, h5]

@[simp]
theorem degreeKindOfNat_eq_degree5_iff
    {d : Nat} :
    degreeKindOfNat d = BoundaryDegreeClass.degree5 <-> d = 5 := by
  classical
  unfold degreeKindOfNat
  by_cases h3 : d = 3
  · simp [h3]
  · by_cases h4 : d = 4
    · simp [h4]
    · by_cases h5 : d = 5
      · simp [h5]
      · simp [h3, h4, h5]

theorem degreeKindOfNat_eq_degree6_of_range
    {d : Nat} (hlo : 3 <= d) (hhi : d <= 6) :
    degreeKindOfNat d = BoundaryDegreeClass.degree6 <-> d = 6 := by
  classical
  constructor
  · intro hkind
    unfold degreeKindOfNat at hkind
    by_cases h3 : d = 3
    · simp [h3] at hkind
    by_cases h4 : d = 4
    · simp [h4] at hkind
    by_cases h5 : d = 5
    · simp [h5] at hkind
    · omega
  · intro h6
    subst d
    simp [degreeKindOfNat]

/-- Concrete degree class for a boundary vertex. -/
def vertexKind
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    BoundaryDegreeClass :=
  degreeKindOfNat (ambientDegree G (P.outerCycle.vertex k))

@[simp]
theorem vertexKind_eq_degree3_iff
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    vertexKind P k = BoundaryDegreeClass.degree3 <->
      IsDegree3 G (P.outerCycle.vertex k) := by
  simp [vertexKind, IsDegree, IsDegree3]

@[simp]
theorem vertexKind_eq_degree4_iff
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    vertexKind P k = BoundaryDegreeClass.degree4 <->
      IsDegree4 G (P.outerCycle.vertex k) := by
  simp [vertexKind, IsDegree, IsDegree4]

@[simp]
theorem vertexKind_eq_degree5_iff
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) (k : Fin P.outerCycle.length) :
    vertexKind P k = BoundaryDegreeClass.degree5 <->
      IsDegree5 G (P.outerCycle.vertex k) := by
  simp [vertexKind, IsDegree, IsDegree5]

theorem vertexKind_eq_degree6_iff
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (degree_ge_three :
      forall k : Fin P.outerCycle.length,
        3 <= ambientDegree G (P.outerCycle.vertex k))
    (k : Fin P.outerCycle.length) :
    vertexKind P k = BoundaryDegreeClass.degree6 <->
      IsDegree6 G (P.outerCycle.vertex k) := by
  simpa [vertexKind, IsDegree, IsDegree6] using
    (degreeKindOfNat_eq_degree6_of_range
      (d := ambientDegree G (P.outerCycle.vertex k))
      (degree_ge_three k)
      (ambientDegree_le_six G (P.outerCycle.vertex k)))

/-! ## Concrete outer-boundary walk package -/

/--
Concrete classification inputs for the selected outer-boundary walk.

The edge split and degree predicates are computed in this file.  The lower
degree bound and long-arc predicate remain explicit local obligations.
-/
structure OuterBoundaryClassificationInputs
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G) where
  degree_ge_three :
    forall k : Fin P.outerCycle.length,
      3 <= ambientDegree G (P.outerCycle.vertex k)
  longArc : Fin P.outerCycle.length -> Prop
  longArcDecidable : forall k : Fin P.outerCycle.length, Decidable (longArc k)

namespace OuterBoundaryClassificationInputs

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}

/-- Build the concrete boundary classification from the selected boundary
cycle, a lower degree bound, and the selected long-arc predicate.  Decidability
of the long-arc predicate is finite/classical data, so callers do not need to
carry it as a separate geometric premise. -/
def ofLongArcPredicate
    (degree_ge_three :
      forall k : Fin P.outerCycle.length,
        3 <= ambientDegree G (P.outerCycle.vertex k))
    (longArc : Fin P.outerCycle.length -> Prop) :
    OuterBoundaryClassificationInputs P where
  degree_ge_three := degree_ge_three
  longArc := longArc
  longArcDecidable := by
    classical
    intro k
    infer_instance

@[simp]
theorem ofLongArcPredicate_longArc
    (degree_ge_three :
      forall k : Fin P.outerCycle.length,
        3 <= ambientDegree G (P.outerCycle.vertex k))
    (longArc : Fin P.outerCycle.length -> Prop) :
    (ofLongArcPredicate (P := P) degree_ge_three longArc).longArc =
      longArc :=
  rfl

@[simp]
theorem ofLongArcPredicate_degree_ge_three
    (degree_ge_three :
      forall k : Fin P.outerCycle.length,
        3 <= ambientDegree G (P.outerCycle.vertex k))
    (longArc : Fin P.outerCycle.length -> Prop)
    (k : Fin P.outerCycle.length) :
    (ofLongArcPredicate (P := P) degree_ge_three longArc).degree_ge_three k =
      degree_ge_three k :=
  rfl

/-- The concrete classified outer-boundary walk. -/
def toOuterBoundaryWalkBookkeeping
    (D : OuterBoundaryClassificationInputs P) :
    OuterBoundaryWalkBookkeeping P
      (IsTriangleEdge G) (IsNontriangleEdge G)
      (IsDegree3 G) (IsDegree4 G) (IsDegree5 G) (IsDegree6 G) where
  data :=
    { edgeKind := edgeKind P
      vertexKind := vertexKind P
      longArc := D.longArc
      longArcDecidable := D.longArcDecidable
      edge_triangleEvidence := edgeKind_triangleEvidence P
      edge_nontriangleEvidence := edgeKind_nontriangleEvidence P
      degree3Evidence := fun k hclass =>
        (vertexKind_eq_degree3_iff P k).1 hclass
      degree4Evidence := fun k hclass =>
        (vertexKind_eq_degree4_iff P k).1 hclass
      degree5Evidence := fun k hclass =>
        (vertexKind_eq_degree5_iff P k).1 hclass
      degree6Evidence := fun k hclass =>
        (vertexKind_eq_degree6_iff P D.degree_ge_three k).1 hclass }

/-- The boundary counts computed from the concrete classified walk. -/
def counts (D : OuterBoundaryClassificationInputs P) : BoundaryCounts :=
  D.toOuterBoundaryWalkBookkeeping.counts

/-- The finite count-realization package computed from the concrete classified
walk. -/
def countsRealization
    (D : OuterBoundaryClassificationInputs P) :
    BoundaryCountsRealization.{0} :=
  D.toOuterBoundaryWalkBookkeeping.toBoundaryCountsRealization

/-- Universe-polymorphic count realization computed from the concrete
classified walk. -/
def countsRealizationLift
    (D : OuterBoundaryClassificationInputs P) :
    BoundaryCountsRealization.{u} :=
  D.toOuterBoundaryWalkBookkeeping.toBoundaryCountsRealizationLift

@[simp]
theorem toOuterBoundaryWalkBookkeeping_counts
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.counts = D.counts :=
  rfl

@[simp]
theorem countsRealization_toBoundaryCounts
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.toBoundaryCounts = D.counts :=
  rfl

@[simp]
theorem countsRealizationLift_toBoundaryCounts
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealizationLift.toBoundaryCounts = D.counts :=
  rfl

@[simp]
theorem countsRealizationLift_bookkeeping
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealizationLift.bookkeeping =
      D.toOuterBoundaryWalkBookkeeping.toBoundaryBookkeepingLift :=
  rfl

/-! ### Concrete index subtypes -/

/-- Boundary indices whose edge is triangular. -/
def triangleEdgeIndices
    (_D : OuterBoundaryClassificationInputs P) : Type :=
  { k : Fin P.outerCycle.length // IsTriangleEdge G (P.outerCycle.edge k) }

/-- Boundary indices whose edge is nontriangular. -/
def nontriangleEdgeIndices
    (_D : OuterBoundaryClassificationInputs P) : Type :=
  { k : Fin P.outerCycle.length // IsNontriangleEdge G (P.outerCycle.edge k) }

/-- Boundary indices whose vertex has ambient degree three. -/
def degree3Indices
    (_D : OuterBoundaryClassificationInputs P) : Type :=
  { k : Fin P.outerCycle.length // IsDegree3 G (P.outerCycle.vertex k) }

/-- Boundary indices whose vertex has ambient degree four. -/
def degree4Indices
    (_D : OuterBoundaryClassificationInputs P) : Type :=
  { k : Fin P.outerCycle.length // IsDegree4 G (P.outerCycle.vertex k) }

/-- Boundary indices whose vertex has ambient degree five. -/
def degree5Indices
    (_D : OuterBoundaryClassificationInputs P) : Type :=
  { k : Fin P.outerCycle.length // IsDegree5 G (P.outerCycle.vertex k) }

/-- Boundary indices whose vertex has ambient degree six. -/
def degree6Indices
    (_D : OuterBoundaryClassificationInputs P) : Type :=
  { k : Fin P.outerCycle.length // IsDegree6 G (P.outerCycle.vertex k) }

/-- Boundary indices selected as long arcs. -/
def longArcIndices
    (D : OuterBoundaryClassificationInputs P) : Type :=
  { k : Fin P.outerCycle.length // D.longArc k }

instance triangleEdgeIndices_fintype
    (D : OuterBoundaryClassificationInputs P) :
    Fintype (D.triangleEdgeIndices) := by
  unfold triangleEdgeIndices
  infer_instance

instance nontriangleEdgeIndices_fintype
    (D : OuterBoundaryClassificationInputs P) :
    Fintype (D.nontriangleEdgeIndices) := by
  unfold nontriangleEdgeIndices
  infer_instance

instance degree3Indices_fintype
    (D : OuterBoundaryClassificationInputs P) :
    Fintype (D.degree3Indices) := by
  unfold degree3Indices
  infer_instance

instance degree4Indices_fintype
    (D : OuterBoundaryClassificationInputs P) :
    Fintype (D.degree4Indices) := by
  unfold degree4Indices
  infer_instance

instance degree5Indices_fintype
    (D : OuterBoundaryClassificationInputs P) :
    Fintype (D.degree5Indices) := by
  unfold degree5Indices
  infer_instance

instance degree6Indices_fintype
    (D : OuterBoundaryClassificationInputs P) :
    Fintype (D.degree6Indices) := by
  unfold degree6Indices
  infer_instance

instance longArcIndices_fintype
    (D : OuterBoundaryClassificationInputs P) :
    Fintype (D.longArcIndices) := by
  unfold longArcIndices
  letI : DecidablePred D.longArc := D.longArcDecidable
  infer_instance

/-! ### Equivalences with the generic walk indices -/

def walkTriangleEdgeIndicesEquiv
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.data.triangleEdgeIndices ≃
      D.triangleEdgeIndices where
  toFun x := ⟨x.1, (edgeKind_eq_triangle_iff P x.1).1 x.2⟩
  invFun x := ⟨x.1, (edgeKind_eq_triangle_iff P x.1).2 x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

def walkNontriangleEdgeIndicesEquiv
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.data.nontriangleEdgeIndices ≃
      D.nontriangleEdgeIndices where
  toFun x := ⟨x.1, (edgeKind_eq_nontriangle_iff P x.1).1 x.2⟩
  invFun x := ⟨x.1, (edgeKind_eq_nontriangle_iff P x.1).2 x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

def walkDegree3IndicesEquiv
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.data.degree3Indices ≃
      D.degree3Indices where
  toFun x := ⟨x.1, (vertexKind_eq_degree3_iff P x.1).1 x.2⟩
  invFun x := ⟨x.1, (vertexKind_eq_degree3_iff P x.1).2 x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

def walkDegree4IndicesEquiv
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.data.degree4Indices ≃
      D.degree4Indices where
  toFun x := ⟨x.1, (vertexKind_eq_degree4_iff P x.1).1 x.2⟩
  invFun x := ⟨x.1, (vertexKind_eq_degree4_iff P x.1).2 x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

def walkDegree5IndicesEquiv
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.data.degree5Indices ≃
      D.degree5Indices where
  toFun x := ⟨x.1, (vertexKind_eq_degree5_iff P x.1).1 x.2⟩
  invFun x := ⟨x.1, (vertexKind_eq_degree5_iff P x.1).2 x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

def walkDegree6IndicesEquiv
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.data.degree6Indices ≃
      D.degree6Indices where
  toFun x := ⟨x.1, (vertexKind_eq_degree6_iff P D.degree_ge_three x.1).1 x.2⟩
  invFun x := ⟨x.1, (vertexKind_eq_degree6_iff P D.degree_ge_three x.1).2 x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

def walkLongArcIndicesEquiv
    (D : OuterBoundaryClassificationInputs P) :
    D.toOuterBoundaryWalkBookkeeping.data.longArcIndices ≃
      D.longArcIndices where
  toFun x := x
  invFun x := x
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

/-! ### Full pointwise boundary rows -/

/-- The concrete edge/vertex/long-arc row at one selected boundary-walk index.

Unlike the finite `M8` spine rows, this is indexed by every
`Fin P.outerCycle.length` position of the selected outer boundary. -/
structure BoundaryIndexClassificationRow
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) where
  edgeKind : BoundaryEdgeClass
  vertexKind : BoundaryDegreeClass
  longArc : Prop
  edgeKind_eq :
    edgeKind = D.toOuterBoundaryWalkBookkeeping.data.edgeKind k
  vertexKind_eq :
    vertexKind = D.toOuterBoundaryWalkBookkeeping.data.vertexKind k
  longArc_eq : longArc = D.longArc k
  triangleEvidence :
    edgeKind = BoundaryEdgeClass.triangle ->
      IsTriangleEdge G (P.outerCycle.edge k)
  nontriangleEvidence :
    edgeKind = BoundaryEdgeClass.nontriangle ->
      IsNontriangleEdge G (P.outerCycle.edge k)
  degree3Evidence :
    vertexKind = BoundaryDegreeClass.degree3 ->
      IsDegree3 G (P.outerCycle.vertex k)
  degree4Evidence :
    vertexKind = BoundaryDegreeClass.degree4 ->
      IsDegree4 G (P.outerCycle.vertex k)
  degree5Evidence :
    vertexKind = BoundaryDegreeClass.degree5 ->
      IsDegree5 G (P.outerCycle.vertex k)
  degree6Evidence :
    vertexKind = BoundaryDegreeClass.degree6 ->
      IsDegree6 G (P.outerCycle.vertex k)

/-- The concrete classification row at an arbitrary boundary-walk index. -/
def boundaryIndexClassificationRow
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    BoundaryIndexClassificationRow D k where
  edgeKind := edgeKind P k
  vertexKind := vertexKind P k
  longArc := D.longArc k
  edgeKind_eq := rfl
  vertexKind_eq := rfl
  longArc_eq := rfl
  triangleEvidence := edgeKind_triangleEvidence P k
  nontriangleEvidence := edgeKind_nontriangleEvidence P k
  degree3Evidence := fun hclass =>
    (vertexKind_eq_degree3_iff P k).1 hclass
  degree4Evidence := fun hclass =>
    (vertexKind_eq_degree4_iff P k).1 hclass
  degree5Evidence := fun hclass =>
    (vertexKind_eq_degree5_iff P k).1 hclass
  degree6Evidence := fun hclass =>
    (vertexKind_eq_degree6_iff P D.degree_ge_three k).1 hclass

@[simp]
theorem boundaryIndexClassificationRow_edgeKind
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    (D.boundaryIndexClassificationRow k).edgeKind =
      D.toOuterBoundaryWalkBookkeeping.data.edgeKind k :=
  rfl

@[simp]
theorem boundaryIndexClassificationRow_vertexKind
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    (D.boundaryIndexClassificationRow k).vertexKind =
      D.toOuterBoundaryWalkBookkeeping.data.vertexKind k :=
  rfl

@[simp]
theorem boundaryIndexClassificationRow_longArc
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    (D.boundaryIndexClassificationRow k).longArc = D.longArc k :=
  rfl

/-- Classification rows for every selected boundary-walk index. -/
def boundaryIndexClassificationRows
    (D : OuterBoundaryClassificationInputs P) :
    forall k : Fin P.outerCycle.length,
      BoundaryIndexClassificationRow D k :=
  fun k => D.boundaryIndexClassificationRow k

/-- The concrete classification row at the cyclic successor of a boundary
index. -/
def nextBoundaryIndexClassificationRow
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    BoundaryIndexClassificationRow D (P.outerCycle.next k) :=
  D.boundaryIndexClassificationRow (P.outerCycle.next k)

@[simp]
theorem nextBoundaryIndexClassificationRow_edgeKind
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    (D.nextBoundaryIndexClassificationRow k).edgeKind =
      D.toOuterBoundaryWalkBookkeeping.data.edgeKind (P.outerCycle.next k) :=
  rfl

@[simp]
theorem nextBoundaryIndexClassificationRow_vertexKind
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    (D.nextBoundaryIndexClassificationRow k).vertexKind =
      D.toOuterBoundaryWalkBookkeeping.data.vertexKind (P.outerCycle.next k) :=
  rfl

/-- The concrete local row used by the strict Lemma 6 carrier source: a
degree-three non-long-arc gap whose successor edge is triangular and whose
successor vertex has degree three or four. -/
structure BoundaryGapTriangleDegree34Row
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) : Prop where
  gapDegree : IsDegree3 G (P.outerCycle.vertex k)
  notLongArc : Not (D.longArc k)
  triangleNext : IsTriangleEdge G (P.outerCycle.edge (P.outerCycle.next k))
  nextDegree :
    IsDegree3 G (P.outerCycle.vertex (P.outerCycle.next k)) \/
      IsDegree4 G (P.outerCycle.vertex (P.outerCycle.next k))

/-- The strict local row is exactly the four concrete classification facts
used by Lemma 6: degree-three gap, non-long-arc gap, triangular successor
edge, and successor degree three or four. -/
theorem boundaryGapTriangleDegree34Row_iff_components
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length) :
    BoundaryGapTriangleDegree34Row D k <->
      IsDegree3 G (P.outerCycle.vertex k) /\
        Not (D.longArc k) /\
        IsTriangleEdge G (P.outerCycle.edge (P.outerCycle.next k)) /\
        (IsDegree3 G (P.outerCycle.vertex (P.outerCycle.next k)) \/
          IsDegree4 G (P.outerCycle.vertex (P.outerCycle.next k))) := by
  constructor
  · intro row
    exact
      ⟨row.gapDegree, row.notLongArc, row.triangleNext, row.nextDegree⟩
  · intro h
    exact
      { gapDegree := h.1
        notLongArc := h.2.1
        triangleNext := h.2.2.1
        nextDegree := h.2.2.2 }

/-- A contradiction for the four concrete local facts rules out the strict
gap/triangle/degree-3-or-4 boundary row. -/
theorem not_boundaryGapTriangleDegree34Row_of_not_components
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length)
    (hnot :
      Not
        (IsDegree3 G (P.outerCycle.vertex k) /\
          Not (D.longArc k) /\
          IsTriangleEdge G (P.outerCycle.edge (P.outerCycle.next k)) /\
          (IsDegree3 G (P.outerCycle.vertex (P.outerCycle.next k)) \/
            IsDegree4 G (P.outerCycle.vertex (P.outerCycle.next k))))) :
    Not (BoundaryGapTriangleDegree34Row D k) := by
  intro row
  exact hnot ((boundaryGapTriangleDegree34Row_iff_components D k).1 row)

/-- A row-wise contradiction for the four concrete local facts gives the
sharper no-gap field over the whole selected boundary walk. -/
theorem no_boundaryGapTriangleDegree34Rows_of_no_components
    (D : OuterBoundaryClassificationInputs P)
    (hno :
      forall k : Fin P.outerCycle.length,
        Not
          (IsDegree3 G (P.outerCycle.vertex k) /\
            Not (D.longArc k) /\
            IsTriangleEdge G (P.outerCycle.edge (P.outerCycle.next k)) /\
            (IsDegree3 G (P.outerCycle.vertex (P.outerCycle.next k)) \/
              IsDegree4 G (P.outerCycle.vertex (P.outerCycle.next k))))) :
    forall k : Fin P.outerCycle.length,
      Not (BoundaryGapTriangleDegree34Row D k) := by
  intro k
  exact not_boundaryGapTriangleDegree34Row_of_not_components D k (hno k)

/-- Build the strict-carrier local row from concrete boundary-walk class
equalities at `k` and its cyclic successor. -/
def boundaryGapTriangleDegree34RowOfClassifications
    (D : OuterBoundaryClassificationInputs P)
    (k : Fin P.outerCycle.length)
    (gapDegree :
      D.toOuterBoundaryWalkBookkeeping.data.vertexKind k =
        BoundaryDegreeClass.degree3)
    (notLongArc : Not (D.longArc k))
    (triangleNext :
      D.toOuterBoundaryWalkBookkeeping.data.edgeKind (P.outerCycle.next k) =
        BoundaryEdgeClass.triangle)
    (nextDegree :
      D.toOuterBoundaryWalkBookkeeping.data.vertexKind (P.outerCycle.next k) =
          BoundaryDegreeClass.degree3 \/
        D.toOuterBoundaryWalkBookkeeping.data.vertexKind (P.outerCycle.next k) =
          BoundaryDegreeClass.degree4) :
    BoundaryGapTriangleDegree34Row D k where
  gapDegree := (D.boundaryIndexClassificationRow k).degree3Evidence gapDegree
  notLongArc := notLongArc
  triangleNext :=
    (D.nextBoundaryIndexClassificationRow k).triangleEvidence triangleNext
  nextDegree := by
    rcases nextDegree with h3 | h4
    · exact Or.inl
        ((D.nextBoundaryIndexClassificationRow k).degree3Evidence h3)
    · exact Or.inr
        ((D.nextBoundaryIndexClassificationRow k).degree4Evidence h4)

/-! ### Count projections -/

@[simp]
theorem counts_d3
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d3 = Fintype.card D.degree3Indices := by
  change
    Fintype.card D.toOuterBoundaryWalkBookkeeping.data.degree3Indices =
      Fintype.card D.degree3Indices
  exact Fintype.card_congr D.walkDegree3IndicesEquiv

@[simp]
theorem counts_d4
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d4 = Fintype.card D.degree4Indices := by
  change
    Fintype.card D.toOuterBoundaryWalkBookkeeping.data.degree4Indices =
      Fintype.card D.degree4Indices
  exact Fintype.card_congr D.walkDegree4IndicesEquiv

@[simp]
theorem counts_d5
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d5 = Fintype.card D.degree5Indices := by
  change
    Fintype.card D.toOuterBoundaryWalkBookkeeping.data.degree5Indices =
      Fintype.card D.degree5Indices
  exact Fintype.card_congr D.walkDegree5IndicesEquiv

@[simp]
theorem counts_d6
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.d6 = Fintype.card D.degree6Indices := by
  change
    Fintype.card D.toOuterBoundaryWalkBookkeeping.data.degree6Indices =
      Fintype.card D.degree6Indices
  exact Fintype.card_congr D.walkDegree6IndicesEquiv

@[simp]
theorem counts_b
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.b = Fintype.card D.nontriangleEdgeIndices := by
  change
    Fintype.card D.toOuterBoundaryWalkBookkeeping.data.nontriangleEdgeIndices =
      Fintype.card D.nontriangleEdgeIndices
  exact Fintype.card_congr D.walkNontriangleEdgeIndicesEquiv

@[simp]
theorem counts_B
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.B = Fintype.card D.longArcIndices := by
  change
    Fintype.card D.toOuterBoundaryWalkBookkeeping.data.longArcIndices =
      Fintype.card D.longArcIndices
  exact Fintype.card_congr D.walkLongArcIndicesEquiv

@[simp]
theorem counts_negativeCount
    (D : OuterBoundaryClassificationInputs P) :
    D.counts.negativeCount =
      Fintype.card D.nontriangleEdgeIndices +
        Fintype.card D.degree5Indices +
        Fintype.card D.degree6Indices := by
  change
    D.counts.b + D.counts.d5 + D.counts.d6 =
      Fintype.card D.nontriangleEdgeIndices +
        Fintype.card D.degree5Indices +
        Fintype.card D.degree6Indices
  rw [counts_b D, counts_d5 D, counts_d6 D]

/-- The concrete finite bookkeeping projected from the classified walk. -/
def boundaryBookkeeping
    (D : OuterBoundaryClassificationInputs P) :
    BoundaryBookkeeping.{0} :=
  D.toOuterBoundaryWalkBookkeeping.toBoundaryBookkeeping

@[simp]
theorem boundaryBookkeeping_toBoundaryCounts
    (D : OuterBoundaryClassificationInputs P) :
    D.boundaryBookkeeping.toBoundaryCounts = D.counts :=
  rfl

@[simp]
theorem countsRealization_bookkeeping
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping = D.boundaryBookkeeping :=
  rfl

@[simp]
theorem countsRealization_bookkeeping_d3
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping.d3 =
      Fintype.card D.degree3Indices := by
  change D.counts.d3 = Fintype.card D.degree3Indices
  exact D.counts_d3

@[simp]
theorem countsRealization_bookkeeping_d4
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping.d4 =
      Fintype.card D.degree4Indices := by
  change D.counts.d4 = Fintype.card D.degree4Indices
  exact D.counts_d4

@[simp]
theorem countsRealization_bookkeeping_d5
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping.d5 =
      Fintype.card D.degree5Indices := by
  change D.counts.d5 = Fintype.card D.degree5Indices
  exact D.counts_d5

@[simp]
theorem countsRealization_bookkeeping_d6
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping.d6 =
      Fintype.card D.degree6Indices := by
  change D.counts.d6 = Fintype.card D.degree6Indices
  exact D.counts_d6

@[simp]
theorem countsRealization_bookkeeping_b
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping.b =
      Fintype.card D.nontriangleEdgeIndices := by
  change D.counts.b = Fintype.card D.nontriangleEdgeIndices
  exact D.counts_b

@[simp]
theorem countsRealization_bookkeeping_B
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping.longArcCount =
      Fintype.card D.longArcIndices := by
  change D.counts.B = Fintype.card D.longArcIndices
  exact D.counts_B

@[simp]
theorem countsRealization_bookkeeping_negativeElementCount
    (D : OuterBoundaryClassificationInputs P) :
    D.countsRealization.bookkeeping.negativeElementCount =
      Fintype.card D.nontriangleEdgeIndices +
        Fintype.card D.degree5Indices +
        Fintype.card D.degree6Indices := by
  change D.counts.negativeCount =
    Fintype.card D.nontriangleEdgeIndices +
      Fintype.card D.degree5Indices +
      Fintype.card D.degree6Indices
  exact D.counts_negativeCount

/-! ## Planar-boundary final facade projections -/

/-- Package the concrete classified walk with explicit angle comparisons in
the shape consumed by `PlanarBoundaryFinal`. -/
def toOuterBoundaryAngleData
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum) :
    OuterBoundaryAngleClosure.OuterBoundaryAngleData.{u} G :=
  PlanarBoundaryFinal.PlanarBoundaryData.outerBoundaryAngleDataOfWalk
    D.toOuterBoundaryWalkBookkeeping geometricAngleSum
    forced_le_geometric geometric_le_polygon

@[simp]
theorem toOuterBoundaryAngleData_core
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum) :
    (D.toOuterBoundaryAngleData geometricAngleSum
      forced_le_geometric geometric_le_polygon).core = P :=
  rfl

@[simp]
theorem toOuterBoundaryAngleData_counts
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum) :
    (D.toOuterBoundaryAngleData geometricAngleSum
      forced_le_geometric geometric_le_polygon).counts = D.counts :=
  rfl

/-- Build planar-boundary data from the concrete classified walk, explicit
angle comparisons, and raw subpolygon data. -/
def toPlanarBoundaryData
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} G :=
  PlanarBoundaryFinal.PlanarBoundaryData.ofOuterBoundaryWalkSubpolygonData
    D.toOuterBoundaryWalkBookkeeping geometricAngleSum
    forced_le_geometric geometric_le_polygon Subpolygon subpolygonData

@[simp]
theorem toPlanarBoundaryData_core
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
      geometric_le_polygon Subpolygon subpolygonData).core = P :=
  rfl

@[simp]
theorem toPlanarBoundaryData_outerBoundaryCounts
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
      geometric_le_polygon Subpolygon subpolygonData).outerBoundaryCounts =
        D.counts :=
  rfl

/-- Count realization carried by the planar-boundary package built from the
concrete classified walk. -/
def toPlanarBoundaryData_countsRealization
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    BoundaryCountsRealization.{u} :=
  (D.toPlanarBoundaryData geometricAngleSum forced_le_geometric
    geometric_le_polygon Subpolygon subpolygonData).outerAngleBounds.countsRealization

@[simp]
theorem toPlanarBoundaryData_countsRealization_toBoundaryCounts
    (D : OuterBoundaryClassificationInputs P)
    (geometricAngleSum : Real)
    (forced_le_geometric :
      D.counts.forcedBoundaryAngleSum <= geometricAngleSum)
    (geometric_le_polygon :
      geometricAngleSum <= D.counts.polygonAngleSum)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> SubpolygonAssembly.SubpolygonCycleCountAngleData G) :
    (D.toPlanarBoundaryData_countsRealization geometricAngleSum
      forced_le_geometric geometric_le_polygon Subpolygon subpolygonData).toBoundaryCounts =
        D.counts :=
  rfl

end OuterBoundaryClassificationInputs

end

end BoundaryWalkClassificationConcrete
end Swanepoel
end ErdosProblems1066
