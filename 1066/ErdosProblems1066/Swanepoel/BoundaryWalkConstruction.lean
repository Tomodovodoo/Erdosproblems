import ErdosProblems1066.Swanepoel.BoundaryWalkBridge
import ErdosProblems1066.Swanepoel.OuterBoundaryCore
import ErdosProblems1066.Swanepoel.BoundaryClassification

/-!
# Boundary-walk construction bookkeeping

This module turns explicit finite boundary-cycle data into the proof-relevant
edge and degree certificates used by `BoundaryClassification`.

The geometric or Jordan-style inputs are not constructed here.  A caller
supplies a boundary cycle, the relevant edge/degree predicates, explicit
evidence for each selected class, and an explicit long-arc predicate.  The
lemmas below only prove finite bookkeeping conversions and projections back to
the existing boundary-walk and outer-boundary interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryWalkConstruction

open BoundaryClassification
open BoundaryCounting
open FaceReduction
open OuterBoundaryInterface
open PlanarInterface

universe u

noncomputable section

variable {n : Nat}

/-! ## Certificate tables over an explicit boundary cycle -/

/-- A table of edge certificates indexed by the edges of a boundary cycle. -/
structure BoundaryEdgeCertificateTable
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G)
    (IsTriangle IsNontriangle : Edge n -> Prop) where
  certificate :
    forall _ : Fin C.length,
      BoundaryEdgeCertificate IsTriangle IsNontriangle
  edge_eq : forall k : Fin C.length, (certificate k).edge = C.edge k

namespace BoundaryEdgeCertificateTable

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {IsTriangle IsNontriangle : Edge n -> Prop}

/-- Build edge certificates from an explicit class function and evidence. -/
def ofKind
    (edgeKind : Fin C.length -> BoundaryEdgeClass)
    (triangleEvidence :
      forall k : Fin C.length,
        edgeKind k = BoundaryEdgeClass.triangle -> IsTriangle (C.edge k))
    (nontriangleEvidence :
      forall k : Fin C.length,
        edgeKind k = BoundaryEdgeClass.nontriangle ->
          IsNontriangle (C.edge k)) :
    BoundaryEdgeCertificateTable C IsTriangle IsNontriangle where
  certificate := fun k =>
    { edge := C.edge k
      kind := edgeKind k
      triangleEvidence := triangleEvidence k
      nontriangleEvidence := nontriangleEvidence k }
  edge_eq := fun _ => rfl

@[simp]
theorem certificate_edge
    (T : BoundaryEdgeCertificateTable C IsTriangle IsNontriangle)
    (k : Fin C.length) :
    (T.certificate k).edge = C.edge k :=
  T.edge_eq k

@[simp]
theorem ofKind_certificate_kind
    (edgeKind : Fin C.length -> BoundaryEdgeClass)
    (triangleEvidence :
      forall k : Fin C.length,
        edgeKind k = BoundaryEdgeClass.triangle -> IsTriangle (C.edge k))
    (nontriangleEvidence :
      forall k : Fin C.length,
        edgeKind k = BoundaryEdgeClass.nontriangle ->
          IsNontriangle (C.edge k))
    (k : Fin C.length) :
    ((ofKind (C := C) edgeKind triangleEvidence nontriangleEvidence).certificate k).kind =
      edgeKind k :=
  rfl

/-- The certified edge is one of the finite cyclic boundary edges. -/
theorem edge_mem_edgeFinset
    (T : BoundaryEdgeCertificateTable C IsTriangle IsNontriangle)
    (k : Fin C.length) :
    Membership.mem C.edgeFinset (T.certificate k).edge := by
  rw [T.edge_eq k]
  exact C.edge_mem_edgeFinset k

/-- A validated edge certificate inherits graph adjacency from the cycle. -/
theorem adjacent
    (T : BoundaryEdgeCertificateTable C IsTriangle IsNontriangle)
    (k : Fin C.length) :
    G.Adj (T.certificate k).edge.1 (T.certificate k).edge.2 := by
  rw [T.edge_eq k]
  exact C.edge_adjacent k

/-- A validated edge certificate inherits unit-distance adjacency. -/
theorem unitDistanceAdj
    (T : BoundaryEdgeCertificateTable C IsTriangle IsNontriangle)
    (k : Fin C.length) :
    GraphBridge.UnitDistanceAdj G.config
      (T.certificate k).edge.1 (T.certificate k).edge.2 := by
  rw [T.edge_eq k]
  exact C.edge_unitDistanceAdj k

/-- A validated edge certificate has Euclidean length one. -/
theorem dist_eq_one
    (T : BoundaryEdgeCertificateTable C IsTriangle IsNontriangle)
    (k : Fin C.length) :
    Geometry.Distance.eucDist
        (G.point (T.certificate k).edge.1)
        (G.point (T.certificate k).edge.2) = 1 := by
  rw [T.edge_eq k]
  exact C.edge_dist_eq_one k

/-- Recover triangle evidence for the cycle edge. -/
theorem isTriangle
    (T : BoundaryEdgeCertificateTable C IsTriangle IsNontriangle)
    {k : Fin C.length}
    (hclass : (T.certificate k).kind = BoundaryEdgeClass.triangle) :
    IsTriangle (C.edge k) := by
  simpa [T.edge_eq k] using (T.certificate k).isTriangle hclass

/-- Recover nontriangle evidence for the cycle edge. -/
theorem isNontriangle
    (T : BoundaryEdgeCertificateTable C IsTriangle IsNontriangle)
    {k : Fin C.length}
    (hclass : (T.certificate k).kind = BoundaryEdgeClass.nontriangle) :
    IsNontriangle (C.edge k) := by
  simpa [T.edge_eq k] using (T.certificate k).isNontriangle hclass

end BoundaryEdgeCertificateTable

/-- A table of degree certificates indexed by the vertices of a boundary cycle. -/
structure BoundaryDegreeCertificateTable
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G)
    (IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop) where
  certificate :
    forall _ : Fin C.length,
      BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6
  vertex_eq : forall k : Fin C.length, (certificate k).vertex = C.vertex k

namespace BoundaryDegreeCertificateTable

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}

/-- Build degree certificates from an explicit class function and evidence. -/
def ofKind
    (vertexKind : Fin C.length -> BoundaryDegreeClass)
    (degree3Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree3 -> IsDegree3 (C.vertex k))
    (degree4Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree4 -> IsDegree4 (C.vertex k))
    (degree5Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree5 -> IsDegree5 (C.vertex k))
    (degree6Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree6 -> IsDegree6 (C.vertex k)) :
    BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6 where
  certificate := fun k =>
    { vertex := C.vertex k
      kind := vertexKind k
      degree3Evidence := degree3Evidence k
      degree4Evidence := degree4Evidence k
      degree5Evidence := degree5Evidence k
      degree6Evidence := degree6Evidence k }
  vertex_eq := fun _ => rfl

@[simp]
theorem certificate_vertex
    (T : BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    (T.certificate k).vertex = C.vertex k :=
  T.vertex_eq k

@[simp]
theorem ofKind_certificate_kind
    (vertexKind : Fin C.length -> BoundaryDegreeClass)
    (degree3Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree3 -> IsDegree3 (C.vertex k))
    (degree4Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree4 -> IsDegree4 (C.vertex k))
    (degree5Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree5 -> IsDegree5 (C.vertex k))
    (degree6Evidence :
      forall k : Fin C.length,
        vertexKind k = BoundaryDegreeClass.degree6 -> IsDegree6 (C.vertex k))
    (k : Fin C.length) :
    ((ofKind (C := C) vertexKind degree3Evidence degree4Evidence
      degree5Evidence degree6Evidence).certificate k).kind =
        vertexKind k :=
  rfl

/-- The validated certificate vertices are injectively indexed. -/
theorem certificate_injective
    (T : BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Function.Injective fun k : Fin C.length => (T.certificate k).vertex := by
  intro i j h
  apply C.simple
  simpa [T.vertex_eq i, T.vertex_eq j] using h

/-- Recover degree-three evidence for the cycle vertex. -/
theorem isDegree3
    (T : BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    {k : Fin C.length}
    (hclass : (T.certificate k).kind = BoundaryDegreeClass.degree3) :
    IsDegree3 (C.vertex k) := by
  simpa [T.vertex_eq k] using (T.certificate k).isDegree3 hclass

/-- Recover degree-four evidence for the cycle vertex. -/
theorem isDegree4
    (T : BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    {k : Fin C.length}
    (hclass : (T.certificate k).kind = BoundaryDegreeClass.degree4) :
    IsDegree4 (C.vertex k) := by
  simpa [T.vertex_eq k] using (T.certificate k).isDegree4 hclass

/-- Recover degree-five evidence for the cycle vertex. -/
theorem isDegree5
    (T : BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    {k : Fin C.length}
    (hclass : (T.certificate k).kind = BoundaryDegreeClass.degree5) :
    IsDegree5 (C.vertex k) := by
  simpa [T.vertex_eq k] using (T.certificate k).isDegree5 hclass

/-- Recover degree-six evidence for the cycle vertex. -/
theorem isDegree6
    (T : BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    {k : Fin C.length}
    (hclass : (T.certificate k).kind = BoundaryDegreeClass.degree6) :
    IsDegree6 (C.vertex k) := by
  simpa [T.vertex_eq k] using (T.certificate k).isDegree6 hclass

end BoundaryDegreeCertificateTable

/-! ## Finite class bookkeeping from indexed boundary data -/

/-- Edge contribution as an `if` expression, useful for finite sums. -/
theorem edge_nontriangleContribution_eq_ite
    (c : BoundaryEdgeClass) :
    BoundaryEdgeClass.nontriangleContribution c =
      if c = BoundaryEdgeClass.nontriangle then 1 else 0 := by
  cases c <;> simp [BoundaryEdgeClass.nontriangleContribution]

/-- Degree negative contribution as two indicator functions. -/
theorem degree_negativeContribution_eq_ite
    (c : BoundaryDegreeClass) :
    BoundaryDegreeClass.negativeContribution c =
      (if c = BoundaryDegreeClass.degree5 then 1 else 0) +
        if c = BoundaryDegreeClass.degree6 then 1 else 0 := by
  cases c <;> simp [BoundaryDegreeClass.negativeContribution]

/--
Explicit finite bookkeeping over one boundary cycle.

`longArc` is a supplied predicate on boundary indices; no geometric long-arc
fact is derived here.
-/
structure BoundaryWalkBookkeeping
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (C : BoundaryCycle G)
    (IsTriangle IsNontriangle : Edge n -> Prop)
    (IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop) where
  edgeKind : Fin C.length -> BoundaryEdgeClass
  vertexKind : Fin C.length -> BoundaryDegreeClass
  longArc : Fin C.length -> Prop
  longArcDecidable : forall k : Fin C.length, Decidable (longArc k)
  edge_triangleEvidence :
    forall k : Fin C.length,
      edgeKind k = BoundaryEdgeClass.triangle -> IsTriangle (C.edge k)
  edge_nontriangleEvidence :
    forall k : Fin C.length,
      edgeKind k = BoundaryEdgeClass.nontriangle -> IsNontriangle (C.edge k)
  degree3Evidence :
    forall k : Fin C.length,
      vertexKind k = BoundaryDegreeClass.degree3 -> IsDegree3 (C.vertex k)
  degree4Evidence :
    forall k : Fin C.length,
      vertexKind k = BoundaryDegreeClass.degree4 -> IsDegree4 (C.vertex k)
  degree5Evidence :
    forall k : Fin C.length,
      vertexKind k = BoundaryDegreeClass.degree5 -> IsDegree5 (C.vertex k)
  degree6Evidence :
    forall k : Fin C.length,
      vertexKind k = BoundaryDegreeClass.degree6 -> IsDegree6 (C.vertex k)

namespace BoundaryWalkBookkeeping

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {C : BoundaryCycle G}
variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}

/-- Certified edge at boundary index `k`. -/
def edgeCertificate
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    BoundaryEdgeCertificate IsTriangle IsNontriangle where
  edge := C.edge k
  kind := D.edgeKind k
  triangleEvidence := D.edge_triangleEvidence k
  nontriangleEvidence := D.edge_nontriangleEvidence k

/-- Certified degree at boundary index `k`. -/
def degreeCertificate
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    BoundaryDegreeCertificate
      IsDegree3 IsDegree4 IsDegree5 IsDegree6 where
  vertex := C.vertex k
  kind := D.vertexKind k
  degree3Evidence := D.degree3Evidence k
  degree4Evidence := D.degree4Evidence k
  degree5Evidence := D.degree5Evidence k
  degree6Evidence := D.degree6Evidence k

@[simp]
theorem edgeCertificate_edge
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    (D.edgeCertificate k).edge = C.edge k :=
  rfl

@[simp]
theorem edgeCertificate_kind
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    (D.edgeCertificate k).kind = D.edgeKind k :=
  rfl

@[simp]
theorem degreeCertificate_vertex
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    (D.degreeCertificate k).vertex = C.vertex k :=
  rfl

@[simp]
theorem degreeCertificate_kind
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin C.length) :
    (D.degreeCertificate k).kind = D.vertexKind k :=
  rfl

/-- Edge certificates packaged as a validated table. -/
def toEdgeCertificateTable
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryEdgeCertificateTable C IsTriangle IsNontriangle where
  certificate := D.edgeCertificate
  edge_eq := fun _ => rfl

/-- Degree certificates packaged as a validated table. -/
def toDegreeCertificateTable
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryDegreeCertificateTable
      C IsDegree3 IsDegree4 IsDegree5 IsDegree6 where
  certificate := D.degreeCertificate
  vertex_eq := fun _ => rfl

/-- Indices of degree-three boundary vertices. -/
def degree3Indices
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Type :=
  { k : Fin C.length // D.vertexKind k = BoundaryDegreeClass.degree3 }

/-- Indices of degree-four boundary vertices. -/
def degree4Indices
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Type :=
  { k : Fin C.length // D.vertexKind k = BoundaryDegreeClass.degree4 }

/-- Indices of degree-five boundary vertices. -/
def degree5Indices
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Type :=
  { k : Fin C.length // D.vertexKind k = BoundaryDegreeClass.degree5 }

/-- Indices of degree-six boundary vertices. -/
def degree6Indices
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Type :=
  { k : Fin C.length // D.vertexKind k = BoundaryDegreeClass.degree6 }

/-- Indices of triangle boundary edges. -/
def triangleEdgeIndices
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Type :=
  { k : Fin C.length // D.edgeKind k = BoundaryEdgeClass.triangle }

/-- Indices of nontriangle boundary edges. -/
def nontriangleEdgeIndices
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Type :=
  { k : Fin C.length // D.edgeKind k = BoundaryEdgeClass.nontriangle }

/-- Indices of supplied long arcs. -/
def longArcIndices
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Type :=
  { k : Fin C.length // D.longArc k }

instance degree3Indices_fintype
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Fintype (D.degree3Indices) := by
  unfold degree3Indices
  infer_instance

instance degree4Indices_fintype
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Fintype (D.degree4Indices) := by
  unfold degree4Indices
  infer_instance

instance degree5Indices_fintype
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Fintype (D.degree5Indices) := by
  unfold degree5Indices
  infer_instance

instance degree6Indices_fintype
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Fintype (D.degree6Indices) := by
  unfold degree6Indices
  infer_instance

instance triangleEdgeIndices_fintype
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Fintype (D.triangleEdgeIndices) := by
  unfold triangleEdgeIndices
  infer_instance

instance nontriangleEdgeIndices_fintype
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Fintype (D.nontriangleEdgeIndices) := by
  unfold nontriangleEdgeIndices
  infer_instance

instance longArcIndices_fintype
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    Fintype (D.longArcIndices) := by
  unfold longArcIndices
  letI : DecidablePred D.longArc := D.longArcDecidable
  infer_instance

/-- Convert indexed boundary-walk classifications to the existing finite
`BoundaryBookkeeping` record. -/
def toBoundaryBookkeeping
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryBookkeeping.{0} where
  degree3Vertices := D.degree3Indices
  degree4Vertices := D.degree4Indices
  degree5Vertices := D.degree5Indices
  degree6Vertices := D.degree6Indices
  triangleEdges := D.triangleEdgeIndices
  nontriangleEdges := D.nontriangleEdgeIndices
  longArcs := D.longArcIndices
  degree3Fintype := inferInstance
  degree4Fintype := inferInstance
  degree5Fintype := inferInstance
  degree6Fintype := inferInstance
  triangleEdgeFintype := inferInstance
  nontriangleEdgeFintype := inferInstance
  longArcFintype := inferInstance

/-- The canonical `BoundaryCountsRealization` induced by indexed data. -/
def toBoundaryCountsRealization
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryCountsRealization.{0} :=
  BoundaryCountsRealization.canonical D.toBoundaryBookkeeping

/-- The realized counts projected from indexed data. -/
def counts
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryCounts :=
  D.toBoundaryBookkeeping.toBoundaryCounts

@[simp]
theorem counts_eq
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.counts = D.toBoundaryBookkeeping.toBoundaryCounts :=
  rfl

@[simp]
theorem toBoundaryBookkeeping_d3
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.toBoundaryBookkeeping.d3 = Fintype.card D.degree3Indices :=
  rfl

@[simp]
theorem toBoundaryBookkeeping_d4
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.toBoundaryBookkeeping.d4 = Fintype.card D.degree4Indices :=
  rfl

@[simp]
theorem toBoundaryBookkeeping_d5
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.toBoundaryBookkeeping.d5 = Fintype.card D.degree5Indices :=
  rfl

@[simp]
theorem toBoundaryBookkeeping_d6
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.toBoundaryBookkeeping.d6 = Fintype.card D.degree6Indices :=
  rfl

@[simp]
theorem toBoundaryBookkeeping_b
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.toBoundaryBookkeeping.b = Fintype.card D.nontriangleEdgeIndices :=
  rfl

@[simp]
theorem toBoundaryBookkeeping_B
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.toBoundaryBookkeeping.longArcCount = Fintype.card D.longArcIndices :=
  rfl

@[simp]
theorem countsRealization_counts
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    D.toBoundaryCountsRealization.toBoundaryCounts = D.counts :=
  rfl

/-- The nontriangle contribution sum is exactly the projected `b` count. -/
theorem nontriangleContribution_sum_eq_b
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    (Finset.univ.sum fun k : Fin C.length =>
      BoundaryEdgeClass.nontriangleContribution (D.edgeKind k)) =
        D.counts.b := by
  classical
  change
    (Finset.univ.sum fun k : Fin C.length =>
      BoundaryEdgeClass.nontriangleContribution (D.edgeKind k)) =
        Fintype.card D.nontriangleEdgeIndices
  unfold nontriangleEdgeIndices
  rw [Fintype.card_subtype]
  simp_rw [edge_nontriangleContribution_eq_ite]
  rw [Finset.sum_boole]
  norm_num

/-- The negative degree contribution sum is exactly `d5 + d6`. -/
theorem degreeNegativeContribution_sum_eq_d5_add_d6
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    (Finset.univ.sum fun k : Fin C.length =>
      BoundaryDegreeClass.negativeContribution (D.vertexKind k)) =
        D.counts.d5 + D.counts.d6 := by
  classical
  change
    (Finset.univ.sum fun k : Fin C.length =>
      BoundaryDegreeClass.negativeContribution (D.vertexKind k)) =
        Fintype.card D.degree5Indices + Fintype.card D.degree6Indices
  unfold degree5Indices degree6Indices
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simp_rw [degree_negativeContribution_eq_ite]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_boole, Finset.sum_boole]
  norm_num

/-- Edge and degree indicator sums realize the negative-element count. -/
theorem contribution_sum_eq_negativeCount
    (D : BoundaryWalkBookkeeping C IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    (Finset.univ.sum fun k : Fin C.length =>
      BoundaryEdgeClass.nontriangleContribution (D.edgeKind k)) +
      (Finset.univ.sum fun k : Fin C.length =>
        BoundaryDegreeClass.negativeContribution (D.vertexKind k)) =
        D.counts.negativeCount := by
  rw [D.nontriangleContribution_sum_eq_b,
    D.degreeNegativeContribution_sum_eq_d5_add_d6]
  simp [BoundaryCounts.negativeCount, Nat.add_assoc]

end BoundaryWalkBookkeeping

/-! ## Outer-boundary adapters -/

/-- Indexed bookkeeping for the selected outer boundary of an
`OuterBoundaryCore`. -/
structure OuterBoundaryWalkBookkeeping
    {G : CanonicalStraightLineUnitDistanceGraph n}
    (P : OuterBoundaryCore G)
    (IsTriangle IsNontriangle : Edge n -> Prop)
    (IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop) where
  data :
    BoundaryWalkBookkeeping P.outerCycle IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6

namespace OuterBoundaryWalkBookkeeping

variable {G : CanonicalStraightLineUnitDistanceGraph n}
variable {P : OuterBoundaryCore G}
variable {IsTriangle IsNontriangle : Edge n -> Prop}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : Fin n -> Prop}

/-- The finite bookkeeping record induced by the outer-boundary walk. -/
def toBoundaryBookkeeping
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryBookkeeping.{0} :=
  D.data.toBoundaryBookkeeping

/-- The `BoundaryCounts` induced by the outer-boundary walk. -/
def counts
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryCounts :=
  D.data.counts

/-- The count-realization certificate induced by the outer-boundary walk. -/
def toBoundaryCountsRealization
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6) :
    BoundaryCountsRealization.{0} :=
  D.data.toBoundaryCountsRealization

/-- Edge certificate for the selected outer boundary. -/
def edgeCertificate
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    BoundaryEdgeCertificate IsTriangle IsNontriangle :=
  D.data.edgeCertificate k

/-- Degree certificate for the selected outer boundary. -/
def degreeCertificate
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    BoundaryDegreeCertificate
      IsDegree3 IsDegree4 IsDegree5 IsDegree6 :=
  D.data.degreeCertificate k

@[simp]
theorem edgeCertificate_edge
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    (D.edgeCertificate k).edge = P.outerCycle.edge k :=
  rfl

@[simp]
theorem degreeCertificate_vertex
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    (D.degreeCertificate k).vertex = P.outerCycle.vertex k :=
  rfl

/-- The certified outer-boundary edge is graph-adjacent. -/
theorem edgeCertificate_adjacent
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    G.Adj (D.edgeCertificate k).edge.1 (D.edgeCertificate k).edge.2 := by
  rw [D.edgeCertificate_edge k]
  exact P.outerCycle.edge_adjacent k

/-- The certified outer-boundary edge has unit-distance adjacency. -/
theorem edgeCertificate_unitDistanceAdj
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    GraphBridge.UnitDistanceAdj G.config
      (D.edgeCertificate k).edge.1 (D.edgeCertificate k).edge.2 := by
  rw [D.edgeCertificate_edge k]
  exact P.outerCycle.edge_unitDistanceAdj k

/-- The certified outer-boundary edge has Euclidean length one. -/
theorem edgeCertificate_dist_eq_one
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    Geometry.Distance.eucDist
        (G.point (D.edgeCertificate k).edge.1)
        (G.point (D.edgeCertificate k).edge.2) = 1 := by
  rw [D.edgeCertificate_edge k]
  exact P.outerCycle.edge_dist_eq_one k

/-- The certified outer-boundary vertex satisfies the supplied boundary
predicate from the core. -/
theorem degreeCertificate_onBoundary
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    P.outerEnclosure.onBoundary (D.degreeCertificate k).vertex := by
  rw [D.degreeCertificate_vertex k]
  simpa [OuterBoundaryCore.outerCycle] using P.boundary_vertex_onBoundary k

/-- The certified outer-boundary vertex is inside or on the supplied
enclosure. -/
theorem degreeCertificate_insideOrOn
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (k : Fin P.outerCycle.length) :
    P.outerEnclosure.insideOrOn (G.point (D.degreeCertificate k).vertex) := by
  rw [D.degreeCertificate_vertex k]
  simpa [OuterBoundaryCore.outerCycle] using P.boundary_point_insideOrOn k

/-- Package the induced counts for the canonical face-counting bridge once the
angle lower bound has been supplied explicitly. -/
def toCanonicalBoundaryCountHypotheses
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (angleLowerBound : D.counts.AngleLowerBound) :
    FaceCountingBridge.CanonicalBoundaryCountHypotheses G :=
  P.toCanonicalBoundaryCountHypotheses D.counts angleLowerBound

/-- Extend an outer-boundary core to the existing package using counts
constructed from the boundary walk. -/
def toOuterBoundaryPackage
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (angleLowerBound : D.counts.AngleLowerBound)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> OuterBoundaryInterface.SubpolygonData G) :
    OuterBoundaryInterface.OuterBoundaryPackage G :=
  P.toOuterBoundaryPackage D.counts angleLowerBound Subpolygon subpolygonData

/-- Extend an outer-boundary core to the construction package using counts
constructed from the boundary walk. -/
def toOuterBoundaryConstruction
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (angleLowerBound : D.counts.AngleLowerBound)
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon -> OuterBoundaryReduction.SubpolygonConstructionData G) :
    OuterBoundaryReduction.OuterBoundaryConstruction G :=
  P.toOuterBoundaryConstruction
    D.counts angleLowerBound Subpolygon subpolygonData

/-- The constructed counts satisfy E12 when the angle lower bound is supplied. -/
theorem boundaryAngleCountInequality
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (angleLowerBound : D.counts.AngleLowerBound) :
    D.counts.d5 + 2 * D.counts.d6 + D.counts.b + D.counts.B + 6 <=
      D.counts.d3 :=
  (D.toCanonicalBoundaryCountHypotheses angleLowerBound).boundaryAngleCountInequality

/-- The constructed counts satisfy the negative-element E12 form when the
angle lower bound is supplied. -/
theorem boundaryNegativeCountInequality
    (D : OuterBoundaryWalkBookkeeping P IsTriangle IsNontriangle
      IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (angleLowerBound : D.counts.AngleLowerBound) :
    D.counts.negativeCount + D.counts.B + 6 <= D.counts.d3 :=
  (D.toCanonicalBoundaryCountHypotheses angleLowerBound).boundaryNegativeCountInequality

end OuterBoundaryWalkBookkeeping

end

end BoundaryWalkConstruction
end Swanepoel
end ErdosProblems1066
