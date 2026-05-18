import ErdosProblems1066.Swanepoel.BoundaryCounting

/-!
# Boundary classification bookkeeping

This module records proof-relevant boundary edge and vertex classifications
without constructing the classifications from geometry.  Its finite
bookkeeping projections feed directly into `BoundaryCounting.BoundaryCounts`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryClassification

open BoundaryCounting

universe u

/-! ## Boundary edge classification -/

/-- Boundary edges are either triangle edges or nontriangle edges for the E12
bookkeeping. -/
inductive BoundaryEdgeClass where
  | triangle
  | nontriangle
  deriving DecidableEq, Repr

namespace BoundaryEdgeClass

/-- Contribution of one boundary edge to the `b` count in `BoundaryCounts`. -/
def nontriangleContribution : BoundaryEdgeClass -> Nat
  | triangle => 0
  | nontriangle => 1

@[simp]
theorem nontriangleContribution_triangle :
    nontriangleContribution triangle = 0 :=
  rfl

@[simp]
theorem nontriangleContribution_nontriangle :
    nontriangleContribution nontriangle = 1 :=
  rfl

end BoundaryEdgeClass

/-- A proof-relevant classification of one boundary edge.

The predicates are parameters so downstream files can plug in their own
geometric or graph-theoretic definitions of triangle and nontriangle edges.
-/
structure BoundaryEdgeCertificate
    {E : Type u} (IsTriangle IsNontriangle : E -> Prop) where
  edge : E
  kind : BoundaryEdgeClass
  triangleEvidence : kind = BoundaryEdgeClass.triangle -> IsTriangle edge
  nontriangleEvidence :
    kind = BoundaryEdgeClass.nontriangle -> IsNontriangle edge

namespace BoundaryEdgeCertificate

variable {E : Type u} {IsTriangle IsNontriangle : E -> Prop}

/-- Constructor for a certified triangle boundary edge. -/
def triangle (edge : E) (h : IsTriangle edge) :
    BoundaryEdgeCertificate IsTriangle IsNontriangle where
  edge := edge
  kind := BoundaryEdgeClass.triangle
  triangleEvidence := fun _ => h
  nontriangleEvidence := by
    intro hclass
    cases hclass

/-- Constructor for a certified nontriangle boundary edge. -/
def nontriangle (edge : E) (h : IsNontriangle edge) :
    BoundaryEdgeCertificate IsTriangle IsNontriangle where
  edge := edge
  kind := BoundaryEdgeClass.nontriangle
  triangleEvidence := by
    intro hclass
    cases hclass
  nontriangleEvidence := fun _ => h

/-- Projection of triangle evidence when the class is triangle. -/
theorem isTriangle
    (C : BoundaryEdgeCertificate IsTriangle IsNontriangle)
    (hclass : C.kind = BoundaryEdgeClass.triangle) :
    IsTriangle C.edge :=
  C.triangleEvidence hclass

/-- Projection of nontriangle evidence when the class is nontriangle. -/
theorem isNontriangle
    (C : BoundaryEdgeCertificate IsTriangle IsNontriangle)
    (hclass : C.kind = BoundaryEdgeClass.nontriangle) :
    IsNontriangle C.edge :=
  C.nontriangleEvidence hclass

@[simp]
theorem triangle_class (edge : E) (h : IsTriangle edge) :
    (triangle (IsNontriangle := IsNontriangle) edge h).kind =
      BoundaryEdgeClass.triangle :=
  rfl

@[simp]
theorem nontriangle_class (edge : E) (h : IsNontriangle edge) :
    (nontriangle (IsTriangle := IsTriangle) edge h).kind =
      BoundaryEdgeClass.nontriangle :=
  rfl

end BoundaryEdgeCertificate

/-! ## Boundary degree classification -/

/-- Degree classes that occur in the outer-boundary E12 count. -/
inductive BoundaryDegreeClass where
  | degree3
  | degree4
  | degree5
  | degree6
  deriving DecidableEq, Repr

namespace BoundaryDegreeClass

/-- The natural-number degree represented by a boundary degree class. -/
def degree : BoundaryDegreeClass -> Nat
  | degree3 => 3
  | degree4 => 4
  | degree5 => 5
  | degree6 => 6

/-- Contribution of one boundary vertex to the negative-element count. -/
def negativeContribution : BoundaryDegreeClass -> Nat
  | degree3 => 0
  | degree4 => 0
  | degree5 => 1
  | degree6 => 1

@[simp]
theorem degree_degree3 : degree degree3 = 3 :=
  rfl

@[simp]
theorem degree_degree4 : degree degree4 = 4 :=
  rfl

@[simp]
theorem degree_degree5 : degree degree5 = 5 :=
  rfl

@[simp]
theorem degree_degree6 : degree degree6 = 6 :=
  rfl

@[simp]
theorem negativeContribution_degree3 :
    negativeContribution degree3 = 0 :=
  rfl

@[simp]
theorem negativeContribution_degree4 :
    negativeContribution degree4 = 0 :=
  rfl

@[simp]
theorem negativeContribution_degree5 :
    negativeContribution degree5 = 1 :=
  rfl

@[simp]
theorem negativeContribution_degree6 :
    negativeContribution degree6 = 1 :=
  rfl

end BoundaryDegreeClass

/-- A proof-relevant classification of one boundary vertex by degree class. -/
structure BoundaryDegreeCertificate
    {V : Type u}
    (IsDegree3 IsDegree4 IsDegree5 IsDegree6 : V -> Prop) where
  vertex : V
  kind : BoundaryDegreeClass
  degree3Evidence : kind = BoundaryDegreeClass.degree3 -> IsDegree3 vertex
  degree4Evidence : kind = BoundaryDegreeClass.degree4 -> IsDegree4 vertex
  degree5Evidence : kind = BoundaryDegreeClass.degree5 -> IsDegree5 vertex
  degree6Evidence : kind = BoundaryDegreeClass.degree6 -> IsDegree6 vertex

namespace BoundaryDegreeCertificate

variable {V : Type u}
variable {IsDegree3 IsDegree4 IsDegree5 IsDegree6 : V -> Prop}

/-- Constructor for a certified degree-three boundary vertex. -/
def degree3 (vertex : V) (h : IsDegree3 vertex) :
    BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6 where
  vertex := vertex
  kind := BoundaryDegreeClass.degree3
  degree3Evidence := fun _ => h
  degree4Evidence := by intro hclass; cases hclass
  degree5Evidence := by intro hclass; cases hclass
  degree6Evidence := by intro hclass; cases hclass

/-- Constructor for a certified degree-four boundary vertex. -/
def degree4 (vertex : V) (h : IsDegree4 vertex) :
    BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6 where
  vertex := vertex
  kind := BoundaryDegreeClass.degree4
  degree3Evidence := by intro hclass; cases hclass
  degree4Evidence := fun _ => h
  degree5Evidence := by intro hclass; cases hclass
  degree6Evidence := by intro hclass; cases hclass

/-- Constructor for a certified degree-five boundary vertex. -/
def degree5 (vertex : V) (h : IsDegree5 vertex) :
    BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6 where
  vertex := vertex
  kind := BoundaryDegreeClass.degree5
  degree3Evidence := by intro hclass; cases hclass
  degree4Evidence := by intro hclass; cases hclass
  degree5Evidence := fun _ => h
  degree6Evidence := by intro hclass; cases hclass

/-- Constructor for a certified degree-six boundary vertex. -/
def degree6 (vertex : V) (h : IsDegree6 vertex) :
    BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6 where
  vertex := vertex
  kind := BoundaryDegreeClass.degree6
  degree3Evidence := by intro hclass; cases hclass
  degree4Evidence := by intro hclass; cases hclass
  degree5Evidence := by intro hclass; cases hclass
  degree6Evidence := fun _ => h

/-- Projection of degree-three evidence when the class is degree three. -/
theorem isDegree3
    (C : BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (hclass : C.kind = BoundaryDegreeClass.degree3) :
    IsDegree3 C.vertex :=
  C.degree3Evidence hclass

/-- Projection of degree-four evidence when the class is degree four. -/
theorem isDegree4
    (C : BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (hclass : C.kind = BoundaryDegreeClass.degree4) :
    IsDegree4 C.vertex :=
  C.degree4Evidence hclass

/-- Projection of degree-five evidence when the class is degree five. -/
theorem isDegree5
    (C : BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (hclass : C.kind = BoundaryDegreeClass.degree5) :
    IsDegree5 C.vertex :=
  C.degree5Evidence hclass

/-- Projection of degree-six evidence when the class is degree six. -/
theorem isDegree6
    (C : BoundaryDegreeCertificate IsDegree3 IsDegree4 IsDegree5 IsDegree6)
    (hclass : C.kind = BoundaryDegreeClass.degree6) :
    IsDegree6 C.vertex :=
  C.degree6Evidence hclass

end BoundaryDegreeCertificate

/-! ## Finite bookkeeping projected to `BoundaryCounts` -/

/-- Finite boundary bookkeeping by degree class, edge class, and long arcs.

Only the cardinalities are used by `BoundaryCounts`; keeping the finite types
separate lets later geometric code supply proof-relevant representatives.
-/
structure BoundaryBookkeeping where
  degree3Vertices : Type u
  degree4Vertices : Type u
  degree5Vertices : Type u
  degree6Vertices : Type u
  triangleEdges : Type u
  nontriangleEdges : Type u
  longArcs : Type u
  degree3Fintype : Fintype degree3Vertices
  degree4Fintype : Fintype degree4Vertices
  degree5Fintype : Fintype degree5Vertices
  degree6Fintype : Fintype degree6Vertices
  triangleEdgeFintype : Fintype triangleEdges
  nontriangleEdgeFintype : Fintype nontriangleEdges
  longArcFintype : Fintype longArcs

namespace BoundaryBookkeeping

/-- Number of boundary vertices classified as degree three. -/
def d3 (B : BoundaryBookkeeping.{u}) : Nat :=
  @Fintype.card B.degree3Vertices B.degree3Fintype

/-- Number of boundary vertices classified as degree four. -/
def d4 (B : BoundaryBookkeeping.{u}) : Nat :=
  @Fintype.card B.degree4Vertices B.degree4Fintype

/-- Number of boundary vertices classified as degree five. -/
def d5 (B : BoundaryBookkeeping.{u}) : Nat :=
  @Fintype.card B.degree5Vertices B.degree5Fintype

/-- Number of boundary vertices classified as degree six. -/
def d6 (B : BoundaryBookkeeping.{u}) : Nat :=
  @Fintype.card B.degree6Vertices B.degree6Fintype

/-- Number of triangle boundary edges recorded by the classification. -/
def triangleEdgeCount (B : BoundaryBookkeeping.{u}) : Nat :=
  @Fintype.card B.triangleEdges B.triangleEdgeFintype

/-- Number of nontriangle boundary edges, the `b` field of `BoundaryCounts`. -/
def b (B : BoundaryBookkeeping.{u}) : Nat :=
  @Fintype.card B.nontriangleEdges B.nontriangleEdgeFintype

/-- Number of long arcs, the `B` field of `BoundaryCounts`. -/
def longArcCount (B : BoundaryBookkeeping.{u}) : Nat :=
  @Fintype.card B.longArcs B.longArcFintype

/-- Boundary-count package consumed by the E12 counting theorem. -/
def toBoundaryCounts (B : BoundaryBookkeeping.{u}) : BoundaryCounts where
  d3 := B.d3
  d4 := B.d4
  d5 := B.d5
  d6 := B.d6
  b := B.b
  B := B.longArcCount

/-- Negative-element count induced by the classification bookkeeping. -/
def negativeElementCount (B : BoundaryBookkeeping.{u}) : Nat :=
  B.b + B.d5 + B.d6

@[simp]
theorem toBoundaryCounts_d3 (B : BoundaryBookkeeping.{u}) :
    B.toBoundaryCounts.d3 = B.d3 :=
  rfl

@[simp]
theorem toBoundaryCounts_d4 (B : BoundaryBookkeeping.{u}) :
    B.toBoundaryCounts.d4 = B.d4 :=
  rfl

@[simp]
theorem toBoundaryCounts_d5 (B : BoundaryBookkeeping.{u}) :
    B.toBoundaryCounts.d5 = B.d5 :=
  rfl

@[simp]
theorem toBoundaryCounts_d6 (B : BoundaryBookkeeping.{u}) :
    B.toBoundaryCounts.d6 = B.d6 :=
  rfl

@[simp]
theorem toBoundaryCounts_b (B : BoundaryBookkeeping.{u}) :
    B.toBoundaryCounts.b = B.b :=
  rfl

@[simp]
theorem toBoundaryCounts_B (B : BoundaryBookkeeping.{u}) :
    B.toBoundaryCounts.B = B.longArcCount :=
  rfl

@[simp]
theorem toBoundaryCounts_negativeCount (B : BoundaryBookkeeping.{u}) :
    B.toBoundaryCounts.negativeCount = B.negativeElementCount :=
  rfl

end BoundaryBookkeeping

/-- A finite classification together with an explicit `BoundaryCounts` record
it is meant to realize. -/
structure BoundaryCountsRealization where
  bookkeeping : BoundaryBookkeeping.{u}
  counts : BoundaryCounts
  realizes : bookkeeping.toBoundaryCounts = counts

namespace BoundaryCountsRealization

/-- Canonical realization by the counts projected from finite bookkeeping. -/
def canonical (B : BoundaryBookkeeping.{u}) :
    BoundaryCountsRealization.{u} where
  bookkeeping := B
  counts := B.toBoundaryCounts
  realizes := rfl

/-- Conditional constructor for realizing a pre-existing `BoundaryCounts`
record. -/
def ofEq (B : BoundaryBookkeeping.{u}) (counts : BoundaryCounts)
    (h : B.toBoundaryCounts = counts) :
    BoundaryCountsRealization.{u} where
  bookkeeping := B
  counts := counts
  realizes := h

/-- Projection to the existing boundary-counting input. -/
def toBoundaryCounts (R : BoundaryCountsRealization.{u}) : BoundaryCounts :=
  R.counts

@[simp]
theorem canonical_counts (B : BoundaryBookkeeping.{u}) :
    (canonical B).toBoundaryCounts = B.toBoundaryCounts :=
  rfl

@[simp]
theorem toBoundaryCounts_eq_counts (R : BoundaryCountsRealization.{u}) :
    R.toBoundaryCounts = R.counts :=
  rfl

theorem counts_eq_projected (R : BoundaryCountsRealization.{u}) :
    R.counts = R.bookkeeping.toBoundaryCounts :=
  R.realizes.symm

/-- Pull an angle lower bound on realized counts back to the projected counts. -/
theorem projected_angleLowerBound
    (R : BoundaryCountsRealization.{u})
    (hangle : R.counts.AngleLowerBound) :
    R.bookkeeping.toBoundaryCounts.AngleLowerBound := by
  simpa [R.realizes]
    using hangle

end BoundaryCountsRealization

end BoundaryClassification
end Swanepoel
end ErdosProblems1066
