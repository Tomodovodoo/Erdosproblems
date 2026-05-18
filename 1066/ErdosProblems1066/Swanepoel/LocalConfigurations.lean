import Mathlib

/-!
# Swanepoel local configuration vocabulary

This file is intentionally small.  It only records names for the finite local
graph patterns and index ranges used in the Swanepoel proof plan.  It does not
assert any geometric existence or exclusion result.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace LocalConfigurations

universe u

/-! ## Local graph language -/

/-- A lightweight loopless undirected graph interface for local configurations. -/
structure LocalGraph (V : Type u) where
  Adj : V -> V -> Prop
  symm : forall {a b : V}, Adj a b -> Adj b a
  loopless : forall a : V, Not (Adj a a)

namespace LocalGraph

variable {V : Type u} (G : LocalGraph V)

/-- A vertex adjacent to both endpoints of an edge candidate. -/
def CommonNeighbor (a b x : V) : Prop :=
  G.Adj x a /\ G.Adj x b

/-- The set of all common neighbors of two vertices. -/
def commonNeighborSet (a b : V) : Set V :=
  {x | G.CommonNeighbor a b x}

/-- A local edge that has a triangle witness. -/
def IsTriangleEdge (a b : V) : Prop :=
  G.Adj a b /\ Exists fun x => G.CommonNeighbor a b x

/-- A local edge with no triangle witness. -/
def IsNontriangleEdge (a b : V) : Prop :=
  G.Adj a b /\ forall x : V, Not (G.CommonNeighbor a b x)

/-- Local boundary edge classification used in the Swanepoel bookkeeping. -/
inductive BoundaryEdgeKind where
  | triangle
  | nontriangle
  deriving DecidableEq, Repr

end LocalGraph

/-! ## `K_{2,3}` pattern -/

/-- Five labelled vertices forming the local `K_{2,3}` pattern:
two left vertices and three distinct common neighbors on the right. -/
structure K23Pattern {V : Type u} (G : LocalGraph V) where
  left0 : V
  left1 : V
  right0 : V
  right1 : V
  right2 : V
  left_ne : Not (left0 = left1)
  right01_ne : Not (right0 = right1)
  right02_ne : Not (right0 = right2)
  right12_ne : Not (right1 = right2)
  right0_common : G.CommonNeighbor left0 left1 right0
  right1_common : G.CommonNeighbor left0 left1 right1
  right2_common : G.CommonNeighbor left0 left1 right2

/-- A graph contains a labelled local `K_{2,3}` pattern. -/
def HasK23 {V : Type u} (G : LocalGraph V) : Prop :=
  Nonempty (K23Pattern (V := V) G)

/-! ## Boundary bookkeeping names -/

/-- Negative elements in the boundary count: a nontriangle edge or a high-degree vertex. -/
inductive NegativeElement (V : Type u) where
  | nontriangleEdge (left right : V)
  | degreeFiveVertex (v : V)
  | degreeSixVertex (v : V)

/-- Left endpoint alternatives for a degree-four arc. -/
inductive LeftEndpointKind where
  | L1
  | L2
  deriving DecidableEq, Repr

/-- Right endpoint alternatives for a degree-four arc. -/
inductive RightEndpointKind where
  | R1
  | R2
  deriving DecidableEq, Repr

/-! ## Broken-lattice paper index ranges -/

/-- Paper indices for `p_0, ..., p_{2m-3}`. -/
abbrev BoundaryIndex (m : Nat) : Type :=
  {i : Nat // i <= 2 * m - 3}

/-- Paper indices for `q_0, ..., q_{2m-4}`. -/
abbrev TriangleIndex (m : Nat) : Type :=
  {i : Nat // i <= 2 * m - 4}

/-- Paper indices for turns `tau_1, ..., tau_{2m-3}`. -/
abbrev TurnIndex (m : Nat) : Type :=
  {i : Nat // 1 <= i /\ i <= 2 * m - 3}

/-- Paper indices for extra neighbors `r_i,s_i`, `i = 1, ..., 2m-5`. -/
abbrev ExtraIndex (m : Nat) : Type :=
  {i : Nat // 1 <= i /\ i <= 2 * m - 5}

/-- Paper indices for Lemma 10 comparisons `s_i = r_{i+1}`. -/
abbrev Lemma10Index (m : Nat) : Type :=
  {i : Nat // 1 <= i /\ i <= 2 * m - 6}

/-- Paper indices for starts of three consecutive Lemma 10 comparisons. -/
abbrev TripleStartIndex (m : Nat) : Type :=
  {i : Nat // 1 <= i /\ i + 2 <= 2 * m - 6}

/-- The labelled vertices in a broken-lattice local configuration. -/
structure BrokenLatticeLabels (V : Type u) (m : Nat) where
  p : BoundaryIndex m -> V
  q : TriangleIndex m -> V
  r : ExtraIndex m -> V
  s : ExtraIndex m -> V

/-- Local predicates attached to broken-lattice labels, without proving any of them. -/
structure BrokenLatticePredicates {V : Type u} (G : LocalGraph V) (m : Nat) where
  labels : BrokenLatticeLabels V m
  boundaryEdge : TriangleIndex m -> Prop
  triangleWitness : TriangleIndex m -> Prop
  extraNeighborWitness : ExtraIndex m -> Prop
  lemma10Equality : Lemma10Index m -> Prop
  tripleEquality : TripleStartIndex m -> Prop

end LocalConfigurations
end Swanepoel
end ErdosProblems1066
