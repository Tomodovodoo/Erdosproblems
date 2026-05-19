import ErdosProblems1066.Swanepoel.BoundaryLabelCertificateAssembly
import ErdosProblems1066.Swanepoel.NoEarlyTripleObstructionConcrete

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Concrete `K_{2,3}` obstruction inputs

This module supplies a small concrete layer in front of
`NoEarlyTripleObstructionConcrete`.

The downstream no-early route wants five implications from an early
triple-equality start to a local `K_{2,3}`.  Here we expose a graph-theoretic
common-neighbor certificate for such a `K_{2,3}`, prove that it feeds the
existing obstruction package, and route the currently available finite
unit-distance local exclusions back into the minimal-failure wrapper without
an extra `K23DegreeReducible` assumption.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace K23ObstructionConcrete

open GraphBridge
open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations
open MinimalFailureLocalExclusions
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleObstructionConcrete

universe u

variable {V : Type u} {G : LocalGraph V}

/-! ## Concrete common-neighbor witnesses -/

/-- Three distinct common neighbors of a pair of distinct vertices. -/
structure ThreeCommonNeighborWitness
    (G : LocalGraph V) where
  left0 : V
  left1 : V
  right0 : V
  right1 : V
  right2 : V
  left_ne : left0 ≠ left1
  right01_ne : right0 ≠ right1
  right02_ne : right0 ≠ right2
  right12_ne : right1 ≠ right2
  right0_common : G.CommonNeighbor left0 left1 right0
  right1_common : G.CommonNeighbor left0 left1 right1
  right2_common : G.CommonNeighbor left0 left1 right2

namespace ThreeCommonNeighborWitness

/-- A labelled `K_{2,3}` pattern is the same data as a concrete
three-common-neighbor witness. -/
def ofK23Pattern (P : K23Pattern G) : ThreeCommonNeighborWitness G where
  left0 := P.left0
  left1 := P.left1
  right0 := P.right0
  right1 := P.right1
  right2 := P.right2
  left_ne := P.left_ne
  right01_ne := P.right01_ne
  right02_ne := P.right02_ne
  right12_ne := P.right12_ne
  right0_common := P.right0_common
  right1_common := P.right1_common
  right2_common := P.right2_common

/-- An existential `K_{2,3}` certificate can be re-labelled as a concrete
three-common-neighbor witness. -/
def ofHasK23 (h : HasK23 G) : ThreeCommonNeighborWitness G :=
  ofK23Pattern (Classical.choice h)

/-- A three-common-neighbor witness is exactly a labelled `K_{2,3}` pattern. -/
def toK23Pattern (W : ThreeCommonNeighborWitness G) : K23Pattern G where
  left0 := W.left0
  left1 := W.left1
  right0 := W.right0
  right1 := W.right1
  right2 := W.right2
  left_ne := W.left_ne
  right01_ne := W.right01_ne
  right02_ne := W.right02_ne
  right12_ne := W.right12_ne
  right0_common := W.right0_common
  right1_common := W.right1_common
  right2_common := W.right2_common

/-- A three-common-neighbor witness produces `HasK23`. -/
theorem hasK23 (W : ThreeCommonNeighborWitness G) : HasK23 G :=
  Nonempty.intro (toK23Pattern W)

section Finite

variable [Fintype V] [DecidableEq V]

/-- The left vertex of a concrete `K_{2,3}` witness has degree at least
three. -/
theorem degree_left0_ge_three (W : ThreeCommonNeighborWitness G) :
    3 <= LocalExclusions.LocalGraph.degree G W.left0 :=
  LocalExclusions.LocalGraph.degree_ge_three_left0_of_K23Pattern
    G (toK23Pattern W)

/-- The other left vertex of a concrete `K_{2,3}` witness has degree at least
three. -/
theorem degree_left1_ge_three (W : ThreeCommonNeighborWitness G) :
    3 <= LocalExclusions.LocalGraph.degree G W.left1 :=
  LocalExclusions.LocalGraph.degree_ge_three_left1_of_K23Pattern
    G (toK23Pattern W)

end Finite

end ThreeCommonNeighborWitness

/-! ## Start-indexed obstruction inputs -/

/-- Concrete local data: each of the five early triple equalities produces a
three-common-neighbor witness. -/
structure M8ConcreteThreeCommonNeighborObstructionInputs
    (P : BrokenLatticePredicates G 8) where
  witness_start1 :
    P.tripleEquality start1 -> ThreeCommonNeighborWitness G
  witness_start2 :
    P.tripleEquality start2 -> ThreeCommonNeighborWitness G
  witness_start3 :
    P.tripleEquality start3 -> ThreeCommonNeighborWitness G
  witness_start4 :
    P.tripleEquality start4 -> ThreeCommonNeighborWitness G
  witness_start5 :
    P.tripleEquality start5 -> ThreeCommonNeighborWitness G

namespace M8ConcreteThreeCommonNeighborObstructionInputs

variable {P : BrokenLatticePredicates G 8}

/-- Convert concrete three-common-neighbor data into the K23 obstruction
package consumed by `NoEarlyTripleObstructionConcrete`. -/
def toK23ObstructionInputs
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P) :
    M8ConcreteK23ObstructionInputs P where
  forbidden_start1 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start1 h)
  forbidden_start2 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start2 h)
  forbidden_start3 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start3 h)
  forbidden_start4 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start4 h)
  forbidden_start5 h := ThreeCommonNeighborWitness.hasK23 (H.witness_start5 h)

/-- Re-label K23 obstruction inputs as explicit three-common-neighbor inputs.
The two structures carry the same local geometry; this direction chooses a
witness from the existential `HasK23` field. -/
def ofK23ObstructionInputs
    (H : M8ConcreteK23ObstructionInputs P) :
    M8ConcreteThreeCommonNeighborObstructionInputs P where
  witness_start1 h := ThreeCommonNeighborWitness.ofHasK23 (H.forbidden_start1 h)
  witness_start2 h := ThreeCommonNeighborWitness.ofHasK23 (H.forbidden_start2 h)
  witness_start3 h := ThreeCommonNeighborWitness.ofHasK23 (H.forbidden_start3 h)
  witness_start4 h := ThreeCommonNeighborWitness.ofHasK23 (H.forbidden_start4 h)
  witness_start5 h := ThreeCommonNeighborWitness.ofHasK23 (H.forbidden_start5 h)

/-- Select the concrete witness attached to any early start. -/
def witness_of_early_triple
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P)
    {a : M8TripleStartIndex}
    (hearly : M8TripleStartEarly a)
    (htriple : P.tripleEquality a) :
    ThreeCommonNeighborWitness G := by
  classical
  by_cases h1 : a.1 = 1
  · have ha : a = start1 := by
      apply Subtype.ext
      simpa [start1, m8TripleStartIndexOfNat] using h1
    cases ha
    exact H.witness_start1 htriple
  by_cases h2 : a.1 = 2
  · have ha : a = start2 := by
      apply Subtype.ext
      simpa [start2, m8TripleStartIndexOfNat] using h2
    cases ha
    exact H.witness_start2 htriple
  by_cases h3 : a.1 = 3
  · have ha : a = start3 := by
      apply Subtype.ext
      simpa [start3, m8TripleStartIndexOfNat] using h3
    cases ha
    exact H.witness_start3 htriple
  by_cases h4 : a.1 = 4
  · have ha : a = start4 := by
      apply Subtype.ext
      simpa [start4, m8TripleStartIndexOfNat] using h4
    cases ha
    exact H.witness_start4 htriple
  have h5 : a.1 = 5 := by
    have hbounds := m8TripleStartIndex_bounds a
    unfold M8TripleStartEarly at hearly
    omega
  have ha : a = start5 := by
    apply Subtype.ext
    simpa [start5, m8TripleStartIndexOfNat] using h5
  cases ha
  exact H.witness_start5 htriple

/-- Concrete three-common-neighbor data plus finite local exclusions give the
five no-early triple exclusions. -/
def toConcreteNoEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyTripleEquality P :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_finiteLocalExclusions
    H.toK23ObstructionInputs E

/-- Concrete three-common-neighbor data plus finite local exclusions give the
abstract no-early predicate. -/
theorem toNoEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8NoEarlyTripleEquality P :=
  (H.toConcreteNoEarlyTripleEquality E).toNoEarlyTripleEquality

/-- Concrete three-common-neighbor data plus finite local exclusions give the
raw late-triples predicate. -/
theorem toBrokenLatticeLateTriples
    [Fintype V] [DecidableEq V]
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8BrokenLatticeLateTriples P :=
  (H.toConcreteNoEarlyTripleEquality E).toBrokenLatticeLateTriples

end M8ConcreteThreeCommonNeighborObstructionInputs

/-- Indexed local data: every early triple equality produces a concrete
three-common-neighbor witness. -/
structure M8EarlyThreeCommonNeighborObstructionInputs
    (P : BrokenLatticePredicates G 8) where
  witness_of_early_triple :
    forall {a : M8TripleStartIndex},
      M8TripleStartEarly a ->
        P.tripleEquality a -> ThreeCommonNeighborWitness G

namespace M8EarlyThreeCommonNeighborObstructionInputs

variable {P : BrokenLatticePredicates G 8}

/-- Restrict indexed early-start data to the five concrete starts. -/
def toConcrete
    (H : M8EarlyThreeCommonNeighborObstructionInputs P) :
    M8ConcreteThreeCommonNeighborObstructionInputs P where
  witness_start1 := H.witness_of_early_triple
    (a := start1) (by simp [M8TripleStartEarly])
  witness_start2 := H.witness_of_early_triple
    (a := start2) (by simp [M8TripleStartEarly])
  witness_start3 := H.witness_of_early_triple
    (a := start3) (by simp [M8TripleStartEarly])
  witness_start4 := H.witness_of_early_triple
    (a := start4) (by simp [M8TripleStartEarly])
  witness_start5 := H.witness_of_early_triple
    (a := start5) (by simp [M8TripleStartEarly])

/-- Indexed early-start common-neighbor data gives the K23 obstruction
package consumed downstream. -/
def toK23ObstructionInputs
    (H : M8EarlyThreeCommonNeighborObstructionInputs P) :
    M8ConcreteK23ObstructionInputs P :=
  H.toConcrete.toK23ObstructionInputs

/-- Indexed early-start common-neighbor data plus finite local exclusions give
the five no-early triple exclusions. -/
def toConcreteNoEarlyTripleEquality
    [Fintype V] [DecidableEq V]
    (H : M8EarlyThreeCommonNeighborObstructionInputs P)
    (E : FiniteLocalExclusionPackage G) :
    M8ConcreteNoEarlyTripleEquality P :=
  H.toConcrete.toConcreteNoEarlyTripleEquality E

/-- Package five concrete start witnesses as the indexed early-start witness
function. -/
def ofConcrete
    (H : M8ConcreteThreeCommonNeighborObstructionInputs P) :
    M8EarlyThreeCommonNeighborObstructionInputs P where
  witness_of_early_triple := by
    intro a hearly htriple
    exact
      M8ConcreteThreeCommonNeighborObstructionInputs.witness_of_early_triple
        H hearly htriple

end M8EarlyThreeCommonNeighborObstructionInputs

/-! ## Bad-adjacency cross-incidence geometry -/

/-- The `q_i` label used in the bad-adjacency row beginning at `i`. -/
def m8BadAdjacencyLeftTriangleIndexOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    TriangleIndex 8 :=
  Subtype.mk i (by
    omega)

/-- The `s_{i+1}` label used in the bad-adjacency row beginning at `i`. -/
def m8BadAdjacencyRightExtraIndexOfNat
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    ExtraIndex 8 :=
  Subtype.mk (i + 1) (by
    omega)

@[simp]
theorem m8BadAdjacencyLeftTriangleIndexOfNat_val
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10).1 = i :=
  rfl

@[simp]
theorem m8BadAdjacencyRightExtraIndexOfNat_val
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    (m8BadAdjacencyRightExtraIndexOfNat i hi hi10).1 = i + 1 :=
  rfl

/-- One bad-adjacency cross row in local-label form: `Adj q_i s_{i+1}`. -/
def M8BadAdjacencyCrossAdjacencyRowAt
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) : Prop :=
  (unitDistanceLocalGraph C).Adj
    (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10))
    (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10))

/-- The matching Euclidean condition for one cross row: `|q_i s_{i+1}| = 1`. -/
def M8BadAdjacencyCrossDistanceRowAt
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) : Prop :=
  _root_.eucDist
      (C.pts (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10)))
      (C.pts (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10))) =
    1

/-- Cross adjacency is exactly the corresponding Euclidean unit-distance row. -/
theorem m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) :
    M8BadAdjacencyCrossAdjacencyRowAt C labels i hi hi10 <->
      M8BadAdjacencyCrossDistanceRowAt C labels i hi hi10 := by
  unfold M8BadAdjacencyCrossAdjacencyRowAt
  unfold M8BadAdjacencyCrossDistanceRowAt
  exact
    GraphBridge.unitDistanceLocalGraph_adj C
      (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10))
      (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10))

/-- The five local-label cross adjacencies needed by the bad-adjacency K23
route: `Adj q_1 s_2` through `Adj q_5 s_6`. -/
structure M8BadAdjacencyCrossAdjacencyRows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8) : Prop where
  adj_q1_s2 :
    M8BadAdjacencyCrossAdjacencyRowAt C labels 1 (by omega) (by omega)
  adj_q2_s3 :
    M8BadAdjacencyCrossAdjacencyRowAt C labels 2 (by omega) (by omega)
  adj_q3_s4 :
    M8BadAdjacencyCrossAdjacencyRowAt C labels 3 (by omega) (by omega)
  adj_q4_s5 :
    M8BadAdjacencyCrossAdjacencyRowAt C labels 4 (by omega) (by omega)
  adj_q5_s6 :
    M8BadAdjacencyCrossAdjacencyRowAt C labels 5 (by omega) (by omega)

/-- The five exact Euclidean unit-distance rows matching the bad-adjacency
cross adjacencies. -/
structure M8BadAdjacencyCrossDistanceRows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8) : Prop where
  dist_q1_s2 :
    M8BadAdjacencyCrossDistanceRowAt C labels 1 (by omega) (by omega)
  dist_q2_s3 :
    M8BadAdjacencyCrossDistanceRowAt C labels 2 (by omega) (by omega)
  dist_q3_s4 :
    M8BadAdjacencyCrossDistanceRowAt C labels 3 (by omega) (by omega)
  dist_q4_s5 :
    M8BadAdjacencyCrossDistanceRowAt C labels 4 (by omega) (by omega)
  dist_q5_s6 :
    M8BadAdjacencyCrossDistanceRowAt C labels 5 (by omega) (by omega)

namespace M8BadAdjacencyCrossAdjacencyRows

variable {n : Nat} {C : _root_.UDConfig n}
variable {labels : BrokenLatticeLabels (Fin n) 8}

/-- Convert the five cross-adjacency rows to their exact Euclidean
unit-distance form. -/
def toDistanceRows
    (H : M8BadAdjacencyCrossAdjacencyRows C labels) :
    M8BadAdjacencyCrossDistanceRows C labels where
  dist_q1_s2 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 1 (by omega) (by omega)).1 H.adj_q1_s2
  dist_q2_s3 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 2 (by omega) (by omega)).1 H.adj_q2_s3
  dist_q3_s4 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 3 (by omega) (by omega)).1 H.adj_q3_s4
  dist_q4_s5 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 4 (by omega) (by omega)).1 H.adj_q4_s5
  dist_q5_s6 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 5 (by omega) (by omega)).1 H.adj_q5_s6

end M8BadAdjacencyCrossAdjacencyRows

namespace M8BadAdjacencyCrossDistanceRows

variable {n : Nat} {C : _root_.UDConfig n}
variable {labels : BrokenLatticeLabels (Fin n) 8}

/-- Convert the five exact Euclidean unit-distance rows to the cross
adjacencies consumed by the K23 route. -/
def toAdjacencyRows
    (H : M8BadAdjacencyCrossDistanceRows C labels) :
    M8BadAdjacencyCrossAdjacencyRows C labels where
  adj_q1_s2 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 1 (by omega) (by omega)).2 H.dist_q1_s2
  adj_q2_s3 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 2 (by omega) (by omega)).2 H.dist_q2_s3
  adj_q3_s4 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 3 (by omega) (by omega)).2 H.dist_q3_s4
  adj_q4_s5 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 4 (by omega) (by omega)).2 H.dist_q4_s5
  adj_q5_s6 :=
    (m8BadAdjacencyCrossAdjacencyRowAt_iff_distanceRowAt
      C labels 5 (by omega) (by omega)).2 H.dist_q5_s6

end M8BadAdjacencyCrossDistanceRows

/-- The five bad-adjacency cross adjacencies are equivalent to the five exact
Euclidean unit-distance rows on the same local labels. -/
theorem m8BadAdjacencyCrossAdjacencyRows_iff_distanceRows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8) :
    M8BadAdjacencyCrossAdjacencyRows C labels <->
      M8BadAdjacencyCrossDistanceRows C labels :=
  Iff.intro
    M8BadAdjacencyCrossAdjacencyRows.toDistanceRows
    M8BadAdjacencyCrossDistanceRows.toAdjacencyRows

/-- Local-label-facing name for the five bad-adjacency cross adjacencies. -/
abbrev M8LocalLabelBadAdjacencyCrossAdjacencyRows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C) : Prop :=
  M8BadAdjacencyCrossAdjacencyRows C localLabels.labels

/-- Local-label-facing name for the five exact bad-adjacency unit-distance
conditions. -/
abbrev M8LocalLabelBadAdjacencyCrossDistanceRows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C) : Prop :=
  M8BadAdjacencyCrossDistanceRows C localLabels.labels

/-- Local-label cross adjacencies are exactly the five named unit-distance
conditions. -/
theorem m8LocalLabelBadAdjacencyCrossAdjacencyRows_iff_distanceRows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C) :
    M8LocalLabelBadAdjacencyCrossAdjacencyRows localLabels <->
      M8LocalLabelBadAdjacencyCrossDistanceRows localLabels :=
  m8BadAdjacencyCrossAdjacencyRows_iff_distanceRows
    C localLabels.labels

/-! These rows are the current exact geometric blocker: the existing local
label package supplies `q_i ~ s_i`, while this package names the separate
`q_i ~ s_{i+1}` unit-distance facts needed by the bad-adjacency route. -/

/-! ### Reduction to selected-label Figure 9 distance data -/

/-- A selected-label Figure 9 distance row whose `qi` and `s` vertices are
fixed to the bad-adjacency cross pair `q_i, s_{i+1}`.  The remaining Figure 9
points are left existential because only the existing `qi_s` unit-distance
field is needed for the K23 cross row. -/
def M8BadAdjacencyCrossFigure9DistanceRowAt
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10) : Prop :=
  Exists fun p : AngleBridgeFacts.Point =>
  Exists fun qj : AngleBridgeFacts.Point =>
  Exists fun r : AngleBridgeFacts.Point =>
    AngleBridgeFacts.Figure9DistanceData
      p
      (C.pts
        (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10)))
      qj
      (C.pts
        (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10)))
      r

/-- Build the selected-label Figure 9 distance row from the actual finite
Figure 9 adjacency/distinctness fields, with `qi` fixed to `q_i` and `s`
fixed to `s_{i+1}`. -/
theorem m8BadAdjacencyCrossFigure9DistanceRowAt_of_selectedFiniteLabelFigure9Row
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10)
    {p qj r : Fin n}
    (hp_qi :
      GraphBridge.UnitDistanceAdj C p
        (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10)))
    (hp_qj : GraphBridge.UnitDistanceAdj C p qj)
    (hqi_s :
      GraphBridge.UnitDistanceAdj C
        (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10))
        (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10)))
    (hqj_r : GraphBridge.UnitDistanceAdj C qj r)
    (hqi_qj :
      Ne (labels.q (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10)) qj)
    (hp_s :
      Ne p (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10)))
    (hp_r : Ne p r)
    (hs_r :
      Ne (labels.s (m8BadAdjacencyRightExtraIndexOfNat i hi hi10)) r) :
    M8BadAdjacencyCrossFigure9DistanceRowAt C labels i hi hi10 := by
  exact
    Exists.intro (C.pts p)
      (Exists.intro (C.pts qj)
        (Exists.intro (C.pts r)
          (AngleBridgeFacts.Figure9DistanceData.ofUDConfigAdj C
            hp_qi hp_qj hqi_s hqj_r hqi_qj hp_s hp_r hs_r)))

/-- A selected-label Figure 9 distance row proves the corresponding exact
bad-adjacency cross unit-distance row. -/
theorem m8BadAdjacencyCrossDistanceRowAt_of_figure9DistanceRowAt
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (i : Nat) (hi : 1 <= i) (hi10 : i <= 10)
    (H : M8BadAdjacencyCrossFigure9DistanceRowAt C labels i hi hi10) :
    M8BadAdjacencyCrossDistanceRowAt C labels i hi hi10 := by
  rcases H with ⟨p, qj, r, D⟩
  unfold M8BadAdjacencyCrossDistanceRowAt
  simpa [AngleBridgeFacts.EucUnit, AngleBridgeFacts.eucDist,
    PlanarInterface.geometry_eucDist_eq_root] using
    D.qi_s

/-- Five selected-label Figure 9 distance rows, one for each bad-adjacency
cross pair. -/
structure M8BadAdjacencyCrossFigure9DistanceRows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8) : Prop where
  fig9_q1_s2 :
    M8BadAdjacencyCrossFigure9DistanceRowAt C labels 1 (by omega) (by omega)
  fig9_q2_s3 :
    M8BadAdjacencyCrossFigure9DistanceRowAt C labels 2 (by omega) (by omega)
  fig9_q3_s4 :
    M8BadAdjacencyCrossFigure9DistanceRowAt C labels 3 (by omega) (by omega)
  fig9_q4_s5 :
    M8BadAdjacencyCrossFigure9DistanceRowAt C labels 4 (by omega) (by omega)
  fig9_q5_s6 :
    M8BadAdjacencyCrossFigure9DistanceRowAt C labels 5 (by omega) (by omega)

/-- Row-wise actual finite Figure 9 source data selected at the
bad-adjacency cross labels `q_i, s_{i+1}` for `i = 1, ..., 5`. -/
abbrev M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8) : Prop :=
  forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
    Exists fun p : Fin n =>
    Exists fun qj : Fin n =>
    Exists fun r : Fin n =>
      GraphBridge.UnitDistanceAdj C p
          (labels.q
            (m8BadAdjacencyLeftTriangleIndexOfNat i hi (by omega))) /\
        GraphBridge.UnitDistanceAdj C p qj /\
        GraphBridge.UnitDistanceAdj C
          (labels.q
            (m8BadAdjacencyLeftTriangleIndexOfNat i hi (by omega)))
          (labels.s
            (m8BadAdjacencyRightExtraIndexOfNat i hi (by omega))) /\
        GraphBridge.UnitDistanceAdj C qj r /\
        Ne
          (labels.q
            (m8BadAdjacencyLeftTriangleIndexOfNat i hi (by omega)))
          qj /\
        Ne p
          (labels.s
            (m8BadAdjacencyRightExtraIndexOfNat i hi (by omega))) /\
        Ne p r /\
        Ne
          (labels.s
            (m8BadAdjacencyRightExtraIndexOfNat i hi (by omega)))
          r

/-- A row-wise actual finite Figure 9 source, selected at `q_i, s_{i+1}`,
supplies the five point-valued Figure 9 distance rows used by the
bad-adjacency route. -/
def m8BadAdjacencyCrossFigure9DistanceRows_of_selectedFiniteLabelFigure9Rows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (H : M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows C labels) :
    M8BadAdjacencyCrossFigure9DistanceRows C labels where
  fig9_q1_s2 := by
    rcases H 1 (by omega) (by omega) with
      ⟨p, qj, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hp_s, hp_r, hs_r⟩
    exact
      m8BadAdjacencyCrossFigure9DistanceRowAt_of_selectedFiniteLabelFigure9Row
        C labels 1 (by omega) (by omega)
        hp_qi hp_qj hqi_s hqj_r hqi_qj hp_s hp_r hs_r
  fig9_q2_s3 := by
    rcases H 2 (by omega) (by omega) with
      ⟨p, qj, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hp_s, hp_r, hs_r⟩
    exact
      m8BadAdjacencyCrossFigure9DistanceRowAt_of_selectedFiniteLabelFigure9Row
        C labels 2 (by omega) (by omega)
        hp_qi hp_qj hqi_s hqj_r hqi_qj hp_s hp_r hs_r
  fig9_q3_s4 := by
    rcases H 3 (by omega) (by omega) with
      ⟨p, qj, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hp_s, hp_r, hs_r⟩
    exact
      m8BadAdjacencyCrossFigure9DistanceRowAt_of_selectedFiniteLabelFigure9Row
        C labels 3 (by omega) (by omega)
        hp_qi hp_qj hqi_s hqj_r hqi_qj hp_s hp_r hs_r
  fig9_q4_s5 := by
    rcases H 4 (by omega) (by omega) with
      ⟨p, qj, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hp_s, hp_r, hs_r⟩
    exact
      m8BadAdjacencyCrossFigure9DistanceRowAt_of_selectedFiniteLabelFigure9Row
        C labels 4 (by omega) (by omega)
        hp_qi hp_qj hqi_s hqj_r hqi_qj hp_s hp_r hs_r
  fig9_q5_s6 := by
    rcases H 5 (by omega) (by omega) with
      ⟨p, qj, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hp_s, hp_r, hs_r⟩
    exact
      m8BadAdjacencyCrossFigure9DistanceRowAt_of_selectedFiniteLabelFigure9Row
        C labels 5 (by omega) (by omega)
        hp_qi hp_qj hqi_s hqj_r hqi_qj hp_s hp_r hs_r

namespace M8BadAdjacencyCrossFigure9DistanceRows

variable {n : Nat} {C : _root_.UDConfig n}
variable {labels : BrokenLatticeLabels (Fin n) 8}

/-- Project the exact K23 bad-adjacency distance rows from selected-label
Figure 9 distance data. -/
def toDistanceRows
    (H : M8BadAdjacencyCrossFigure9DistanceRows C labels) :
    M8BadAdjacencyCrossDistanceRows C labels where
  dist_q1_s2 :=
    m8BadAdjacencyCrossDistanceRowAt_of_figure9DistanceRowAt
      C labels 1 (by omega) (by omega) H.fig9_q1_s2
  dist_q2_s3 :=
    m8BadAdjacencyCrossDistanceRowAt_of_figure9DistanceRowAt
      C labels 2 (by omega) (by omega) H.fig9_q2_s3
  dist_q3_s4 :=
    m8BadAdjacencyCrossDistanceRowAt_of_figure9DistanceRowAt
      C labels 3 (by omega) (by omega) H.fig9_q3_s4
  dist_q4_s5 :=
    m8BadAdjacencyCrossDistanceRowAt_of_figure9DistanceRowAt
      C labels 4 (by omega) (by omega) H.fig9_q4_s5
  dist_q5_s6 :=
    m8BadAdjacencyCrossDistanceRowAt_of_figure9DistanceRowAt
      C labels 5 (by omega) (by omega) H.fig9_q5_s6

end M8BadAdjacencyCrossFigure9DistanceRows

/-- Selected-label Figure 9 distance rows reduce to the exact K23
bad-adjacency Euclidean distance rows. -/
theorem m8BadAdjacencyCrossDistanceRows_of_figure9DistanceRows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (H : M8BadAdjacencyCrossFigure9DistanceRows C labels) :
    M8BadAdjacencyCrossDistanceRows C labels :=
  H.toDistanceRows

/-- Actual finite selected-label Figure 9 rows reduce directly to the exact
K23 bad-adjacency Euclidean distance rows. -/
theorem m8BadAdjacencyCrossDistanceRows_of_selectedFiniteLabelFigure9Rows
    {n : Nat} (C : _root_.UDConfig n)
    (labels : BrokenLatticeLabels (Fin n) 8)
    (H : M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows C labels) :
    M8BadAdjacencyCrossDistanceRows C labels :=
  m8BadAdjacencyCrossDistanceRows_of_figure9DistanceRows C labels
    (m8BadAdjacencyCrossFigure9DistanceRows_of_selectedFiniteLabelFigure9Rows
      C labels H)

/-- Local-label-facing actual finite selected Figure 9 rows for the five
bad-adjacency cross pairs. -/
abbrev M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C) : Prop :=
  M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows C localLabels.labels

/-- Local-label-facing selected Figure 9 distance rows for the five
bad-adjacency cross pairs. -/
abbrev M8LocalLabelBadAdjacencyCrossFigure9DistanceRows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C) : Prop :=
  M8BadAdjacencyCrossFigure9DistanceRows C localLabels.labels

section BoundaryLabelSelectedFigure9Rows

open BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate

/-- The remaining noncollision row needed to package a generated
bad-adjacency incidence as finite selected Figure 9 data. -/
theorem rightP_badAdjacencyLeft_ne_r_badAdjacencyRight
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10) :
    Not
      (K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.lemma8.r (badAdjacencyRightExtraOfNat i hi hi10)) := by
  intro h
  have hp :
      K.spine.rightP (badAdjacencyLeftExtraOfNat i hi hi10) =
        K.spine.leftP (badAdjacencyRightExtraOfNat i hi hi10) :=
    rightP_badAdjacencyLeft_eq_leftP_badAdjacencyRight (K := K) hi hi10
  exact
    K.lemma8.r_not_forbidden
      (badAdjacencyRightExtraOfNat i hi hi10)
      (Or.inl (h.symm.trans hp))

/-- A generated local-label bad-adjacency row gives a positive finite
selected Figure 9 row for the K23 cross pair `q_i, s_{i+1}`. -/
theorem m8BadAdjacencyCrossSelectedFiniteLabelFigure9RowAt_of_badAdjacencyLocalLabelIncidenceRowAt
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    {i : Nat} (hi : 1 <= i) (hi10 : i <= 10)
    (H :
      BadAdjacencyLocalLabelIncidenceRowAt K i hi hi10) :
    Exists fun p : Fin n =>
    Exists fun qj : Fin n =>
    Exists fun r : Fin n =>
      GraphBridge.UnitDistanceAdj C p
          (K.toM8LocalLabels.labels.q
            (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10)) /\
        GraphBridge.UnitDistanceAdj C p qj /\
        GraphBridge.UnitDistanceAdj C
          (K.toM8LocalLabels.labels.q
            (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10))
          (K.toM8LocalLabels.labels.s
            (m8BadAdjacencyRightExtraIndexOfNat i hi hi10)) /\
        GraphBridge.UnitDistanceAdj C qj r /\
        Ne
          (K.toM8LocalLabels.labels.q
            (m8BadAdjacencyLeftTriangleIndexOfNat i hi hi10))
          qj /\
        Ne p
          (K.toM8LocalLabels.labels.s
            (m8BadAdjacencyRightExtraIndexOfNat i hi hi10)) /\
        Ne p r /\
        Ne
          (K.toM8LocalLabels.labels.s
            (m8BadAdjacencyRightExtraIndexOfNat i hi hi10))
          r := by
  let left := badAdjacencyLeftExtraOfNat i hi hi10
  let right := badAdjacencyRightExtraOfNat i hi hi10
  refine
    Exists.intro (K.spine.rightP left)
      (Exists.intro (K.spine.centerQ right)
        (Exists.intro (K.lemma8.r right) ?_))
  refine
    And.intro
      (by
        exact
          GraphBridge.unitDistanceAdj_symm C
            (K.spine.centerQ_adj_rightP left)) ?_
  refine
    And.intro
      (by
        have hcp :
            GraphBridge.UnitDistanceAdj C
              (K.spine.centerQ right) (K.spine.rightP left) := by
          simpa [left, right,
            rightP_badAdjacencyLeft_eq_leftP_badAdjacencyRight
              (K := K) hi hi10] using
            K.spine.centerQ_adj_leftP right
        exact GraphBridge.unitDistanceAdj_symm C hcp) ?_
  refine
    And.intro
      (by
        simpa [left, right,
          M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows,
          M8BadAdjacencyCrossAdjacencyRowAt,
          m8BadAdjacencyLeftTriangleIndexOfNat,
          m8BadAdjacencyRightExtraIndexOfNat,
          BadAdjacencyLocalLabelIncidenceRowAt,
          badAdjacencyLeftExtraOfNat, badAdjacencyRightExtraOfNat,
          badAdjacencyLemma10IndexOfNat] using H) ?_
  refine And.intro (K.lemma8.r_neighbor right) ?_
  refine
    And.intro
      (centerQ_badAdjacencyLeft_ne_centerQ_badAdjacencyRight
        (K := K) hi hi10) ?_
  refine
    And.intro
      (rightP_badAdjacencyLeft_ne_s_right (K := K) hi hi10) ?_
  refine And.intro (rightP_badAdjacencyLeft_ne_r_badAdjacencyRight K hi hi10) ?_
  intro hsr
  exact K.lemma8.r_ne_s right hsr.symm

/-- Generated local-label bad-adjacency incidence rows supply the positive
finite selected Figure 9 rows for all five K23 cross pairs. -/
theorem m8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows_of_badAdjacencyLocalLabelIncidenceRowAt
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (H :
      forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
        BadAdjacencyLocalLabelIncidenceRowAt K i hi (by omega)) :
    M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows
      K.toM8LocalLabels := by
  intro i hi hi5
  exact
    m8BadAdjacencyCrossSelectedFiniteLabelFigure9RowAt_of_badAdjacencyLocalLabelIncidenceRowAt
      (K := K) hi (by omega) (H i hi hi5)

/-- The assembly-local selected finite Figure 9 rows reduce to the downstream
K23 selected finite Figure 9 cross rows for the same generated labels. -/
theorem m8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows_of_boundarySelectedFiniteLabelFigure9Rows
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (H : BadAdjacencySelectedFiniteLabelFigure9Rows K) :
    M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows
      K.toM8LocalLabels := by
  intro i hi hi5
  simpa
    [M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows,
      M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows,
      BadAdjacencySelectedFiniteLabelFigure9Rows,
      BadAdjacencySelectedFiniteLabelFigure9RowAt,
      m8BadAdjacencyLeftTriangleIndexOfNat,
      m8BadAdjacencyRightExtraIndexOfNat,
      badAdjacencyLeftExtraOfNat, badAdjacencyRightExtraOfNat,
      badAdjacencyLemma10IndexOfNat]
    using H i hi hi5

end BoundaryLabelSelectedFigure9Rows

/-- Local selected-label Figure 9 distance rows prove the exact local
bad-adjacency cross distance rows. -/
theorem m8LocalLabelBadAdjacencyCrossDistanceRows_of_figure9DistanceRows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C)
    (H : M8LocalLabelBadAdjacencyCrossFigure9DistanceRows localLabels) :
    M8LocalLabelBadAdjacencyCrossDistanceRows localLabels :=
  m8BadAdjacencyCrossDistanceRows_of_figure9DistanceRows
    C localLabels.labels H

/-- Actual finite selected-label Figure 9 rows prove the exact local
bad-adjacency cross distance rows. -/
theorem m8LocalLabelBadAdjacencyCrossDistanceRows_of_selectedFiniteLabelFigure9Rows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C)
    (H :
      M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows
        localLabels) :
    M8LocalLabelBadAdjacencyCrossDistanceRows localLabels :=
  m8BadAdjacencyCrossDistanceRows_of_selectedFiniteLabelFigure9Rows
    C localLabels.labels H

/-- Actual finite selected-label Figure 9 rows also give the local
bad-adjacency cross adjacency rows. -/
theorem m8LocalLabelBadAdjacencyCrossAdjacencyRows_of_selectedFiniteLabelFigure9Rows
    {n : Nat} {C : _root_.UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C)
    (H :
      M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows
        localLabels) :
    M8LocalLabelBadAdjacencyCrossAdjacencyRows localLabels :=
  (m8LocalLabelBadAdjacencyCrossAdjacencyRows_iff_distanceRows
    localLabels).2
    (m8LocalLabelBadAdjacencyCrossDistanceRows_of_selectedFiniteLabelFigure9Rows
      localLabels H)

/-- Selected finite Figure 9 rows at the assembled local labels supply the
finite-label bad-adjacency incidence package used by the boundary-label
route. -/
def badAdjacencyFiniteLabelIncidenceRows_of_selectedFiniteLabelFigure9Rows
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (H :
      M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows
        K.toM8LocalLabels) :
    BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyFiniteLabelIncidenceRows
      K := by
  let Hcross :=
    m8LocalLabelBadAdjacencyCrossAdjacencyRows_of_selectedFiniteLabelFigure9Rows
      K.toM8LocalLabels H
  exact
    { adj_q1_s2 := by
        simpa
          [M8LocalLabelBadAdjacencyCrossAdjacencyRows,
            M8BadAdjacencyCrossAdjacencyRowAt,
            m8BadAdjacencyLeftTriangleIndexOfNat,
            m8BadAdjacencyRightExtraIndexOfNat,
            BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyFiniteLabelIncidenceRowAt]
          using Hcross.adj_q1_s2
      adj_q2_s3 := by
        simpa
          [M8LocalLabelBadAdjacencyCrossAdjacencyRows,
            M8BadAdjacencyCrossAdjacencyRowAt,
            m8BadAdjacencyLeftTriangleIndexOfNat,
            m8BadAdjacencyRightExtraIndexOfNat,
            BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyFiniteLabelIncidenceRowAt]
          using Hcross.adj_q2_s3
      adj_q3_s4 := by
        simpa
          [M8LocalLabelBadAdjacencyCrossAdjacencyRows,
            M8BadAdjacencyCrossAdjacencyRowAt,
            m8BadAdjacencyLeftTriangleIndexOfNat,
            m8BadAdjacencyRightExtraIndexOfNat,
            BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyFiniteLabelIncidenceRowAt]
          using Hcross.adj_q3_s4
      adj_q4_s5 := by
        simpa
          [M8LocalLabelBadAdjacencyCrossAdjacencyRows,
            M8BadAdjacencyCrossAdjacencyRowAt,
            m8BadAdjacencyLeftTriangleIndexOfNat,
            m8BadAdjacencyRightExtraIndexOfNat,
            BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyFiniteLabelIncidenceRowAt]
          using Hcross.adj_q4_s5
      adj_q5_s6 := by
        simpa
          [M8LocalLabelBadAdjacencyCrossAdjacencyRows,
            M8BadAdjacencyCrossAdjacencyRowAt,
            m8BadAdjacencyLeftTriangleIndexOfNat,
            m8BadAdjacencyRightExtraIndexOfNat,
            BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyFiniteLabelIncidenceRowAt]
          using Hcross.adj_q5_s6 }

/-- Row-wise local-label incidence form of the same selected finite Figure 9
bridge. -/
theorem badAdjacencyLocalLabelIncidenceRowAt_of_selectedFiniteLabelFigure9Rows
    {n : Nat} {C : _root_.UDConfig n}
    {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
    {connectedNoCut :
      CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (K :
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate
        D connectedNoCut hmin)
    (H :
      M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows
        K.toM8LocalLabels) :
    forall (i : Nat) (hi : 1 <= i) (hi5 : i <= 5),
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyLocalLabelIncidenceRowAt
        K i hi (by omega) := by
  intro i hi hi5
  rcases H i hi hi5 with
    ⟨p, qj, r, hp_qi, hp_qj, hqi_s, hqj_r, hqi_qj, hp_s, hp_r, hs_r⟩
  simpa
    [M8LocalLabelBadAdjacencyCrossSelectedFiniteLabelFigure9Rows,
      M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows,
      BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.BadAdjacencyLocalLabelIncidenceRowAt,
      m8BadAdjacencyLeftTriangleIndexOfNat,
      m8BadAdjacencyRightExtraIndexOfNat]
    using hqi_s

/-! ## No-assumption finite-local-exclusion routes -/

/-- If the unit-distance local graph has no `K_{2,3}`, then the
`K23DegreeReducible` premise used by the older minimal-failure route is
available vacuously. -/
theorem K23DegreeReducible_of_not_hasK23
    {n : Nat} {C : _root_.UDConfig n}
    (hno : ¬ HasK23 (unitDistanceLocalGraph C)) :
    K23DegreeReducible C := by
  intro P
  exact False.elim (hno (Nonempty.intro P))

/-- A finite local-exclusion package supplies the vacuous
`K23DegreeReducible` input for the unit-distance graph. -/
theorem K23DegreeReducible_of_finiteLocalExclusionPackage
    {n : Nat} {C : _root_.UDConfig n}
    (E : FiniteLocalExclusionPackage (unitDistanceLocalGraph C)) :
    K23DegreeReducible C :=
  K23DegreeReducible_of_not_hasK23 E.noK23

/-- The already-proved unit-distance finite local exclusions provide the
degree-reducibility input required by the minimal-failure K23 wrapper. -/
theorem K23DegreeReducible_of_unitDistanceConfig
    {n : Nat} (C : _root_.UDConfig n) :
    K23DegreeReducible C :=
  K23DegreeReducible_of_finiteLocalExclusionPackage
    (finiteLocalExclusionPackage_of_unitDistanceConfig C)

/-- Minimal-failure finite local exclusions with no separate
`K23DegreeReducible` assumption. -/
def finiteLocalExclusionPackage_of_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    FiniteLocalExclusionPackage (unitDistanceLocalGraph C) :=
  FiniteLocalExclusionPackage.of_not_hasK23
    (MinimalFailureLocalExclusions.not_hasK23_of_minimalFailure hmin)

/-- Minimal failures inherit the no-`K_{2,3}` exclusion without any extra
local-deletion assumption. -/
theorem not_hasK23_of_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) :
    ¬ HasK23 (unitDistanceLocalGraph C) :=
  MinimalFailureLocalExclusions.not_hasK23_of_minimalFailure hmin

/-- Minimal failures inherit the common-neighbor cap without any extra
local-deletion assumption. -/
theorem commonNeighborFinset_card_le_two_of_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) {a b : Fin n} (hab : a ≠ b) :
    (LocalExclusions.LocalGraph.commonNeighborFinset
      (unitDistanceLocalGraph C) a b).card <= 2 :=
  MinimalFailureLocalExclusions.commonNeighborFinset_card_le_two_of_minimalFailure
    hmin hab

/-! ## Direct downstream wrappers -/

/-- K23 obstruction inputs route through the existing minimal-failure
turn/window/no-early wrapper without requiring callers to provide a separate
`K23DegreeReducible` argument. -/
def turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure_noAssumptions
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H : M8ConcreteK23ObstructionInputs localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure
    (C := C) (hmin := hmin) (localLabels := localLabels)
    A H (K23DegreeReducible_of_unitDistanceConfig C) W

/-- Concrete three-common-neighbor obstruction data route directly into the
minimal-failure turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_threeCommonNeighborObstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      M8ConcreteThreeCommonNeighborObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  turnWindowNoEarlyPackage_of_K23Obstruction_minimalFailure_noAssumptions
    A H.toK23ObstructionInputs W

/-- Indexed early-start common-neighbor obstruction data route directly into
the minimal-failure turn/window/no-early package. -/
def turnWindowNoEarlyPackage_of_earlyThreeCommonNeighborObstruction_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    {localLabels : M8ConstructionInterface.M8LocalLabels C}
    (A : M8TurnBoundsFromArc.NonconcaveArcTurnData)
    (H :
      M8EarlyThreeCommonNeighborObstructionInputs
        localLabels.predicates.data)
    (W :
      M8WindowGeometryFromContainment.M8WindowContainment
        localLabels A.toM8TurnBounds) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  turnWindowNoEarlyPackage_of_threeCommonNeighborObstruction_minimalFailure
    A H.toConcrete W

end K23ObstructionConcrete
end Swanepoel
end ErdosProblems1066

end
