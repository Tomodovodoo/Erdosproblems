import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete

set_option autoImplicit false

/-!
# Forbidden-label distinctness for the concrete Lemma 8 reducer

`Lemma8ExistenceConcrete.FourForbiddenNeighborFrame` needs adjacency from
`q_i` to `q_{i-1}, q_{i+1}` and pairwise distinctness of the four forbidden
labels

`p_i, p_{i+1}, q_{i-1}, q_{i+1}`.

Two of the distinctness clauses are already forced by the neighboring
triangle witnesses: `q_{i-1}` is adjacent to `p_i`, and `q_{i+1}` is adjacent
to `p_{i+1}`.  This file isolates the remaining finite certificate fields and
proves that they feed the frame used by the degree-six count.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8ForbiddenDistinctConcrete

open BoundarySpineFiniteCertificate
open GraphBridge
open Lemma8ExistenceConcrete
open M8LabelsFromBoundaryInterface

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {H : M8BoundaryCutDegreeContext C}
variable {S : M8BoundarySpine H}

/-! ## Adjacent neighboring triangle labels -/

theorem right_prev_boundaryIndex_eq_left
    (i : M8ExtraIndex) :
    m8BoundaryIndexRight (m8TriangleIndexPrevOfExtra i) =
      m8BoundaryIndexLeft (m8TriangleIndexOfExtra i) := by
  ext
  simp [m8BoundaryIndexRight, m8BoundaryIndexLeft,
    m8TriangleIndexPrevOfExtra, m8TriangleIndexOfExtra]
  have hi := i.2
  omega

theorem left_next_boundaryIndex_eq_right
    (i : M8ExtraIndex) :
    m8BoundaryIndexLeft (m8TriangleIndexNextOfExtra i) =
      m8BoundaryIndexRight (m8TriangleIndexOfExtra i) := by
  ext
  simp [m8BoundaryIndexRight, m8BoundaryIndexLeft,
    m8TriangleIndexNextOfExtra, m8TriangleIndexOfExtra]

theorem prevQ_adj_leftP
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.prevQ i) (S.leftP i) := by
  simpa [M8BoundarySpine.prevQ, M8BoundarySpine.leftP,
    right_prev_boundaryIndex_eq_left i] using
    (S.triangleWitness (m8TriangleIndexPrevOfExtra i)).2

theorem nextQ_adj_rightP
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.nextQ i) (S.rightP i) := by
  simpa [M8BoundarySpine.nextQ, M8BoundarySpine.rightP,
    left_next_boundaryIndex_eq_right i] using
    (S.triangleWitness (m8TriangleIndexNextOfExtra i)).1

theorem leftP_ne_prevQ
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    Not (S.leftP i = S.prevQ i) := by
  intro h
  have hadj : (unitDistanceLocalGraph C).Adj (S.prevQ i) (S.leftP i) :=
    prevQ_adj_leftP S i
  rw [h] at hadj
  exact (unitDistanceLocalGraph C).loopless (S.prevQ i) hadj

theorem rightP_ne_nextQ
    (S : M8BoundarySpine H) (i : M8ExtraIndex) :
    Not (S.rightP i = S.nextQ i) := by
  intro h
  have hadj : (unitDistanceLocalGraph C).Adj (S.nextQ i) (S.rightP i) :=
    nextQ_adj_rightP S i
  rw [h] at hadj
  exact (unitDistanceLocalGraph C).loopless (S.nextQ i) hadj

/-! ## Pairwise distinct forbidden labels -/

/-- Pairwise distinctness of the four forbidden labels
`leftP, rightP, prevQ, nextQ`. -/
structure FourForbiddenLabelsPairwiseDistinct
    (S : M8BoundarySpine H) (i : M8ExtraIndex) : Prop where
  left_ne_right : Not (S.leftP i = S.rightP i)
  left_ne_prev : Not (S.leftP i = S.prevQ i)
  left_ne_next : Not (S.leftP i = S.nextQ i)
  right_ne_prev : Not (S.rightP i = S.prevQ i)
  right_ne_next : Not (S.rightP i = S.nextQ i)
  prev_ne_next : Not (S.prevQ i = S.nextQ i)

namespace FourForbiddenLabelsPairwiseDistinct

variable {i : M8ExtraIndex}

theorem forbidden_card_eq_four
    (D : FourForbiddenLabelsPairwiseDistinct S i) :
    (forbiddenNeighborFinset S i).card = 4 := by
  classical
  let a := S.leftP i
  let b := S.rightP i
  let c := S.prevQ i
  let d := S.nextQ i
  have hab : Not (a = b) := D.left_ne_right
  have hac : Not (a = c) := D.left_ne_prev
  have had : Not (a = d) := D.left_ne_next
  have hbc : Not (b = c) := D.right_ne_prev
  have hbd : Not (b = d) := D.right_ne_next
  have hcd : Not (c = d) := D.prev_ne_next
  change ({a, b, c, d} : Finset (Fin n)).card = 4
  simp [hab, hac, had, hbc, hbd, hcd]

theorem of_forbidden_card_eq_four
    (hcard : (forbiddenNeighborFinset S i).card = 4) :
    FourForbiddenLabelsPairwiseDistinct S i := by
  classical
  have false_of_subset_three :
      forall {a b c : Fin n},
        forbiddenNeighborFinset S i <= ({a, b, c} : Finset (Fin n)) ->
          False := by
    intro a b c hsubset
    have hle : (forbiddenNeighborFinset S i).card <= 3 := by
      exact le_trans (Finset.card_le_card hsubset) Finset.card_le_three
    omega
  refine
    { left_ne_right := ?_
      left_ne_prev := ?_
      left_ne_next := ?_
      right_ne_prev := ?_
      right_ne_next := ?_
      prev_ne_next := ?_ }
  · intro h
    simp [M8BoundarySpine.leftP, M8BoundarySpine.rightP] at h
    apply false_of_subset_three
      (a := S.rightP i) (b := S.prevQ i) (c := S.nextQ i)
    intro x hx
    rcases (mem_forbiddenNeighborFinset S i x).1 hx with hx | hx | hx | hx <;>
      simp [hx, h, M8BoundarySpine.leftP, M8BoundarySpine.rightP,
        M8BoundarySpine.prevQ, M8BoundarySpine.nextQ]
  · intro h
    simp [M8BoundarySpine.leftP, M8BoundarySpine.prevQ] at h
    apply false_of_subset_three
      (a := S.rightP i) (b := S.prevQ i) (c := S.nextQ i)
    intro x hx
    rcases (mem_forbiddenNeighborFinset S i x).1 hx with hx | hx | hx | hx <;>
      simp [hx, h, M8BoundarySpine.leftP, M8BoundarySpine.rightP,
        M8BoundarySpine.prevQ, M8BoundarySpine.nextQ]
  · intro h
    simp [M8BoundarySpine.leftP, M8BoundarySpine.nextQ] at h
    apply false_of_subset_three
      (a := S.rightP i) (b := S.prevQ i) (c := S.nextQ i)
    intro x hx
    rcases (mem_forbiddenNeighborFinset S i x).1 hx with hx | hx | hx | hx <;>
      simp [hx, h, M8BoundarySpine.leftP, M8BoundarySpine.rightP,
        M8BoundarySpine.prevQ, M8BoundarySpine.nextQ]
  · intro h
    simp [M8BoundarySpine.rightP, M8BoundarySpine.prevQ] at h
    apply false_of_subset_three
      (a := S.leftP i) (b := S.prevQ i) (c := S.nextQ i)
    intro x hx
    rcases (mem_forbiddenNeighborFinset S i x).1 hx with hx | hx | hx | hx <;>
      simp [hx, h, M8BoundarySpine.leftP, M8BoundarySpine.rightP,
        M8BoundarySpine.prevQ, M8BoundarySpine.nextQ]
  · intro h
    simp [M8BoundarySpine.rightP, M8BoundarySpine.nextQ] at h
    apply false_of_subset_three
      (a := S.leftP i) (b := S.prevQ i) (c := S.nextQ i)
    intro x hx
    rcases (mem_forbiddenNeighborFinset S i x).1 hx with hx | hx | hx | hx <;>
      simp [hx, h, M8BoundarySpine.leftP, M8BoundarySpine.rightP,
        M8BoundarySpine.prevQ, M8BoundarySpine.nextQ]
  · intro h
    simp [M8BoundarySpine.prevQ, M8BoundarySpine.nextQ] at h
    apply false_of_subset_three
      (a := S.leftP i) (b := S.rightP i) (c := S.nextQ i)
    intro x hx
    rcases (mem_forbiddenNeighborFinset S i x).1 hx with hx | hx | hx | hx <;>
      simp [hx, h, M8BoundarySpine.leftP, M8BoundarySpine.rightP,
        M8BoundarySpine.prevQ, M8BoundarySpine.nextQ]

theorem pairwiseDistinct_iff_forbidden_card_eq_four :
    FourForbiddenLabelsPairwiseDistinct S i <->
      (forbiddenNeighborFinset S i).card = 4 := by
  constructor
  · intro D
    exact D.forbidden_card_eq_four
  · intro hcard
    exact of_forbidden_card_eq_four hcard

theorem ofFrame
    (F : FourForbiddenNeighborFrame S i) :
    FourForbiddenLabelsPairwiseDistinct S i := by
  exact
    { left_ne_right := leftP_ne_rightP S i
      left_ne_prev := F.left_ne_prev
      left_ne_next := F.left_ne_next
      right_ne_prev := F.right_ne_prev
      right_ne_next := F.right_ne_next
      prev_ne_next := F.prev_ne_next }

end FourForbiddenLabelsPairwiseDistinct

/-! ## Forbidden distinctness reduced to the remaining finite collisions -/

/-- The honest boundary spine already supplies half of the forbidden-label
distinctness facts.  The full per-index forbidden distinctness package is
therefore equivalent to the three remaining finite no-collision checks:
`leftP != nextQ`, `rightP != prevQ`, and `prevQ != nextQ`. -/
theorem fourForbiddenLabelsPairwiseDistinct_iff_remaining_three
    {i : M8ExtraIndex} :
    FourForbiddenLabelsPairwiseDistinct S i <->
      Not (S.leftP i = S.nextQ i) /\
      Not (S.rightP i = S.prevQ i) /\
      Not (S.prevQ i = S.nextQ i) := by
  constructor
  · intro D
    exact ⟨D.left_ne_next, D.right_ne_prev, D.prev_ne_next⟩
  · intro h
    exact
      { left_ne_right := leftP_ne_rightP S i
        left_ne_prev := leftP_ne_prevQ S i
        left_ne_next := h.1
        right_ne_prev := h.2.1
        right_ne_next := rightP_ne_nextQ S i
        prev_ne_next := h.2.2 }

/-- Family form: all forbidden-label distinctness fields for the real M8
spine reduce to one finite family of the three remaining no-collision facts. -/
theorem fourForbiddenLabelsPairwiseDistinct_family_iff_remaining_three :
    (forall i : M8ExtraIndex, FourForbiddenLabelsPairwiseDistinct S i) <->
      forall i : M8ExtraIndex,
        Not (S.leftP i = S.nextQ i) /\
        Not (S.rightP i = S.prevQ i) /\
        Not (S.prevQ i = S.nextQ i) := by
  constructor
  · intro h i
    exact (fourForbiddenLabelsPairwiseDistinct_iff_remaining_three
      (S := S) (i := i)).1 (h i)
  · intro h i
    exact (fourForbiddenLabelsPairwiseDistinct_iff_remaining_three
      (S := S) (i := i)).2 (h i)

/-- Constructor direction of the family reduction, useful for downstream
Lemma 8 label packages that only want the concrete distinctness fields. -/
theorem fourForbiddenLabelsPairwiseDistinct_family_of_remaining_three
    (h :
      forall i : M8ExtraIndex,
        Not (S.leftP i = S.nextQ i) /\
        Not (S.rightP i = S.prevQ i) /\
        Not (S.prevQ i = S.nextQ i)) :
    forall i : M8ExtraIndex, FourForbiddenLabelsPairwiseDistinct S i :=
  (fourForbiddenLabelsPairwiseDistinct_family_iff_remaining_three
    (S := S)).2 h

/-! ## Distinctness from the named Lemma 8 extra-neighbor package -/

/-- The Lemma 8 named-extra-neighbor package makes the concrete
extra-neighbor finset have cardinality two, without using forbidden-label
distinctness. -/
theorem extraNeighborFinset_card_eq_two_of_lemma8Combinatorics
    (E : M8Lemma8Combinatorics S) (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 := by
  classical
  have hsubset :
      extraNeighborFinset S i <=
        ({E.r i, E.s i} : Finset (Fin n)) := by
    intro x hx
    have hx' := (mem_extraNeighborFinset S i x).1 hx
    rcases E.named_of_extra_neighbor hx'.1 hx'.2 with h | h <;> simp [h]
  have hsupset :
      ({E.r i, E.s i} : Finset (Fin n)) <=
        extraNeighborFinset S i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · subst x
      exact (mem_extraNeighborFinset S i (E.r i)).2
        (And.intro (E.r_neighbor i) (E.r_not_forbidden i))
    · subst x
      exact (mem_extraNeighborFinset S i (E.s i)).2
        (And.intro (E.s_neighbor i) (E.s_not_forbidden i))
  have hset :
      extraNeighborFinset S i = ({E.r i, E.s i} : Finset (Fin n)) :=
    Finset.Subset.antisymm hsubset hsupset
  rw [hset]
  simp [E.r_ne_s i]

/-- If the Lemma 8 package names exactly two extra neighbors and the center has
degree six, then the four forbidden labels must occupy four distinct vertices.
-/
theorem forbiddenNeighborFinset_card_eq_four_of_lemma8Combinatorics_and_centerDegreeSix
    (E : M8Lemma8Combinatorics S) {i : M8ExtraIndex}
    (hdegree : centerDegree S i = 6) :
    (forbiddenNeighborFinset S i).card = 4 := by
  classical
  have hneighbor_subset :
      LocalExclusions.LocalGraph.neighborFinset
          (unitDistanceLocalGraph C) (S.centerQ i) <=
        forbiddenNeighborFinset S i ∪ extraNeighborFinset S i :=
    FourForbiddenNeighborFrame.neighborFinset_subset_forbidden_union_extra
      (S := S) (i := i)
  have hneighbor_card :
      (LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C)
        (S.q (m8TriangleIndexOfExtra i))).card = 6 := by
    simpa [centerDegree, LocalExclusions.LocalGraph.degree,
      M8BoundarySpine.centerQ] using hdegree
  have hle_union :
      6 <= (forbiddenNeighborFinset S i ∪ extraNeighborFinset S i).card := by
    have hcard_le := Finset.card_le_card hneighbor_subset
    simpa [hneighbor_card] using hcard_le
  have hdisjoint :
      Disjoint (forbiddenNeighborFinset S i) (extraNeighborFinset S i) :=
    FourForbiddenNeighborFrame.disjoint_forbidden_extra (S := S) (i := i)
  have hunion_card :
      (forbiddenNeighborFinset S i ∪ extraNeighborFinset S i).card =
        (forbiddenNeighborFinset S i).card +
          (extraNeighborFinset S i).card :=
    Finset.card_union_of_disjoint hdisjoint
  have hextra :
      (extraNeighborFinset S i).card = 2 :=
    extraNeighborFinset_card_eq_two_of_lemma8Combinatorics E i
  have hge : 4 <= (forbiddenNeighborFinset S i).card := by
    omega
  have hle : (forbiddenNeighborFinset S i).card <= 4 := by
    change
      ({S.leftP i, S.rightP i, S.prevQ i, S.nextQ i} :
        Finset (Fin n)).card <= 4
    exact Finset.card_le_four
  exact le_antisymm hle hge

/-- Pointwise forbidden-label distinctness follows from the honest center
degree-six field plus the Lemma 8 named-extra-neighbor package. -/
theorem fourForbiddenLabelsPairwiseDistinct_of_lemma8Combinatorics_and_centerDegreeSix
    (E : M8Lemma8Combinatorics S) {i : M8ExtraIndex}
    (hdegree : centerDegree S i = 6) :
    FourForbiddenLabelsPairwiseDistinct S i :=
  FourForbiddenLabelsPairwiseDistinct.of_forbidden_card_eq_four
    (forbiddenNeighborFinset_card_eq_four_of_lemma8Combinatorics_and_centerDegreeSix
      (S := S) E hdegree)

/-- Family form of forbidden-label distinctness from the Lemma 8 package and
the center-degree-six field. -/
theorem fourForbiddenLabelsPairwiseDistinct_family_of_lemma8Combinatorics_and_centerDegreeSix
    (E : M8Lemma8Combinatorics S)
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6) :
    forall i : M8ExtraIndex, FourForbiddenLabelsPairwiseDistinct S i :=
  fun i =>
    fourForbiddenLabelsPairwiseDistinct_of_lemma8Combinatorics_and_centerDegreeSix
      (S := S) E (hdegree i)

/-- The exact remaining no-collision family follows from the Lemma 8 package
and the center-degree-six field. -/
theorem remaining_three_noCollision_of_lemma8Combinatorics_and_centerDegreeSix
    (E : M8Lemma8Combinatorics S)
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6) :
    forall i : M8ExtraIndex,
      Not (S.leftP i = S.nextQ i) /\
      Not (S.rightP i = S.prevQ i) /\
      Not (S.prevQ i = S.nextQ i) :=
  (fourForbiddenLabelsPairwiseDistinct_family_iff_remaining_three
    (S := S)).1
    (fourForbiddenLabelsPairwiseDistinct_family_of_lemma8Combinatorics_and_centerDegreeSix
      (S := S) E hdegree)

/-! ## The smallest extra finite frame certificate -/

/--
The finite payload not already forced by the boundary spine and neighboring
triangle witnesses.

`left_ne_prev` and `right_ne_next` are omitted deliberately: they follow from
looplessness because `q_{i-1}` is adjacent to `p_i` and `q_{i+1}` is adjacent
to `p_{i+1}`.  The boundary edge gives `left_ne_right`.
-/
structure FourForbiddenFrameCore
    (S : M8BoundarySpine H) (i : M8ExtraIndex) : Prop where
  prev_adj : (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.prevQ i)
  next_adj : (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.nextQ i)
  left_ne_next : Not (S.leftP i = S.nextQ i)
  right_ne_prev : Not (S.rightP i = S.prevQ i)
  prev_ne_next : Not (S.prevQ i = S.nextQ i)

namespace FourForbiddenFrameCore

variable {i : M8ExtraIndex}

theorem pairwiseDistinct
    (K : FourForbiddenFrameCore S i) :
    FourForbiddenLabelsPairwiseDistinct S i := by
  exact
    { left_ne_right := leftP_ne_rightP S i
      left_ne_prev := leftP_ne_prevQ S i
      left_ne_next := K.left_ne_next
      right_ne_prev := K.right_ne_prev
      right_ne_next := rightP_ne_nextQ S i
      prev_ne_next := K.prev_ne_next }

theorem left_ne_right
    (K : FourForbiddenFrameCore S i) :
    Not (S.leftP i = S.rightP i) :=
  K.pairwiseDistinct.left_ne_right

theorem left_ne_prev
    (K : FourForbiddenFrameCore S i) :
    Not (S.leftP i = S.prevQ i) :=
  K.pairwiseDistinct.left_ne_prev

theorem right_ne_next
    (K : FourForbiddenFrameCore S i) :
    Not (S.rightP i = S.nextQ i) :=
  K.pairwiseDistinct.right_ne_next

theorem forbidden_card_eq_four
    (K : FourForbiddenFrameCore S i) :
    (forbiddenNeighborFinset S i).card = 4 :=
  K.pairwiseDistinct.forbidden_card_eq_four

/-- The isolated finite payload feeds the degree-six frame used in
`Lemma8ExistenceConcrete`. -/
def toFourForbiddenNeighborFrame
    (K : FourForbiddenFrameCore S i) :
    FourForbiddenNeighborFrame S i where
  prev_adj := K.prev_adj
  next_adj := K.next_adj
  left_ne_prev := leftP_ne_prevQ S i
  left_ne_next := K.left_ne_next
  right_ne_prev := K.right_ne_prev
  right_ne_next := rightP_ne_nextQ S i
  prev_ne_next := K.prev_ne_next

theorem forbidden_subset_neighborFinset
    (K : FourForbiddenFrameCore S i) :
    forbiddenNeighborFinset S i <=
      LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i) :=
  K.toFourForbiddenNeighborFrame.forbidden_subset_neighborFinset

theorem neighborFinset_eq_forbidden_union_extra
    (K : FourForbiddenFrameCore S i) :
    LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i) =
      forbiddenNeighborFinset S i ∪ extraNeighborFinset S i :=
  K.toFourForbiddenNeighborFrame.neighborFinset_eq_forbidden_union_extra

theorem neighborFinset_card_eq_forbidden_add_extra
    (K : FourForbiddenFrameCore S i) :
    (LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i)).card =
      (forbiddenNeighborFinset S i).card +
        (extraNeighborFinset S i).card :=
  K.toFourForbiddenNeighborFrame.neighborFinset_card_eq_forbidden_add_extra

theorem centerDegree_eq_four_add_extraNeighborFinset_card
    (K : FourForbiddenFrameCore S i) :
    centerDegree S i = 4 + (extraNeighborFinset S i).card := by
  have hcard := K.neighborFinset_card_eq_forbidden_add_extra
  have hfor := K.forbidden_card_eq_four
  simpa [centerDegree, LocalExclusions.LocalGraph.degree, hfor] using hcard

theorem centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two
    (K : FourForbiddenFrameCore S i) :
    centerDegree S i = 6 <-> (extraNeighborFinset S i).card = 2 := by
  constructor
  · intro hdegree
    exact
      K.toFourForbiddenNeighborFrame.extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
        hdegree
  · intro hcard
    have hdecomp :=
      centerDegree_eq_four_add_extraNeighborFinset_card (S := S) K
    omega

theorem extraNeighborFinset_card_le_two
    (K : FourForbiddenFrameCore S i) :
    (extraNeighborFinset S i).card <= 2 :=
  K.toFourForbiddenNeighborFrame.extraNeighborFinset_card_le_two

theorem extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    (K : FourForbiddenFrameCore S i)
    (hdegree : centerDegree S i = 6) :
    (extraNeighborFinset S i).card = 2 :=
  (K.toFourForbiddenNeighborFrame).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    hdegree

end FourForbiddenFrameCore

/-! ## Family and finite-certificate routing -/

/-- A finite family of the per-index frame cores. -/
structure M8FourForbiddenFrameCore
    (S : M8BoundarySpine H) : Prop where
  core : forall i : M8ExtraIndex, FourForbiddenFrameCore S i

namespace M8FourForbiddenFrameCore

theorem core_holds
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    FourForbiddenFrameCore S i :=
  K.core i

def toForbiddenFrame
    (K : M8FourForbiddenFrameCore S) :
    forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i :=
  fun i => (K.core i).toFourForbiddenNeighborFrame

theorem prev_adj
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.prevQ i) :=
  (K.core i).prev_adj

theorem next_adj
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj (S.centerQ i) (S.nextQ i) :=
  (K.core i).next_adj

theorem pairwiseDistinct
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    FourForbiddenLabelsPairwiseDistinct S i :=
  (K.core i).pairwiseDistinct

theorem left_ne_right
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    Not (S.leftP i = S.rightP i) :=
  (K.core i).left_ne_right

theorem left_ne_prev
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    Not (S.leftP i = S.prevQ i) :=
  (K.core i).left_ne_prev

theorem left_ne_next
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    Not (S.leftP i = S.nextQ i) :=
  (K.core i).left_ne_next

theorem right_ne_prev
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    Not (S.rightP i = S.prevQ i) :=
  (K.core i).right_ne_prev

theorem right_ne_next
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    Not (S.rightP i = S.nextQ i) :=
  (K.core i).right_ne_next

theorem prev_ne_next
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    Not (S.prevQ i = S.nextQ i) :=
  (K.core i).prev_ne_next

theorem forbidden_card_eq_four
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    (forbiddenNeighborFinset S i).card = 4 :=
  (K.core i).forbidden_card_eq_four

theorem neighborFinset_card_eq_forbidden_add_extra
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    (LocalExclusions.LocalGraph.neighborFinset
        (unitDistanceLocalGraph C) (S.centerQ i)).card =
      (forbiddenNeighborFinset S i).card +
        (extraNeighborFinset S i).card :=
  (K.core i).neighborFinset_card_eq_forbidden_add_extra

theorem centerDegree_eq_four_add_extraNeighborFinset_card
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    centerDegree S i = 4 + (extraNeighborFinset S i).card :=
  (K.core i).centerDegree_eq_four_add_extraNeighborFinset_card

theorem centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    centerDegree S i = 6 <-> (extraNeighborFinset S i).card = 2 :=
  (K.core i).centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two

theorem extraNeighborFinset_card_le_two
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card <= 2 :=
  (K.core i).extraNeighborFinset_card_le_two

theorem extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    (K : M8FourForbiddenFrameCore S)
    (hdegree : forall i : M8ExtraIndex, centerDegree S i = 6)
    (i : M8ExtraIndex) :
    (extraNeighborFinset S i).card = 2 :=
  (K.core i).extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    (hdegree i)

end M8FourForbiddenFrameCore

/-! ## Center-degree six from real frame core and Lemma 8 witnesses -/

/-- The honest frame core plus the named Lemma 8 extra-neighbor package closes
the real center-degree-six field.  Lemma 8 supplies exact cardinality two for
the non-forbidden neighbors, and the frame core identifies degree six with
that exact cardinality. -/
theorem centerDegreeSix_of_lemma8Combinatorics_and_frameCore
    (E : M8Lemma8Combinatorics S)
    (F : M8FourForbiddenFrameCore S) :
    forall i : M8ExtraIndex, centerDegree S i = 6 := by
  intro i
  exact (F.centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two i).2
    (extraNeighborFinset_card_eq_two_of_lemma8Combinatorics E i)

/-- Forbidden-label pairwise distinctness from the same real frame core and
Lemma 8 witness package, routed through the closed center-degree-six field. -/
theorem fourForbiddenLabelsPairwiseDistinct_family_of_lemma8Combinatorics_and_frameCore
    (E : M8Lemma8Combinatorics S)
    (F : M8FourForbiddenFrameCore S) :
    forall i : M8ExtraIndex, FourForbiddenLabelsPairwiseDistinct S i :=
  fourForbiddenLabelsPairwiseDistinct_family_of_lemma8Combinatorics_and_centerDegreeSix
    (S := S) E
    (centerDegreeSix_of_lemma8Combinatorics_and_frameCore
      (S := S) E F)

/-- The remaining finite forbidden-label no-collisions follow from the real
frame core once the Lemma 8 witnesses are attached. -/
theorem remaining_three_noCollision_of_lemma8Combinatorics_and_frameCore
    (E : M8Lemma8Combinatorics S)
    (F : M8FourForbiddenFrameCore S) :
    forall i : M8ExtraIndex,
      Not (S.leftP i = S.nextQ i) /\
      Not (S.rightP i = S.prevQ i) /\
      Not (S.prevQ i = S.nextQ i) :=
  remaining_three_noCollision_of_lemma8Combinatorics_and_centerDegreeSix
    (S := S) E
    (centerDegreeSix_of_lemma8Combinatorics_and_frameCore
      (S := S) E F)

namespace FinitePQSpineRoute

universe u

variable {D : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (BoundaryFaceCountingToM8.CanonicalUDGraph C)}
variable {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
variable {hmin : MinimalGraphFacts.IsMinimalClearedFailure C}

/-- The same minimal frame-core certificate, specialized to the spine
generated by an explicit finite `p/q` boundary certificate. -/
abbrev FourForbiddenFrameCoreFamily
    (K : M8FinitePQSpineCertificate D) : Prop :=
  M8FourForbiddenFrameCore (K.toM8BoundarySpine connectedNoCut hmin)

/-- Route a finite `p/q` certificate plus the isolated frame-core family into
the `FourForbiddenNeighborFrame` family consumed by `Lemma8ExistenceConcrete`.
-/
def toForbiddenFrame
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K) :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (K.toM8BoundarySpine connectedNoCut hmin) i :=
  F.toForbiddenFrame

theorem core_holds
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K)
    (i : M8ExtraIndex) :
    FourForbiddenFrameCore
      (K.toM8BoundarySpine connectedNoCut hmin) i :=
  F.core_holds i

theorem pairwiseDistinct
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K)
    (i : M8ExtraIndex) :
    FourForbiddenLabelsPairwiseDistinct
      (K.toM8BoundarySpine connectedNoCut hmin) i :=
  F.pairwiseDistinct i

theorem forbidden_card_eq_four
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K)
    (i : M8ExtraIndex) :
    (forbiddenNeighborFinset
      (K.toM8BoundarySpine connectedNoCut hmin) i).card = 4 :=
  F.forbidden_card_eq_four i

theorem centerDegree_eq_four_add_extraNeighborFinset_card
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K)
    (i : M8ExtraIndex) :
    centerDegree (K.toM8BoundarySpine connectedNoCut hmin) i =
      4 +
        (extraNeighborFinset
          (K.toM8BoundarySpine connectedNoCut hmin) i).card :=
  F.centerDegree_eq_four_add_extraNeighborFinset_card i

theorem centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K)
    (i : M8ExtraIndex) :
    centerDegree (K.toM8BoundarySpine connectedNoCut hmin) i = 6 <->
      (extraNeighborFinset
        (K.toM8BoundarySpine connectedNoCut hmin) i).card = 2 :=
  F.centerDegree_eq_six_iff_extraNeighborFinset_card_eq_two i

theorem extraNeighborFinset_card_eq_two_of_centerDegree_eq_six
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K)
    (hdegree : forall i : M8ExtraIndex,
      centerDegree (K.toM8BoundarySpine connectedNoCut hmin) i = 6)
    (i : M8ExtraIndex) :
      (extraNeighborFinset
        (K.toM8BoundarySpine connectedNoCut hmin) i).card = 2 :=
  F.extraNeighborFinset_card_eq_two_of_centerDegree_eq_six hdegree i

/-- The finite-spine frame-core payload is exactly the raw field projection of
the four-forbidden frame core on the generated spine. -/
def toFinitePQSpineFrameCoreFields
    (K : M8FinitePQSpineCertificate D)
    (F : FourForbiddenFrameCoreFamily
      (connectedNoCut := connectedNoCut) (hmin := hmin) K) :
    M8FinitePQSpineFrameCoreFields K connectedNoCut hmin where
  prev_adj := fun i => M8FourForbiddenFrameCore.prev_adj F i
  next_adj := fun i => M8FourForbiddenFrameCore.next_adj F i
  left_ne_next := fun i => M8FourForbiddenFrameCore.left_ne_next F i
  right_ne_prev := fun i => M8FourForbiddenFrameCore.right_ne_prev F i
  prev_ne_next := fun i => M8FourForbiddenFrameCore.prev_ne_next F i

end FinitePQSpineRoute

end

end Lemma8ForbiddenDistinctConcrete
end Swanepoel
end ErdosProblems1066
