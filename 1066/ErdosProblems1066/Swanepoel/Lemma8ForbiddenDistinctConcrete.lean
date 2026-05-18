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

end FinitePQSpineRoute

end

end Lemma8ForbiddenDistinctConcrete
end Swanepoel
end ErdosProblems1066
