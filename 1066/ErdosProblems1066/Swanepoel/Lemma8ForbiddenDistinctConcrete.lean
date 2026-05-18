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

def toForbiddenFrame
    (K : M8FourForbiddenFrameCore S) :
    forall i : M8ExtraIndex, FourForbiddenNeighborFrame S i :=
  fun i => (K.core i).toFourForbiddenNeighborFrame

theorem pairwiseDistinct
    (K : M8FourForbiddenFrameCore S) (i : M8ExtraIndex) :
    FourForbiddenLabelsPairwiseDistinct S i :=
  (K.core i).pairwiseDistinct

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

end FinitePQSpineRoute

end

end Lemma8ForbiddenDistinctConcrete
end Swanepoel
end ErdosProblems1066
