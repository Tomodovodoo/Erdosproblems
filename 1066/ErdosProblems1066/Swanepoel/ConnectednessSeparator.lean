import ErdosProblems1066.Swanepoel.CounterexamplePipeline
import ErdosProblems1066.Swanepoel.InducedSubconfiguration
import ErdosProblems1066.Swanepoel.MinimalGraphFacts

/-!
# Anticomplete separators for the Swanepoel unit-distance graph

This module packages a finite anticomplete two-block partition of `Fin n` for
`GraphBridge.unitDistanceSimpleGraph C`.  It is deliberately structural: no
planarity, no no-cut-vertex theorem, and no minimum-degree input is used.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace ConnectednessSeparator

open CounterexamplePipeline
open GraphBridge
open InducedSubconfiguration
open MinimalCounterexample

noncomputable section

/-- A finite anticomplete partition of the vertex set of the unit-distance
simple graph attached to `C`.

The two sides are nonempty, disjoint, cover all of `Fin n`, and have no
unit-distance edge from the left side to the right side. -/
structure FinAnticompletePartition {n : Nat} (C : _root_.UDConfig n) where
  left : Finset (Fin n)
  right : Finset (Fin n)
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disjoint : Disjoint left right
  cover : left ∪ right = Finset.univ
  anticomplete :
    forall i : Fin n, i ∈ left ->
      forall j : Fin n, j ∈ right ->
        ¬ (unitDistanceSimpleGraph C).Adj i j

namespace FinAnticompletePartition

variable {n : Nat} {C : _root_.UDConfig n}

/-- The induced configuration on the left side of the partition. -/
def leftInduced (P : FinAnticompletePartition C) :
    Induced (m := P.left.card) C P.left :=
  InducedSubconfiguration.ofFinset C P.left

/-- The induced configuration on the right side of the partition. -/
def rightInduced (P : FinAnticompletePartition C) :
    Induced (m := P.right.card) C P.right :=
  InducedSubconfiguration.ofFinset C P.right

@[simp]
lemma leftInduced_image_univ (P : FinAnticompletePartition C) :
    ((Finset.univ : Finset (Fin P.left.card)).image P.leftInduced.embed) =
      P.left :=
  P.leftInduced.image_univ

@[simp]
lemma rightInduced_image_univ (P : FinAnticompletePartition C) :
    ((Finset.univ : Finset (Fin P.right.card)).image P.rightInduced.embed) =
      P.right :=
  P.rightInduced.image_univ

lemma mem_left_or_mem_right (P : FinAnticompletePartition C) (v : Fin n) :
    v ∈ P.left ∨ v ∈ P.right := by
  have hv : v ∈ P.left ∪ P.right := by
    simp [P.cover]
  exact Finset.mem_union.mp hv

lemma not_mem_right_of_mem_left (P : FinAnticompletePartition C) {v : Fin n}
    (hv : v ∈ P.left) :
    v ∉ P.right := by
  exact fun hvRight => (Finset.disjoint_left.mp P.disjoint) hv hvRight

lemma not_mem_left_of_mem_right (P : FinAnticompletePartition C) {v : Fin n}
    (hv : v ∈ P.right) :
    v ∉ P.left := by
  exact fun hvLeft => (Finset.disjoint_left.mp P.disjoint) hvLeft hv

lemma no_adj_left_right (P : FinAnticompletePartition C) {i j : Fin n}
    (hi : i ∈ P.left) (hj : j ∈ P.right) :
    ¬ (unitDistanceSimpleGraph C).Adj i j :=
  P.anticomplete i hi j hj

lemma no_adj_right_left (P : FinAnticompletePartition C) {i j : Fin n}
    (hi : i ∈ P.right) (hj : j ∈ P.left) :
    ¬ (unitDistanceSimpleGraph C).Adj i j := by
  intro h
  exact P.anticomplete j hj i hi ((unitDistanceSimpleGraph C).symm h)

lemma no_unit_left_right (P : FinAnticompletePartition C) {i j : Fin n}
    (hi : i ∈ P.left) (hj : j ∈ P.right) :
    eucDist (C.pts i) (C.pts j) ≠ 1 := by
  intro hunit
  exact P.anticomplete i hi j hj
    ((unitDistanceSimpleGraph_adj C i j).2 hunit)

lemma no_unit_right_left (P : FinAnticompletePartition C) {i j : Fin n}
    (hi : i ∈ P.right) (hj : j ∈ P.left) :
    eucDist (C.pts i) (C.pts j) ≠ 1 := by
  intro hunit
  exact P.no_unit_left_right hj hi (by simpa [eucDist_comm] using hunit)

lemma leftInduced_embed_mem (P : FinAnticompletePartition C)
    (i : Fin P.left.card) :
    P.leftInduced.embed i ∈ P.left := by
  have hmem :
      P.leftInduced.embed i ∈
        ((Finset.univ : Finset (Fin P.left.card)).image
          P.leftInduced.embed) :=
    Finset.mem_image_of_mem P.leftInduced.embed (Finset.mem_univ i)
  simpa using hmem

lemma rightInduced_embed_mem (P : FinAnticompletePartition C)
    (i : Fin P.right.card) :
    P.rightInduced.embed i ∈ P.right := by
  have hmem :
      P.rightInduced.embed i ∈
        ((Finset.univ : Finset (Fin P.right.card)).image
          P.rightInduced.embed) :=
    Finset.mem_image_of_mem P.rightInduced.embed (Finset.mem_univ i)
  simpa using hmem

lemma card_eq_left_add_right (P : FinAnticompletePartition C) :
    n = P.left.card + P.right.card := by
  have hcard := Finset.card_union_of_disjoint P.disjoint
  rw [P.cover] at hcard
  simpa using hcard

lemma left_card_lt (P : FinAnticompletePartition C) :
    P.left.card < n := by
  have hcard := P.card_eq_left_add_right
  have hright : 0 < P.right.card := Finset.card_pos.mpr P.right_nonempty
  omega

lemma right_card_lt (P : FinAnticompletePartition C) :
    P.right.card < n := by
  have hcard := P.card_eq_left_add_right
  have hleft : 0 < P.left.card := Finset.card_pos.mpr P.left_nonempty
  omega

private lemma image_subset_left (P : FinAnticompletePartition C)
    {s : Finset (Fin P.left.card)} :
    s.image P.leftInduced.embed ⊆ P.left := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.leftInduced_embed_mem i

private lemma image_subset_right (P : FinAnticompletePartition C)
    {s : Finset (Fin P.right.card)} :
    s.image P.rightInduced.embed ⊆ P.right := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.rightInduced_embed_mem i

/-- Cleared independent sets on the two induced sides combine to a cleared
independent set in the ambient configuration. -/
theorem hasCleared_of_induced_hasCleared (P : FinAnticompletePartition C)
    (hleft :
      HasClearedEightThirtyOneIndependentSet P.leftInduced.config)
    (hright :
      HasClearedEightThirtyOneIndependentSet P.rightInduced.config) :
    HasClearedEightThirtyOneIndependentSet C := by
  rcases hleft with ⟨sLeft, hsLeftIndep, hsLeftBound⟩
  rcases hright with ⟨sRight, hsRightIndep, hsRightBound⟩
  let leftImage : Finset (Fin n) := sLeft.image P.leftInduced.embed
  let rightImage : Finset (Fin n) := sRight.image P.rightInduced.embed
  have hleftImageIndep : C.IsIndep leftImage :=
    P.leftInduced.image_indep hsLeftIndep
  have hrightImageIndep : C.IsIndep rightImage :=
    P.rightInduced.image_indep hsRightIndep
  have hcross :
      forall x : Fin n, x ∈ leftImage ->
        forall y : Fin n, y ∈ rightImage -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1 := by
    intro x hx y hy _hxy
    exact P.no_unit_left_right (image_subset_left P hx)
      (image_subset_right P hy)
  let combined : Finset (Fin n) := leftImage ∪ rightImage
  have hcombinedIndep : C.IsIndep combined :=
    union_indep_of_cross_nonunit hleftImageIndep hrightImageIndep hcross
  have himagesDisjoint : Disjoint leftImage rightImage := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    exact (Finset.disjoint_left.mp P.disjoint)
      (image_subset_left P hxLeft) (image_subset_right P hxRight)
  have hcombinedCard :
      combined.card = sLeft.card + sRight.card := by
    have hcard := Finset.card_union_of_disjoint himagesDisjoint
    simpa [combined, leftImage, rightImage,
      Finset.card_image_of_injective _ P.leftInduced.embed_injective,
      Finset.card_image_of_injective _ P.rightInduced.embed_injective] using hcard
  have hbound :
      ClearedEightThirtyOneBound n (sLeft.card + sRight.card) := by
    unfold ClearedEightThirtyOneBound at *
    have hcard := P.card_eq_left_add_right
    omega
  exact ⟨combined, hcombinedIndep, by simpa [hcombinedCard] using hbound⟩

/-- Contradiction-routing form: an uncleared ambient configuration cannot have
an anticomplete partition whose two induced sides are already cleared. -/
theorem contradiction_of_induced_hasCleared (P : FinAnticompletePartition C)
    (hC : ¬ HasClearedEightThirtyOneIndependentSet C)
    (hleft :
      HasClearedEightThirtyOneIndependentSet P.leftInduced.config)
    (hright :
      HasClearedEightThirtyOneIndependentSet P.rightInduced.config) :
    False :=
  hC (P.hasCleared_of_induced_hasCleared hleft hright)

/-- A finite anticomplete partition is impossible in a minimal cleared failure. -/
theorem contradiction_of_minimalClearedFailure (P : FinAnticompletePartition C)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    False :=
  P.contradiction_of_induced_hasCleared
    (MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin)
    (MinimalGraphFacts.smaller_hasCleared_of_minimalClearedFailure hmin
      P.leftInduced.config P.left_card_lt)
    (MinimalGraphFacts.smaller_hasCleared_of_minimalClearedFailure hmin
      P.rightInduced.config P.right_card_lt)

end FinAnticompletePartition

end

end ConnectednessSeparator
end Swanepoel
end ErdosProblems1066
