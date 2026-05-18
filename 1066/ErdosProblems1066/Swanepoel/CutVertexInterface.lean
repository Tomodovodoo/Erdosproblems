import ErdosProblems1066.Swanepoel.ConnectednessSeparator

/-!
# Cut-vertex and slack interfaces for the Swanepoel route

This module records cut-vertex data as explicit hypotheses.  In particular, it
does not derive any no-cut-vertex statement from minimality.  The useful
downstream object is a concrete separator witness, together with conditional
gluing lemmas for independent sets whose cleared `8 / 31` bounds have enough
surplus to pay for the omitted cut vertex.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexInterface

open CounterexamplePipeline
open GraphBridge
open InducedSubconfiguration

noncomputable section

/-! ## Explicit cut-vertex witnesses -/

/-- A labelled cut-vertex partition for the unit-distance graph of `C`.

The sets `left` and `right` are the two nonempty sides after deleting `cut`.
They are disjoint, avoid `cut`, cover all remaining vertices, and have no
unit-distance edge between them.  This is data, not a theorem about minimal
counterexamples. -/
structure CutVertexPartition {n : Nat} (C : _root_.UDConfig n) where
  cut : Fin n
  left : Finset (Fin n)
  right : Finset (Fin n)
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  left_cut_not_mem : cut ∉ left
  right_cut_not_mem : cut ∉ right
  disjoint : Disjoint left right
  cover_without_cut : left ∪ right = Finset.univ.erase cut
  anticomplete :
    forall i : Fin n, i ∈ left ->
      forall j : Fin n, j ∈ right ->
        ¬ (unitDistanceSimpleGraph C).Adj i j

/-- The proposition that no cut-vertex partition has been supplied.  This is a
separate assumption for downstream files; it is intentionally not connected to
minimality here. -/
def NoCutVertex {n : Nat} (C : _root_.UDConfig n) : Prop :=
  ¬ Nonempty (CutVertexPartition C)

/-- A named certificate for files that prefer structures over bare negations. -/
structure NoCutVertexCertificate {n : Nat} (C : _root_.UDConfig n) : Prop where
  no_cut_vertex : NoCutVertex C

namespace NoCutVertexCertificate

variable {n : Nat} {C : _root_.UDConfig n}

lemma not_partition (H : NoCutVertexCertificate C) :
    ¬ Nonempty (CutVertexPartition C) :=
  H.no_cut_vertex

lemma false_of_partition (H : NoCutVertexCertificate C)
    (P : CutVertexPartition C) : False :=
  H.no_cut_vertex ⟨P⟩

end NoCutVertexCertificate

namespace CutVertexPartition

variable {n : Nat} {C : _root_.UDConfig n}

/-- The induced configuration on the left side after removing the cut vertex. -/
def leftInduced (P : CutVertexPartition C) :
    Induced (m := P.left.card) C P.left :=
  InducedSubconfiguration.ofFinset C P.left

/-- The induced configuration on the right side after removing the cut vertex. -/
def rightInduced (P : CutVertexPartition C) :
    Induced (m := P.right.card) C P.right :=
  InducedSubconfiguration.ofFinset C P.right

@[simp]
lemma leftInduced_image_univ (P : CutVertexPartition C) :
    ((Finset.univ : Finset (Fin P.left.card)).image P.leftInduced.embed) =
      P.left :=
  P.leftInduced.image_univ

@[simp]
lemma rightInduced_image_univ (P : CutVertexPartition C) :
    ((Finset.univ : Finset (Fin P.right.card)).image P.rightInduced.embed) =
      P.right :=
  P.rightInduced.image_univ

lemma mem_left_or_mem_right_of_ne_cut (P : CutVertexPartition C)
    {v : Fin n} (hv : v ≠ P.cut) :
    v ∈ P.left ∨ v ∈ P.right := by
  have hvCover : v ∈ P.left ∪ P.right := by
    rw [P.cover_without_cut]
    exact Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
  exact Finset.mem_union.mp hvCover

lemma left_subset_erase_cut (P : CutVertexPartition C) :
    P.left ⊆ Finset.univ.erase P.cut := by
  intro v hv
  rw [← P.cover_without_cut]
  exact Finset.mem_union_left P.right hv

lemma right_subset_erase_cut (P : CutVertexPartition C) :
    P.right ⊆ Finset.univ.erase P.cut := by
  intro v hv
  rw [← P.cover_without_cut]
  exact Finset.mem_union_right P.left hv

lemma no_adj_left_right (P : CutVertexPartition C) {i j : Fin n}
    (hi : i ∈ P.left) (hj : j ∈ P.right) :
    ¬ (unitDistanceSimpleGraph C).Adj i j :=
  P.anticomplete i hi j hj

lemma no_adj_right_left (P : CutVertexPartition C) {i j : Fin n}
    (hi : i ∈ P.right) (hj : j ∈ P.left) :
    ¬ (unitDistanceSimpleGraph C).Adj i j := by
  intro h
  exact P.anticomplete j hj i hi ((unitDistanceSimpleGraph C).symm h)

lemma no_unit_left_right (P : CutVertexPartition C) {i j : Fin n}
    (hi : i ∈ P.left) (hj : j ∈ P.right) :
    eucDist (C.pts i) (C.pts j) ≠ 1 := by
  intro hunit
  exact P.anticomplete i hi j hj
    ((unitDistanceSimpleGraph_adj C i j).2 hunit)

lemma no_unit_right_left (P : CutVertexPartition C) {i j : Fin n}
    (hi : i ∈ P.right) (hj : j ∈ P.left) :
    eucDist (C.pts i) (C.pts j) ≠ 1 := by
  intro hunit
  exact P.no_unit_left_right hj hi (by simpa [eucDist_comm] using hunit)

lemma leftInduced_embed_mem (P : CutVertexPartition C)
    (i : Fin P.left.card) :
    P.leftInduced.embed i ∈ P.left := by
  have hmem :
      P.leftInduced.embed i ∈
        ((Finset.univ : Finset (Fin P.left.card)).image
          P.leftInduced.embed) :=
    Finset.mem_image_of_mem P.leftInduced.embed (Finset.mem_univ i)
  simpa using hmem

lemma rightInduced_embed_mem (P : CutVertexPartition C)
    (i : Fin P.right.card) :
    P.rightInduced.embed i ∈ P.right := by
  have hmem :
      P.rightInduced.embed i ∈
        ((Finset.univ : Finset (Fin P.right.card)).image
          P.rightInduced.embed) :=
    Finset.mem_image_of_mem P.rightInduced.embed (Finset.mem_univ i)
  simpa using hmem

lemma card_eq_left_add_right_add_one (P : CutVertexPartition C) :
    n = P.left.card + P.right.card + 1 := by
  have hcard := Finset.card_union_of_disjoint P.disjoint
  rw [P.cover_without_cut] at hcard
  have hcut : P.cut ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ P.cut
  have herase :
      (Finset.univ.erase P.cut : Finset (Fin n)).card + 1 = n := by
    rw [Finset.card_erase_of_mem hcut]
    simp only [Finset.card_univ, Fintype.card_fin]
    have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le P.cut.val) P.cut.2
    omega
  omega

lemma left_card_lt (P : CutVertexPartition C) :
    P.left.card < n := by
  have hcard := P.card_eq_left_add_right_add_one
  omega

lemma right_card_lt (P : CutVertexPartition C) :
    P.right.card < n := by
  have hcard := P.card_eq_left_add_right_add_one
  omega

private lemma image_subset_left (P : CutVertexPartition C)
    {s : Finset (Fin P.left.card)} :
    s.image P.leftInduced.embed ⊆ P.left := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.leftInduced_embed_mem i

private lemma image_subset_right (P : CutVertexPartition C)
    {s : Finset (Fin P.right.card)} :
    s.image P.rightInduced.embed ⊆ P.right := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.rightInduced_embed_mem i

/-! ## Slack packages and conditional gluing -/

/-- An independent set with at least `surplus` units of cleared `8 / 31`
slack: `31 * |s| >= 8 * n + surplus`. -/
structure SlackIndependentSet {m : Nat} (Csmall : _root_.UDConfig m)
    (surplus : Nat) where
  carrier : Finset (Fin m)
  indep : Csmall.IsIndep carrier
  surplus_bound : 8 * m + surplus <= 31 * carrier.card

namespace SlackIndependentSet

variable {m : Nat} {Csmall : _root_.UDConfig m} {surplus : Nat}

lemma hasCleared (S : SlackIndependentSet Csmall surplus) :
    HasClearedEightThirtyOneIndependentSet Csmall := by
  refine ⟨S.carrier, S.indep, ?_⟩
  unfold MinimalCounterexample.ClearedEightThirtyOneBound
  exact Nat.le_trans (Nat.le_add_right (8 * m) surplus) S.surplus_bound

end SlackIndependentSet

/-- Side data for gluing across a cut vertex after the cut vertex has been
deleted from both sides.  The final field is the explicit slack needed to pay
for the one omitted vertex. -/
structure CutVertexSlackGluingData (P : CutVertexPartition C) where
  leftSurplus : Nat
  rightSurplus : Nat
  leftSet : SlackIndependentSet P.leftInduced.config leftSurplus
  rightSet : SlackIndependentSet P.rightInduced.config rightSurplus
  pays_cut_vertex : 8 <= leftSurplus + rightSurplus

/-- The left projection of cut-vertex slack data. -/
def CutVertexSlackGluingData.leftCleared
    {P : CutVertexPartition C} (D : CutVertexSlackGluingData P) :
    HasClearedEightThirtyOneIndependentSet P.leftInduced.config :=
  D.leftSet.hasCleared

/-- The right projection of cut-vertex slack data. -/
def CutVertexSlackGluingData.rightCleared
    {P : CutVertexPartition C} (D : CutVertexSlackGluingData P) :
    HasClearedEightThirtyOneIndependentSet P.rightInduced.config :=
  D.rightSet.hasCleared

/-- Independent sets on the two cut sides glue when their explicit surplus is
large enough to pay for the deleted cut vertex. -/
theorem hasCleared_of_cutVertexSlack
    (P : CutVertexPartition C) (D : CutVertexSlackGluingData P) :
    HasClearedEightThirtyOneIndependentSet C := by
  let leftImage : Finset (Fin n) := D.leftSet.carrier.image P.leftInduced.embed
  let rightImage : Finset (Fin n) := D.rightSet.carrier.image P.rightInduced.embed
  have hleftSubset : leftImage ⊆ P.left := by
    simpa [leftImage] using
      (image_subset_left P (s := D.leftSet.carrier))
  have hrightSubset : rightImage ⊆ P.right := by
    simpa [rightImage] using
      (image_subset_right P (s := D.rightSet.carrier))
  have hleftImageIndep : C.IsIndep leftImage :=
    P.leftInduced.image_indep D.leftSet.indep
  have hrightImageIndep : C.IsIndep rightImage :=
    P.rightInduced.image_indep D.rightSet.indep
  have hcross :
      forall x : Fin n, x ∈ leftImage ->
        forall y : Fin n, y ∈ rightImage -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1 := by
    intro x hx y hy _hxy
    exact P.no_unit_left_right (hleftSubset hx) (hrightSubset hy)
  let combined : Finset (Fin n) := leftImage ∪ rightImage
  have hcombinedIndep : C.IsIndep combined :=
    MinimalCounterexample.union_indep_of_cross_nonunit
      hleftImageIndep hrightImageIndep hcross
  have himagesDisjoint : Disjoint leftImage rightImage := by
    rw [Finset.disjoint_left]
    intro x hxLeft hxRight
    exact (Finset.disjoint_left.mp P.disjoint)
      (hleftSubset hxLeft) (hrightSubset hxRight)
  have hcombinedCard :
      combined.card = D.leftSet.carrier.card + D.rightSet.carrier.card := by
    have hcard := Finset.card_union_of_disjoint himagesDisjoint
    simpa [combined, leftImage, rightImage,
      Finset.card_image_of_injective _ P.leftInduced.embed_injective,
      Finset.card_image_of_injective _ P.rightInduced.embed_injective] using hcard
  have hbound :
      MinimalCounterexample.ClearedEightThirtyOneBound n
        (D.leftSet.carrier.card + D.rightSet.carrier.card) := by
    unfold MinimalCounterexample.ClearedEightThirtyOneBound
    have hcard := P.card_eq_left_add_right_add_one
    have hleft := D.leftSet.surplus_bound
    have hright := D.rightSet.surplus_bound
    have hpay := D.pays_cut_vertex
    omega
  exact ⟨combined, hcombinedIndep, by simpa [hcombinedCard] using hbound⟩

/-- Contradiction-routing form of the slack gluing lemma. -/
theorem contradiction_of_cutVertexSlack
    (P : CutVertexPartition C)
    (hC : ¬ HasClearedEightThirtyOneIndependentSet C)
    (D : CutVertexSlackGluingData P) :
    False :=
  hC (hasCleared_of_cutVertexSlack P D)

end CutVertexPartition

end

end CutVertexInterface
end Swanepoel
end ErdosProblems1066
