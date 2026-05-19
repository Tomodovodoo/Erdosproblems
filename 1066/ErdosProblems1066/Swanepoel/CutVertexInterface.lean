import ErdosProblems1066.Swanepoel.ConnectednessSeparator
import ErdosProblems1066.Swanepoel.SmallIndependentNeighborhood

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

/-- The left side with the cut vertex reinserted. -/
def leftWithCut (P : CutVertexPartition C) : Finset (Fin n) :=
  insert P.cut P.left

/-- The right side with the cut vertex reinserted. -/
def rightWithCut (P : CutVertexPartition C) : Finset (Fin n) :=
  insert P.cut P.right

/-- The induced configuration on the left side with the cut vertex. -/
def leftWithCutInduced (P : CutVertexPartition C) :
    Induced (m := P.leftWithCut.card) C P.leftWithCut :=
  InducedSubconfiguration.ofFinset C P.leftWithCut

/-- The induced configuration on the right side with the cut vertex. -/
def rightWithCutInduced (P : CutVertexPartition C) :
    Induced (m := P.rightWithCut.card) C P.rightWithCut :=
  InducedSubconfiguration.ofFinset C P.rightWithCut

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

@[simp]
lemma leftWithCutInduced_image_univ (P : CutVertexPartition C) :
    ((Finset.univ : Finset (Fin P.leftWithCut.card)).image
        P.leftWithCutInduced.embed) =
      P.leftWithCut :=
  P.leftWithCutInduced.image_univ

@[simp]
lemma rightWithCutInduced_image_univ (P : CutVertexPartition C) :
    ((Finset.univ : Finset (Fin P.rightWithCut.card)).image
        P.rightWithCutInduced.embed) =
      P.rightWithCut :=
  P.rightWithCutInduced.image_univ

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

/-- One vertex from each side of a cut partition is an independent pair. -/
theorem independent_pair_left_right (P : CutVertexPartition C)
    {l r : Fin n} (hl : l ∈ P.left) (hr : r ∈ P.right) :
    C.IsIndep ({l, r} : Finset (Fin n)) := by
  intro i hi j hj hij
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl
  · rcases hj with rfl | rfl
    · exact False.elim (hij rfl)
    · exact P.no_unit_left_right hl hr
  · rcases hj with rfl | rfl
    · exact P.no_unit_right_left hr hl
    · exact False.elim (hij rfl)

/-- Every cut partition supplies a concrete independent two-point set, one
point on each side. -/
theorem exists_independent_pair_left_right (P : CutVertexPartition C) :
    Exists fun S : Finset (Fin n) =>
      S.card = 2 /\ C.IsIndep S /\ S <= P.left ∪ P.right := by
  rcases P.left_nonempty with ⟨l, hl⟩
  rcases P.right_nonempty with ⟨r, hr⟩
  have hne : l ≠ r := by
    intro h
    subst r
    exact (Finset.disjoint_left.mp P.disjoint) hl hr
  refine ⟨{l, r}, ?_, ?_, ?_⟩
  · simp [hne]
  · exact P.independent_pair_left_right hl hr
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_union_left P.right hl
    · exact Finset.mem_union_right P.left hr

/-- The cross-side pair is already small enough for the no-cut
deficient-neighborhood branch; only the outside-neighborhood bound remains. -/
theorem exists_small_independent_pair_left_right
    (P : CutVertexPartition C) :
    Exists fun S : Finset (Fin n) =>
      S.Nonempty /\ C.IsIndep S /\ S.card <= 8 /\
        S <= P.left ∪ P.right := by
  rcases P.exists_independent_pair_left_right with
    ⟨S, hcard, hindep, hsubset⟩
  refine ⟨S, ?_, hindep, ?_, hsubset⟩
  · exact Finset.card_pos.mp (by omega)
  · omega

/-- The explicit cut-side cover for the outside neighborhood of a pair
chosen with one vertex on each side of the partition.  Any outside neighbor
of the left vertex is either the cut vertex or remains on the left side, and
symmetrically for the right vertex. -/
def crossPairSideNeighborhoodCover (P : CutVertexPartition C)
    (l r : Fin n) : Finset (Fin n) :=
  insert P.cut
    ((P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1) ∪
      (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1))

theorem crossPairSideNeighborhoodCover_card_eq
    (P : CutVertexPartition C) (l r : Fin n) :
    (P.crossPairSideNeighborhoodCover l r).card =
      (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
        (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card + 1 := by
  classical
  let leftNeighbors : Finset (Fin n) :=
    P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1
  let rightNeighbors : Finset (Fin n) :=
    P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1
  have hcut :
      P.cut ∉ leftNeighbors ∪ rightNeighbors := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hleft | hright
    · exact P.left_cut_not_mem (Finset.mem_filter.mp hleft).1
    · exact P.right_cut_not_mem (Finset.mem_filter.mp hright).1
  have hdisjoint : Disjoint leftNeighbors rightNeighbors := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvRight
    exact (Finset.disjoint_left.mp P.disjoint)
      (Finset.mem_filter.mp hvLeft).1
      (Finset.mem_filter.mp hvRight).1
  calc
    (P.crossPairSideNeighborhoodCover l r).card
        = (insert P.cut (leftNeighbors ∪ rightNeighbors)).card := by
            rfl
    _ = (leftNeighbors ∪ rightNeighbors).card + 1 := by
            rw [Finset.card_insert_of_notMem hcut]
    _ = leftNeighbors.card + rightNeighbors.card + 1 := by
            rw [Finset.card_union_of_disjoint hdisjoint]
    _ =
        (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
          (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card + 1 := by
            rfl

theorem crossPairSideNeighborhoodCover_card_lt_six_of_sideNeighborCards_le_four
    (P : CutVertexPartition C) {l r : Fin n}
    (hside :
      (P.left.filter fun v => eucDist (C.pts l) (C.pts v) = 1).card +
        (P.right.filter fun v => eucDist (C.pts r) (C.pts v) = 1).card <= 4) :
    (P.crossPairSideNeighborhoodCover l r).card < 6 := by
  rw [P.crossPairSideNeighborhoodCover_card_eq l r]
  omega

theorem outsideNeighborhoodOf_pair_subset_crossPairSideNeighborhoodCover
    (P : CutVertexPartition C) {l r : Fin n}
    (hl : l ∈ P.left) (hr : r ∈ P.right) :
    SmallIndependentNeighborhood.outsideNeighborhoodOf C
        ({l, r} : Finset (Fin n)) <=
      P.crossPairSideNeighborhoodCover l r := by
  intro v hv
  rcases
    (SmallIndependentNeighborhood.mem_outsideNeighborhoodOf
      C ({l, r} : Finset (Fin n)) v).1 hv with
    ⟨_hnotS, hunit⟩
  rcases hunit with ⟨u, hu, hdist⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with hu | hu
  · subst u
    by_cases hvcut : v = P.cut
    · exact Finset.mem_insert.mpr (Or.inl hvcut)
    · rcases P.mem_left_or_mem_right_of_ne_cut hvcut with hvleft | hvright
      · have hvfilter :
          v ∈ P.left.filter (fun w => eucDist (C.pts l) (C.pts w) = 1) :=
            Finset.mem_filter.mpr ⟨hvleft, hdist⟩
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union_left _ hvfilter))
      · exact False.elim (P.no_unit_left_right hl hvright hdist)
  · subst u
    by_cases hvcut : v = P.cut
    · exact Finset.mem_insert.mpr (Or.inl hvcut)
    · rcases P.mem_left_or_mem_right_of_ne_cut hvcut with hvleft | hvright
      · exact False.elim (P.no_unit_right_left hr hvleft hdist)
      · have hvfilter :
          v ∈ P.right.filter (fun w => eucDist (C.pts r) (C.pts w) = 1) :=
            Finset.mem_filter.mpr ⟨hvright, hdist⟩
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union_right _ hvfilter))

theorem outsideNeighborhoodOf_pair_card_le_crossPairSideNeighborhoodCover_card
    (P : CutVertexPartition C) {l r : Fin n}
    (hl : l ∈ P.left) (hr : r ∈ P.right) :
    (SmallIndependentNeighborhood.outsideNeighborhoodOf C
        ({l, r} : Finset (Fin n))).card <=
      (P.crossPairSideNeighborhoodCover l r).card :=
  Finset.card_le_card
    (P.outsideNeighborhoodOf_pair_subset_crossPairSideNeighborhoodCover
      hl hr)

theorem outsideNeighborhoodOf_pair_card_lt_six_of_cover_card_lt_six
    (P : CutVertexPartition C) {l r : Fin n}
    (hl : l ∈ P.left) (hr : r ∈ P.right)
    (hcover : (P.crossPairSideNeighborhoodCover l r).card < 6) :
    (SmallIndependentNeighborhood.outsideNeighborhoodOf C
        ({l, r} : Finset (Fin n))).card < 6 :=
  lt_of_le_of_lt
    (P.outsideNeighborhoodOf_pair_card_le_crossPairSideNeighborhoodCover_card
      hl hr)
    hcover

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

lemma leftWithCutInduced_embed_mem (P : CutVertexPartition C)
    (i : Fin P.leftWithCut.card) :
    P.leftWithCutInduced.embed i ∈ P.leftWithCut := by
  have hmem :
      P.leftWithCutInduced.embed i ∈
        ((Finset.univ : Finset (Fin P.leftWithCut.card)).image
          P.leftWithCutInduced.embed) :=
    Finset.mem_image_of_mem P.leftWithCutInduced.embed (Finset.mem_univ i)
  simpa using hmem

lemma rightWithCutInduced_embed_mem (P : CutVertexPartition C)
    (i : Fin P.rightWithCut.card) :
    P.rightWithCutInduced.embed i ∈ P.rightWithCut := by
  have hmem :
      P.rightWithCutInduced.embed i ∈
        ((Finset.univ : Finset (Fin P.rightWithCut.card)).image
          P.rightWithCutInduced.embed) :=
    Finset.mem_image_of_mem P.rightWithCutInduced.embed (Finset.mem_univ i)
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

lemma leftWithCut_card (P : CutVertexPartition C) :
    P.leftWithCut.card = P.left.card + 1 := by
  simp [leftWithCut, P.left_cut_not_mem]

lemma rightWithCut_card (P : CutVertexPartition C) :
    P.rightWithCut.card = P.right.card + 1 := by
  simp [rightWithCut, P.right_cut_not_mem]

lemma leftWithCut_card_lt (P : CutVertexPartition C) :
    P.leftWithCut.card < n := by
  have hcard := P.card_eq_left_add_right_add_one
  have hleft := P.leftWithCut_card
  have hrightPos : 0 < P.right.card := Finset.card_pos.mpr P.right_nonempty
  omega

lemma rightWithCut_card_lt (P : CutVertexPartition C) :
    P.rightWithCut.card < n := by
  have hcard := P.card_eq_left_add_right_add_one
  have hright := P.rightWithCut_card
  have hleftPos : 0 < P.left.card := Finset.card_pos.mpr P.left_nonempty
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

private lemma image_subset_leftWithCut (P : CutVertexPartition C)
    {s : Finset (Fin P.leftWithCut.card)} :
    s.image P.leftWithCutInduced.embed ⊆ P.leftWithCut := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.leftWithCutInduced_embed_mem i

private lemma image_subset_rightWithCut (P : CutVertexPartition C)
    {s : Finset (Fin P.rightWithCut.card)} :
    s.image P.rightWithCutInduced.embed ⊆ P.rightWithCut := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.rightWithCutInduced_embed_mem i

private def inducedPreimageSet {m : Nat} {kept : Finset (Fin n)}
    (I : Induced (m := m) C kept) (t : Finset (Fin n)) :
    Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter fun i => I.embed i ∈ t

private lemma inducedPreimageSet_image_eq {m : Nat}
    {kept : Finset (Fin n)} (I : Induced (m := m) C kept)
    {t : Finset (Fin n)} (hsubset : t ⊆ kept) :
    (inducedPreimageSet I t).image I.embed = t := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro hv
    rcases (I.mem_kept_iff v).1 (hsubset hv) with ⟨i, hi⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simpa [hi] using hv⟩

private lemma inducedPreimageSet_card_eq {m : Nat}
    {kept : Finset (Fin n)} (I : Induced (m := m) C kept)
    {t : Finset (Fin n)} (hsubset : t ⊆ kept) :
    (inducedPreimageSet I t).card = t.card := by
  have hcard :=
    Finset.card_image_of_injective (inducedPreimageSet I t) I.embed_injective
  rw [inducedPreimageSet_image_eq I hsubset] at hcard
  exact hcard.symm

private lemma inducedPreimageSet_indep {m : Nat}
    {kept : Finset (Fin n)} (I : Induced (m := m) C kept)
    {t : Finset (Fin n)} (ht : C.IsIndep t)
    (hsubset : t ⊆ kept) :
    I.config.IsIndep (inducedPreimageSet I t) := by
  refine I.preimage_indep_of_image_indep ?_
  simpa [inducedPreimageSet_image_eq I hsubset] using ht

def leftSetInLeftWithCut (P : CutVertexPartition C)
    (s : Finset (Fin P.left.card)) : Finset (Fin P.leftWithCut.card) :=
  inducedPreimageSet P.leftWithCutInduced (s.image P.leftInduced.embed)

def rightSetInRightWithCut (P : CutVertexPartition C)
    (s : Finset (Fin P.right.card)) : Finset (Fin P.rightWithCut.card) :=
  inducedPreimageSet P.rightWithCutInduced (s.image P.rightInduced.embed)

lemma leftSetInLeftWithCut_image (P : CutVertexPartition C)
    (s : Finset (Fin P.left.card)) :
    (P.leftSetInLeftWithCut s).image P.leftWithCutInduced.embed =
      s.image P.leftInduced.embed := by
  apply inducedPreimageSet_image_eq
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact Finset.mem_insert.mpr (Or.inr (P.leftInduced_embed_mem i))

lemma rightSetInRightWithCut_image (P : CutVertexPartition C)
    (s : Finset (Fin P.right.card)) :
    (P.rightSetInRightWithCut s).image P.rightWithCutInduced.embed =
      s.image P.rightInduced.embed := by
  apply inducedPreimageSet_image_eq
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact Finset.mem_insert.mpr (Or.inr (P.rightInduced_embed_mem i))

lemma leftSetInLeftWithCut_card (P : CutVertexPartition C)
    (s : Finset (Fin P.left.card)) :
    (P.leftSetInLeftWithCut s).card = s.card := by
  have hcard :=
    inducedPreimageSet_card_eq P.leftWithCutInduced
      (t := s.image P.leftInduced.embed) ?_
  · simpa [leftSetInLeftWithCut,
      Finset.card_image_of_injective _ P.leftInduced.embed_injective] using hcard
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact Finset.mem_insert.mpr (Or.inr (P.leftInduced_embed_mem i))

lemma rightSetInRightWithCut_card (P : CutVertexPartition C)
    (s : Finset (Fin P.right.card)) :
    (P.rightSetInRightWithCut s).card = s.card := by
  have hcard :=
    inducedPreimageSet_card_eq P.rightWithCutInduced
      (t := s.image P.rightInduced.embed) ?_
  · simpa [rightSetInRightWithCut,
      Finset.card_image_of_injective _ P.rightInduced.embed_injective] using hcard
  · intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact Finset.mem_insert.mpr (Or.inr (P.rightInduced_embed_mem i))

lemma leftSetInLeftWithCut_indep (P : CutVertexPartition C)
    {s : Finset (Fin P.left.card)}
    (hs : P.leftInduced.config.IsIndep s) :
    P.leftWithCutInduced.config.IsIndep (P.leftSetInLeftWithCut s) := by
  refine inducedPreimageSet_indep P.leftWithCutInduced
    (P.leftInduced.image_indep hs) ?_
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact Finset.mem_insert.mpr (Or.inr (P.leftInduced_embed_mem i))

lemma rightSetInRightWithCut_indep (P : CutVertexPartition C)
    {s : Finset (Fin P.right.card)}
    (hs : P.rightInduced.config.IsIndep s) :
    P.rightWithCutInduced.config.IsIndep (P.rightSetInRightWithCut s) := by
  refine inducedPreimageSet_indep P.rightWithCutInduced
    (P.rightInduced.image_indep hs) ?_
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact Finset.mem_insert.mpr (Or.inr (P.rightInduced_embed_mem i))

lemma leftSetInLeftWithCut_avoids_cut (P : CutVertexPartition C)
    (s : Finset (Fin P.left.card)) :
    P.cut ∉ (P.leftSetInLeftWithCut s).image P.leftWithCutInduced.embed := by
  rw [P.leftSetInLeftWithCut_image s]
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
  exact P.left_cut_not_mem (by simpa [hi] using P.leftInduced_embed_mem i)

lemma rightSetInRightWithCut_avoids_cut (P : CutVertexPartition C)
    (s : Finset (Fin P.right.card)) :
    P.cut ∉ (P.rightSetInRightWithCut s).image P.rightWithCutInduced.embed := by
  rw [P.rightSetInRightWithCut_image s]
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
  exact P.right_cut_not_mem (by simpa [hi] using P.rightInduced_embed_mem i)

/-! ## Direct Lemma 3 gluing cases -/

/-- Paper Lemma 3 direct gluing, left-plus-cut case.

If a cleared witness on `left ∪ {cut}` avoids the cut vertex, then it glues
with any cleared witness on the right side and clears the ambient
configuration.  This is a genuine cut-partition contradiction branch and does
not use pointwise side-card exactness for the original left/right sides. -/
theorem hasCleared_of_leftWithCut_avoids_cut_and_right
    (P : CutVertexPartition C)
    {sLeft : Finset (Fin P.leftWithCut.card)}
    {sRight : Finset (Fin P.right.card)}
    (hsLeftIndep : P.leftWithCutInduced.config.IsIndep sLeft)
    (hsLeftBound :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.leftWithCut.card sLeft.card)
    (hcutAvoid : P.cut ∉ sLeft.image P.leftWithCutInduced.embed)
    (hsRightIndep : P.rightInduced.config.IsIndep sRight)
    (hsRightBound :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.right.card sRight.card) :
    HasClearedEightThirtyOneIndependentSet C := by
  let leftImage : Finset (Fin n) := sLeft.image P.leftWithCutInduced.embed
  let rightImage : Finset (Fin n) := sRight.image P.rightInduced.embed
  have hleftSubset : leftImage ⊆ P.leftWithCut := by
    simpa [leftImage] using
      (image_subset_leftWithCut P (s := sLeft))
  have hrightSubset : rightImage ⊆ P.right := by
    simpa [rightImage] using
      (image_subset_right P (s := sRight))
  have hleftImageIndep : C.IsIndep leftImage :=
    P.leftWithCutInduced.image_indep hsLeftIndep
  have hrightImageIndep : C.IsIndep rightImage :=
    P.rightInduced.image_indep hsRightIndep
  have hcross :
      forall x : Fin n, x ∈ leftImage ->
        forall y : Fin n, y ∈ rightImage -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1 := by
    intro x hx y hy _hxy hunit
    have hxSide : x ∈ P.leftWithCut := hleftSubset hx
    have hyRight : y ∈ P.right := hrightSubset hy
    have hxLeft : x ∈ P.left := by
      rcases Finset.mem_insert.mp (by simpa [leftWithCut] using hxSide) with
        hcut | hleft
      · exact False.elim (hcutAvoid (by simpa [leftImage, hcut] using hx))
      · exact hleft
    exact P.no_unit_left_right hxLeft hyRight hunit
  let combined : Finset (Fin n) := leftImage ∪ rightImage
  have hcombinedIndep : C.IsIndep combined :=
    MinimalCounterexample.union_indep_of_cross_nonunit
      hleftImageIndep hrightImageIndep hcross
  have himagesDisjoint : Disjoint leftImage rightImage := by
    rw [Finset.disjoint_left]
    intro x hxLeftImage hxRightImage
    have hxSide : x ∈ P.leftWithCut := hleftSubset hxLeftImage
    have hxRight : x ∈ P.right := hrightSubset hxRightImage
    rcases Finset.mem_insert.mp (by simpa [leftWithCut] using hxSide) with
      hcut | hxLeft
    · subst x
      exact P.right_cut_not_mem hxRight
    · exact (Finset.disjoint_left.mp P.disjoint) hxLeft hxRight
  have hcombinedCard :
      combined.card = sLeft.card + sRight.card := by
    have hcard := Finset.card_union_of_disjoint himagesDisjoint
    simpa [combined, leftImage, rightImage,
      Finset.card_image_of_injective _ P.leftWithCutInduced.embed_injective,
      Finset.card_image_of_injective _ P.rightInduced.embed_injective] using hcard
  have hbound :
      MinimalCounterexample.ClearedEightThirtyOneBound n
        (sLeft.card + sRight.card) := by
    unfold MinimalCounterexample.ClearedEightThirtyOneBound at *
    have hcard := P.card_eq_left_add_right_add_one
    have hleftCard := P.leftWithCut_card
    omega
  exact ⟨combined, hcombinedIndep, by simpa [hcombinedCard] using hbound⟩

/-- Symmetric direct gluing branch for a cleared witness on
`right ∪ {cut}` that avoids the cut vertex. -/
theorem hasCleared_of_left_and_rightWithCut_avoids_cut
    (P : CutVertexPartition C)
    {sLeft : Finset (Fin P.left.card)}
    {sRight : Finset (Fin P.rightWithCut.card)}
    (hsLeftIndep : P.leftInduced.config.IsIndep sLeft)
    (hsLeftBound :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.left.card sLeft.card)
    (hsRightIndep : P.rightWithCutInduced.config.IsIndep sRight)
    (hsRightBound :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.rightWithCut.card sRight.card)
    (hcutAvoid : P.cut ∉ sRight.image P.rightWithCutInduced.embed) :
    HasClearedEightThirtyOneIndependentSet C := by
  let leftImage : Finset (Fin n) := sLeft.image P.leftInduced.embed
  let rightImage : Finset (Fin n) := sRight.image P.rightWithCutInduced.embed
  have hleftSubset : leftImage ⊆ P.left := by
    simpa [leftImage] using
      (image_subset_left P (s := sLeft))
  have hrightSubset : rightImage ⊆ P.rightWithCut := by
    simpa [rightImage] using
      (image_subset_rightWithCut P (s := sRight))
  have hleftImageIndep : C.IsIndep leftImage :=
    P.leftInduced.image_indep hsLeftIndep
  have hrightImageIndep : C.IsIndep rightImage :=
    P.rightWithCutInduced.image_indep hsRightIndep
  have hcross :
      forall x : Fin n, x ∈ leftImage ->
        forall y : Fin n, y ∈ rightImage -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1 := by
    intro x hx y hy _hxy hunit
    have hxLeft : x ∈ P.left := hleftSubset hx
    have hySide : y ∈ P.rightWithCut := hrightSubset hy
    have hyRight : y ∈ P.right := by
      rcases Finset.mem_insert.mp (by simpa [rightWithCut] using hySide) with
        hcut | hright
      · exact False.elim (hcutAvoid (by simpa [rightImage, hcut] using hy))
      · exact hright
    exact P.no_unit_left_right hxLeft hyRight hunit
  let combined : Finset (Fin n) := leftImage ∪ rightImage
  have hcombinedIndep : C.IsIndep combined :=
    MinimalCounterexample.union_indep_of_cross_nonunit
      hleftImageIndep hrightImageIndep hcross
  have himagesDisjoint : Disjoint leftImage rightImage := by
    rw [Finset.disjoint_left]
    intro x hxLeftImage hxRightImage
    have hxLeft : x ∈ P.left := hleftSubset hxLeftImage
    have hxSide : x ∈ P.rightWithCut := hrightSubset hxRightImage
    rcases Finset.mem_insert.mp (by simpa [rightWithCut] using hxSide) with
      hcut | hxRight
    · subst x
      exact P.left_cut_not_mem hxLeft
    · exact (Finset.disjoint_left.mp P.disjoint) hxLeft hxRight
  have hcombinedCard :
      combined.card = sLeft.card + sRight.card := by
    have hcard := Finset.card_union_of_disjoint himagesDisjoint
    simpa [combined, leftImage, rightImage,
      Finset.card_image_of_injective _ P.leftInduced.embed_injective,
      Finset.card_image_of_injective _ P.rightWithCutInduced.embed_injective] using hcard
  have hbound :
      MinimalCounterexample.ClearedEightThirtyOneBound n
        (sLeft.card + sRight.card) := by
    unfold MinimalCounterexample.ClearedEightThirtyOneBound at *
    have hcard := P.card_eq_left_add_right_add_one
    have hrightCard := P.rightWithCut_card
    omega
  exact ⟨combined, hcombinedIndep, by simpa [hcombinedCard] using hbound⟩

/-- If cleared witnesses on both plus-sides contain the cut vertex, their
ambient images glue across the cut counted once.  The caller supplies the
corresponding one-cut cardinal bound. -/
theorem hasCleared_of_leftWithCut_and_rightWithCut_contain_cut
    (P : CutVertexPartition C)
    {sLeft : Finset (Fin P.leftWithCut.card)}
    {sRight : Finset (Fin P.rightWithCut.card)}
    (hsLeftIndep : P.leftWithCutInduced.config.IsIndep sLeft)
    (hcutLeft : P.cut ∈ sLeft.image P.leftWithCutInduced.embed)
    (hsRightIndep : P.rightWithCutInduced.config.IsIndep sRight)
    (hcutRight : P.cut ∈ sRight.image P.rightWithCutInduced.embed)
    (hbound :
      MinimalCounterexample.ClearedEightThirtyOneBound n
        (sLeft.card + sRight.card - 1)) :
    HasClearedEightThirtyOneIndependentSet C := by
  let leftImage : Finset (Fin n) := sLeft.image P.leftWithCutInduced.embed
  let rightImage : Finset (Fin n) := sRight.image P.rightWithCutInduced.embed
  have hleftSubset : leftImage ⊆ P.leftWithCut := by
    simpa [leftImage] using
      (image_subset_leftWithCut P (s := sLeft))
  have hrightSubset : rightImage ⊆ P.rightWithCut := by
    simpa [rightImage] using
      (image_subset_rightWithCut P (s := sRight))
  have hleftImageIndep : C.IsIndep leftImage :=
    P.leftWithCutInduced.image_indep hsLeftIndep
  have hrightImageIndep : C.IsIndep rightImage :=
    P.rightWithCutInduced.image_indep hsRightIndep
  have hcross :
      forall x : Fin n, x ∈ leftImage ->
        forall y : Fin n, y ∈ rightImage -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1 := by
    intro x hx y hy hxy hunit
    by_cases hxc : x = P.cut
    · subst x
      exact hrightImageIndep P.cut (by simpa [rightImage] using hcutRight)
        y hy hxy hunit
    · by_cases hyc : y = P.cut
      · subst y
        exact hleftImageIndep x hx P.cut
          (by simpa [leftImage] using hcutLeft) hxc hunit
      · have hxSide : x ∈ P.leftWithCut := hleftSubset hx
        have hySide : y ∈ P.rightWithCut := hrightSubset hy
        have hxLeft : x ∈ P.left := by
          rcases Finset.mem_insert.mp (by simpa [leftWithCut] using hxSide) with
            hcut | hleft
          · exact False.elim (hxc hcut)
          · exact hleft
        have hyRight : y ∈ P.right := by
          rcases Finset.mem_insert.mp (by simpa [rightWithCut] using hySide) with
            hcut | hright
          · exact False.elim (hyc hcut)
          · exact hright
        exact P.no_unit_left_right hxLeft hyRight hunit
  let combined : Finset (Fin n) := leftImage ∪ rightImage
  have hcombinedIndep : C.IsIndep combined :=
    MinimalCounterexample.union_indep_of_cross_nonunit
      hleftImageIndep hrightImageIndep hcross
  have hinter : leftImage ∩ rightImage = ({P.cut} : Finset (Fin n)) := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxLeftImage, hxRightImage⟩
      have hxSide : x ∈ P.leftWithCut := hleftSubset hxLeftImage
      have hxRightSide : x ∈ P.rightWithCut := hrightSubset hxRightImage
      rcases Finset.mem_insert.mp (by simpa [leftWithCut] using hxSide) with
        hcut | hxLeft
      · exact Finset.mem_singleton.mpr hcut
      · rcases Finset.mem_insert.mp
          (by simpa [rightWithCut] using hxRightSide) with hcut | hxRight
        · exact Finset.mem_singleton.mpr hcut
        · exact False.elim
            ((Finset.disjoint_left.mp P.disjoint) hxLeft hxRight)
    · intro hx
      have hxc : x = P.cut := by simpa using hx
      subst x
      exact Finset.mem_inter.mpr
        ⟨by simpa [leftImage] using hcutLeft,
          by simpa [rightImage] using hcutRight⟩
  have hcombinedCard :
      combined.card = sLeft.card + sRight.card - 1 := by
    have hcard := Finset.card_union_add_card_inter leftImage rightImage
    have hleftCard :
        leftImage.card = sLeft.card := by
      simpa [leftImage] using
        (Finset.card_image_of_injective sLeft
          P.leftWithCutInduced.embed_injective)
    have hrightCard :
        rightImage.card = sRight.card := by
      simpa [rightImage] using
        (Finset.card_image_of_injective sRight
          P.rightWithCutInduced.embed_injective)
    have hinterCard : (leftImage ∩ rightImage).card = 1 := by
      simp [hinter]
    have hsum : combined.card + 1 = sLeft.card + sRight.card := by
      simpa [combined, hleftCard, hrightCard, hinterCard] using hcard
    omega
  exact ⟨combined, hcombinedIndep, by simpa [hcombinedCard] using hbound⟩

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
