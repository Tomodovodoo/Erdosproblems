import ErdosProblems1066.Swanepoel.CutVertexPayForCutArithmetic

set_option autoImplicit false

/-!
# Cut-vertex side cardinality from minimality

Minimality supplies cleared witnesses on the two proper sides of a supplied
cut-vertex partition.  The existing deletion/minimality API does not determine
that the particular witnesses chosen by `sideSurplusData_of_minimalFailure`
have enough combined cardinality to pay for the deleted cut vertex.

This file therefore isolates that remaining graph/cardinality input in its
most direct form and routes it through the existing pay-for-cut arithmetic.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexSlackFromDeletion

open CounterexamplePipeline
open CutVertexInterface

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

namespace CutVertexSideSurplusData

variable {P : CutVertexPartition C}

/-! ## Ambient images of the two side witnesses -/

/-- The left side witness, embedded back into the ambient configuration. -/
def leftImage (D : CutVertexSideSurplusData P) : Finset (Fin n) :=
  D.leftSet.carrier.image P.leftInduced.embed

/-- The right side witness, embedded back into the ambient configuration. -/
def rightImage (D : CutVertexSideSurplusData P) : Finset (Fin n) :=
  D.rightSet.carrier.image P.rightInduced.embed

/-- The ambient independent-set candidate obtained by gluing the two side
witnesses without reinserting the cut vertex. -/
def combinedImage (D : CutVertexSideSurplusData P) : Finset (Fin n) :=
  D.leftImage ∪ D.rightImage

theorem leftImage_subset_left (D : CutVertexSideSurplusData P) :
    D.leftImage ⊆ P.left := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.leftInduced_embed_mem i

theorem rightImage_subset_right (D : CutVertexSideSurplusData P) :
    D.rightImage ⊆ P.right := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
  exact P.rightInduced_embed_mem i

/-- The two ambient side images are disjoint because the cut partition sides
are disjoint. -/
theorem sideImages_disjoint (D : CutVertexSideSurplusData P) :
    Disjoint D.leftImage D.rightImage := by
  rw [Finset.disjoint_left]
  intro v hvLeft hvRight
  exact (Finset.disjoint_left.mp P.disjoint)
    (D.leftImage_subset_left hvLeft) (D.rightImage_subset_right hvRight)

/-- The combined ambient side image has exactly the sum of the two side
carrier cardinalities. -/
theorem combinedImage_card (D : CutVertexSideSurplusData P) :
    D.combinedImage.card =
      D.leftSet.carrier.card + D.rightSet.carrier.card := by
  have hcard := Finset.card_union_of_disjoint D.sideImages_disjoint
  simpa [combinedImage, leftImage, rightImage,
    Finset.card_image_of_injective _ P.leftInduced.embed_injective,
    Finset.card_image_of_injective _ P.rightInduced.embed_injective] using hcard

theorem leftImage_indep (D : CutVertexSideSurplusData P) :
    C.IsIndep D.leftImage :=
  P.leftInduced.image_indep D.leftSet.indep

theorem rightImage_indep (D : CutVertexSideSurplusData P) :
    C.IsIndep D.rightImage :=
  P.rightInduced.image_indep D.rightSet.indep

theorem sideImages_cross_nonunit (D : CutVertexSideSurplusData P) :
    forall x : Fin n, x ∈ D.leftImage ->
      forall y : Fin n, y ∈ D.rightImage -> x ≠ y ->
        eucDist (C.pts x) (C.pts y) ≠ 1 := by
  intro x hx y hy _hxy
  exact P.no_unit_left_right
    (D.leftImage_subset_left hx) (D.rightImage_subset_right hy)

/-- The disjoint union of the two side witnesses is independent in the
ambient configuration. -/
theorem combinedImage_indep (D : CutVertexSideSurplusData P) :
    C.IsIndep D.combinedImage := by
  unfold combinedImage
  exact MinimalCounterexample.union_indep_of_cross_nonunit
    D.leftImage_indep D.rightImage_indep D.sideImages_cross_nonunit

/-- If the glued ambient side image satisfies the cleared cardinal bound, it
is an ambient cleared independent set. -/
theorem hasCleared_of_combinedImage_cardBound
    (D : CutVertexSideSurplusData P)
    (hbound : 8 * n <= 31 * D.combinedImage.card) :
    HasClearedEightThirtyOneIndependentSet C := by
  refine ⟨D.combinedImage, D.combinedImage_indep, ?_⟩
  simpa [MinimalCounterexample.ClearedEightThirtyOneBound] using hbound

/-- The existing ambient side-cardinality wrapper is exactly the cardinal
bound for the glued ambient side image. -/
theorem hasCleared_of_ambientCardBound
    (D : CutVertexSideSurplusData P)
    (hbound : D.AmbientCardBound) :
    HasClearedEightThirtyOneIndependentSet C := by
  apply D.hasCleared_of_combinedImage_cardBound
  rw [D.combinedImage_card]
  simpa [AmbientCardBound] using hbound

/-- Sum-of-side-cardinalities form of the previous gluing implication. -/
theorem hasCleared_of_sideCardSumBound
    (D : CutVertexSideSurplusData P)
    (hbound :
      8 * n <= 31 *
        (D.leftSet.carrier.card + D.rightSet.carrier.card)) :
    HasClearedEightThirtyOneIndependentSet C :=
  D.hasCleared_of_ambientCardBound (by
    simpa [AmbientCardBound] using hbound)

/-- With exact side surplus equations, paying the cut vertex is equivalent to
the ambient cardinal bound for the glued side witnesses.  This is the converse
of the arithmetic direction in `CutVertexPayForCutArithmetic`. -/
theorem ambientCardBound_of_exactSideSurpluses_of_paysCut
    (D : CutVertexSideSurplusData P)
    (hexact : D.ExactSideSurpluses)
    (hpay : D.PaysCut) :
    D.AmbientCardBound := by
  rcases D.side_slack_eqs_of_exactSideSurpluses hexact with
    ⟨hleft, hright⟩
  have hcard := P.card_eq_left_add_right_add_one
  unfold AmbientCardBound
  unfold PaysCut at hpay
  omega

/-- Exact side surpluses identify the paper cardinality input with the
pay-for-cut arithmetic field. -/
theorem ambientCardBound_iff_paysCut_of_exactSideSurpluses
    (D : CutVertexSideSurplusData P)
    (hexact : D.ExactSideSurpluses) :
    D.AmbientCardBound <-> D.PaysCut := by
  constructor
  · exact D.paysCut_of_exactSideSurpluses_of_ambientCardBound hexact
  · exact D.ambientCardBound_of_exactSideSurpluses_of_paysCut hexact

/-- Exact side surpluses plus pay-for-cut glue the two side witnesses into an
ambient cleared independent set. -/
theorem hasCleared_of_exactSideSurpluses_of_paysCut
    (D : CutVertexSideSurplusData P)
    (hexact : D.ExactSideSurpluses)
    (hpay : D.PaysCut) :
    HasClearedEightThirtyOneIndependentSet C :=
  D.hasCleared_of_ambientCardBound
    (D.ambientCardBound_of_exactSideSurpluses_of_paysCut hexact hpay)

end CutVertexSideSurplusData

/-- The exact cardinal fact still needed for the concrete side witnesses
chosen from minimality: for every cut-vertex partition, their combined size
already satisfies the ambient `8 / 31` bound. -/
def CutVertexDeletionSideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    8 * n <=
      31 *
        ((sideSurplusData_of_minimalFailure hmin P).leftSet.carrier.card +
          (sideSurplusData_of_minimalFailure hmin P).rightSet.carrier.card)

/-- The same exact cardinal fact, expressed as the cardinal bound for the
actual glued ambient side image. -/
def CutVertexDeletionCombinedImageBoundFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    8 * n <=
      31 * (sideSurplusData_of_minimalFailure hmin P).combinedImage.card

/-- The side-cardinality exact fact gives the bound for the glued ambient
side image. -/
theorem combinedImageBoundFact_of_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : CutVertexDeletionSideCardExactFact hmin) :
    CutVertexDeletionCombinedImageBoundFact hmin := by
  intro P
  rw [(sideSurplusData_of_minimalFailure hmin P).combinedImage_card]
  exact hcard P

/-- The glued ambient side-image cardinal bound gives the wrapper-free
side-cardinality exact fact. -/
theorem sideCardExactFact_of_combinedImageBoundFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : CutVertexDeletionCombinedImageBoundFact hmin) :
    CutVertexDeletionSideCardExactFact hmin := by
  intro P
  have hbound := hcard P
  rw [(sideSurplusData_of_minimalFailure hmin P).combinedImage_card] at hbound
  exact hbound

/-- The wrapper-free side-cardinality exact fact is equivalent to the bound on
the actual glued ambient side image. -/
theorem sideCardExactFact_iff_combinedImageBoundFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <->
      CutVertexDeletionCombinedImageBoundFact hmin := by
  constructor
  case mp =>
    exact combinedImageBoundFact_of_sideCardExactFact hmin
  case mpr =>
    exact sideCardExactFact_of_combinedImageBoundFact hmin

/-- The exact cardinal statement is precisely the paper-level side-cardinality
fact expressed without the `AmbientCardBound` wrapper. -/
theorem sideCardPaperFact_of_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : CutVertexDeletionSideCardExactFact hmin) :
    CutVertexDeletionSideCardPaperFact hmin := by
  intro P
  simpa [CutVertexDeletionSideCardExactFact,
    CutVertexSideSurplusData.AmbientCardBound]
    using hcard P

/-- The wrapper-free exact cardinal statement follows back from the existing
paper-level side-cardinality fact. -/
theorem sideCardExactFact_of_sideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hpaper : CutVertexDeletionSideCardPaperFact hmin) :
    CutVertexDeletionSideCardExactFact hmin := by
  intro P
  simpa [CutVertexDeletionSideCardExactFact,
    CutVertexSideSurplusData.AmbientCardBound]
    using hpaper P

/-- The isolated exact cardinal fact is equivalent to the existing paper-level
side-cardinality interface. -/
theorem sideCardExactFact_iff_sideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <->
      CutVertexDeletionSideCardPaperFact hmin := by
  constructor
  case mp =>
    exact sideCardPaperFact_of_sideCardExactFact hmin
  case mpr =>
    exact sideCardExactFact_of_sideCardPaperFact hmin

/-- For the side witnesses constructed from minimality, the exact cardinal
input is equivalent to the missing pay-for-cut arithmetic. -/
theorem sideCardExactFact_iff_missingArithmetic
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <->
      CutVertexDeletionMissingArithmetic hmin := by
  constructor
  · intro hcard P
    exact
      (sideSurplusData_of_minimalFailure hmin P).paysCut_of_exactSideSurpluses_of_ambientCardBound
        (sideSurplusData_of_minimalFailure_exactSideSurpluses hmin P)
        (by
          simpa [CutVertexDeletionSideCardExactFact,
            CutVertexSideSurplusData.AmbientCardBound] using hcard P)
  · intro harith P
    exact
      (sideSurplusData_of_minimalFailure hmin P).ambientCardBound_of_exactSideSurpluses_of_paysCut
        (sideSurplusData_of_minimalFailure_exactSideSurpluses hmin P)
        (harith P)

/-- The exact per-partition cardinal fact supplies the remaining deletion
slack fact used by the cut-vertex closure route. -/
theorem deletionSlackFact_of_minimalFailure_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : CutVertexDeletionSideCardExactFact hmin) :
    CutVertexDeletionSlackFact C :=
  deletionSlackFact_of_minimalFailure_sideCardPaperFact hmin
    (sideCardPaperFact_of_sideCardExactFact hmin hcard)

/-- Uniform no-cut over minimal cleared failures. -/
abbrev MinimalFailureNoCutVertexFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    MinimalGraphFacts.IsMinimalClearedFailure C -> NoCutVertex C

/-! ## Direct plus-side cut-partition gluing cases -/

/-- Minimality clears the left side with the cut vertex reinserted: the right
side is nonempty, so this induced subconfiguration is still proper. -/
theorem leftWithCut_hasCleared_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    HasClearedEightThirtyOneIndependentSet
      P.leftWithCutInduced.config :=
  MinimalGraphFacts.smaller_hasCleared_of_minimalClearedFailure
    hmin P.leftWithCutInduced.config P.leftWithCut_card_lt

/-- Minimality clears the right side with the cut vertex reinserted. -/
theorem rightWithCut_hasCleared_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    HasClearedEightThirtyOneIndependentSet
      P.rightWithCutInduced.config :=
  MinimalGraphFacts.smaller_hasCleared_of_minimalClearedFailure
    hmin P.rightWithCutInduced.config P.rightWithCut_card_lt

/-- The minimality-selected cleared witness on `left ∪ {cut}`. -/
def leftWithCutMinimalitySet
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Finset (Fin P.leftWithCut.card) :=
  Classical.choose (leftWithCut_hasCleared_of_minimalFailure hmin P)

/-- The minimality-selected cleared witness on `right ∪ {cut}`. -/
def rightWithCutMinimalitySet
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Finset (Fin P.rightWithCut.card) :=
  Classical.choose (rightWithCut_hasCleared_of_minimalFailure hmin P)

/-- The minimality-selected cleared witness on the left side without the cut. -/
def leftSideMinimalitySet
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Finset (Fin P.left.card) :=
  Classical.choose (leftSide_hasCleared_of_minimalFailure hmin P)

/-- The minimality-selected cleared witness on the right side without the cut. -/
def rightSideMinimalitySet
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Finset (Fin P.right.card) :=
  Classical.choose (rightSide_hasCleared_of_minimalFailure hmin P)

theorem leftWithCutMinimalitySet_indep
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    P.leftWithCutInduced.config.IsIndep
      (leftWithCutMinimalitySet hmin P) :=
  (Classical.choose_spec
    (leftWithCut_hasCleared_of_minimalFailure hmin P)).1

theorem leftWithCutMinimalitySet_bound
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    MinimalCounterexample.ClearedEightThirtyOneBound
      P.leftWithCut.card (leftWithCutMinimalitySet hmin P).card :=
  (Classical.choose_spec
    (leftWithCut_hasCleared_of_minimalFailure hmin P)).2

theorem rightWithCutMinimalitySet_indep
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    P.rightWithCutInduced.config.IsIndep
      (rightWithCutMinimalitySet hmin P) :=
  (Classical.choose_spec
    (rightWithCut_hasCleared_of_minimalFailure hmin P)).1

theorem rightWithCutMinimalitySet_bound
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    MinimalCounterexample.ClearedEightThirtyOneBound
      P.rightWithCut.card (rightWithCutMinimalitySet hmin P).card :=
  (Classical.choose_spec
    (rightWithCut_hasCleared_of_minimalFailure hmin P)).2

theorem leftSideMinimalitySet_indep
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    P.leftInduced.config.IsIndep (leftSideMinimalitySet hmin P) :=
  (Classical.choose_spec
    (leftSide_hasCleared_of_minimalFailure hmin P)).1

theorem leftSideMinimalitySet_bound
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    MinimalCounterexample.ClearedEightThirtyOneBound
      P.left.card (leftSideMinimalitySet hmin P).card :=
  (Classical.choose_spec
    (leftSide_hasCleared_of_minimalFailure hmin P)).2

theorem rightSideMinimalitySet_indep
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    P.rightInduced.config.IsIndep (rightSideMinimalitySet hmin P) :=
  (Classical.choose_spec
    (rightSide_hasCleared_of_minimalFailure hmin P)).1

theorem rightSideMinimalitySet_bound
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    MinimalCounterexample.ClearedEightThirtyOneBound
      P.right.card (rightSideMinimalitySet hmin P).card :=
  (Classical.choose_spec
    (rightSide_hasCleared_of_minimalFailure hmin P)).2

/-- Direct cut-partition contradiction for the first paper Lemma 3 case:
the selected cleared witness on `left ∪ {cut}` avoids the cut vertex, so it
glues with the selected right-side witness. -/
theorem false_of_minimalFailure_leftWithCutMinimalitySet_avoids_cut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (havoid :
      P.cut ∉
        (leftWithCutMinimalitySet hmin P).image
          P.leftWithCutInduced.embed) :
    False :=
  MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    (P.hasCleared_of_leftWithCut_avoids_cut_and_right
      (leftWithCutMinimalitySet_indep hmin P)
      (leftWithCutMinimalitySet_bound hmin P)
      havoid
      (rightSideMinimalitySet_indep hmin P)
      (rightSideMinimalitySet_bound hmin P))

/-- Symmetric direct cut-partition contradiction when the selected cleared
witness on `right ∪ {cut}` avoids the cut vertex. -/
theorem false_of_minimalFailure_rightWithCutMinimalitySet_avoids_cut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (havoid :
      P.cut ∉
        (rightWithCutMinimalitySet hmin P).image
          P.rightWithCutInduced.embed) :
    False :=
  MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    (P.hasCleared_of_left_and_rightWithCut_avoids_cut
      (leftSideMinimalitySet_indep hmin P)
      (leftSideMinimalitySet_bound hmin P)
      (rightWithCutMinimalitySet_indep hmin P)
      (rightWithCutMinimalitySet_bound hmin P)
      havoid)

/-- Explicit left-plus-side cleared witness that avoids the cut vertex. -/
abbrev LeftWithCutAvoidsCutClearedData
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  Exists fun sLeft : Finset (Fin P.leftWithCut.card) =>
    P.leftWithCutInduced.config.IsIndep sLeft /\
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.leftWithCut.card sLeft.card /\
      P.cut ∉ sLeft.image P.leftWithCutInduced.embed

/-- Explicit right-plus-side cleared witness that avoids the cut vertex. -/
abbrev RightWithCutAvoidsCutClearedData
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  Exists fun sRight : Finset (Fin P.rightWithCut.card) =>
    P.rightWithCutInduced.config.IsIndep sRight /\
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.rightWithCut.card sRight.card /\
      P.cut ∉ sRight.image P.rightWithCutInduced.embed

abbrev CutPartitionPlusSideAvoidsCutData
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  LeftWithCutAvoidsCutClearedData hmin P \/
    RightWithCutAvoidsCutClearedData hmin P

/-- The left plus-side is cut-forced at the cleared threshold: every cleared
witness on `left ∪ {cut}` contains the cut vertex. -/
abbrev LeftWithCutCutForcedClearedData
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  forall sLeft : Finset (Fin P.leftWithCut.card),
    P.leftWithCutInduced.config.IsIndep sLeft ->
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.leftWithCut.card sLeft.card ->
        P.cut ∈ sLeft.image P.leftWithCutInduced.embed

/-- The right plus-side is cut-forced at the cleared threshold. -/
abbrev RightWithCutCutForcedClearedData
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  forall sRight : Finset (Fin P.rightWithCut.card),
    P.rightWithCutInduced.config.IsIndep sRight ->
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.rightWithCut.card sRight.card ->
        P.cut ∈ sRight.image P.rightWithCutInduced.embed

/-- The exact local obstruction to the plus-side avoidance source: both
plus-sides force every cleared witness to use the cut vertex. -/
abbrev CutPartitionBothPlusSidesCutForcedData
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  LeftWithCutCutForcedClearedData hmin P /\
    RightWithCutCutForcedClearedData hmin P

theorem leftWithCutCutForcedClearedData_iff_not_avoidsCutClearedData
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    LeftWithCutCutForcedClearedData hmin P <->
      Not (LeftWithCutAvoidsCutClearedData hmin P) := by
  classical
  constructor
  · intro hforced havoidData
    rcases havoidData with ⟨sLeft, hsLeftIndep, hsLeftBound, havoid⟩
    exact havoid (hforced sLeft hsLeftIndep hsLeftBound)
  · intro hnot sLeft hsLeftIndep hsLeftBound
    by_contra havoid
    exact hnot ⟨sLeft, hsLeftIndep, hsLeftBound, havoid⟩

theorem rightWithCutCutForcedClearedData_iff_not_avoidsCutClearedData
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    RightWithCutCutForcedClearedData hmin P <->
      Not (RightWithCutAvoidsCutClearedData hmin P) := by
  classical
  constructor
  · intro hforced havoidData
    rcases havoidData with ⟨sRight, hsRightIndep, hsRightBound, havoid⟩
    exact havoid (hforced sRight hsRightIndep hsRightBound)
  · intro hnot sRight hsRightIndep hsRightBound
    by_contra havoid
    exact hnot ⟨sRight, hsRightIndep, hsRightBound, havoid⟩

/-- Pointwise sharp form of the corrected Lemma 3 branch: proving plus-side
avoidance is exactly ruling out simultaneous cut-forcing on the two plus
sides. -/
theorem cutPartitionPlusSideAvoidsCutData_iff_not_bothPlusSidesCutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    CutPartitionPlusSideAvoidsCutData hmin P <->
      Not (CutPartitionBothPlusSidesCutForcedData hmin P) := by
  classical
  constructor
  · intro hplus hforced
    cases hplus with
    | inl hleft =>
        exact
          (leftWithCutCutForcedClearedData_iff_not_avoidsCutClearedData
            hmin P).1 hforced.1 hleft
    | inr hright =>
        exact
          (rightWithCutCutForcedClearedData_iff_not_avoidsCutClearedData
            hmin P).1 hforced.2 hright
  · intro hnotForced
    by_cases hleft : LeftWithCutAvoidsCutClearedData hmin P
    · exact Or.inl hleft
    · by_cases hright : RightWithCutAvoidsCutClearedData hmin P
      · exact Or.inr hright
      · exact False.elim
          (hnotForced
            ⟨(leftWithCutCutForcedClearedData_iff_not_avoidsCutClearedData
                hmin P).2 hleft,
              (rightWithCutCutForcedClearedData_iff_not_avoidsCutClearedData
                hmin P).2 hright⟩)

/-- If both plus-side images contain the cut vertex, their union is independent:
inside each plus-side this is inherited from the induced witness, and away
from the cut the two sides have no cross unit-distance edges. -/
theorem plusSideImages_indep_of_cut_mem_both
    (P : CutVertexPartition C)
    {sLeft : Finset (Fin P.leftWithCut.card)}
    {sRight : Finset (Fin P.rightWithCut.card)}
    (hsLeftIndep : P.leftWithCutInduced.config.IsIndep sLeft)
    (hsRightIndep : P.rightWithCutInduced.config.IsIndep sRight)
    (hcutLeft : P.cut ∈ sLeft.image P.leftWithCutInduced.embed)
    (hcutRight : P.cut ∈ sRight.image P.rightWithCutInduced.embed) :
    C.IsIndep
      (sLeft.image P.leftWithCutInduced.embed ∪
        sRight.image P.rightWithCutInduced.embed) := by
  let leftImage : Finset (Fin n) := sLeft.image P.leftWithCutInduced.embed
  let rightImage : Finset (Fin n) := sRight.image P.rightWithCutInduced.embed
  have hleftImageIndep : C.IsIndep leftImage := by
    simpa [leftImage] using P.leftWithCutInduced.image_indep hsLeftIndep
  have hrightImageIndep : C.IsIndep rightImage := by
    simpa [rightImage] using P.rightWithCutInduced.image_indep hsRightIndep
  have hcutLeftImage : P.cut ∈ leftImage := by
    simpa [leftImage] using hcutLeft
  have hcutRightImage : P.cut ∈ rightImage := by
    simpa [rightImage] using hcutRight
  have hcross :
      forall x : Fin n, x ∈ leftImage ->
        forall y : Fin n, y ∈ rightImage -> x ≠ y ->
          eucDist (C.pts x) (C.pts y) ≠ 1 := by
    intro x hx y hy hxy hunit
    by_cases hxcut : x = P.cut
    · subst x
      exact hrightImageIndep P.cut hcutRightImage y hy hxy hunit
    by_cases hycut : y = P.cut
    · subst y
      exact hleftImageIndep x hx P.cut hcutLeftImage hxy hunit
    have hxSide : x ∈ P.leftWithCut := by
      rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      exact P.leftWithCutInduced_embed_mem i
    have hySide : y ∈ P.rightWithCut := by
      rcases Finset.mem_image.mp hy with ⟨j, _hj, rfl⟩
      exact P.rightWithCutInduced_embed_mem j
    have hxLeft : x ∈ P.left := by
      rcases Finset.mem_insert.mp
          (by
            simpa [CutVertexPartition.leftWithCut] using hxSide) with
        hcut | hleft
      · exact False.elim (hxcut hcut)
      · exact hleft
    have hyRight : y ∈ P.right := by
      rcases Finset.mem_insert.mp
          (by
            simpa [CutVertexPartition.rightWithCut] using hySide) with
        hcut | hright
      · exact False.elim (hycut hcut)
      · exact hright
    exact P.no_unit_left_right hxLeft hyRight hunit
  simpa [leftImage, rightImage] using
    MinimalCounterexample.union_indep_of_cross_nonunit
      hleftImageIndep hrightImageIndep hcross

/-- Both plus-side witnesses containing the cut give an ambient cleared
witness as soon as their union has the ambient cleared cardinality. -/
theorem hasCleared_of_plusSideImages_cut_mem_both_of_union_cardBound
    (P : CutVertexPartition C)
    {sLeft : Finset (Fin P.leftWithCut.card)}
    {sRight : Finset (Fin P.rightWithCut.card)}
    (hsLeftIndep : P.leftWithCutInduced.config.IsIndep sLeft)
    (hsRightIndep : P.rightWithCutInduced.config.IsIndep sRight)
    (hcutLeft : P.cut ∈ sLeft.image P.leftWithCutInduced.embed)
    (hcutRight : P.cut ∈ sRight.image P.rightWithCutInduced.embed)
    (hbound :
      MinimalCounterexample.ClearedEightThirtyOneBound n
        (sLeft.image P.leftWithCutInduced.embed ∪
          sRight.image P.rightWithCutInduced.embed).card) :
    HasClearedEightThirtyOneIndependentSet C :=
  ⟨sLeft.image P.leftWithCutInduced.embed ∪
      sRight.image P.rightWithCutInduced.embed,
    plusSideImages_indep_of_cut_mem_both P
      hsLeftIndep hsRightIndep hcutLeft hcutRight,
    hbound⟩

theorem leftWithCutAvoidsCutClearedData_of_minimalitySet_avoids_cut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (havoid :
      P.cut ∉
        (leftWithCutMinimalitySet hmin P).image
          P.leftWithCutInduced.embed) :
    LeftWithCutAvoidsCutClearedData hmin P :=
  ⟨leftWithCutMinimalitySet hmin P,
    leftWithCutMinimalitySet_indep hmin P,
    leftWithCutMinimalitySet_bound hmin P,
    havoid⟩

theorem rightWithCutAvoidsCutClearedData_of_minimalitySet_avoids_cut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (havoid :
      P.cut ∉
        (rightWithCutMinimalitySet hmin P).image
          P.rightWithCutInduced.embed) :
    RightWithCutAvoidsCutClearedData hmin P :=
  ⟨rightWithCutMinimalitySet hmin P,
    rightWithCutMinimalitySet_indep hmin P,
    rightWithCutMinimalitySet_bound hmin P,
    havoid⟩

/-- Concrete named-witness version of the plus-side payload: one of the two
minimality-selected witnesses on `left ∪ {cut}` or `right ∪ {cut}` avoids the
cut vertex. -/
abbrev CutPartitionPlusSideMinimalityWitnessAvoidsCut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  P.cut ∉
      (leftWithCutMinimalitySet hmin P).image
        P.leftWithCutInduced.embed ∨
    P.cut ∉
      (rightWithCutMinimalitySet hmin P).image
        P.rightWithCutInduced.embed

theorem cutPartitionPlusSideAvoidsCutData_of_minimalityWitness_avoids_cut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (havoid : CutPartitionPlusSideMinimalityWitnessAvoidsCut hmin P) :
    CutPartitionPlusSideAvoidsCutData hmin P := by
  cases havoid with
  | inl hleft =>
      exact Or.inl
        (leftWithCutAvoidsCutClearedData_of_minimalitySet_avoids_cut
          hmin P hleft)
  | inr hright =>
      exact Or.inr
        (rightWithCutAvoidsCutClearedData_of_minimalitySet_avoids_cut
          hmin P hright)

abbrev MinimalFailureCutPartitionPlusSideMinimalityWitnessAvoidsCut : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C),
      CutPartitionPlusSideMinimalityWitnessAvoidsCut hmin P

/-- A pointwise non-side-card payload for a supplied cut partition: one of the
two plus-side minimality witnesses avoids the cut vertex.  Either branch gives
a direct glued independent set in the ambient minimal failure. -/
theorem false_of_minimalFailure_plusSideAvoidsCutData
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hpayload : CutPartitionPlusSideAvoidsCutData hmin P) :
    False := by
  cases hpayload with
  | inl hleft =>
      rcases hleft with ⟨sLeft, hsLeftIndep, hsLeftBound, havoid⟩
      exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
        (P.hasCleared_of_leftWithCut_avoids_cut_and_right
          hsLeftIndep hsLeftBound havoid
          (rightSideMinimalitySet_indep hmin P)
          (rightSideMinimalitySet_bound hmin P))
  | inr hright =>
      rcases hright with ⟨sRight, hsRightIndep, hsRightBound, havoid⟩
      exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
        (P.hasCleared_of_left_and_rightWithCut_avoids_cut
          (leftSideMinimalitySet_indep hmin P)
          (leftSideMinimalitySet_bound hmin P)
          hsRightIndep hsRightBound havoid)

abbrev MinimalFailureCutPartitionPlusSideAvoidsCutData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C),
      CutPartitionPlusSideAvoidsCutData hmin P

theorem leftWithCutMinimalitySet_cut_mem_of_cutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : LeftWithCutCutForcedClearedData hmin P) :
    P.cut ∈
      (leftWithCutMinimalitySet hmin P).image
        P.leftWithCutInduced.embed := by
  exact hforced
    (leftWithCutMinimalitySet hmin P)
    (leftWithCutMinimalitySet_indep hmin P)
    (leftWithCutMinimalitySet_bound hmin P)

theorem rightWithCutMinimalitySet_cut_mem_of_cutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : RightWithCutCutForcedClearedData hmin P) :
    P.cut ∈
      (rightWithCutMinimalitySet hmin P).image
        P.rightWithCutInduced.embed := by
  exact hforced
    (rightWithCutMinimalitySet hmin P)
    (rightWithCutMinimalitySet_indep hmin P)
    (rightWithCutMinimalitySet_bound hmin P)

/-- Concrete cardinal payload for the simultaneous cut-forcing branch: the
union of the two plus-side minimality witnesses, sharing the cut vertex once,
already has the ambient cleared cardinality. -/
abbrev CutPartitionPlusSideMinimalityUnionCardBound
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  MinimalCounterexample.ClearedEightThirtyOneBound n
    ((leftWithCutMinimalitySet hmin P).image P.leftWithCutInduced.embed ∪
      (rightWithCutMinimalitySet hmin P).image
        P.rightWithCutInduced.embed).card

/-- If both plus sides force the cut and the two selected plus-side witnesses
still clear after identifying that shared cut vertex, minimality is
contradicted. -/
theorem false_of_minimalFailure_bothPlusSidesCutForced_of_plusSideMinimalityUnionCardBound
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : CutPartitionBothPlusSidesCutForcedData hmin P)
    (hbound : CutPartitionPlusSideMinimalityUnionCardBound hmin P) :
    False := by
  rcases hforced with ⟨hforcedLeft, hforcedRight⟩
  have hcutLeft :
      P.cut ∈
        (leftWithCutMinimalitySet hmin P).image
          P.leftWithCutInduced.embed :=
    leftWithCutMinimalitySet_cut_mem_of_cutForced hmin P hforcedLeft
  have hcutRight :
      P.cut ∈
        (rightWithCutMinimalitySet hmin P).image
          P.rightWithCutInduced.embed :=
    rightWithCutMinimalitySet_cut_mem_of_cutForced hmin P hforcedRight
  exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    (hasCleared_of_plusSideImages_cut_mem_both_of_union_cardBound P
      (leftWithCutMinimalitySet_indep hmin P)
      (rightWithCutMinimalitySet_indep hmin P)
      hcutLeft hcutRight hbound)

theorem not_plusSideMinimalityUnionCardBound_of_minimalFailure_bothPlusSidesCutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : CutPartitionBothPlusSidesCutForcedData hmin P) :
    Not (CutPartitionPlusSideMinimalityUnionCardBound hmin P) := by
  intro hbound
  exact
    false_of_minimalFailure_bothPlusSidesCutForced_of_plusSideMinimalityUnionCardBound
      hmin P hforced hbound

theorem not_leftSideMinimalitySet_plusBound_of_leftWithCutCutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : LeftWithCutCutForcedClearedData hmin P) :
    ¬ MinimalCounterexample.ClearedEightThirtyOneBound
      P.leftWithCut.card (leftSideMinimalitySet hmin P).card := by
  intro hbound
  let sPlus := P.leftSetInLeftWithCut (leftSideMinimalitySet hmin P)
  have hcard :
      sPlus.card = (leftSideMinimalitySet hmin P).card := by
    simpa [sPlus] using
      P.leftSetInLeftWithCut_card (leftSideMinimalitySet hmin P)
  have hboundPlus :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.leftWithCut.card sPlus.card := by
    unfold MinimalCounterexample.ClearedEightThirtyOneBound at *
    omega
  have hcut :
      P.cut ∈ sPlus.image P.leftWithCutInduced.embed :=
    hforced sPlus
      (by
        simpa [sPlus] using
          P.leftSetInLeftWithCut_indep
            (leftSideMinimalitySet_indep hmin P))
      hboundPlus
  have havoid :
      P.cut ∉ sPlus.image P.leftWithCutInduced.embed := by
    simpa [sPlus] using
      P.leftSetInLeftWithCut_avoids_cut
        (leftSideMinimalitySet hmin P)
  exact havoid hcut

theorem not_rightSideMinimalitySet_plusBound_of_rightWithCutCutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : RightWithCutCutForcedClearedData hmin P) :
    ¬ MinimalCounterexample.ClearedEightThirtyOneBound
      P.rightWithCut.card (rightSideMinimalitySet hmin P).card := by
  intro hbound
  let sPlus := P.rightSetInRightWithCut (rightSideMinimalitySet hmin P)
  have hcard :
      sPlus.card = (rightSideMinimalitySet hmin P).card := by
    simpa [sPlus] using
      P.rightSetInRightWithCut_card (rightSideMinimalitySet hmin P)
  have hboundPlus :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.rightWithCut.card sPlus.card := by
    unfold MinimalCounterexample.ClearedEightThirtyOneBound at *
    omega
  have hcut :
      P.cut ∈ sPlus.image P.rightWithCutInduced.embed :=
    hforced sPlus
      (by
        simpa [sPlus] using
          P.rightSetInRightWithCut_indep
            (rightSideMinimalitySet_indep hmin P))
      hboundPlus
  have havoid :
      P.cut ∉ sPlus.image P.rightWithCutInduced.embed := by
    simpa [sPlus] using
      P.rightSetInRightWithCut_avoids_cut
        (rightSideMinimalitySet hmin P)
  exact havoid hcut

theorem leftSideMinimalitySet_card_lt_leftWithCutMinimalitySet_card_of_cutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : LeftWithCutCutForcedClearedData hmin P) :
    (leftSideMinimalitySet hmin P).card <
      (leftWithCutMinimalitySet hmin P).card := by
  have hnot :=
    not_leftSideMinimalitySet_plusBound_of_leftWithCutCutForced
      hmin P hforced
  by_contra hlt
  have hle :
      (leftWithCutMinimalitySet hmin P).card <=
        (leftSideMinimalitySet hmin P).card :=
    Nat.le_of_not_gt hlt
  have hplus := leftWithCutMinimalitySet_bound hmin P
  have hsidePlus :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.leftWithCut.card (leftSideMinimalitySet hmin P).card := by
    unfold MinimalCounterexample.ClearedEightThirtyOneBound at *
    omega
  exact hnot hsidePlus

theorem rightSideMinimalitySet_card_lt_rightWithCutMinimalitySet_card_of_cutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : RightWithCutCutForcedClearedData hmin P) :
    (rightSideMinimalitySet hmin P).card <
      (rightWithCutMinimalitySet hmin P).card := by
  have hnot :=
    not_rightSideMinimalitySet_plusBound_of_rightWithCutCutForced
      hmin P hforced
  by_contra hlt
  have hle :
      (rightWithCutMinimalitySet hmin P).card <=
        (rightSideMinimalitySet hmin P).card :=
    Nat.le_of_not_gt hlt
  have hplus := rightWithCutMinimalitySet_bound hmin P
  have hsidePlus :
      MinimalCounterexample.ClearedEightThirtyOneBound
        P.rightWithCut.card (rightSideMinimalitySet hmin P).card := by
    unfold MinimalCounterexample.ClearedEightThirtyOneBound at *
    omega
  exact hnot hsidePlus

theorem leftWithCutMinimalitySet_slack_ge_twentyThree_of_cutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : LeftWithCutCutForcedClearedData hmin P) :
    8 * P.leftWithCut.card + 23 <=
      31 * (leftWithCutMinimalitySet hmin P).card := by
  have hlt :=
    leftSideMinimalitySet_card_lt_leftWithCutMinimalitySet_card_of_cutForced
      hmin P hforced
  have hside := leftSideMinimalitySet_bound hmin P
  have hcard := P.leftWithCut_card
  unfold MinimalCounterexample.ClearedEightThirtyOneBound at hside
  omega

theorem rightWithCutMinimalitySet_slack_ge_twentyThree_of_cutForced
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : RightWithCutCutForcedClearedData hmin P) :
    8 * P.rightWithCut.card + 23 <=
      31 * (rightWithCutMinimalitySet hmin P).card := by
  have hlt :=
    rightSideMinimalitySet_card_lt_rightWithCutMinimalitySet_card_of_cutForced
      hmin P hforced
  have hside := rightSideMinimalitySet_bound hmin P
  have hcard := P.rightWithCut_card
  unfold MinimalCounterexample.ClearedEightThirtyOneBound at hside
  omega

theorem false_of_minimalFailure_bothPlusSidesCutForcedData
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C)
    (hforced : CutPartitionBothPlusSidesCutForcedData hmin P) :
    False := by
  rcases hforced with ⟨hleftForced, hrightForced⟩
  have hleftCut :
      P.cut ∈
        (leftWithCutMinimalitySet hmin P).image
          P.leftWithCutInduced.embed :=
    leftWithCutMinimalitySet_cut_mem_of_cutForced hmin P hleftForced
  have hrightCut :
      P.cut ∈
        (rightWithCutMinimalitySet hmin P).image
          P.rightWithCutInduced.embed :=
    rightWithCutMinimalitySet_cut_mem_of_cutForced hmin P hrightForced
  have hleftSlack :=
    leftWithCutMinimalitySet_slack_ge_twentyThree_of_cutForced
      hmin P hleftForced
  have hrightSlack :=
    rightWithCutMinimalitySet_slack_ge_twentyThree_of_cutForced
      hmin P hrightForced
  have hbound :
      MinimalCounterexample.ClearedEightThirtyOneBound n
        ((leftWithCutMinimalitySet hmin P).card +
          (rightWithCutMinimalitySet hmin P).card - 1) := by
    have hcard := P.card_eq_left_add_right_add_one
    have hleftCard := P.leftWithCut_card
    have hrightCard := P.rightWithCut_card
    have hleftPos : 1 <= (leftWithCutMinimalitySet hmin P).card := by
      omega
    have hrightPos : 1 <= (rightWithCutMinimalitySet hmin P).card := by
      omega
    unfold MinimalCounterexample.ClearedEightThirtyOneBound
    omega
  exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    (P.hasCleared_of_leftWithCut_and_rightWithCut_contain_cut
      (leftWithCutMinimalitySet_indep hmin P)
      hleftCut
      (rightWithCutMinimalitySet_indep hmin P)
      hrightCut
      hbound)

/-- Global spelling of the exact local obstruction to plus-side avoidance. -/
abbrev MinimalFailureNoBothPlusSidesCutForcedData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C),
      Not (CutPartitionBothPlusSidesCutForcedData hmin P)

theorem plusSideAvoidsCutData_of_noBothPlusSidesCutForcedData
    (H : MinimalFailureNoBothPlusSidesCutForcedData) :
    MinimalFailureCutPartitionPlusSideAvoidsCutData := by
  intro n C hmin P
  exact
    (cutPartitionPlusSideAvoidsCutData_iff_not_bothPlusSidesCutForced
      hmin P).2 (H C hmin P)

theorem noBothPlusSidesCutForcedData_of_plusSideAvoidsCutData
    (H : MinimalFailureCutPartitionPlusSideAvoidsCutData) :
    MinimalFailureNoBothPlusSidesCutForcedData := by
  intro n C hmin P
  exact
    (cutPartitionPlusSideAvoidsCutData_iff_not_bothPlusSidesCutForced
      hmin P).1 (H C hmin P)

theorem plusSideAvoidsCutData_iff_noBothPlusSidesCutForcedData :
    MinimalFailureCutPartitionPlusSideAvoidsCutData <->
      MinimalFailureNoBothPlusSidesCutForcedData := by
  constructor
  · exact noBothPlusSidesCutForcedData_of_plusSideAvoidsCutData
  · exact plusSideAvoidsCutData_of_noBothPlusSidesCutForcedData

theorem noBothPlusSidesCutForcedData_of_minimalFailure :
    MinimalFailureNoBothPlusSidesCutForcedData := by
  intro n C hmin P hforced
  exact false_of_minimalFailure_bothPlusSidesCutForcedData hmin P hforced

theorem plusSideAvoidsCutData_of_refuting_bothPlusSidesCutForced :
    MinimalFailureCutPartitionPlusSideAvoidsCutData :=
  plusSideAvoidsCutData_of_noBothPlusSidesCutForcedData
    noBothPlusSidesCutForcedData_of_minimalFailure

/-- Uniform no-cut from the concrete plus-side avoidance payload.  This is a
direct cut-partition contradiction branch, not the refuted pointwise side-card
route. -/
theorem minimalFailureNoCutVertexFamily_of_plusSideAvoidsCutData
    (H : MinimalFailureCutPartitionPlusSideAvoidsCutData) :
    MinimalFailureNoCutVertexFamily := by
  intro n C hmin hcut
  rcases hcut with ⟨P⟩
  exact false_of_minimalFailure_plusSideAvoidsCutData hmin P (H C hmin P)

theorem minimalFailureNoCutVertexFamily_of_noBothPlusSidesCutForcedData
    (H : MinimalFailureNoBothPlusSidesCutForcedData) :
    MinimalFailureNoCutVertexFamily :=
  minimalFailureNoCutVertexFamily_of_plusSideAvoidsCutData
    (plusSideAvoidsCutData_of_noBothPlusSidesCutForcedData H)

theorem minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced :
    MinimalFailureNoCutVertexFamily :=
  minimalFailureNoCutVertexFamily_of_plusSideAvoidsCutData
    plusSideAvoidsCutData_of_refuting_bothPlusSidesCutForced

theorem minimalFailureCutPartitionPlusSideAvoidsCutData_of_minimalityWitnessAvoidsCut
    (H : MinimalFailureCutPartitionPlusSideMinimalityWitnessAvoidsCut) :
    MinimalFailureCutPartitionPlusSideAvoidsCutData := by
  intro n C hmin P
  exact
    cutPartitionPlusSideAvoidsCutData_of_minimalityWitness_avoids_cut
      hmin P (H C hmin P)

/-- Route the concrete named-witness source through the direct non-side-card
plus-side contradiction. -/
theorem minimalFailureNoCutVertexFamily_of_plusSideMinimalityWitnessAvoidsCut
    (H : MinimalFailureCutPartitionPlusSideMinimalityWitnessAvoidsCut) :
    MinimalFailureNoCutVertexFamily :=
  minimalFailureNoCutVertexFamily_of_plusSideAvoidsCutData
    (minimalFailureCutPartitionPlusSideAvoidsCutData_of_minimalityWitnessAvoidsCut
      H)

/-- At an actual minimal-failure cut partition, the plus-side avoidance data
itself is contradictory. -/
theorem cutPartitionPlusSideAvoidsCutData_iff_false_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    CutPartitionPlusSideAvoidsCutData hmin P <-> False := by
  constructor
  · exact false_of_minimalFailure_plusSideAvoidsCutData hmin P
  · intro hfalse
    exact False.elim hfalse

/-- Once no cut partition exists, the plus-side avoidance source is vacuous. -/
theorem cutPartitionPlusSideAvoidsCutData_of_noCutVertex
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : NoCutVertex C)
    (P : CutVertexPartition C) :
    CutPartitionPlusSideAvoidsCutData hmin P :=
  False.elim (hno (Nonempty.intro P))

/-- Converse direction for the exact no-cut boundary of the plus-side source. -/
theorem plusSideAvoidsCutData_of_minimalFailureNoCutVertexFamily
    (H : MinimalFailureNoCutVertexFamily) :
    MinimalFailureCutPartitionPlusSideAvoidsCutData := by
  intro n C hmin P
  exact cutPartitionPlusSideAvoidsCutData_of_noCutVertex hmin (H C hmin) P

/-- The plus-side avoidance source is exactly the minimal-failure no-cut
family: forward by gluing, backward vacuously. -/
theorem plusSideAvoidsCutData_iff_minimalFailureNoCutVertexFamily :
    MinimalFailureCutPartitionPlusSideAvoidsCutData <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  · exact minimalFailureNoCutVertexFamily_of_plusSideAvoidsCutData
  · exact plusSideAvoidsCutData_of_minimalFailureNoCutVertexFamily

/-! ## What minimality alone refutes -/

/-- In a minimal cleared failure, the concrete glued side image for a supplied
cut partition cannot itself satisfy the ambient cleared cardinal bound. -/
theorem not_combinedImage_cardBound_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    ¬ 8 * n <=
      31 * (sideSurplusData_of_minimalFailure hmin P).combinedImage.card := by
  intro hbound
  exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    ((sideSurplusData_of_minimalFailure hmin P).hasCleared_of_combinedImage_cardBound
      hbound)

/-- Consequently, for a supplied cut partition, minimality alone refutes the
sum-of-side-cardinalities exact bound rather than proving it. -/
theorem not_sideCardExactForPartition_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    ¬ 8 * n <=
      31 *
        ((sideSurplusData_of_minimalFailure hmin P).leftSet.carrier.card +
          (sideSurplusData_of_minimalFailure hmin P).rightSet.carrier.card) := by
  intro hbound
  let D := sideSurplusData_of_minimalFailure hmin P
  have hcombined : 8 * n <= 31 * D.combinedImage.card := by
    rw [D.combinedImage_card]
    simpa [D] using hbound
  exact not_combinedImage_cardBound_of_minimalFailure hmin P hcombined

/-- If an actual cut partition is supplied, the universal exact-cardinality
fact is incompatible with minimality. -/
theorem not_sideCardExactFact_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    ¬ CutVertexDeletionSideCardExactFact hmin := by
  intro hcard
  exact not_sideCardExactForPartition_of_minimalFailure hmin P (hcard P)

/-- For a supplied cut partition, the side witnesses chosen from minimality
cannot satisfy the pay-for-cut field. -/
theorem not_paysCut_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    ¬ (sideSurplusData_of_minimalFailure hmin P).PaysCut := by
  intro hpay
  exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    ((sideSurplusData_of_minimalFailure hmin P).hasCleared_of_exactSideSurpluses_of_paysCut
      (sideSurplusData_of_minimalFailure_exactSideSurpluses hmin P)
      hpay)

/-- Thus an actual cut partition is incompatible with the universal missing
pay-for-cut arithmetic for the minimality-selected side witnesses. -/
theorem not_missingArithmetic_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    ¬ CutVertexDeletionMissingArithmetic hmin := by
  intro harith
  exact not_paysCut_of_minimalFailure_partition hmin P (harith P)

/-- Any supplied cut partition is incompatible with an all-partitions deletion
slack fact in a minimal cleared failure. -/
theorem not_deletionSlackFact_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    ¬ CutVertexDeletionSlackFact C := by
  intro hslack
  rcases hslack P with ⟨D⟩
  exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    (CutVertexPartition.hasCleared_of_cutVertexSlack P D)

/-- Contradiction-routing form: the missing pay-for-cut arithmetic would imply
there is no cut-vertex partition. -/
theorem noCutVertex_of_minimalFailure_missingArithmetic
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (harith : CutVertexDeletionMissingArithmetic hmin) :
    NoCutVertex C := by
  rintro ⟨P⟩
  exact not_missingArithmetic_of_minimalFailure_partition hmin P harith

/-- Contradiction-routing form for the side-cardinality interface. -/
theorem noCutVertex_of_minimalFailure_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : CutVertexDeletionSideCardExactFact hmin) :
    NoCutVertex C := by
  rintro ⟨P⟩
  exact not_sideCardExactFact_of_minimalFailure_partition hmin P hcard

/-- Direct no-cut route from a deletion slack fact, avoiding any extra
positive-cardinality facade. -/
theorem noCutVertex_of_minimalFailure_deletionSlackFact_direct
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexDeletionSlackFact C) :
    NoCutVertex C := by
  rintro ⟨P⟩
  exact not_deletionSlackFact_of_minimalFailure_partition hmin P hslack

/-! ## Source-level Lemma 3 no-cut family -/

/-- Pointwise side-card data for one supplied cut partition.  This is the
exact concrete cardinal field whose attempted extraction from minimality would
pay for the deleted cut vertex. -/
abbrev CutPartitionSideCardData
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  8 * n <=
    31 *
      ((sideSurplusData_of_minimalFailure hmin P).leftSet.carrier.card +
        (sideSurplusData_of_minimalFailure hmin P).rightSet.carrier.card)

/-- Pointwise side-card data for the supplied cut partition.  This is the
paper Lemma 3 cut-vertex source with the partition still exposed. -/
abbrev MinimalFailureCutPartitionSideCardData : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C),
      CutPartitionSideCardData hmin P

/-- Uniform exact side-card data, packaged per minimal failure. -/
abbrev MinimalFailureSideCardExactFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      CutVertexDeletionSideCardExactFact hmin

/-- Pointwise side-card data is the same as the bound on the glued ambient
image of the two minimality-selected side witnesses. -/
theorem cutPartitionSideCardData_iff_combinedImageBound
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    CutPartitionSideCardData hmin P <->
      8 * n <=
        31 * (sideSurplusData_of_minimalFailure hmin P).combinedImage.card := by
  let D := sideSurplusData_of_minimalFailure hmin P
  constructor
  · intro hcard
    rw [D.combinedImage_card]
    simpa [CutPartitionSideCardData, D] using hcard
  · intro hbound
    rw [D.combinedImage_card] at hbound
    simpa [CutPartitionSideCardData, D] using hbound

/-- A supplied cut partition in a minimal cleared failure refutes the exact
pointwise side-card datum for the minimality-selected side witnesses. -/
theorem not_cutPartitionSideCardData_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (CutPartitionSideCardData hmin P) := by
  intro hcard
  exact not_sideCardExactForPartition_of_minimalFailure hmin P
    (by simpa [CutPartitionSideCardData] using hcard)

/-- Equivalently, the exposed pointwise side-card datum is false for an actual
cut partition in a minimal cleared failure. -/
theorem cutPartitionSideCardData_iff_false_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    CutPartitionSideCardData hmin P <-> False := by
  constructor
  · exact not_cutPartitionSideCardData_of_minimalFailure_partition hmin P
  · intro hfalse
    exact False.elim hfalse

/-- Once no cut partition exists, the pointwise side-card datum is vacuous. -/
theorem cutPartitionSideCardData_of_noCutVertex
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : NoCutVertex C)
    (P : CutVertexPartition C) :
    CutPartitionSideCardData hmin P :=
  False.elim (hno (Nonempty.intro P))

/-- The pointwise exposed side-card source is the same data as the exact
per-minimal-failure side-card family. -/
theorem sideCardExactFamily_of_cutPartitionSideCardData
    (H : MinimalFailureCutPartitionSideCardData) :
    MinimalFailureSideCardExactFamily := by
  intro n C hmin P
  exact H C hmin P

/-- Direct paper Lemma 3 no-cut source from the exact side-card family.
For a supplied cut partition, the side-card datum would glue the two
minimality-selected side witnesses into a cleared ambient set, contradicting
minimal failure. -/
theorem minimalFailureNoCutVertexFamily_of_sideCardExactFamily
    (H : MinimalFailureSideCardExactFamily) :
    MinimalFailureNoCutVertexFamily := by
  intro n C hmin hcut
  rcases hcut with ⟨P⟩
  exact not_sideCardExactFact_of_minimalFailure_partition hmin P (H C hmin)

/-- Direct paper Lemma 3 no-cut source from pointwise cut-partition
side-card data, without passing through the exact blocker equivalence. -/
theorem minimalFailureNoCutVertexFamily_of_cutPartitionSideCardData
    (H : MinimalFailureCutPartitionSideCardData) :
    MinimalFailureNoCutVertexFamily :=
  minimalFailureNoCutVertexFamily_of_sideCardExactFamily
    (sideCardExactFamily_of_cutPartitionSideCardData H)

/-- Conversely, a no-cut family makes the exposed cut-partition side-card
source vacuous.  Thus the proposed source is exactly no-cut, not an
independent consequence of minimality. -/
theorem cutPartitionSideCardData_of_minimalFailureNoCutVertexFamily
    (H : MinimalFailureNoCutVertexFamily) :
    MinimalFailureCutPartitionSideCardData := by
  intro n C hmin P
  exact cutPartitionSideCardData_of_noCutVertex hmin (H C hmin) P

/-- The exposed side-card source is equivalent to the desired minimal-failure
no-cut theorem. -/
theorem cutPartitionSideCardData_iff_minimalFailureNoCutVertexFamily :
    MinimalFailureCutPartitionSideCardData <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  · exact minimalFailureNoCutVertexFamily_of_cutPartitionSideCardData
  · exact cutPartitionSideCardData_of_minimalFailureNoCutVertexFamily

end

end CutVertexSlackFromDeletion
end Swanepoel
end ErdosProblems1066
