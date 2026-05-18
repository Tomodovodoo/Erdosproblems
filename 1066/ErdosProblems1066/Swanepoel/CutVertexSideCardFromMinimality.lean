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

end

end CutVertexSlackFromDeletion
end Swanepoel
end ErdosProblems1066
