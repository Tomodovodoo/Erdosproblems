import ErdosProblems1066.Swanepoel.NoCutBlockerEliminationW24
import ErdosProblems1066.Swanepoel.PayForCutArithmeticW16
import ErdosProblems1066.Swanepoel.LocalDeletionConstructors
import ErdosProblems1066.Swanepoel.LocalDeletionEliminatorWithCardBound

set_option autoImplicit false

/-!
# W25 cut-vertex contradiction inhabitation boundary

This file attacks the W24 no-cut gap at the partition level.

The current imported facts still do not prove an unconditional contradiction
from a supplied cut partition.  What they do prove is sharp: blocker
elimination is equivalent to the pointwise pay-for-cut statement for the
minimality-selected side witnesses, equivalently to the pointwise exact
side-cardinality inequality, equivalently to the pointwise deletion-slack
gluing data.

For an actual blocker, the same local/minimality lemmas prove the negations of
those pointwise facts.  Thus the remaining gap is not bookkeeping around W24:
it is precisely the missing arithmetic/side-cardinality theorem that would pay
for the deleted cut vertex in every minimal cut partition.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexContradictionInhabitationW25

open CutVertexInterface
open CutVertexSlackFromDeletion
open MinimalGraphFacts

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  NoCutBlockerEliminationW24.MinimalCutVertexBlocker

abbrev MinimalCutVertexBlockerExists : Prop :=
  Nonempty MinimalCutVertexBlocker

/-- W24's exact partition contradiction target. -/
abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  NoCutBlockerEliminationW24.MinimalFailureCutVertexContradictionFamily

/-- The smallest pointwise pay-for-cut atom: for each supplied cut partition,
the two side witnesses selected by minimality pay for the deleted cut vertex. -/
abbrev MinimalFailurePointwisePayForCutFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C),
      NoCutMinimalityProofW15.MinimalitySelectedPartitionPaysCut hmin P

/-- The same atom in explicit side-cardinality form. -/
abbrev MinimalFailurePointwiseSideCardFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C),
      PayForCutArithmeticW16.MinimalitySelectedPartitionSideCardInequality
        hmin P

/-- The same atom as a bound on the glued ambient image of the two side
witnesses. -/
abbrev MinimalFailurePointwiseCombinedImageBoundFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C),
      8 * n <= 31 * (sideSurplusData_of_minimalFailure hmin P).combinedImage.card

/-- The same atom as actual gluing data for each supplied partition. -/
abbrev MinimalFailurePointwiseDeletionSlackFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C),
      Nonempty (CutVertexPartition.CutVertexSlackGluingData P)

/-- The W13 extraction-input facade, pointwise over minimal cleared failures. -/
abbrev MinimalFailureExtractionInputFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      NoCutVertexExtractionW13.NoCutVertexExtractionInput hmin

variable {n : Nat} {C : _root_.UDConfig n}
variable (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C)

/-- Pointwise pay-for-cut immediately glues the two sides and contradicts
minimality for a supplied cut partition. -/
theorem false_of_minimalFailure_partition_pointwisePayForCut
    (hpay :
      NoCutMinimalityProofW15.MinimalitySelectedPartitionPaysCut hmin P) :
    False :=
  NoCutMinimalityProofW15.not_minimalitySelectedPartitionPaysCut_of_minimalFailure_partition
    hmin P hpay

/-- Pointwise side-cardinality is exactly enough to pay for the cut, hence it
also contradicts minimality for a supplied partition. -/
theorem false_of_minimalFailure_partition_pointwiseSideCard
    (hcard :
      PayForCutArithmeticW16.MinimalitySelectedPartitionSideCardInequality
        hmin P) :
    False :=
  PayForCutArithmeticW16.not_sideCardInequality_of_minimalFailure_partition
    hmin P hcard

/-- The glued ambient side-image bound directly contradicts minimality. -/
theorem false_of_minimalFailure_partition_combinedImageBound
    (hbound :
      8 * n <= 31 * (sideSurplusData_of_minimalFailure hmin P).combinedImage.card) :
    False :=
  CutVertexSlackFromDeletion.not_combinedImage_cardBound_of_minimalFailure
    hmin P hbound

/-- Pointwise deletion-slack gluing data is already enough to clear the
ambient configuration, contradicting minimality. -/
theorem false_of_minimalFailure_partition_pointwiseDeletionSlack
    (hmin : IsMinimalClearedFailure C) (P : CutVertexPartition C)
    (hslack : Nonempty (CutVertexPartition.CutVertexSlackGluingData P)) :
    False := by
  rcases hslack with ⟨D⟩
  exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    (CutVertexPartition.hasCleared_of_cutVertexSlack P D)

/-- The W24 contradiction family is exactly the pointwise pay-for-cut family:
the reverse direction is vacuous because a contradiction supplies any
pointwise arithmetic fact. -/
theorem cutVertexContradictionFamily_iff_pointwisePayForCutFamily :
    MinimalFailureCutVertexContradictionFamily <->
      MinimalFailurePointwisePayForCutFamily := by
  constructor
  · intro H n C hmin P
    exact False.elim (H C hmin P)
  · intro H n C hmin P
    exact false_of_minimalFailure_partition_pointwisePayForCut
      hmin P (H C hmin P)

/-- Pay-for-cut and side-cardinality are the same remaining pointwise input. -/
theorem pointwisePayForCutFamily_iff_pointwiseSideCardFamily :
    MinimalFailurePointwisePayForCutFamily <->
      MinimalFailurePointwiseSideCardFamily := by
  constructor
  · intro H n C hmin P
    exact
      (PayForCutArithmeticW16.minimalitySelectedPartitionPaysCut_iff_sideCardInequality
        hmin P).1 (H C hmin P)
  · intro H n C hmin P
    exact
      (PayForCutArithmeticW16.minimalitySelectedPartitionPaysCut_iff_sideCardInequality
        hmin P).2 (H C hmin P)

/-- The pointwise side-cardinality family is the W24 exact side-cardinality
family, written without the wrapper. -/
theorem pointwiseSideCardFamily_iff_w24SideCardExactFamily :
    MinimalFailurePointwiseSideCardFamily <->
      NoCutBlockerEliminationW24.MinimalFailureSideCardExactFamily := by
  constructor
  · intro H n C hmin P
    exact H C hmin P
  · intro H n C hmin P
    exact H C hmin P

/-- The pointwise pay-for-cut family is the W24 missing-arithmetic family. -/
theorem pointwisePayForCutFamily_iff_w24MissingArithmeticFamily :
    MinimalFailurePointwisePayForCutFamily <->
      NoCutBlockerEliminationW24.MinimalFailureMissingArithmeticFamily := by
  constructor
  · intro H n C hmin P
    exact H C hmin P
  · intro H n C hmin P
    exact H C hmin P

/-- Side-cardinality is also equivalent to bounding the actual glued ambient
image of the two side witnesses. -/
theorem pointwiseSideCardFamily_iff_combinedImageBoundFamily :
    MinimalFailurePointwiseSideCardFamily <->
      MinimalFailurePointwiseCombinedImageBoundFamily := by
  constructor
  · intro H n C hmin P
    rw [(sideSurplusData_of_minimalFailure hmin P).combinedImage_card]
    exact H C hmin P
  · intro H n C hmin P
    have hbound := H C hmin P
    rw [(sideSurplusData_of_minimalFailure hmin P).combinedImage_card] at hbound
    exact hbound

/-- The pointwise deletion-slack family is exactly W24's deletion-slack
family with the per-partition quantifier exposed. -/
theorem pointwiseDeletionSlackFamily_iff_w24DeletionSlackFamily :
    MinimalFailurePointwiseDeletionSlackFamily <->
      NoCutBlockerEliminationW24.MinimalFailureDeletionSlackFamily := by
  constructor
  · intro H n C hmin P
    exact H C hmin P
  · intro H n C hmin P
    exact H C hmin P

/-- Per-partition deletion slack is equivalent to W24's contradiction family. -/
theorem cutVertexContradictionFamily_iff_pointwiseDeletionSlackFamily :
    MinimalFailureCutVertexContradictionFamily <->
      MinimalFailurePointwiseDeletionSlackFamily := by
  constructor
  · intro H n C hmin P
    exact False.elim (H C hmin P)
  · intro H n C hmin P
    exact false_of_minimalFailure_partition_pointwiseDeletionSlack
      hmin P (H C hmin P)

/-- W13's extraction input is another facade for the same no-cut content. -/
theorem extractionInputFamily_iff_cutVertexContradictionFamily :
    MinimalFailureExtractionInputFamily <->
      MinimalFailureCutVertexContradictionFamily := by
  constructor
  · intro H n C hmin P
    exact
      NoCutVertexExtractionW13.cutVertexPartition_obstructs_extractionInput_of_minimalFailure
        hmin P (H C hmin)
  · intro H n C hmin
    have hno : NoCutVertex C := by
      rintro ⟨P⟩
      exact H C hmin P
    exact
      (NoCutVertexExtractionW13.noCutVertexExtractionInput_iff_noCutVertex_of_minimalFailure
        hmin).2 hno

/-- W25 blocker-elimination boundary in the smallest pay-for-cut form. -/
theorem not_nonempty_minimalCutVertexBlocker_iff_pointwisePayForCutFamily :
    Not (Nonempty MinimalCutVertexBlocker) <->
      MinimalFailurePointwisePayForCutFamily :=
  NoCutBlockerEliminationW24.not_blocker_iff_cutVertexContradictionFamily.trans
    cutVertexContradictionFamily_iff_pointwisePayForCutFamily

/-- W25 blocker-elimination boundary in exact side-cardinality form. -/
theorem not_nonempty_minimalCutVertexBlocker_iff_pointwiseSideCardFamily :
    Not (Nonempty MinimalCutVertexBlocker) <->
      MinimalFailurePointwiseSideCardFamily :=
  not_nonempty_minimalCutVertexBlocker_iff_pointwisePayForCutFamily.trans
    pointwisePayForCutFamily_iff_pointwiseSideCardFamily

/-- W25 blocker-elimination boundary in glued-image cardinality form. -/
theorem not_nonempty_minimalCutVertexBlocker_iff_combinedImageBoundFamily :
    Not (Nonempty MinimalCutVertexBlocker) <->
      MinimalFailurePointwiseCombinedImageBoundFamily :=
  not_nonempty_minimalCutVertexBlocker_iff_pointwiseSideCardFamily.trans
    pointwiseSideCardFamily_iff_combinedImageBoundFamily

/-- W25 blocker-elimination boundary in per-partition deletion-slack form. -/
theorem not_nonempty_minimalCutVertexBlocker_iff_pointwiseDeletionSlackFamily :
    Not (Nonempty MinimalCutVertexBlocker) <->
      MinimalFailurePointwiseDeletionSlackFamily :=
  NoCutBlockerEliminationW24.not_blocker_iff_cutVertexContradictionFamily.trans
    cutVertexContradictionFamily_iff_pointwiseDeletionSlackFamily

/-- W25 blocker-elimination boundary in W13 extraction-input form. -/
theorem not_nonempty_minimalCutVertexBlocker_iff_extractionInputFamily :
    Not (Nonempty MinimalCutVertexBlocker) <->
      MinimalFailureExtractionInputFamily :=
  NoCutBlockerEliminationW24.not_blocker_iff_cutVertexContradictionFamily.trans
    extractionInputFamily_iff_cutVertexContradictionFamily.symm

/-- A concrete blocker refutes the exact pointwise pay-for-cut atom for its
own cut partition. -/
theorem blocker_obstructs_pointwisePayForCut
    (B : MinimalCutVertexBlocker) :
    Not
      (NoCutMinimalityProofW15.MinimalitySelectedPartitionPaysCut
        B.minimal B.cut) :=
  NoCutMinimalityProofW15.not_minimalitySelectedPartitionPaysCut_of_minimalFailure_partition
    B.minimal B.cut

/-- A concrete blocker refutes the exact pointwise side-cardinality atom for
its own cut partition. -/
theorem blocker_obstructs_pointwiseSideCard
    (B : MinimalCutVertexBlocker) :
    Not
      (PayForCutArithmeticW16.MinimalitySelectedPartitionSideCardInequality
        B.minimal B.cut) :=
  PayForCutArithmeticW16.not_sideCardInequality_of_minimalFailure_partition
    B.minimal B.cut

/-- A concrete blocker refutes pointwise deletion-slack gluing data for its
own cut partition. -/
theorem blocker_obstructs_pointwiseDeletionSlack
    (B : MinimalCutVertexBlocker) :
    Not (Nonempty (CutVertexPartition.CutVertexSlackGluingData B.cut)) := by
  intro hslack
  exact false_of_minimalFailure_partition_pointwiseDeletionSlack
    B.minimal B.cut hslack

/-- A concrete blocker refutes the W13 extraction input for its minimal
failure. -/
theorem blocker_obstructs_extractionInput
    (B : MinimalCutVertexBlocker) :
    Not (NoCutVertexExtractionW13.NoCutVertexExtractionInput B.minimal) :=
  NoCutVertexExtractionW13.cutVertexPartition_obstructs_extractionInput_of_minimalFailure
    B.minimal B.cut

/-- If the local deletion modules eliminate every minimal cleared failure,
then the W24 cut-partition contradiction family follows. -/
theorem cutVertexContradictionFamily_of_degreeDeletionEliminator
    (hdel :
      LocalDeletionConstructors.MinimalFailureDegreeDeletionEliminator) :
    MinimalFailureCutVertexContradictionFamily := by
  intro n C hmin _P
  exact
    LocalDeletionConstructors.no_minimalClearedFailure_of_degreeDeletionEliminator
      hdel C hmin

/-- Local closed-neighborhood deletion data is therefore enough to eliminate
the concrete cut-vertex blocker. -/
theorem not_nonempty_minimalCutVertexBlocker_of_localClosedNeighborhoodDeletionEliminator
    (hdel :
      LocalDeletionConstructors.MinimalFailureLocalClosedNeighborhoodDeletionEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) :=
  NoCutBlockerEliminationW24.not_blocker_of_cutVertexContradictionFamily
    (cutVertexContradictionFamily_of_degreeDeletionEliminator
      (LocalDeletionConstructors.degreeDeletionEliminator_of_localClosedNeighborhoodDeletionEliminator
        hdel))

/-- The direct-card-bound local deletion module gives the same blocker
elimination once such data is available for every minimal cleared failure. -/
theorem not_nonempty_minimalCutVertexBlocker_of_directCardBoundCertificateEliminator
    (hdel :
      LocalDeletionEliminatorWithCardBound.MinimalFailureDirectCardBoundCertificateEliminator) :
    Not (Nonempty MinimalCutVertexBlocker) := by
  intro hblocker
  rcases hblocker with ⟨B⟩
  exact
    LocalDeletionEliminatorWithCardBound.no_minimalClearedFailure_of_directCardBoundCertificateEliminator
      hdel B.C B.minimal

end

end CutVertexContradictionInhabitationW25
end Swanepoel
end ErdosProblems1066
