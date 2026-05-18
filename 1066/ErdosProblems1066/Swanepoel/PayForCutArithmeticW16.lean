import ErdosProblems1066.Swanepoel.NoCutMinimalityProofW15

set_option autoImplicit false

/-!
# W16 pay-for-cut arithmetic

This file exposes the remaining W15 pay-for-cut input as the exact side-card
inequality for the witnesses selected by minimality.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PayForCutArithmeticW16

open CutVertexInterface
open CutVertexSlackFromDeletion
open NoCutMinimalityProofW15

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

/-- Pointwise side-card inequality for the two witnesses selected by
minimality on a supplied cut partition. -/
def MinimalitySelectedPartitionSideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  8 * n <=
    31 *
      ((sideSurplusData_of_minimalFailure hmin P).leftSet.carrier.card +
        (sideSurplusData_of_minimalFailure hmin P).rightSet.carrier.card)

/-- Uniform side-card inequality for all supplied cut partitions. -/
def MinimalitySelectedSideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    MinimalitySelectedPartitionSideCardInequality hmin P

/-- The pointwise W15 pay-for-cut field is exactly the explicit side-card
inequality for the selected witnesses. -/
theorem minimalitySelectedPartitionPaysCut_iff_sideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    MinimalitySelectedPartitionPaysCut hmin P <->
      MinimalitySelectedPartitionSideCardInequality hmin P := by
  let D := sideSurplusData_of_minimalFailure hmin P
  simpa [MinimalitySelectedPartitionPaysCut,
    MinimalitySelectedPartitionSideCardInequality,
    CutVertexSideSurplusData.AmbientCardBound, D] using
    (D.ambientCardBound_iff_paysCut_of_exactSideSurpluses
      (sideSurplusData_of_minimalFailure_exactSideSurpluses hmin P)).symm

/-- The uniform W15 pay-for-cut input is exactly the explicit uniform
side-card inequality. -/
theorem minimalitySelectedPayForCut_iff_sideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      MinimalitySelectedSideCardInequality hmin := by
  constructor
  case mp =>
    intro hpay P
    exact
      (minimalitySelectedPartitionPaysCut_iff_sideCardInequality hmin P).1
        (hpay P)
  case mpr =>
    intro hcard P
    exact
      (minimalitySelectedPartitionPaysCut_iff_sideCardInequality hmin P).2
        (hcard P)

/-- The explicit uniform side-card inequality is the existing exact-card
interface. -/
theorem sideCardInequality_iff_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedSideCardInequality hmin <->
      CutVertexDeletionSideCardExactFact hmin := by
  rfl

/-- W16 restatement: W15 pay-for-cut and the exact-card interface are the
same remaining input. -/
theorem minimalitySelectedPayForCut_iff_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionSideCardExactFact hmin :=
  (minimalitySelectedPayForCut_iff_sideCardInequality hmin).trans
    (sideCardInequality_iff_sideCardExactFact hmin)

/-- The W15 pay-for-cut input is also equivalent to the bound on the glued
ambient side image. -/
theorem minimalitySelectedPayForCut_iff_combinedImageBoundFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionCombinedImageBoundFact hmin :=
  (minimalitySelectedPayForCut_iff_sideCardExactFact hmin).trans
    (sideCardExactFact_iff_combinedImageBoundFact hmin)

/-- The W15 pay-for-cut input is equivalent to the older paper-card wrapper. -/
theorem minimalitySelectedPayForCut_iff_sideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionSideCardPaperFact hmin :=
  (minimalitySelectedPayForCut_iff_sideCardExactFact hmin).trans
    (sideCardExactFact_iff_sideCardPaperFact hmin)

/-- The W15 missing arithmetic is exactly the explicit uniform side-card
inequality. -/
theorem cutVertexDeletionMissingArithmetic_iff_sideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionMissingArithmetic hmin <->
      MinimalitySelectedSideCardInequality hmin :=
  (minimalitySelectedPayForCut_iff_missingArithmetic hmin).symm.trans
    (minimalitySelectedPayForCut_iff_sideCardInequality hmin)

/-- Final W16 reduction: under minimality, the explicit side-card inequality
is equivalent to no supplied cut partition. -/
theorem sideCardInequality_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedSideCardInequality hmin <-> NoCutVertex C :=
  (sideCardInequality_iff_sideCardExactFact hmin).trans
    (NoCutVertexExtractionW13.sideCardExactFact_iff_noCutVertex_of_minimalFailure
      hmin)

/-- W16 no-cut form of the W15 blocker. -/
theorem minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <-> NoCutVertex C :=
  (minimalitySelectedPayForCut_iff_sideCardInequality hmin).trans
    (sideCardInequality_iff_noCutVertex_of_minimalFailure hmin)

/-- A supplied cut partition refutes the pointwise inequality for the selected
side witnesses. -/
theorem not_sideCardInequality_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (MinimalitySelectedPartitionSideCardInequality hmin P) := by
  intro hcard
  exact
    not_sideCardExactForPartition_of_minimalFailure hmin P
      (by
        simpa [MinimalitySelectedPartitionSideCardInequality] using hcard)

/-- A supplied cut partition refutes the uniform explicit side-card
inequality. -/
theorem cutVertexPartition_obstructs_sideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (MinimalitySelectedSideCardInequality hmin) := by
  intro hcard
  exact not_sideCardInequality_of_minimalFailure_partition hmin P (hcard P)

/-- The pointwise inequality would produce the pointwise W15 pay-for-cut
field, and hence contradict minimality for an actual partition. -/
theorem not_partitionPaysCut_via_sideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (MinimalitySelectedPartitionPaysCut hmin P) := by
  intro hpay
  exact
    not_sideCardInequality_of_minimalFailure_partition hmin P
      ((minimalitySelectedPartitionPaysCut_iff_sideCardInequality hmin P).1
        hpay)

end

end PayForCutArithmeticW16
end Swanepoel
end ErdosProblems1066
