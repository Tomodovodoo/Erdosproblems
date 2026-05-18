import ErdosProblems1066.Swanepoel.PayForCutArithmeticW16

set_option autoImplicit false

/-!
# W17 concrete pay-for-cut inequality

This file keeps the W16 blocker in its concrete side-cardinality form.  The
checked outcome is a sharp split: under minimality, the uniform concrete
inequality is exactly the W15 pay-for-cut input and exactly the no-cut branch.
If a cut partition is supplied, the selected pointwise inequality fails.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace PayForCutConcreteInequalityW17

open CutVertexInterface
open CutVertexSlackFromDeletion

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

/-- The concrete sum of the two side-cardinalities selected by minimality for
a supplied cut partition. -/
def selectedSideCardSum
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Nat :=
  (sideSurplusData_of_minimalFailure hmin P).leftSet.carrier.card +
    (sideSurplusData_of_minimalFailure hmin P).rightSet.carrier.card

/-- The pointwise concrete side-card inequality selected by minimality. -/
def ConcreteSelectedSideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  8 * n <= 31 * selectedSideCardSum hmin P

/-- The uniform concrete side-card inequality over all supplied cut
partitions. -/
def ConcreteSelectedSideCardInequalityAll
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    ConcreteSelectedSideCardInequality hmin P

/-- The concrete pointwise formula is the W16 selected side-card formula. -/
theorem concreteSelectedSideCardInequality_iff_w16
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    ConcreteSelectedSideCardInequality hmin P <->
      PayForCutArithmeticW16.MinimalitySelectedPartitionSideCardInequality
        hmin P := by
  rfl

/-- The concrete uniform formula is the W16 uniform selected side-card
formula. -/
theorem concreteSelectedSideCardInequalityAll_iff_w16
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ConcreteSelectedSideCardInequalityAll hmin <->
      PayForCutArithmeticW16.MinimalitySelectedSideCardInequality hmin := by
  rfl

/-- For one partition, paying for the cut vertex is exactly the concrete
side-card inequality for the selected witnesses. -/
theorem selectedPartitionPaysCut_iff_concreteSideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    NoCutMinimalityProofW15.MinimalitySelectedPartitionPaysCut hmin P <->
      ConcreteSelectedSideCardInequality hmin P := by
  exact
    (PayForCutArithmeticW16.minimalitySelectedPartitionPaysCut_iff_sideCardInequality
      hmin P).trans
      (concreteSelectedSideCardInequality_iff_w16 hmin P).symm

/-- The W15 pay-for-cut input is exactly the concrete uniform side-card
inequality. -/
theorem minimalitySelectedPayForCut_iff_concreteSideCardInequalityAll
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    NoCutMinimalityProofW15.MinimalitySelectedPayForCut hmin <->
      ConcreteSelectedSideCardInequalityAll hmin := by
  constructor
  case mp =>
    intro hpay P
    exact
      (selectedPartitionPaysCut_iff_concreteSideCardInequality hmin P).1
        (hpay P)
  case mpr =>
    intro hcard P
    exact
      (selectedPartitionPaysCut_iff_concreteSideCardInequality hmin P).2
        (hcard P)

/-- Under minimality, the concrete side-card inequality closes exactly when
there is no supplied cut partition. -/
theorem concreteSideCardInequalityAll_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ConcreteSelectedSideCardInequalityAll hmin <-> NoCutVertex C := by
  exact
    (concreteSelectedSideCardInequalityAll_iff_w16 hmin).trans
      (PayForCutArithmeticW16.sideCardInequality_iff_noCutVertex_of_minimalFailure
        hmin)

/-- No supplied cut partition makes the concrete uniform inequality vacuous. -/
theorem concreteSideCardInequalityAll_of_noCutVertex
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    ConcreteSelectedSideCardInequalityAll hmin :=
  (concreteSideCardInequalityAll_iff_noCutVertex_of_minimalFailure hmin).2 hno

/-- The concrete uniform inequality gives the no-cut branch. -/
theorem noCutVertex_of_concreteSideCardInequalityAll
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : ConcreteSelectedSideCardInequalityAll hmin) :
    NoCutVertex C :=
  (concreteSideCardInequalityAll_iff_noCutVertex_of_minimalFailure hmin).1
    hcard

/-- A supplied partition refutes the selected concrete pointwise inequality. -/
theorem not_concreteSideCardInequality_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (ConcreteSelectedSideCardInequality hmin P) := by
  intro hcard
  exact
    PayForCutArithmeticW16.not_sideCardInequality_of_minimalFailure_partition
      hmin P
      ((concreteSelectedSideCardInequality_iff_w16 hmin P).1 hcard)

/-- A supplied partition refutes the concrete uniform inequality. -/
theorem cutVertexPartition_obstructs_concreteSideCardInequalityAll
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (ConcreteSelectedSideCardInequalityAll hmin) := by
  intro hcard
  exact
    not_concreteSideCardInequality_of_minimalFailure_partition hmin P
      (hcard P)

/-- Concrete W17 split: either there is no supplied cut partition, or some
supplied partition fails the selected pointwise side-card inequality. -/
theorem noCutVertex_or_exists_failed_concreteSideCardInequality
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Or (NoCutVertex C)
      (Exists fun P : CutVertexPartition C =>
        Not (ConcreteSelectedSideCardInequality hmin P)) := by
  by_cases hno : NoCutVertex C
  case pos =>
    exact Or.inl hno
  case neg =>
    have hpart : Nonempty (CutVertexPartition C) := by
      exact Classical.not_not.mp (by
        simpa [NoCutVertex] using hno)
    cases hpart with
    | intro P =>
        exact Or.inr
          (Exists.intro P
            (not_concreteSideCardInequality_of_minimalFailure_partition
              hmin P))

/-- The W15 pay-for-cut input is also exactly the concrete no-cut branch. -/
theorem minimalitySelectedPayForCut_iff_concreteNoCutBranch
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    NoCutMinimalityProofW15.MinimalitySelectedPayForCut hmin <->
      NoCutVertex C :=
  (minimalitySelectedPayForCut_iff_concreteSideCardInequalityAll hmin).trans
    (concreteSideCardInequalityAll_iff_noCutVertex_of_minimalFailure hmin)

end

end PayForCutConcreteInequalityW17
end Swanepoel
end ErdosProblems1066
