import ErdosProblems1066.PachToth.SmallComplementExactBlocksW16
import ErdosProblems1066.PachToth.SmallComplementConcreteBlocksW17
import ErdosProblems1066.PachToth.SmallCaseCertificates
import ErdosProblems1066.PachToth.LargeThresholdSmallCasesW15
import ErdosProblems1066.PachToth.SmallLargeInputPackageAssemblyW21

set_option autoImplicit false

/-!
# W22 finite small-complement closure

This module keeps the W21 small/large splice honest: the remaining finite side
is exactly a block-threshold family of exact-chain or exact-block certificates.
It also names the concrete threshold-six and threshold-seven closures already
available from W16/W17 in the W21 `SmallComplement` vocabulary.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallComplementClosureW22

noncomputable section

abbrev ExactTarget : Prop :=
  SmallLargeInputPackageAssemblyW21.ExactTarget

abbrev EventualTarget : Prop :=
  SmallLargeInputPackageAssemblyW21.EventualTarget

abbrev ArbitraryTarget : Prop :=
  SmallLargeInputPackageAssemblyW21.ArbitraryTarget

abbrev SmallComplement (K0 : Nat) : Prop :=
  SmallLargeInputPackageAssemblyW21.SmallComplement K0

abbrev ExactBlockTarget (k : Nat) : Prop :=
  LargeThresholdSmallCasesW15.ExactBlockTarget k

abbrev ExactBlockThresholdEvidence (K0 : Nat) :=
  LargeSmallCaseClosureW14.ExactBlockThresholdEvidence K0

abbrev ExactChainThresholdEvidence (K0 : Nat) :=
  LargeSmallCaseClosureW14.ExactChainThresholdEvidence K0

abbrev LargeClosedPlacementFields (K0 : Nat) :=
  SmallLargeInputPackageAssemblyW21.LargeClosedPlacementFields K0

abbrev AllPositiveFields :=
  SmallComplementExactBlocksW16.AllPositiveFields

abbrev ConcreteValueMatrixFamily :=
  SmallComplementExactBlocksW16.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  SmallComplementExactBlocksW16.CandidateValueMatrixFamily

abbrev AllPositiveCertificateRows :=
  SmallComplementConcreteBlocksW17.AllPositiveCertificateRows

abbrev SmallLengthExactBlockTargets :=
  SmallComplementConcreteBlocksW17.SmallLengthExactBlockTargets

abbrev ExactBlocksTwoThroughFive :=
  SmallComplementConcreteBlocksW17.ExactBlocksTwoThroughFive

abbrev ConcreteOneBlockCertificate
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :=
  ExactBlockCertificateW13.ConcreteOneBlockCertificate orientation

abbrev blockThresholdSix : Nat :=
  SmallComplementConcreteBlocksW17.blockThresholdSix

abbrev blockThresholdSeven : Nat :=
  SmallComplementConcreteBlocksW17.blockThresholdSeven

abbrev ExactBlockTargetsBelowThreshold (K0 : Nat) : Prop :=
  forall k : Nat, k < K0 -> 0 < k -> ExactBlockTarget k

abbrev ExactChainTargetsBelowThreshold (K0 : Nat) : Type :=
  forall k : Nat, k < K0 -> 0 < k -> SplitSoundness.ExactChainUpper k

/-! ## Direct finite-complement closure -/

theorem smallComplement_mono
    {K0 K1 : Nat} (hK : K0 <= K1)
    (small : SmallComplement K1) :
    SmallComplement K0 := by
  intro n hn
  exact small n (Nat.lt_of_lt_of_le hn (Nat.mul_le_mul_left 16 hK))

theorem smallComplement_of_le_one
    {K0 : Nat} (hK0 : K0 <= 1) :
    SmallComplement K0 :=
  LargeThresholdSmallCasesW15.smallComplement_atMostOne hK0

theorem smallComplement_zero :
    SmallComplement 0 :=
  smallComplement_of_le_one (by norm_num)

theorem smallComplement_one :
    SmallComplement 1 :=
  smallComplement_of_le_one (by norm_num)

theorem exactBlockThresholdEvidence_of_smallComplement
    {K0 : Nat} (small : SmallComplement K0) :
    ExactBlockThresholdEvidence K0 :=
  LargeThresholdSmallCasesW15.exactBlockThresholdEvidenceOfSmallComplement
    small

def exactChainThresholdEvidence_of_smallComplement
    {K0 : Nat} (small : SmallComplement K0) :
    ExactChainThresholdEvidence K0 :=
  LargeThresholdSmallCasesW15.exactChainThresholdEvidenceOfSmallComplement
    small

theorem smallComplement_of_exactBlockThresholdEvidence
    {K0 : Nat} (E : ExactBlockThresholdEvidence K0) :
    SmallComplement K0 :=
  (LargeThresholdSmallCasesW15.smallComplement_iff_exactBlockThresholdEvidence
    K0).2 E

theorem smallComplement_of_exactChainThresholdEvidence
    {K0 : Nat} (E : ExactChainThresholdEvidence K0) :
    SmallComplement K0 := by
  intro n hn
  exact
    LargeSmallCaseClosureW14.ExactChainThresholdEvidence.targetUpperConstructionFiveSixteenSmallUpTo
      E n hn

theorem smallComplement_iff_exactBlockThresholdEvidence
    (K0 : Nat) :
    SmallComplement K0 <-> ExactBlockThresholdEvidence K0 :=
  LargeThresholdSmallCasesW15.smallComplement_iff_exactBlockThresholdEvidence K0

theorem smallComplement_iff_exactBlockTargetsBelowThreshold
    (K0 : Nat) :
    SmallComplement K0 <-> ExactBlockTargetsBelowThreshold K0 := by
  constructor
  case mp =>
    intro small k hklt hk
    exact
      LargeThresholdSmallCasesW15.exactBlockTarget_of_smallComplement
        small hklt hk
  case mpr =>
    intro exactBlock
    exact smallComplement_of_exactBlockThresholdEvidence
      { exactBlock := exactBlock }

theorem smallComplement_of_exactBlockTargetsBelowThreshold
    {K0 : Nat} (exactBlock : ExactBlockTargetsBelowThreshold K0) :
    SmallComplement K0 :=
  (smallComplement_iff_exactBlockTargetsBelowThreshold K0).2 exactBlock

theorem exactBlockTargetsBelowThreshold_of_smallComplement
    {K0 : Nat} (small : SmallComplement K0) :
    ExactBlockTargetsBelowThreshold K0 :=
  (smallComplement_iff_exactBlockTargetsBelowThreshold K0).1 small

theorem smallComplement_iff_nonempty_exactChainThresholdEvidence
    (K0 : Nat) :
    SmallComplement K0 <-> Nonempty (ExactChainThresholdEvidence K0) := by
  constructor
  case mp =>
    intro small
    exact Nonempty.intro (exactChainThresholdEvidence_of_smallComplement small)
  case mpr =>
    intro E
    rcases E with ⟨E⟩
    exact smallComplement_of_exactChainThresholdEvidence E

theorem smallComplement_iff_nonempty_exactChainTargetsBelowThreshold
    (K0 : Nat) :
    SmallComplement K0 <-> Nonempty (ExactChainTargetsBelowThreshold K0) := by
  constructor
  case mp =>
    intro small
    exact Nonempty.intro (exactChainThresholdEvidence_of_smallComplement small).chain
  case mpr =>
    intro chain
    rcases chain with ⟨chain⟩
    exact smallComplement_of_exactChainThresholdEvidence
      { chain := chain }

theorem smallComplement_of_exactChainTargetsBelowThreshold
    {K0 : Nat} (chain : ExactChainTargetsBelowThreshold K0) :
    SmallComplement K0 :=
  (smallComplement_iff_nonempty_exactChainTargetsBelowThreshold K0).2
    (Nonempty.intro chain)

def exactChainTargetsBelowThreshold_of_smallComplement
    {K0 : Nat} (small : SmallComplement K0) :
    ExactChainTargetsBelowThreshold K0 :=
  (exactChainThresholdEvidence_of_smallComplement small).chain

/-! ## Named small exact-block certificates -/

def smallLengthExactBlockTargetsOfSmallComplementSix
    (small : SmallComplement blockThresholdSix) :
    SmallLengthExactBlockTargets where
  lengthOne := by
    simpa [ExactBlockTarget] using
      exactBlockTargetsBelowThreshold_of_smallComplement small 1
        (by
          rw [SmallComplementConcreteBlocksW17.blockThresholdSix]
          norm_num)
        (by norm_num)
  lengthTwo := by
    simpa [ExactBlockTarget] using
      exactBlockTargetsBelowThreshold_of_smallComplement small 2
        (by
          rw [SmallComplementConcreteBlocksW17.blockThresholdSix]
          norm_num)
        (by norm_num)
  lengthThree := by
    simpa [ExactBlockTarget] using
      exactBlockTargetsBelowThreshold_of_smallComplement small 3
        (by
          rw [SmallComplementConcreteBlocksW17.blockThresholdSix]
          norm_num)
        (by norm_num)
  lengthFour := by
    simpa [ExactBlockTarget] using
      exactBlockTargetsBelowThreshold_of_smallComplement small 4
        (by
          rw [SmallComplementConcreteBlocksW17.blockThresholdSix]
          norm_num)
        (by norm_num)
  lengthFive := by
    simpa [ExactBlockTarget] using
      exactBlockTargetsBelowThreshold_of_smallComplement small 5
        (by
          rw [SmallComplementConcreteBlocksW17.blockThresholdSix]
          norm_num)
        (by norm_num)

theorem smallComplement_six_iff_nonempty_smallLengthExactBlockTargets :
    SmallComplement blockThresholdSix <-> Nonempty SmallLengthExactBlockTargets := by
  constructor
  case mp =>
    intro small
    exact Nonempty.intro (smallLengthExactBlockTargetsOfSmallComplementSix small)
  case mpr =>
    intro C
    rcases C with ⟨C⟩
    exact
      SmallComplementConcreteBlocksW17.smallComplement_six_of_smallLengthExactBlockTargets
        C

theorem smallComplement_six_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    SmallComplement blockThresholdSix :=
  smallComplement_six_iff_nonempty_smallLengthExactBlockTargets.2
    (Nonempty.intro C)

theorem smallComplement_of_smallLengthExactBlockTargets_le_six
    {K0 : Nat} (C : SmallLengthExactBlockTargets)
    (hK0 : K0 <= blockThresholdSix) :
    SmallComplement K0 :=
  smallComplement_mono hK0
    (smallComplement_six_of_smallLengthExactBlockTargets C)

theorem smallComplement_six_of_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallComplement blockThresholdSix :=
  C.smallComplement_six oneBlock

theorem smallComplement_of_exactBlocksTwoThroughFive_le_six
    {K0 : Nat}
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation)
    (hK0 : K0 <= blockThresholdSix) :
    SmallComplement K0 :=
  smallComplement_mono hK0
    (smallComplement_six_of_exactBlocksTwoThroughFive C oneBlock)

theorem smallComplement_two_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallComplement 2 :=
  SmallComplementExactBlocksW16.smallComplement_two_of_concreteOneBlockCertificate
    oneBlock

theorem smallComplement_two_iff_lengthOneExactBlock :
    SmallComplement 2 <-> ExactBlockTarget 1 := by
  constructor
  case mp =>
    intro small
    exact exactBlockTargetsBelowThreshold_of_smallComplement small 1
      (by norm_num)
      (by norm_num)
  case mpr =>
    intro lengthOne
    exact smallComplement_of_exactBlockTargetsBelowThreshold
      (fun k hklt hk => by
        have hkone : k = 1 := by
          omega
        subst k
        simpa using lengthOne)

theorem smallComplement_six_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallComplement blockThresholdSix :=
  SmallComplementConcreteBlocksW17.smallComplement_six_of_allPositiveCertificateRows
    C

theorem smallComplement_seven_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallComplement blockThresholdSeven :=
  SmallComplementConcreteBlocksW17.smallComplement_seven_of_allPositiveCertificateRows
    C

theorem smallComplement_of_allPositiveFields
    (K0 : Nat) (F : AllPositiveFields) :
    SmallComplement K0 :=
  SmallComplementExactBlocksW16.smallComplement_of_allPositiveFields K0 F

theorem smallComplement_of_concreteValueMatrixFamily
    (K0 : Nat) (C : ConcreteValueMatrixFamily) :
    SmallComplement K0 :=
  SmallComplementExactBlocksW16.smallComplement_of_concreteValueMatrixFamily
    K0 C

theorem smallComplement_of_candidateValueMatrixFamily
    (K0 : Nat) (C : CandidateValueMatrixFamily) :
    SmallComplement K0 :=
  SmallComplementExactBlocksW16.smallComplement_of_candidateValueMatrixFamily
    K0 C

/-! ## W21 large-field reductions to the finite side -/

theorem arbitraryTarget_iff_exactBlockTargetsBelowThreshold_of_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    ArbitraryTarget <-> ExactBlockTargetsBelowThreshold K0 :=
  (SmallLargeInputPackageAssemblyW21.arbitraryTarget_of_largeClosedPlacementFields_iff_smallComplement
    L).trans
    (smallComplement_iff_exactBlockTargetsBelowThreshold K0)

theorem arbitraryTarget_iff_exactChainTargetsBelowThreshold_of_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    ArbitraryTarget <-> Nonempty (ExactChainTargetsBelowThreshold K0) :=
  (SmallLargeInputPackageAssemblyW21.arbitraryTarget_of_largeClosedPlacementFields_iff_smallComplement
    L).trans
    (smallComplement_iff_nonempty_exactChainTargetsBelowThreshold K0)

theorem exact_eventual_arbitrary_iff_exactBlockTargetsBelowThreshold_of_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    (ExactTarget /\ EventualTarget /\ ArbitraryTarget) <->
      ExactBlockTargetsBelowThreshold K0 :=
  (SmallLargeInputPackageAssemblyW21.exact_eventual_arbitrary_of_largeClosedPlacementFields_iff_smallComplement
    L).trans
    (smallComplement_iff_exactBlockTargetsBelowThreshold K0)

theorem exact_eventual_arbitrary_iff_exactChainTargetsBelowThreshold_of_largeClosedPlacementFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) :
    (ExactTarget /\ EventualTarget /\ ArbitraryTarget) <->
      Nonempty (ExactChainTargetsBelowThreshold K0) :=
  (SmallLargeInputPackageAssemblyW21.exact_eventual_arbitrary_of_largeClosedPlacementFields_iff_smallComplement
    L).trans
    (smallComplement_iff_nonempty_exactChainTargetsBelowThreshold K0)

theorem arbitraryTarget_iff_nonempty_smallLengthExactBlockTargets_of_largeClosedPlacementFields_six
    (L : LargeClosedPlacementFields blockThresholdSix) :
    ArbitraryTarget <-> Nonempty SmallLengthExactBlockTargets :=
  (SmallLargeInputPackageAssemblyW21.arbitraryTarget_of_largeClosedPlacementFields_iff_smallComplement
    L).trans
    smallComplement_six_iff_nonempty_smallLengthExactBlockTargets

theorem exact_eventual_arbitrary_iff_nonempty_smallLengthExactBlockTargets_of_largeClosedPlacementFields_six
    (L : LargeClosedPlacementFields blockThresholdSix) :
    (ExactTarget /\ EventualTarget /\ ArbitraryTarget) <->
      Nonempty SmallLengthExactBlockTargets :=
  (SmallLargeInputPackageAssemblyW21.exact_eventual_arbitrary_of_largeClosedPlacementFields_iff_smallComplement
    L).trans
    smallComplement_six_iff_nonempty_smallLengthExactBlockTargets

theorem exact_eventual_arbitrary_of_largeClosedPlacementFields_allPositiveFields
    {K0 : Nat} (L : LargeClosedPlacementFields K0) (F : AllPositiveFields) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (SmallLargeInputPackageAssemblyW21.exact_eventual_arbitrary_of_largeClosedPlacementFields_iff_smallComplement
    L).2
    (smallComplement_of_allPositiveFields K0 F)

theorem exact_eventual_arbitrary_of_largeClosedPlacementFields_concreteValueMatrixFamily
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (C : ConcreteValueMatrixFamily) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (SmallLargeInputPackageAssemblyW21.exact_eventual_arbitrary_of_largeClosedPlacementFields_iff_smallComplement
    L).2
    (smallComplement_of_concreteValueMatrixFamily K0 C)

theorem exact_eventual_arbitrary_of_largeClosedPlacementFields_candidateValueMatrixFamily
    {K0 : Nat} (L : LargeClosedPlacementFields K0)
    (C : CandidateValueMatrixFamily) :
    ExactTarget /\ EventualTarget /\ ArbitraryTarget :=
  (SmallLargeInputPackageAssemblyW21.exact_eventual_arbitrary_of_largeClosedPlacementFields_iff_smallComplement
    L).2
    (smallComplement_of_candidateValueMatrixFamily K0 C)

end

end SmallComplementClosureW22
end PachToth
end ErdosProblems1066
