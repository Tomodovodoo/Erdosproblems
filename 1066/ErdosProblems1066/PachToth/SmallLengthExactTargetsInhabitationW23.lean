import ErdosProblems1066.PachToth.SmallCaseCertificates
import ErdosProblems1066.PachToth.SmallComplementExactBlocksW16
import ErdosProblems1066.PachToth.SmallComplementConcreteBlocksW17
import ErdosProblems1066.PachToth.FiniteGraph
import ErdosProblems1066.PachToth.SmallComplementClosureW22

set_option autoImplicit false

/-!
# W23 small-length exact-target inhabitation

This module gives the direct constructors and equivalences for the finite
small-complement side isolated in W22.  It keeps the data honest: exact block
targets below block six, `SmallLengthExactBlockTargets`, and
`SmallComplement 6` are all interconverted through the existing W16/W17/W22
surfaces and the checked small-case certificates.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthExactTargetsInhabitationW23

open FiniteGraph

noncomputable section

abbrev SmallComplement (K0 : Nat) : Prop :=
  SmallComplementClosureW22.SmallComplement K0

abbrev ExactVertexTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ExactVertexTargetsBelow (N0 : Nat) : Prop :=
  targetUpperConstructionFiveSixteenSmallUpTo N0

abbrev ExactFiniteTarget (k : Nat) : Prop :=
  SmallComplementClosureW22.ExactBlockTarget k

abbrev ExactBlockTargetsBelowThreshold (K0 : Nat) : Prop :=
  SmallComplementClosureW22.ExactBlockTargetsBelowThreshold K0

abbrev SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.SmallLengthExactBlockTargets

abbrev ExactBlocksTwoThroughFive :=
  SmallComplementClosureW22.ExactBlocksTwoThroughFive

abbrev ConcreteOneBlockCertificate
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :=
  SmallComplementClosureW22.ConcreteOneBlockCertificate orientation

abbrev AllPositiveFields :=
  SmallComplementClosureW22.AllPositiveFields

abbrev ConcreteValueMatrixFamily :=
  SmallComplementClosureW22.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  SmallComplementClosureW22.CandidateValueMatrixFamily

abbrev AllPositiveCertificateRows :=
  SmallComplementClosureW22.AllPositiveCertificateRows

abbrev blockThresholdSix : Nat :=
  SmallComplementClosureW22.blockThresholdSix

abbrev ExactFiniteTargetsBelowSix : Prop :=
  ExactBlockTargetsBelowThreshold blockThresholdSix

abbrev LocalVertex :=
  FiniteGraph.LocalVertex

abbrev LocalIndependent (s : Finset LocalVertex) : Prop :=
  FiniteGraph.IsIndependent s

/-! ## Checked finite graph and small-case targets -/

theorem finiteGraph_localIndependent_card_le_six
    (s : Finset LocalVertex) (hs : LocalIndependent s) :
    s.card <= 6 :=
  FiniteGraph.alpha_le_six s hs

theorem finiteGraph_extractedSixSet_card :
    FiniteGraph.extractedSixSet.card = 6 :=
  FiniteGraph.extractedSixSet_card

theorem exactVertexTarget_of_lt_sixteen
    {n : Nat} (hn : n < 16) :
    ExactVertexTarget n :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenAt_of_lt_sixteen
    hn

theorem exactVertexTargetsBelow_sixteen :
    ExactVertexTargetsBelow 16 :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_sixteen

theorem exactVertexTargetsBelow_of_le_sixteen
    {N0 : Nat} (hN0 : N0 <= 16) :
    ExactVertexTargetsBelow N0 :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_of_le_sixteen
    hN0

theorem exactVertexTargetsBelow_blockThresholdSix_of_exactFiniteTargets
    (E : ExactFiniteTargetsBelowSix) :
    ExactVertexTargetsBelow (16 * blockThresholdSix) :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
    blockThresholdSix E

theorem exactVertexTargetsBelow_ninetySix_of_exactFiniteTargets
    (E : ExactFiniteTargetsBelowSix) :
    ExactVertexTargetsBelow (16 * 6) := by
  simpa [blockThresholdSix, SmallComplementClosureW22.blockThresholdSix,
    SmallComplementConcreteBlocksW17.blockThresholdSix] using
    exactVertexTargetsBelow_blockThresholdSix_of_exactFiniteTargets E

/-! ## Exact finite targets, small-length targets, and small complement six -/

def exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactFiniteTargetsBelowSix :=
  SmallComplementClosureW22.exactBlockTargetsBelowThreshold_of_smallComplement
    (SmallComplementClosureW22.smallComplement_six_of_smallLengthExactBlockTargets
      C)

def smallLengthExactBlockTargetsOfExactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.smallLengthExactBlockTargetsOfSmallComplementSix
    (SmallComplementClosureW22.smallComplement_of_exactBlockTargetsBelowThreshold
      E)

theorem smallComplement_blockThresholdSix_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    SmallComplement blockThresholdSix :=
  SmallComplementClosureW22.smallComplement_of_exactBlockTargetsBelowThreshold
    E

theorem smallComplement_six_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    SmallComplement 6 := by
  simpa [blockThresholdSix, SmallComplementClosureW22.blockThresholdSix,
    SmallComplementConcreteBlocksW17.blockThresholdSix] using
    smallComplement_blockThresholdSix_of_exactFiniteTargetsBelowSix E

theorem exactFiniteTargetsBelowSix_iff_smallComplement_blockThresholdSix :
    ExactFiniteTargetsBelowSix <-> SmallComplement blockThresholdSix :=
  (SmallComplementClosureW22.smallComplement_iff_exactBlockTargetsBelowThreshold
    blockThresholdSix).symm

theorem smallComplement_six_iff_nonempty_smallLengthExactBlockTargets :
    SmallComplement 6 <-> Nonempty SmallLengthExactBlockTargets := by
  simpa [blockThresholdSix, SmallComplementClosureW22.blockThresholdSix,
    SmallComplementConcreteBlocksW17.blockThresholdSix] using
    SmallComplementClosureW22.smallComplement_six_iff_nonempty_smallLengthExactBlockTargets

theorem nonempty_smallLengthExactBlockTargets_iff_exactFiniteTargetsBelowSix :
    Nonempty SmallLengthExactBlockTargets <-> ExactFiniteTargetsBelowSix := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro C =>
        exact exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets C
  case mpr =>
    intro E
    exact
      Nonempty.intro
        (smallLengthExactBlockTargetsOfExactFiniteTargetsBelowSix E)

theorem nonempty_smallLengthExactBlockTargets_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    Nonempty SmallLengthExactBlockTargets :=
  nonempty_smallLengthExactBlockTargets_iff_exactFiniteTargetsBelowSix.2 E

theorem exactFiniteTargetsBelowSix_of_smallComplement_six
    (small : SmallComplement 6) :
    ExactFiniteTargetsBelowSix := by
  exact
    exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
      (SmallComplementClosureW22.smallLengthExactBlockTargetsOfSmallComplementSix
        (by
          simpa [blockThresholdSix, SmallComplementClosureW22.blockThresholdSix,
            SmallComplementConcreteBlocksW17.blockThresholdSix] using small))

/-! ## W16/W17 certificate constructors -/

theorem exactFiniteTarget_one_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactFiniteTarget 1 :=
  SmallComplementClosureW22.smallComplement_two_iff_lengthOneExactBlock.1
    (SmallComplementClosureW22.smallComplement_two_of_concreteOneBlockCertificate
      oneBlock)

def smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallLengthExactBlockTargets :=
  SmallComplementConcreteBlocksW17.ExactBlocksTwoThroughFive.toSmallLengthExactBlockTargets
    blocks oneBlock

theorem exactFiniteTargetsBelowSix_of_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactFiniteTargetsBelowSix :=
  exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
      blocks oneBlock)

theorem smallComplement_blockThresholdSix_of_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallComplement blockThresholdSix :=
  SmallComplementClosureW22.smallComplement_six_of_exactBlocksTwoThroughFive
    blocks oneBlock

theorem smallComplement_six_of_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallComplement 6 := by
  simpa [blockThresholdSix, SmallComplementClosureW22.blockThresholdSix,
    SmallComplementConcreteBlocksW17.blockThresholdSix] using
    smallComplement_blockThresholdSix_of_exactBlocksTwoThroughFive
      blocks oneBlock

theorem exactFiniteTarget_two_of_exactBlocksTwoThroughFive
    (blocks : ExactBlocksTwoThroughFive) :
    ExactFiniteTarget 2 :=
  blocks.lengthTwo

theorem exactFiniteTarget_three_of_exactBlocksTwoThroughFive
    (blocks : ExactBlocksTwoThroughFive) :
    ExactFiniteTarget 3 :=
  blocks.lengthThree

theorem exactFiniteTarget_four_of_exactBlocksTwoThroughFive
    (blocks : ExactBlocksTwoThroughFive) :
    ExactFiniteTarget 4 :=
  blocks.lengthFourFive.lengthFour

theorem exactFiniteTarget_five_of_exactBlocksTwoThroughFive
    (blocks : ExactBlocksTwoThroughFive) :
    ExactFiniteTarget 5 :=
  blocks.lengthFourFive.lengthFive

theorem smallComplement_blockThresholdSix_of_allPositiveFields
    (F : AllPositiveFields) :
    SmallComplement blockThresholdSix :=
  SmallComplementClosureW22.smallComplement_of_allPositiveFields
    blockThresholdSix F

theorem smallComplement_six_of_allPositiveFields
    (F : AllPositiveFields) :
    SmallComplement 6 := by
  simpa [blockThresholdSix, SmallComplementClosureW22.blockThresholdSix,
    SmallComplementConcreteBlocksW17.blockThresholdSix] using
    smallComplement_blockThresholdSix_of_allPositiveFields F

def smallLengthExactBlockTargetsOfAllPositiveFields
    (F : AllPositiveFields) :
    SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.smallLengthExactBlockTargetsOfSmallComplementSix
    (smallComplement_blockThresholdSix_of_allPositiveFields F)

theorem exactFiniteTargetsBelowSix_of_allPositiveFields
    (F : AllPositiveFields) :
    ExactFiniteTargetsBelowSix :=
  exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfAllPositiveFields F)

theorem smallComplement_blockThresholdSix_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallComplement blockThresholdSix :=
  SmallComplementClosureW22.smallComplement_six_of_allPositiveCertificateRows
    C

theorem smallComplement_six_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallComplement 6 := by
  simpa [blockThresholdSix, SmallComplementClosureW22.blockThresholdSix,
    SmallComplementConcreteBlocksW17.blockThresholdSix] using
    smallComplement_blockThresholdSix_of_allPositiveCertificateRows C

def smallLengthExactBlockTargetsOfAllPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.smallLengthExactBlockTargetsOfSmallComplementSix
    (smallComplement_blockThresholdSix_of_allPositiveCertificateRows C)

theorem exactFiniteTargetsBelowSix_of_allPositiveCertificateRows
    (C : AllPositiveCertificateRows) :
    ExactFiniteTargetsBelowSix :=
  exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfAllPositiveCertificateRows C)

theorem smallComplement_blockThresholdSix_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SmallComplement blockThresholdSix :=
  SmallComplementClosureW22.smallComplement_of_concreteValueMatrixFamily
    blockThresholdSix C

def smallLengthExactBlockTargetsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.smallLengthExactBlockTargetsOfSmallComplementSix
    (smallComplement_blockThresholdSix_of_concreteValueMatrixFamily C)

theorem exactFiniteTargetsBelowSix_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ExactFiniteTargetsBelowSix :=
  exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfConcreteValueMatrixFamily C)

theorem smallComplement_blockThresholdSix_of_candidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    SmallComplement blockThresholdSix :=
  SmallComplementClosureW22.smallComplement_of_candidateValueMatrixFamily
    blockThresholdSix C

def smallLengthExactBlockTargetsOfCandidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    SmallLengthExactBlockTargets :=
  SmallComplementClosureW22.smallLengthExactBlockTargetsOfSmallComplementSix
    (smallComplement_blockThresholdSix_of_candidateValueMatrixFamily C)

theorem exactFiniteTargetsBelowSix_of_candidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    ExactFiniteTargetsBelowSix :=
  exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfCandidateValueMatrixFamily C)

end

end SmallLengthExactTargetsInhabitationW23
end PachToth
end ErdosProblems1066
