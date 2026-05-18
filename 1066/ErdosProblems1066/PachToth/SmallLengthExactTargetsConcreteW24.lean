import ErdosProblems1066.PachToth.SmallLengthExactTargetsInhabitationW23
import ErdosProblems1066.PachToth.SmallComplementExactBlocksW16
import ErdosProblems1066.PachToth.SmallComplementConcreteBlocksW17
import ErdosProblems1066.PachToth.FiniteGraph
import ErdosProblems1066.PachToth.SmallCaseCertificates
import ErdosProblems1066.PachToth.RemainderConstruction
import ErdosProblems1066.PachToth.ArbitraryNClosureCandidate
import ErdosProblems1066.PachToth.ArbitraryNExactRemainderClosure
import ErdosProblems1066.PachToth.SplitRealizationFinal

set_option autoImplicit false

/-!
# W24 concrete small-length exact targets

This module is a concrete facade over W23 and the arbitrary-`n` split route.
It packages the exact block sizes one through five, the checked finite
remainders, and the exact-chain constructors in the shapes consumed by
arbitrary-`n` split obligations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallLengthExactTargetsConcreteW24

open Arithmetic
open FiniteGraph

noncomputable section

abbrev ExactBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

abbrev ExactVertexTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

abbrev ExactVertexTargetsBelow (N0 : Nat) : Prop :=
  targetUpperConstructionFiveSixteenSmallUpTo N0

abbrev ExactArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactChainUpper (k : Nat) :=
  SplitSoundness.ExactChainUpper k

abbrev RemainderUpper (r : Nat) :=
  SplitSoundness.RemainderUpper r

abbrev RemainderBound (r : Nat) : Prop :=
  Exists fun C : _root_.UDConfig r =>
    forall s : Finset (Fin r), C.IsIndep s -> s.card <= ceilDiv r 3

abbrev SmallLengthExactBlockTargets :=
  SmallLengthExactTargetsInhabitationW23.SmallLengthExactBlockTargets

abbrev ExactFiniteTargetsBelowSix :=
  SmallLengthExactTargetsInhabitationW23.ExactFiniteTargetsBelowSix

abbrev ExactBlocksTwoThroughFive :=
  SmallLengthExactTargetsInhabitationW23.ExactBlocksTwoThroughFive

abbrev ConcreteOneBlockCertificate
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :=
  SmallLengthExactTargetsInhabitationW23.ConcreteOneBlockCertificate orientation

abbrev blockThresholdSix : Nat :=
  SmallLengthExactTargetsInhabitationW23.blockThresholdSix

abbrev ExactBlocksOneThroughFive : Prop :=
  ExactBlockTarget 1 ∧ ExactBlockTarget 2 ∧ ExactBlockTarget 3 ∧
    ExactBlockTarget 4 ∧ ExactBlockTarget 5

/-! ## Finite graph surface -/

theorem localIndependent_card_le_six
    (s : Finset LocalVertex) (hs : FiniteGraph.IsIndependent s) :
    s.card <= 6 :=
  SmallLengthExactTargetsInhabitationW23.finiteGraph_localIndependent_card_le_six
    s hs

theorem extractedSixSet_card :
    FiniteGraph.extractedSixSet.card = 6 :=
  SmallLengthExactTargetsInhabitationW23.finiteGraph_extractedSixSet_card

/-! ## Exact block targets one through five -/

def smallLengthExactBlockTargetsOfExactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    SmallLengthExactBlockTargets where
  lengthOne := H.1
  lengthTwo := H.2.1
  lengthThree := H.2.2.1
  lengthFour := H.2.2.2.1
  lengthFive := H.2.2.2.2

theorem exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlocksOneThroughFive :=
  ⟨C.lengthOne, C.lengthTwo, C.lengthThree, C.lengthFour, C.lengthFive⟩

theorem nonempty_smallLengthExactBlockTargets_iff_exactBlocksOneThroughFive :
    Nonempty SmallLengthExactBlockTargets <-> ExactBlocksOneThroughFive := by
  constructor
  · intro h
    rcases h with ⟨C⟩
    exact exactBlocksOneThroughFive_of_smallLengthExactBlockTargets C
  · intro H
    exact Nonempty.intro
      (smallLengthExactBlockTargetsOfExactBlocksOneThroughFive H)

theorem exactBlockTargetBelowSix_of_exactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    forall k : Nat, k < 6 -> 0 < k -> ExactBlockTarget k := by
  intro k hklt hkpos
  have hk :
      k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
    omega
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact H.1
  · exact H.2.1
  · exact H.2.2.1
  · exact H.2.2.2.1
  · exact H.2.2.2.2

theorem exactFiniteTargetsBelowSix_of_exactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    ExactFiniteTargetsBelowSix :=
  SmallLengthExactTargetsInhabitationW23.exactFiniteTargetsBelowSixOfSmallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfExactBlocksOneThroughFive H)

theorem exactBlockTarget_one_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    ExactBlockTarget 1 :=
  E 1
    (by
      simp [SmallLengthExactTargetsInhabitationW23.blockThresholdSix,
        SmallComplementClosureW22.blockThresholdSix,
        SmallComplementConcreteBlocksW17.blockThresholdSix])
    (by norm_num)

theorem exactBlockTarget_two_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    ExactBlockTarget 2 :=
  E 2
    (by
      simp [SmallLengthExactTargetsInhabitationW23.blockThresholdSix,
        SmallComplementClosureW22.blockThresholdSix,
        SmallComplementConcreteBlocksW17.blockThresholdSix])
    (by norm_num)

theorem exactBlockTarget_three_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    ExactBlockTarget 3 :=
  E 3
    (by
      simp [SmallLengthExactTargetsInhabitationW23.blockThresholdSix,
        SmallComplementClosureW22.blockThresholdSix,
        SmallComplementConcreteBlocksW17.blockThresholdSix])
    (by norm_num)

theorem exactBlockTarget_four_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    ExactBlockTarget 4 :=
  E 4
    (by
      simp [SmallLengthExactTargetsInhabitationW23.blockThresholdSix,
        SmallComplementClosureW22.blockThresholdSix,
        SmallComplementConcreteBlocksW17.blockThresholdSix])
    (by norm_num)

theorem exactBlockTarget_five_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    ExactBlockTarget 5 :=
  E 5
    (by
      simp [SmallLengthExactTargetsInhabitationW23.blockThresholdSix,
        SmallComplementClosureW22.blockThresholdSix,
        SmallComplementConcreteBlocksW17.blockThresholdSix])
    (by norm_num)

theorem exactBlocksOneThroughFive_of_exactFiniteTargetsBelowSix
    (E : ExactFiniteTargetsBelowSix) :
    ExactBlocksOneThroughFive :=
  ⟨exactBlockTarget_one_of_exactFiniteTargetsBelowSix E,
    exactBlockTarget_two_of_exactFiniteTargetsBelowSix E,
    exactBlockTarget_three_of_exactFiniteTargetsBelowSix E,
    exactBlockTarget_four_of_exactFiniteTargetsBelowSix E,
    exactBlockTarget_five_of_exactFiniteTargetsBelowSix E⟩

theorem exactFiniteTargetsBelowSix_iff_exactBlocksOneThroughFive :
    ExactFiniteTargetsBelowSix <-> ExactBlocksOneThroughFive := by
  constructor
  · exact exactBlocksOneThroughFive_of_exactFiniteTargetsBelowSix
  · exact exactFiniteTargetsBelowSix_of_exactBlocksOneThroughFive

theorem exactBlockTarget_one_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlockTarget 1 :=
  C.lengthOne

theorem exactBlockTarget_two_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlockTarget 2 :=
  C.lengthTwo

theorem exactBlockTarget_three_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlockTarget 3 :=
  C.lengthThree

theorem exactBlockTarget_four_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlockTarget 4 :=
  C.lengthFour

theorem exactBlockTarget_five_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactBlockTarget 5 :=
  C.lengthFive

theorem exactBlockTarget_one_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactBlockTarget 1 :=
  SmallLengthExactTargetsInhabitationW23.exactFiniteTarget_one_of_concreteOneBlockCertificate
    oneBlock

def exactBlocksOneThroughFiveOfExactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (SmallLengthExactTargetsInhabitationW23.smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
      blocks oneBlock)

theorem exactFiniteTargetsBelowSix_of_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactFiniteTargetsBelowSix :=
  exactFiniteTargetsBelowSix_of_exactBlocksOneThroughFive
    (exactBlocksOneThroughFiveOfExactBlocksTwoThroughFive blocks oneBlock)

/-! ## Exact-chain constructors for split obligations -/

theorem exactBlockTarget_of_exactChainUpper
    {k : Nat} (chain : ExactChainUpper k) :
    ExactBlockTarget k := by
  refine ⟨chain.config, ?_⟩
  intro s hs
  have hbound := chain.independent_card_le_five_mul s hs
  have hceil : ceilDiv (5 * (16 * k)) 16 = 5 * k := by
    unfold ceilDiv
    omega
  simpa [ExactBlockTarget, hceil] using hbound

def exactChainUpperOfExactBlockTarget
    {k : Nat} (H : ExactBlockTarget k) :
    ExactChainUpper k :=
  SmallCaseCertificates.exactChainUpperOfExactBlockTarget H

theorem nonempty_exactChainUpper_iff_exactBlockTarget
    (k : Nat) :
    Nonempty (ExactChainUpper k) <-> ExactBlockTarget k := by
  constructor
  · intro h
    rcases h with ⟨chain⟩
    exact exactBlockTarget_of_exactChainUpper chain
  · intro H
    exact Nonempty.intro (exactChainUpperOfExactBlockTarget H)

def exactChainUpperBelowSix_of_exactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    forall k : Nat, k < 6 -> 0 < k -> ExactChainUpper k := by
  intro k hklt hkpos
  exact exactChainUpperOfExactBlockTarget
    (exactBlockTargetBelowSix_of_exactBlocksOneThroughFive H k hklt hkpos)

def exactChainSmallCaseCertificatesBelowSix_of_exactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    SmallCaseReduction.ExactChainSmallCaseCertificates (16 * 6) :=
  SmallCaseCertificates.exactChainSmallCaseCertificatesBelowBlockThresholdOfExactBlockTargets
    6 (exactBlockTargetBelowSix_of_exactBlocksOneThroughFive H)

theorem exactVertexTargetsBelow_ninetySix_of_exactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    ExactVertexTargetsBelow (16 * 6) :=
  SmallCaseReduction.targetUpperConstructionFiveSixteenSmallUpTo_of_exactChainCertificates
    (exactChainSmallCaseCertificatesBelowSix_of_exactBlocksOneThroughFive H)

theorem exactVertexTargetsBelow_ninetySix_of_smallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    ExactVertexTargetsBelow (16 * 6) :=
  exactVertexTargetsBelow_ninetySix_of_exactBlocksOneThroughFive
    (exactBlocksOneThroughFive_of_smallLengthExactBlockTargets C)

/-! ## Checked finite remainders -/

theorem remainderBound_of_lt_sixteen
    {r : Nat} (hr : r < 16) :
    RemainderBound r :=
  RemainderConstruction.exists_remainder_config_mod_sixteen hr

def remainderUpperOfRemainderBound
    {r : Nat} (H : RemainderBound r) :
    RemainderUpper r where
  config := Classical.choose H
  independent_card_le_ceil_third := Classical.choose_spec H

theorem remainderBound_of_remainderUpper
    {r : Nat} (R : RemainderUpper r) :
    RemainderBound r :=
  ⟨R.config, R.independent_card_le_ceil_third⟩

theorem nonempty_remainderUpper_iff_remainderBound
    (r : Nat) :
    Nonempty (RemainderUpper r) <-> RemainderBound r := by
  constructor
  · intro h
    rcases h with ⟨R⟩
    exact remainderBound_of_remainderUpper R
  · intro H
    exact Nonempty.intro (remainderUpperOfRemainderBound H)

def checkedRemainderUpperOfLtSixteen
    {r : Nat} (hr : r < 16) :
    RemainderUpper r :=
  ArbitraryNExactRemainderClosure.checkedRemainderUpperOfLtSixteen hr

theorem nonempty_remainderUpper_of_lt_sixteen
    {r : Nat} (hr : r < 16) :
    Nonempty (RemainderUpper r) :=
  (nonempty_remainderUpper_iff_remainderBound r).2
    (remainderBound_of_lt_sixteen hr)

theorem exactVertexTarget_remainder_of_lt_sixteen
    {r : Nat} (hr : r < 16) :
    ExactVertexTarget r :=
  SmallCaseCertificates.targetUpperConstructionFiveSixteenAt_of_lt_sixteen hr

theorem exactVertexTargetsBelow_sixteen :
    ExactVertexTargetsBelow 16 :=
  SmallLengthExactTargetsInhabitationW23.exactVertexTargetsBelow_sixteen

/-! ## Arbitrary-`n` split reductions -/

theorem exactVertexTarget_of_exactTarget_checkedRemainder_divMod
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    ExactVertexTarget n :=
  ArbitraryNExactRemainderClosure.targetUpperConstructionFiveSixteenAt_of_exactTarget_checkedRemainder_divMod
    Hexact n

theorem exactArbitraryTarget_of_exactTarget_checkedRemainder
    (Hexact : targetUpperConstructionFiveSixteen) :
    ExactArbitraryTarget :=
  ArbitraryNExactRemainderClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget_checkedRemainder
    Hexact

theorem exactArbitraryTarget_of_eventually_exactBlocksOneThroughFive
    (Hlarge :
      forall n : Nat, 16 * 6 <= n -> ExactVertexTarget n)
    (Hsmall : ExactBlocksOneThroughFive) :
    ExactArbitraryTarget :=
  ArbitraryNClosureCandidate.arbitrary_of_eventually_exactBlockSmallCases
    6 Hlarge
    (exactBlockTargetBelowSix_of_exactBlocksOneThroughFive Hsmall)

theorem exactArbitraryTarget_of_eventually_smallLengthExactBlockTargets
    (Hlarge :
      forall n : Nat, 16 * 6 <= n -> ExactVertexTarget n)
    (C : SmallLengthExactBlockTargets) :
    ExactArbitraryTarget :=
  exactArbitraryTarget_of_eventually_exactBlocksOneThroughFive
    Hlarge
    (exactBlocksOneThroughFive_of_smallLengthExactBlockTargets C)

theorem exactArbitraryTarget_of_eventually_exactFiniteTargetsBelowSix
    (Hlarge :
      forall n : Nat, 16 * 6 <= n -> ExactVertexTarget n)
    (E : ExactFiniteTargetsBelowSix) :
    ExactArbitraryTarget :=
  exactArbitraryTarget_of_eventually_exactBlocksOneThroughFive
    Hlarge
    (exactBlocksOneThroughFive_of_exactFiniteTargetsBelowSix E)

theorem exactArbitraryTarget_of_eventually_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (Hlarge :
      forall n : Nat, 16 * 6 <= n -> ExactVertexTarget n)
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    ExactArbitraryTarget :=
  exactArbitraryTarget_of_eventually_exactBlocksOneThroughFive
    Hlarge
    (exactBlocksOneThroughFiveOfExactBlocksTwoThroughFive blocks oneBlock)

end

end SmallLengthExactTargetsConcreteW24
end PachToth
end ErdosProblems1066
