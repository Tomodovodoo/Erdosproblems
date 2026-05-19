import ErdosProblems1066.PachToth.SmallLengthExactTargetsInhabitationW23
import ErdosProblems1066.PachToth.SmallComplementExactBlocksW16
import ErdosProblems1066.PachToth.SmallComplementConcreteBlocksW17
import ErdosProblems1066.PachToth.ExactBlocksTwoThroughFiveProducerW18
import ErdosProblems1066.PachToth.ClosedPlacementSmallKCertificatesW19
import ErdosProblems1066.PachToth.TransitionAlternativeW13
import ErdosProblems1066.PachToth.FiniteGraph
import ErdosProblems1066.PachToth.DeformedPlacement
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

abbrev PeriodCandidateFamily :=
  ExactBlocksTwoThroughFiveProducerW18.PeriodCandidateFamily

abbrev CandidateSmallRowValueRows (period : PeriodCandidateFamily) :=
  ExactBlocksTwoThroughFiveProducerW18.CandidateSmallRowValueRows period

abbrev FlexibleGeneratedClosureFamily :=
  ClosedPlacementSmallKCertificatesW19.FlexibleGeneratedClosureFamily

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

theorem concreteOneBlockCertificate_absent
    {orientation : Fin 1 -> OrientationData.BlockOrientation} :
    Not (ConcreteOneBlockCertificate orientation) := by
  intro oneBlock
  exact
    TransitionAlternativeW13.concreteTransitionObligations_oneBlock_closure_blocked
      ExactBlockCertificateW13.oneBlockPositive orientation oneBlock.closure

theorem not_exists_concreteOneBlockCertificate :
    Not
      (Exists fun orientation : Fin 1 -> OrientationData.BlockOrientation =>
        ConcreteOneBlockCertificate orientation) := by
  intro h
  cases h with
  | intro orientation oneBlock =>
      exact concreteOneBlockCertificate_absent (orientation := orientation) oneBlock

theorem exactBlockTarget_of_deformedClosedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    ExactBlockTarget k := by
  refine Exists.intro P.config ?_
  intro s hs
  have hbound : s.card <= 5 * k :=
    IndexedChain.independent_card_le_five_mul hk
      P.toIndexedChainRealization s hs
  have hceil : ceilDiv (5 * (16 * k)) 16 = 5 * k := by
    unfold ceilDiv
    omega
  simpa [hceil] using hbound

theorem exactBlockTarget_one_of_deformedClosedPlacement
    {hpos : 0 < 1}
    (P : DeformedPlacement.ClosedPlacement 1 hpos) :
    ExactBlockTarget 1 := by
  simpa using exactBlockTarget_of_deformedClosedPlacement P

theorem deformedLengthOnePositive : 0 < 1 := by
  norm_num

abbrev DeformedLengthOneSource : Type :=
  DeformedPlacement.ClosedPlacement 1 deformedLengthOnePositive

abbrev DeformedLengthOneGeometry : Type :=
  DeformedPlacement.LengthOneGeometry

theorem exactBlockTarget_one_of_deformedLengthOneSource
    (source : DeformedLengthOneSource) :
    ExactBlockTarget 1 :=
  exactBlockTarget_one_of_deformedClosedPlacement source

def deformedLengthOneSourceOfGeometry
    (geometry : DeformedLengthOneGeometry) :
    DeformedLengthOneSource :=
  geometry.toClosedPlacement

theorem exactBlockTarget_one_of_deformedLengthOneGeometry
    (geometry : DeformedLengthOneGeometry) :
    ExactBlockTarget 1 :=
  exactBlockTarget_one_of_deformedLengthOneSource
    (deformedLengthOneSourceOfGeometry geometry)

theorem nonempty_deformedLengthOneSource_iff_deformedLengthOneGeometry :
    Nonempty DeformedLengthOneSource <->
      Nonempty DeformedLengthOneGeometry := by
  simpa [DeformedLengthOneSource, DeformedLengthOneGeometry,
    deformedLengthOnePositive] using
    (DeformedPlacement.nonempty_closedPlacement_one_iff_lengthOneGeometry
      (hpos := deformedLengthOnePositive))

def deformedLengthOneSourceOfSmallExplicitTransitionCertificates
    (C :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    DeformedLengthOneSource := by
  have hproof :
      ClosedPlacementSmallKCertificatesW19.onePositive =
        deformedLengthOnePositive :=
    Subsingleton.elim _ _
  cases hproof
  exact C.lengthOne.toClosedPlacement

theorem nonempty_deformedLengthOneSource_of_smallExplicitTransitionCertificates
    (H :
      Nonempty
        ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    Nonempty DeformedLengthOneSource := by
  rcases H with ⟨C⟩
  exact
    ⟨deformedLengthOneSourceOfSmallExplicitTransitionCertificates C⟩

def exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates
    (C :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    ExactBlocksTwoThroughFive where
  lengthTwo := by
    simpa using
      ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
        C.lengthTwo
  lengthThree := by
    simpa using
      ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
        C.lengthThree
  lengthFourFive :=
    { lengthFour := by
        simpa using
          ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
            C.lengthFour
      lengthFive := by
        simpa using
          ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
            C.lengthFive }

theorem nonempty_exactBlocksTwoThroughFive_of_smallExplicitTransitionCertificates
    (H :
      Nonempty
        ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    Nonempty ExactBlocksTwoThroughFive := by
  rcases H with ⟨C⟩
  exact
    ⟨exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates C⟩

def deformedLengthOneSourceOfSmallExplicitTransitionCertificateSource
    (S :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    DeformedLengthOneSource := by
  have hproof :
      ClosedPlacementSmallKCertificatesW19.onePositive =
        deformedLengthOnePositive :=
    Subsingleton.elim _ _
  cases hproof
  exact S.lengthOneClosedPlacement

def exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificateSource
    (S :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    ExactBlocksTwoThroughFive where
  lengthTwo := by
    simpa using
      ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
        S.lengthTwo
  lengthThree := by
    simpa using
      ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
        S.lengthThree
  lengthFourFive :=
    { lengthFour := by
        simpa using
          ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
            S.lengthFour
      lengthFive := by
        simpa using
          ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
            S.lengthFive }

theorem nonempty_deformedLengthOneSource_of_smallExplicitTransitionCertificateSource
    (H :
      Nonempty
        ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    Nonempty DeformedLengthOneSource := by
  rcases H with ⟨S⟩
  exact
    ⟨deformedLengthOneSourceOfSmallExplicitTransitionCertificateSource S⟩

theorem nonempty_exactBlocksTwoThroughFive_of_smallExplicitTransitionCertificateSource
    (H :
      Nonempty
        ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    Nonempty ExactBlocksTwoThroughFive := by
  rcases H with ⟨S⟩
  exact
    ⟨exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificateSource S⟩

theorem exactLocalPoint_missing_collapsedConnector_T2_2_T1_1 :
    Not
      (_root_.eucDist
        (ExactLocalGeometry.localPoint LocalVertex.T2_2)
        (ExactLocalGeometry.localPoint LocalVertex.T1_1) = 1) := by
  intro hunit
  have hunit' :
      Geometry.Distance.eucDist
        (ExactLocalGeometry.localPoint LocalVertex.T2_2)
        (ExactLocalGeometry.localPoint LocalVertex.T1_1) = 1 := by
    simpa using hunit
  have hsq :
      (((ExactLocalGeometry.localNorm4 LocalVertex.T2_2
          LocalVertex.T1_1 : Int) : Real) / 4) = 1 := by
    rw [<- ExactLocalGeometry.local_sqDist' LocalVertex.T2_2
      LocalVertex.T1_1]
    exact
      (Geometry.Distance.eucDist_eq_one_iff
        (ExactLocalGeometry.localPoint LocalVertex.T2_2)
        (ExactLocalGeometry.localPoint LocalVertex.T1_1)).1 hunit'
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, LocalVertex.T, LocalVertex.T2_2,
    LocalVertex.T1_1] at hsq

theorem not_deformedLengthOneGeometry_exactLocalPoint :
    Not
      (Exists fun geometry : DeformedLengthOneGeometry =>
        geometry.point = ExactLocalGeometry.localPoint) := by
  intro h
  rcases h with ⟨geometry, hpoint⟩
  have hconn :
      CrossBlock.NextConnector LocalVertex.T2_2 LocalVertex.T1_1 := by
    decide
  have hunit :=
    geometry.collapsed_connector_edges_unit
      LocalVertex.T2_2 LocalVertex.T1_1 hconn
  exact exactLocalPoint_missing_collapsedConnector_T2_2_T1_1
    (by simpa [hpoint] using hunit)

def smallLengthExactBlockTargetsOfLengthOneAndExactBlocksTwoThroughFive
    (lengthOne : ExactBlockTarget 1)
    (blocks : ExactBlocksTwoThroughFive) :
    SmallLengthExactBlockTargets where
  lengthOne := lengthOne
  lengthTwo := blocks.lengthTwo
  lengthThree := blocks.lengthThree
  lengthFour := blocks.lengthFourFive.lengthFour
  lengthFive := blocks.lengthFourFive.lengthFive

def exactBlocksOneThroughFiveOfLengthOneAndExactBlocksTwoThroughFive
    (lengthOne : ExactBlockTarget 1)
    (blocks : ExactBlocksTwoThroughFive) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfLengthOneAndExactBlocksTwoThroughFive
      lengthOne blocks)

theorem nonempty_smallLengthExactBlockTargets_of_lengthOne_and_exactBlocksTwoThroughFive
    (lengthOne : ExactBlockTarget 1)
    (blocks : ExactBlocksTwoThroughFive) :
    Nonempty SmallLengthExactBlockTargets :=
  Nonempty.intro
    (smallLengthExactBlockTargetsOfLengthOneAndExactBlocksTwoThroughFive
      lengthOne blocks)

def smallLengthExactBlockTargetsOfDeformedLengthOneAndExactBlocksTwoThroughFive
    {hpos : 0 < 1}
    (placement : DeformedPlacement.ClosedPlacement 1 hpos)
    (blocks : ExactBlocksTwoThroughFive) :
    SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsOfLengthOneAndExactBlocksTwoThroughFive
    (exactBlockTarget_one_of_deformedClosedPlacement placement) blocks

def exactBlocksOneThroughFiveOfDeformedLengthOneAndExactBlocksTwoThroughFive
    {hpos : 0 < 1}
    (placement : DeformedPlacement.ClosedPlacement 1 hpos)
    (blocks : ExactBlocksTwoThroughFive) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfDeformedLengthOneAndExactBlocksTwoThroughFive
      placement blocks)

theorem nonempty_smallLengthExactBlockTargets_of_deformedLengthOne_and_exactBlocksTwoThroughFive
    {hpos : 0 < 1}
    (placement : DeformedPlacement.ClosedPlacement 1 hpos)
    (blocks : ExactBlocksTwoThroughFive) :
    Nonempty SmallLengthExactBlockTargets :=
  Nonempty.intro
    (smallLengthExactBlockTargetsOfDeformedLengthOneAndExactBlocksTwoThroughFive
      placement blocks)

def smallLengthExactBlockTargetsOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    (source : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsOfLengthOneAndExactBlocksTwoThroughFive
    (exactBlockTarget_one_of_deformedLengthOneSource source) blocks

def exactBlocksOneThroughFiveOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    (source : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    (smallLengthExactBlockTargetsOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
      source blocks)

theorem exactBlocksOneThroughFive_of_deformedLengthOneSource_and_exactBlocksTwoThroughFive
    (source : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFiveOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    source blocks

theorem exactBlocksOneThroughFive_of_nonempty_deformedLengthOneSource_and_exactBlocksTwoThroughFive
    (Hone : Nonempty DeformedLengthOneSource)
    (Hblocks : Nonempty ExactBlocksTwoThroughFive) :
    ExactBlocksOneThroughFive := by
  cases Hone with
  | intro source =>
      cases Hblocks with
      | intro blocks =>
          exact
            exactBlocksOneThroughFive_of_deformedLengthOneSource_and_exactBlocksTwoThroughFive
              source blocks

structure DeformedLengthOneExactBlocksTwoThroughFiveSource where
  lengthOne : DeformedLengthOneSource
  blocksTwoThroughFive : ExactBlocksTwoThroughFive

namespace DeformedLengthOneExactBlocksTwoThroughFiveSource

def toSmallLengthExactBlockTargets
    (S : DeformedLengthOneExactBlocksTwoThroughFiveSource) :
    SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsOfDeformedLengthOneSourceAndExactBlocksTwoThroughFive
    S.lengthOne S.blocksTwoThroughFive

def exactBlocksOneThroughFive
    (S : DeformedLengthOneExactBlocksTwoThroughFiveSource) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    S.toSmallLengthExactBlockTargets

end DeformedLengthOneExactBlocksTwoThroughFiveSource

def deformedLengthOneExactBlocksTwoThroughFiveSourceOfSources
    (lengthOne : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    DeformedLengthOneExactBlocksTwoThroughFiveSource where
  lengthOne := lengthOne
  blocksTwoThroughFive := blocks

theorem nonempty_deformedLengthOneExactBlocksTwoThroughFiveSource_iff_sources :
    Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource <->
      Nonempty DeformedLengthOneSource /\
        Nonempty ExactBlocksTwoThroughFive := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro S =>
        exact And.intro
          (Nonempty.intro S.lengthOne)
          (Nonempty.intro S.blocksTwoThroughFive)
  case mpr =>
    intro h
    cases h.1 with
    | intro lengthOne =>
        cases h.2 with
        | intro blocks =>
            exact Nonempty.intro
              (deformedLengthOneExactBlocksTwoThroughFiveSourceOfSources
                lengthOne blocks)

theorem nonempty_smallLengthExactBlockTargets_of_deformedLengthOneExactBlocksTwoThroughFiveSource
    (H : Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource) :
    Nonempty SmallLengthExactBlockTargets := by
  cases H with
  | intro S =>
      exact Nonempty.intro S.toSmallLengthExactBlockTargets

theorem exactBlocksOneThroughFive_of_deformedLengthOneExactBlocksTwoThroughFiveSource
    (S : DeformedLengthOneExactBlocksTwoThroughFiveSource) :
    ExactBlocksOneThroughFive :=
  S.exactBlocksOneThroughFive

def deformedLengthOneExactBlocksTwoThroughFiveSourceOfSmallExplicitTransitionCertificates
    (C :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    DeformedLengthOneExactBlocksTwoThroughFiveSource :=
  deformedLengthOneExactBlocksTwoThroughFiveSourceOfSources
    (deformedLengthOneSourceOfSmallExplicitTransitionCertificates C)
    (exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificates C)

def deformedLengthOneExactBlocksTwoThroughFiveSourceOfSmallExplicitTransitionCertificateSource
    (S :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    DeformedLengthOneExactBlocksTwoThroughFiveSource :=
  deformedLengthOneExactBlocksTwoThroughFiveSourceOfSources
    (deformedLengthOneSourceOfSmallExplicitTransitionCertificateSource S)
    (exactBlocksTwoThroughFiveOfSmallExplicitTransitionCertificateSource S)

theorem nonempty_deformedLengthOneExactBlocksTwoThroughFiveSource_of_smallExplicitTransitionCertificates
    (H :
      Nonempty
        ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource := by
  cases H with
  | intro C =>
      exact
        Nonempty.intro
          (deformedLengthOneExactBlocksTwoThroughFiveSourceOfSmallExplicitTransitionCertificates
            C)

theorem nonempty_deformedLengthOneExactBlocksTwoThroughFiveSource_of_smallExplicitTransitionCertificateSource
    (H :
      Nonempty
        ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource) :
    Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource := by
  cases H with
  | intro S =>
      exact
        Nonempty.intro
          (deformedLengthOneExactBlocksTwoThroughFiveSourceOfSmallExplicitTransitionCertificateSource
            S)

def deformedLengthOneExactBlocksTwoThroughFiveSourceOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    DeformedLengthOneExactBlocksTwoThroughFiveSource :=
  deformedLengthOneExactBlocksTwoThroughFiveSourceOfSmallExplicitTransitionCertificateSource
    (ClosedPlacementSmallKCertificatesW19.smallExplicitTransitionCertificateSourceOfFlexibleGeneratedClosureFamily
      F)

theorem nonempty_deformedLengthOneExactBlocksTwoThroughFiveSource_of_flexibleGeneratedClosureFamily
    (H : Nonempty FlexibleGeneratedClosureFamily) :
    Nonempty DeformedLengthOneExactBlocksTwoThroughFiveSource := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (deformedLengthOneExactBlocksTwoThroughFiveSourceOfFlexibleGeneratedClosureFamily
            F)

structure SmallExactBlockTargetCertificate where
  lengthOne : ExactBlockTarget 1
  blocksTwoThroughFive : ExactBlocksTwoThroughFive

namespace SmallExactBlockTargetCertificate

def toSmallLengthExactBlockTargets
    (C : SmallExactBlockTargetCertificate) :
    SmallLengthExactBlockTargets :=
  smallLengthExactBlockTargetsOfLengthOneAndExactBlocksTwoThroughFive
    C.lengthOne C.blocksTwoThroughFive

def exactBlocksOneThroughFive
    (C : SmallExactBlockTargetCertificate) :
    ExactBlocksOneThroughFive :=
  exactBlocksOneThroughFive_of_smallLengthExactBlockTargets
    C.toSmallLengthExactBlockTargets

end SmallExactBlockTargetCertificate

def smallExactBlockTargetCertificateOfExactBlocksOneThroughFive
    (H : ExactBlocksOneThroughFive) :
    SmallExactBlockTargetCertificate where
  lengthOne := H.1
  blocksTwoThroughFive :=
    { lengthTwo := H.2.1
      lengthThree := H.2.2.1
      lengthFourFive :=
        { lengthFour := H.2.2.2.1
          lengthFive := H.2.2.2.2 } }

theorem nonempty_smallExactBlockTargetCertificate_iff_exactBlocksOneThroughFive :
    Nonempty SmallExactBlockTargetCertificate <-> ExactBlocksOneThroughFive := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro C =>
        exact C.exactBlocksOneThroughFive
  case mpr =>
    intro H
    exact Nonempty.intro
      (smallExactBlockTargetCertificateOfExactBlocksOneThroughFive H)

theorem nonempty_smallExactBlockTargetCertificate_iff_lengthOne_and_blocksTwoThroughFive :
    Nonempty SmallExactBlockTargetCertificate <->
      ExactBlockTarget 1 /\ Nonempty ExactBlocksTwoThroughFive := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro C =>
        exact And.intro C.lengthOne (Nonempty.intro C.blocksTwoThroughFive)
  case mpr =>
    intro h
    cases h.2 with
    | intro blocks =>
        exact Nonempty.intro
          { lengthOne := h.1
            blocksTwoThroughFive := blocks }

theorem nonempty_smallLengthExactBlockTargets_iff_smallExactBlockTargetCertificate :
    Nonempty SmallLengthExactBlockTargets <->
      Nonempty SmallExactBlockTargetCertificate :=
  Iff.trans nonempty_smallLengthExactBlockTargets_iff_exactBlocksOneThroughFive
    nonempty_smallExactBlockTargetCertificate_iff_exactBlocksOneThroughFive.symm

def exactBlocksTwoThroughFiveOfCandidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    (rows : CandidateSmallRowValueRows period) :
    ExactBlocksTwoThroughFive :=
  ExactBlocksTwoThroughFiveProducerW18.exactBlocksOfCandidateSmallRowValueRows
    rows

def smallExactBlockTargetCertificateOfLengthOneAndCandidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    (lengthOne : ExactBlockTarget 1)
    (rows : CandidateSmallRowValueRows period) :
    SmallExactBlockTargetCertificate where
  lengthOne := lengthOne
  blocksTwoThroughFive :=
    exactBlocksTwoThroughFiveOfCandidateSmallRowValueRows rows

def smallLengthExactBlockTargetsOfLengthOneAndCandidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    (lengthOne : ExactBlockTarget 1)
    (rows : CandidateSmallRowValueRows period) :
    SmallLengthExactBlockTargets :=
  (smallExactBlockTargetCertificateOfLengthOneAndCandidateSmallRowValueRows
    lengthOne rows).toSmallLengthExactBlockTargets

theorem exactBlocksOneThroughFive_of_lengthOne_and_candidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    (lengthOne : ExactBlockTarget 1)
    (rows : CandidateSmallRowValueRows period) :
    ExactBlocksOneThroughFive :=
  (smallExactBlockTargetCertificateOfLengthOneAndCandidateSmallRowValueRows
    lengthOne rows).exactBlocksOneThroughFive

theorem nonempty_smallLengthExactBlockTargets_of_lengthOne_and_candidateSmallRowValueRows
    {period : PeriodCandidateFamily}
    (lengthOne : ExactBlockTarget 1)
    (rows : CandidateSmallRowValueRows period) :
    Nonempty SmallLengthExactBlockTargets :=
  Nonempty.intro
    (smallLengthExactBlockTargetsOfLengthOneAndCandidateSmallRowValueRows
      lengthOne rows)

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

theorem exactBlockTargetBelow_of_exactBlocksOneThroughFive
    {K0 : Nat} (hK0 : K0 <= 6)
    (H : ExactBlocksOneThroughFive) :
    forall k : Nat, k < K0 -> 0 < k -> ExactBlockTarget k := by
  intro k hklt hkpos
  exact
    exactBlockTargetBelowSix_of_exactBlocksOneThroughFive H k
      (Nat.lt_of_lt_of_le hklt hK0) hkpos

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

theorem exactArbitraryTarget_of_eventually_le_six_exactBlocksOneThroughFive
    {K0 : Nat} (hK0 : K0 <= 6)
    (Hlarge :
      forall n : Nat, 16 * K0 <= n -> ExactVertexTarget n)
    (Hsmall : ExactBlocksOneThroughFive) :
    ExactArbitraryTarget :=
  ArbitraryNClosureCandidate.arbitrary_of_eventually_exactBlockSmallCases
    K0 Hlarge
    (exactBlockTargetBelow_of_exactBlocksOneThroughFive hK0 Hsmall)

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

theorem exactArbitraryTarget_of_eventually_deformedLengthOneSource_and_exactBlocksTwoThroughFive
    (Hlarge :
      forall n : Nat, 16 * 6 <= n -> ExactVertexTarget n)
    (source : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    ExactArbitraryTarget :=
  exactArbitraryTarget_of_eventually_exactBlocksOneThroughFive
    Hlarge
    (exactBlocksOneThroughFive_of_deformedLengthOneSource_and_exactBlocksTwoThroughFive
      source blocks)

theorem exactArbitraryTarget_of_eventually_le_six_deformedLengthOneSource_and_exactBlocksTwoThroughFive
    {K0 : Nat} (hK0 : K0 <= 6)
    (Hlarge :
      forall n : Nat, 16 * K0 <= n -> ExactVertexTarget n)
    (source : DeformedLengthOneSource)
    (blocks : ExactBlocksTwoThroughFive) :
    ExactArbitraryTarget :=
  exactArbitraryTarget_of_eventually_le_six_exactBlocksOneThroughFive
    hK0 Hlarge
    (exactBlocksOneThroughFive_of_deformedLengthOneSource_and_exactBlocksTwoThroughFive
      source blocks)

end

end SmallLengthExactTargetsConcreteW24
end PachToth
end ErdosProblems1066
