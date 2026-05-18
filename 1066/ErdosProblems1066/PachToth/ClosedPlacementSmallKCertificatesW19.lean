import ErdosProblems1066.PachToth.ClosedChainConstruction
import ErdosProblems1066.PachToth.ClosedPlacementExactRouteW14
import ErdosProblems1066.PachToth.ExactBlocksTwoThroughFiveProducerW18
import ErdosProblems1066.PachToth.SmallComplementConcreteBlocksW17

set_option autoImplicit false

/-!
# W19 small closed-placement certificate facade

This file records only checked adapters.  A closed placement, an explicit
closed-placement certificate, a successor-compatible orbit, or finite
role-hinged/generated data gives the exact `16 * k` target through the existing
closed-placement route.  For the supported small split, the five positive block
counts are gathered into the existing `SmallLengthExactBlockTargets` and hence
the W17 small-complement statements.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementSmallKCertificatesW19

open FiniteGraph

noncomputable section

abbrev ExplicitClosedPlacementCertificate :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate

abbrev ExplicitTransitionClosedPlacementCertificate :=
  ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate

abbrev SuccessorCompatibleCyclicPointOrbit :=
  ClosedChainExistence.SuccessorCompatibleCyclicPointOrbit

abbrev IsometricSuccessorCompatibleCyclicPointOrbit :=
  ClosedChainExistence.IsometricSuccessorCompatibleCyclicPointOrbit

abbrev RoleHingedGeneratedClosureData :=
  GeneratedMetricClosure.RoleHingedGeneratedClosureData

abbrev RoleHingedCandidateCertificate :=
  FiniteSearchCertificate.RoleHingedCandidateCertificate

abbrev AllPositiveNonConnectorFields :=
  FiniteCertificateObligationsW12.AllPositiveNonConnectorFields

abbrev ConcreteValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev CandidateValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily

abbrev SmallLengthExactBlockTargets :=
  SmallLengthClosureW11.SmallLengthExactBlockTargets

abbrev ExactBlocksTwoThroughFive :=
  SmallComplementConcreteBlocksW17.ExactBlocksTwoThroughFive

abbrev CandidateSmallRowValueRows :=
  ExactBlocksTwoThroughFiveProducerW18.CandidateSmallRowValueRows

abbrev ConcreteOneBlockCertificate :=
  ExactBlockCertificateW13.ConcreteOneBlockCertificate

theorem onePositive : 0 < 1 := by
  decide

theorem twoPositive : 0 < 2 := by
  decide

theorem threePositive : 0 < 3 := by
  decide

theorem fourPositive : 0 < 4 := by
  decide

theorem fivePositive : 0 < 5 := by
  decide

/-! ## Generic closed-placement target adapters -/

theorem targetUpperConstructionFiveSixteenAt_of_closedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    ClosedPlacementExactRouteW14.targetUpperConstructionFiveSixteenAt_of_closedPlacement
      hk P

theorem targetUpperConstructionFiveSixteenAt_of_explicit_certificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact targetUpperConstructionFiveSixteenAt_of_closedPlacement C.toClosedPlacement

theorem targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitTransitionClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact targetUpperConstructionFiveSixteenAt_of_closedPlacement C.toClosedPlacement

theorem targetUpperConstructionFiveSixteenAt_of_closedChainPlacement
    {k : Nat} {hk : 0 < k}
    (P : PlacementBridge.ClosedChainPlacement k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_explicit_certificate
      (ClosedChainConstruction.explicitCertificateOfClosedChainPlacement P)

theorem targetUpperConstructionFiveSixteenAt_of_orientedClosedChainPlacement
    {k : Nat} {hk : 0 < k}
    (P : OrientationData.OrientedClosedChainPlacement k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      (ClosedChainConstruction.explicitTransitionCertificateOfOrientedClosedChainPlacement
        P)

theorem targetUpperConstructionFiveSixteenAt_of_successorCompatibleOrbit
    {k : Nat} {hk : 0 < k}
    (O : SuccessorCompatibleCyclicPointOrbit k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact targetUpperConstructionFiveSixteenAt_of_closedPlacement O.toClosedPlacement

theorem targetUpperConstructionFiveSixteenAt_of_isometricSuccessorCompatibleOrbit
    {k : Nat} {hk : 0 < k}
    (O : IsometricSuccessorCompatibleCyclicPointOrbit k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact targetUpperConstructionFiveSixteenAt_of_closedPlacement O.toClosedPlacement

/-! ## Generated and finite certificate surfaces -/

def explicitTransitionCertificateOfRoleHingedGeneratedClosureData
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  G.toExplicitTransitionClosedPlacementCertificate

theorem targetUpperConstructionFiveSixteenAt_of_roleHingedGeneratedClosureData
    {k : Nat} {hk : 0 < k}
    (G : RoleHingedGeneratedClosureData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      (explicitTransitionCertificateOfRoleHingedGeneratedClosureData G)

def explicitTransitionCertificateOfRoleHingedCandidateCertificate
    {T : FiniteSearchCertificate.RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    ExplicitTransitionClosedPlacementCertificate C.data.k C.data.hk :=
  C.toRoleHingedGeneratedClosureData.toExplicitTransitionClosedPlacementCertificate

theorem targetUpperConstructionFiveSixteenAt_of_roleHingedCandidateCertificate
    {T : FiniteSearchCertificate.RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    targetUpperConstructionFiveSixteenAt (16 * C.data.k) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      (explicitTransitionCertificateOfRoleHingedCandidateCertificate C)

def explicitTransitionCertificateOfAllPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  GeneratedSeparationInterface.explicitTransitionClosedPlacementCertificate_reduced
    C.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (C.orientation k hk)
    (C.period.generatedPeriod k hk)
    (C.reducedMetricHypotheses k hk)

theorem targetUpperConstructionFiveSixteenAt_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      (explicitTransitionCertificateOfAllPositiveNonConnectorFields C k hk)

def explicitTransitionCertificateOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionCertificateOfAllPositiveNonConnectorFields
    (FiniteCertificateInstantiationW13.fieldsOfConcreteValueMatrixFamily C)
    k hk

def explicitTransitionCertificateOfCandidateValueMatrixFamily
    (C : CandidateValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  explicitTransitionCertificateOfAllPositiveNonConnectorFields
    (FiniteCertificateInstantiationW13.fieldsOfCandidateValueMatrixFamily C)
    k hk

/-! ## The supported small positive block split -/

structure SmallExplicitTransitionCertificates where
  lengthOne :
    ExplicitTransitionClosedPlacementCertificate 1 onePositive
  lengthTwo :
    ExplicitTransitionClosedPlacementCertificate 2 twoPositive
  lengthThree :
    ExplicitTransitionClosedPlacementCertificate 3 threePositive
  lengthFour :
    ExplicitTransitionClosedPlacementCertificate 4 fourPositive
  lengthFive :
    ExplicitTransitionClosedPlacementCertificate 5 fivePositive

namespace SmallExplicitTransitionCertificates

def toSmallLengthExactBlockTargets
    (C : SmallExplicitTransitionCertificates) :
    SmallLengthExactBlockTargets where
  lengthOne :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      C.lengthOne
  lengthTwo :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      C.lengthTwo
  lengthThree :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      C.lengthThree
  lengthFour :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      C.lengthFour
  lengthFive :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      C.lengthFive

theorem targetUpperConstructionFiveSixteenSmallUpTo_six
    (C : SmallExplicitTransitionCertificates) :
    targetUpperConstructionFiveSixteenSmallUpTo
      (16 * SmallComplementConcreteBlocksW17.blockThresholdSix) := by
  simpa [SmallComplementConcreteBlocksW17.blockThresholdSix] using
    C.toSmallLengthExactBlockTargets.smallUpToSix

theorem smallComplement_six
    (C : SmallExplicitTransitionCertificates) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix := by
  exact
    SmallComplementConcreteBlocksW17.smallComplement_six_of_smallLengthExactBlockTargets
      C.toSmallLengthExactBlockTargets

end SmallExplicitTransitionCertificates

def smallExplicitTransitionCertificatesOfAllPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    SmallExplicitTransitionCertificates where
  lengthOne :=
    explicitTransitionCertificateOfAllPositiveNonConnectorFields C 1
      onePositive
  lengthTwo :=
    explicitTransitionCertificateOfAllPositiveNonConnectorFields C 2
      twoPositive
  lengthThree :=
    explicitTransitionCertificateOfAllPositiveNonConnectorFields C 3
      threePositive
  lengthFour :=
    explicitTransitionCertificateOfAllPositiveNonConnectorFields C 4
      fourPositive
  lengthFive :=
    explicitTransitionCertificateOfAllPositiveNonConnectorFields C 5
      fivePositive

def smallExplicitTransitionCertificatesOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SmallExplicitTransitionCertificates :=
  smallExplicitTransitionCertificatesOfAllPositiveNonConnectorFields
    (FiniteCertificateInstantiationW13.fieldsOfConcreteValueMatrixFamily C)

def smallExplicitTransitionCertificatesOfCandidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    SmallExplicitTransitionCertificates :=
  smallExplicitTransitionCertificatesOfAllPositiveNonConnectorFields
    (FiniteCertificateInstantiationW13.fieldsOfCandidateValueMatrixFamily C)

theorem smallComplement_six_of_allPositiveNonConnectorFields
    (C : AllPositiveNonConnectorFields) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix :=
  (smallExplicitTransitionCertificatesOfAllPositiveNonConnectorFields C)
    |>.smallComplement_six

theorem smallComplement_six_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix :=
  (smallExplicitTransitionCertificatesOfConcreteValueMatrixFamily C)
    |>.smallComplement_six

theorem smallComplement_six_of_candidateValueMatrixFamily
    (C : CandidateValueMatrixFamily) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix :=
  (smallExplicitTransitionCertificatesOfCandidateValueMatrixFamily C)
    |>.smallComplement_six

/-! ## Existing exact-block split, sharpened to the same small facade -/

theorem targetUpperConstructionFiveSixteenAt_one_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ConcreteOneBlockCertificate orientation) :
    targetUpperConstructionFiveSixteenAt (16 * 1) := by
  simpa using
    ExactBlockCertificateW13.targetUpperConstructionFiveSixteenAt_of_concreteOneBlockCertificate
      C

def smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallLengthExactBlockTargets :=
  blocks.toSmallLengthExactBlockTargets oneBlock

theorem smallComplement_six_of_exactBlocksTwoThroughFive
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (blocks : ExactBlocksTwoThroughFive)
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix :=
  blocks.smallComplement_six oneBlock

theorem smallComplement_two_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallComplementExactBlocksW16.SmallComplement 2 := by
  simpa using
    SmallComplementExactBlocksW16.smallComplement_two_of_concreteOneBlockCertificate
      oneBlock

def smallLengthExactBlockTargetsOfCandidateSmallRowValueRows
    {period : ExactBlocksTwoThroughFiveProducerW18.PeriodCandidateFamily}
    (smallRows : CandidateSmallRowValueRows period)
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallLengthExactBlockTargets :=
  (ExactBlocksTwoThroughFiveProducerW18.exactBlocksOfCandidateSmallRowValueRows
    smallRows)
      |>.toSmallLengthExactBlockTargets oneBlock

theorem smallComplement_six_of_candidateSmallRowValueRows
    {period : ExactBlocksTwoThroughFiveProducerW18.PeriodCandidateFamily}
    (smallRows : CandidateSmallRowValueRows period)
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (oneBlock : ConcreteOneBlockCertificate orientation) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix := by
  exact
    (ExactBlocksTwoThroughFiveProducerW18.exactBlocksOfCandidateSmallRowValueRows
      smallRows)
        |>.smallComplement_six oneBlock

end

end ClosedPlacementSmallKCertificatesW19
end PachToth
end ErdosProblems1066
