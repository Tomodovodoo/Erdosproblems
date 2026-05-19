import ErdosProblems1066.PachToth.ClosedChainConstruction
import ErdosProblems1066.PachToth.ClosedPlacementExactRouteW14
import ErdosProblems1066.PachToth.ExactTargetCandidateClosure
import ErdosProblems1066.PachToth.ExactBlocksTwoThroughFiveProducerW18
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition
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

abbrev R2 := Prod Real Real

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

abbrev FlexibleGeneratedClosureData :=
  FlexibleExactLocalTransition.GeneratedClosureData

abbrev FlexibleGeneratedClosureFamily :=
  FlexibleExactLocalTransition.GeneratedClosureFamily

abbrev MinimalExactTargetCertificate :=
  ExactTargetCandidateClosure.MinimalExactTargetCertificate

abbrev DeformedLengthOneGeometry :=
  DeformedPlacement.LengthOneGeometry

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

def explicitTransitionCertificateOfFlexibleGeneratedClosureData
    {k : Nat} {hk : 0 < k}
    (G : FlexibleGeneratedClosureData k hk) :
    ExplicitTransitionClosedPlacementCertificate k hk :=
  G.toExplicitTransitionClosedPlacementCertificate

def lengthOneExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ExplicitTransitionClosedPlacementCertificate 1 onePositive :=
  explicitTransitionCertificateOfFlexibleGeneratedClosureData
    (F.data 1 onePositive)

/-- The extra datum needed to fill the transition-certificate `lengthOne`
field from the deformed one-block geometry.  The closed-placement route only
needs `geometry`; the transition-certificate facade also needs a certified
self-transition for that same point map. -/
structure DeformedLengthOneTransitionGeometry where
  geometry : DeformedLengthOneGeometry
  transition :
    OrientationData.TransitionCertificate geometry.point geometry.point

def lengthOneClosedPlacementOfDeformedGeometry
    (geometry : DeformedLengthOneGeometry) :
    DeformedPlacement.ClosedPlacement 1 onePositive := by
  have hproof :
      onePositive = DeformedPlacement.lengthOnePositive :=
    Subsingleton.elim onePositive DeformedPlacement.lengthOnePositive
  cases hproof
  exact geometry.toClosedPlacement

theorem targetUpperConstructionFiveSixteenAt_one_of_deformedGeometry
    (geometry : DeformedLengthOneGeometry) :
    targetUpperConstructionFiveSixteenAt (16 * 1) :=
  targetUpperConstructionFiveSixteenAt_of_closedPlacement
    (lengthOneClosedPlacementOfDeformedGeometry geometry)

def lengthOneExplicitTransitionCertificateOfDeformedTransitionGeometry
    (G : DeformedLengthOneTransitionGeometry) :
    ExplicitTransitionClosedPlacementCertificate 1 onePositive where
  point := fun _ v => G.geometry.point v
  transition := by
    intro _
    simpa using G.transition
  separated := by
    intro i u j v hne
    have hij : i = j := Subsingleton.elim i j
    have huv : Ne u v := by
      intro huv
      exact hne (by
        cases hij
        cases huv
        rfl)
    simpa using G.geometry.separated u v huv
  same_block_edges_unit := by
    intro _ u v huv hadj
    exact G.geometry.same_block_edges_unit u v huv hadj

def deformedLengthOneTransitionGeometryOfExplicitTransitionCertificate
    (C : ExplicitTransitionClosedPlacementCertificate 1 onePositive) :
    DeformedLengthOneTransitionGeometry where
  geometry :=
    DeformedPlacement.lengthOneGeometryOfClosedPlacement C.toClosedPlacement
  transition := by
    have hsucc :
        Arithmetic.cyclicSucc onePositive (0 : Fin 1) = (0 : Fin 1) :=
      Subsingleton.elim _ _
    simpa [DeformedPlacement.lengthOneGeometryOfClosedPlacement, hsucc] using
      C.transition 0

theorem nonempty_lengthOneExplicitTransitionCertificate_iff_deformedTransitionGeometry :
    Nonempty (ExplicitTransitionClosedPlacementCertificate 1 onePositive) <->
      Nonempty DeformedLengthOneTransitionGeometry := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro C =>
        exact Nonempty.intro
          (deformedLengthOneTransitionGeometryOfExplicitTransitionCertificate C)
  case mpr =>
    intro h
    cases h with
    | intro G =>
        exact Nonempty.intro
          (lengthOneExplicitTransitionCertificateOfDeformedTransitionGeometry G)

def lengthTwoExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ExplicitTransitionClosedPlacementCertificate 2 twoPositive :=
  explicitTransitionCertificateOfFlexibleGeneratedClosureData
    (F.data 2 twoPositive)

def lengthThreeExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ExplicitTransitionClosedPlacementCertificate 3 threePositive :=
  explicitTransitionCertificateOfFlexibleGeneratedClosureData
    (F.data 3 threePositive)

def lengthFourExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ExplicitTransitionClosedPlacementCertificate 4 fourPositive :=
  explicitTransitionCertificateOfFlexibleGeneratedClosureData
    (F.data 4 fourPositive)

def lengthFiveExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    ExplicitTransitionClosedPlacementCertificate 5 fivePositive :=
  explicitTransitionCertificateOfFlexibleGeneratedClosureData
    (F.data 5 fivePositive)

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

structure SmallExplicitTransitionCertificateSource where
  lengthOne : DeformedLengthOneTransitionGeometry
  lengthTwo :
    ExplicitTransitionClosedPlacementCertificate 2 twoPositive
  lengthThree :
    ExplicitTransitionClosedPlacementCertificate 3 threePositive
  lengthFour :
    ExplicitTransitionClosedPlacementCertificate 4 fourPositive
  lengthFive :
    ExplicitTransitionClosedPlacementCertificate 5 fivePositive

namespace SmallExplicitTransitionCertificateSource

def lengthOneClosedPlacement
    (S : SmallExplicitTransitionCertificateSource) :
    DeformedPlacement.ClosedPlacement 1 onePositive :=
  lengthOneClosedPlacementOfDeformedGeometry S.lengthOne.geometry

def toSmallExplicitTransitionCertificates
    (S : SmallExplicitTransitionCertificateSource) :
    SmallExplicitTransitionCertificates where
  lengthOne :=
    lengthOneExplicitTransitionCertificateOfDeformedTransitionGeometry
      S.lengthOne
  lengthTwo := S.lengthTwo
  lengthThree := S.lengthThree
  lengthFour := S.lengthFour
  lengthFive := S.lengthFive

def toSmallLengthExactBlockTargets
    (S : SmallExplicitTransitionCertificateSource) :
    SmallLengthExactBlockTargets where
  lengthOne :=
    targetUpperConstructionFiveSixteenAt_of_closedPlacement
      S.lengthOneClosedPlacement
  lengthTwo :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      S.lengthTwo
  lengthThree :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      S.lengthThree
  lengthFour :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      S.lengthFour
  lengthFive :=
    targetUpperConstructionFiveSixteenAt_of_explicit_transition_certificate
      S.lengthFive

theorem smallComplement_six
    (S : SmallExplicitTransitionCertificateSource) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix := by
  exact
    SmallComplementConcreteBlocksW17.smallComplement_six_of_smallLengthExactBlockTargets
      S.toSmallLengthExactBlockTargets

end SmallExplicitTransitionCertificateSource

def smallExplicitTransitionCertificateSourceOfSmallExplicitTransitionCertificates
    (C : SmallExplicitTransitionCertificates) :
    SmallExplicitTransitionCertificateSource where
  lengthOne :=
    deformedLengthOneTransitionGeometryOfExplicitTransitionCertificate
      C.lengthOne
  lengthTwo := C.lengthTwo
  lengthThree := C.lengthThree
  lengthFour := C.lengthFour
  lengthFive := C.lengthFive

theorem nonempty_smallExplicitTransitionCertificates_iff_source :
    Nonempty SmallExplicitTransitionCertificates <->
      Nonempty SmallExplicitTransitionCertificateSource := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro C =>
        exact Nonempty.intro
          (smallExplicitTransitionCertificateSourceOfSmallExplicitTransitionCertificates
            C)
  case mpr =>
    intro h
    cases h with
    | intro S =>
        exact Nonempty.intro S.toSmallExplicitTransitionCertificates

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

def smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    SmallExplicitTransitionCertificates where
  lengthOne :=
    lengthOneExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily F
  lengthTwo :=
    lengthTwoExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily F
  lengthThree :=
    lengthThreeExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily F
  lengthFour :=
    lengthFourExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily F
  lengthFive :=
    lengthFiveExplicitTransitionCertificateOfFlexibleGeneratedClosureFamily F

def smallExplicitTransitionCertificateSourceOfFlexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    SmallExplicitTransitionCertificateSource :=
  smallExplicitTransitionCertificateSourceOfSmallExplicitTransitionCertificates
    (smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily F)

theorem nonempty_smallExplicitTransitionCertificateSource_of_flexibleGeneratedClosureFamily
    (H : Nonempty FlexibleGeneratedClosureFamily) :
    Nonempty SmallExplicitTransitionCertificateSource := by
  cases H with
  | intro F =>
      exact
        Nonempty.intro
          (smallExplicitTransitionCertificateSourceOfFlexibleGeneratedClosureFamily F)

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

theorem smallComplement_six_of_flexibleGeneratedClosureFamily
    (F : FlexibleGeneratedClosureFamily) :
    SmallComplementConcreteBlocksW17.SmallComplement
      SmallComplementConcreteBlocksW17.blockThresholdSix :=
  (smallExplicitTransitionCertificatesOfFlexibleGeneratedClosureFamily F)
    |>.smallComplement_six

abbrev ConcreteExactLocalSameResidualRow : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (RoleHingeConcreteSearch.samePlaceNext source u)
              (RoleHingeConcreteSearch.samePlaceNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

theorem no_concreteExactLocalSameResidualRow :
    Not ConcreteExactLocalSameResidualRow :=
  RoleHingeExactLocalFinite.not_samePlaceNext_full_nonPortPair_rest

theorem not_minimalExactTargetCertificate_currentExactLocalRoute :
    Not (Nonempty MinimalExactTargetCertificate) :=
  ExactTargetCandidateClosure.not_minimalExactTargetCertificate

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
