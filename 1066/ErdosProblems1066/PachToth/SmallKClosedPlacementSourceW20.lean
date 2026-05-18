import ErdosProblems1066.PachToth.ClosedPlacementSmallKCertificatesW19
import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19

set_option autoImplicit false

/-!
# W20 small-k closed-placement sources

This file strengthens the W19 small facade by naming source packages for the
positive block counts below six.  A source may carry explicit closed-placement
certificates, a global certificate producer, or the exact one-block plus
two-through-five finite rows already available from the small-complement
modules.
-/

namespace ErdosProblems1066
namespace PachToth
namespace SmallKClosedPlacementSourceW20

noncomputable section

abbrev ExplicitClosedPlacementCertificate (k : Nat) (hk : 0 < k) :=
  ClosedPlacementSmallKCertificatesW19.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitTransitionClosedPlacementCertificate (k : Nat) (hk : 0 < k) :=
  ClosedPlacementSmallKCertificatesW19.ExplicitTransitionClosedPlacementCertificate
    k hk

abbrev ExplicitClosedPlacementCertificateProducer :=
  ClosedPlacementTargetWrappersW19.ExplicitClosedPlacementCertificateProducer

abbrev ClosedPlacementCertificateProducer :=
  ClosedPlacementTargetWrappersW19.ClosedPlacementCertificateProducer

abbrev SmallLengthExactBlockTargets :=
  ClosedPlacementSmallKCertificatesW19.SmallLengthExactBlockTargets

abbrev SmallComplement (K0 : Nat) : Prop :=
  SmallComplementConcreteBlocksW17.SmallComplement K0

abbrev ExactBlocksTwoThroughFive :=
  ClosedPlacementSmallKCertificatesW19.ExactBlocksTwoThroughFive

abbrev CandidateSmallRowValueRows :=
  ClosedPlacementSmallKCertificatesW19.CandidateSmallRowValueRows

abbrev ConcreteOneBlockCertificate
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :=
  ClosedPlacementSmallKCertificatesW19.ConcreteOneBlockCertificate orientation

abbrev PeriodCandidateFamily :=
  ExactBlocksTwoThroughFiveProducerW18.PeriodCandidateFamily

abbrev RoleHingedPeriodSearchFamily :=
  ConcreteValueCertificateExamples.RoleHingedPeriodSearchFamily

abbrev NonConnectorValueMatrix :=
  ConcreteValueCertificateExamples.NonConnectorValueMatrix

theorem onePositive : 0 < 1 :=
  ClosedPlacementSmallKCertificatesW19.onePositive

theorem twoPositive : 0 < 2 :=
  ClosedPlacementSmallKCertificatesW19.twoPositive

theorem threePositive : 0 < 3 :=
  ClosedPlacementSmallKCertificatesW19.threePositive

theorem fourPositive : 0 < 4 :=
  ClosedPlacementSmallKCertificatesW19.fourPositive

theorem fivePositive : 0 < 5 :=
  ClosedPlacementSmallKCertificatesW19.fivePositive

/-! ## Small explicit certificate packages -/

structure SmallExplicitClosedPlacementCertificates where
  lengthOne : ExplicitClosedPlacementCertificate 1 onePositive
  lengthTwo : ExplicitClosedPlacementCertificate 2 twoPositive
  lengthThree : ExplicitClosedPlacementCertificate 3 threePositive
  lengthFour : ExplicitClosedPlacementCertificate 4 fourPositive
  lengthFive : ExplicitClosedPlacementCertificate 5 fivePositive

namespace SmallExplicitClosedPlacementCertificates

def toSmallLengthExactBlockTargets
    (C : SmallExplicitClosedPlacementCertificates) :
    SmallLengthExactBlockTargets where
  lengthOne :=
    ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_certificate
        C.lengthOne
  lengthTwo :=
    ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_certificate
        C.lengthTwo
  lengthThree :=
    ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_certificate
        C.lengthThree
  lengthFour :=
    ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_certificate
        C.lengthFour
  lengthFive :=
    ClosedPlacementSmallKCertificatesW19.targetUpperConstructionFiveSixteenAt_of_explicit_certificate
        C.lengthFive

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (C : SmallExplicitClosedPlacementCertificates)
    (k : Nat) (hklt : k < 6) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  C.toSmallLengthExactBlockTargets.exactBlock k hklt hk

theorem targetUpperConstructionFiveSixteenSmallUpTo_six
    (C : SmallExplicitClosedPlacementCertificates) :
    targetUpperConstructionFiveSixteenSmallUpTo
      (16 * SmallComplementConcreteBlocksW17.blockThresholdSix) := by
  simpa [SmallComplementConcreteBlocksW17.blockThresholdSix] using
    C.toSmallLengthExactBlockTargets.smallUpToSix

theorem smallComplement_six
    (C : SmallExplicitClosedPlacementCertificates) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  SmallComplementConcreteBlocksW17.smallComplement_six_of_smallLengthExactBlockTargets
    C.toSmallLengthExactBlockTargets

end SmallExplicitClosedPlacementCertificates

def smallExplicitClosedPlacementCertificatesOfTransitionCertificates
    (C :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    SmallExplicitClosedPlacementCertificates where
  lengthOne := C.lengthOne.toExplicitClosedPlacementCertificate
  lengthTwo := C.lengthTwo.toExplicitClosedPlacementCertificate
  lengthThree := C.lengthThree.toExplicitClosedPlacementCertificate
  lengthFour := C.lengthFour.toExplicitClosedPlacementCertificate
  lengthFive := C.lengthFive.toExplicitClosedPlacementCertificate

def smallExplicitClosedPlacementCertificatesOfProducer
    (P : ExplicitClosedPlacementCertificateProducer) :
    SmallExplicitClosedPlacementCertificates where
  lengthOne := P 1 onePositive
  lengthTwo := P 2 twoPositive
  lengthThree := P 3 threePositive
  lengthFour := P 4 fourPositive
  lengthFive := P 5 fivePositive

def smallExplicitClosedPlacementCertificatesOfAllPositiveNonConnectorFields
    (C :
      ClosedPlacementSmallKCertificatesW19.AllPositiveNonConnectorFields) :
    SmallExplicitClosedPlacementCertificates :=
  smallExplicitClosedPlacementCertificatesOfTransitionCertificates
    (ClosedPlacementSmallKCertificatesW19.smallExplicitTransitionCertificatesOfAllPositiveNonConnectorFields
      C)

def smallExplicitClosedPlacementCertificatesOfConcreteValueMatrixFamily
    (C :
      ClosedPlacementSmallKCertificatesW19.ConcreteValueMatrixFamily) :
    SmallExplicitClosedPlacementCertificates :=
  smallExplicitClosedPlacementCertificatesOfTransitionCertificates
    (ClosedPlacementSmallKCertificatesW19.smallExplicitTransitionCertificatesOfConcreteValueMatrixFamily
      C)

def smallExplicitClosedPlacementCertificatesOfCandidateValueMatrixFamily
    (C :
      ClosedPlacementSmallKCertificatesW19.CandidateValueMatrixFamily) :
    SmallExplicitClosedPlacementCertificates :=
  smallExplicitClosedPlacementCertificatesOfTransitionCertificates
    (ClosedPlacementSmallKCertificatesW19.smallExplicitTransitionCertificatesOfCandidateValueMatrixFamily
      C)

/-! ## Normalized exact small-k sources -/

structure SmallKExactClosedPlacementSource where
  exactBlocks : SmallLengthExactBlockTargets

namespace SmallKExactClosedPlacementSource

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (S : SmallKExactClosedPlacementSource)
    (k : Nat) (hklt : k < 6) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  S.exactBlocks.exactBlock k hklt hk

theorem targetUpperConstructionFiveSixteenSmallUpTo_six
    (S : SmallKExactClosedPlacementSource) :
    targetUpperConstructionFiveSixteenSmallUpTo
      (16 * SmallComplementConcreteBlocksW17.blockThresholdSix) := by
  simpa [SmallComplementConcreteBlocksW17.blockThresholdSix] using
    S.exactBlocks.smallUpToSix

theorem smallComplement_six
    (S : SmallKExactClosedPlacementSource) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  SmallComplementConcreteBlocksW17.smallComplement_six_of_smallLengthExactBlockTargets
    S.exactBlocks

def ofSmallLengthExactBlockTargets
    (C : SmallLengthExactBlockTargets) :
    SmallKExactClosedPlacementSource where
  exactBlocks := C

def ofSmallExplicitClosedPlacementCertificates
    (C : SmallExplicitClosedPlacementCertificates) :
    SmallKExactClosedPlacementSource where
  exactBlocks := C.toSmallLengthExactBlockTargets

def ofSmallExplicitTransitionCertificates
    (C :
      ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificates) :
    SmallKExactClosedPlacementSource :=
  ofSmallExplicitClosedPlacementCertificates
    (smallExplicitClosedPlacementCertificatesOfTransitionCertificates C)

def ofProducer
    (P : ExplicitClosedPlacementCertificateProducer) :
    SmallKExactClosedPlacementSource :=
  ofSmallExplicitClosedPlacementCertificates
    (smallExplicitClosedPlacementCertificatesOfProducer P)

def ofAllPositiveNonConnectorFields
    (C :
      ClosedPlacementSmallKCertificatesW19.AllPositiveNonConnectorFields) :
    SmallKExactClosedPlacementSource :=
  ofSmallExplicitClosedPlacementCertificates
    (smallExplicitClosedPlacementCertificatesOfAllPositiveNonConnectorFields C)

def ofConcreteValueMatrixFamily
    (C :
      ClosedPlacementSmallKCertificatesW19.ConcreteValueMatrixFamily) :
    SmallKExactClosedPlacementSource :=
  ofSmallExplicitClosedPlacementCertificates
    (smallExplicitClosedPlacementCertificatesOfConcreteValueMatrixFamily C)

def ofCandidateValueMatrixFamily
    (C :
      ClosedPlacementSmallKCertificatesW19.CandidateValueMatrixFamily) :
    SmallKExactClosedPlacementSource :=
  ofSmallExplicitClosedPlacementCertificates
    (smallExplicitClosedPlacementCertificatesOfCandidateValueMatrixFamily C)

end SmallKExactClosedPlacementSource

/-! ## Global producers as small-k sources -/

structure GlobalExplicitClosedPlacementSource where
  certificate : ExplicitClosedPlacementCertificateProducer

namespace GlobalExplicitClosedPlacementSource

def certificateProducer
    (S : GlobalExplicitClosedPlacementSource) :
    ClosedPlacementCertificateProducer where
  certificate := S.certificate

def toSmallExplicitClosedPlacementCertificates
    (S : GlobalExplicitClosedPlacementSource) :
    SmallExplicitClosedPlacementCertificates :=
  smallExplicitClosedPlacementCertificatesOfProducer S.certificate

def toSmallKExactClosedPlacementSource
    (S : GlobalExplicitClosedPlacementSource) :
    SmallKExactClosedPlacementSource :=
  SmallKExactClosedPlacementSource.ofProducer S.certificate

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (S : GlobalExplicitClosedPlacementSource)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificates
      S.certificate k hk

theorem targetUpperConstructionFiveSixteen
    (S : GlobalExplicitClosedPlacementSource) :
    targetUpperConstructionFiveSixteen :=
  ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteen_of_certificateProducer
      S.certificateProducer

theorem smallComplement_six
    (S : GlobalExplicitClosedPlacementSource) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  S.toSmallKExactClosedPlacementSource.smallComplement_six

end GlobalExplicitClosedPlacementSource

def globalSourceOfInputPackage
    (P : ExplicitClosedPlacementProducerW19.InputPackage) :
    GlobalExplicitClosedPlacementSource where
  certificate := P.explicitClosedPlacementCertificate

def smallKSourceOfInputPackage
    (P : ExplicitClosedPlacementProducerW19.InputPackage) :
    SmallKExactClosedPlacementSource :=
  (globalSourceOfInputPackage P).toSmallKExactClosedPlacementSource

theorem smallComplement_six_of_inputPackage
    (P : ExplicitClosedPlacementProducerW19.InputPackage) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  (smallKSourceOfInputPackage P).smallComplement_six

/-! ## Exact block packages from small finite rows -/

structure ExactBlockSourcePackage where
  orientation : Fin 1 -> OrientationData.BlockOrientation
  oneBlock : ConcreteOneBlockCertificate orientation
  blocksTwoThroughFive : ExactBlocksTwoThroughFive

namespace ExactBlockSourcePackage

def toSmallLengthExactBlockTargets
    (P : ExactBlockSourcePackage) :
    SmallLengthExactBlockTargets :=
  ClosedPlacementSmallKCertificatesW19.smallLengthExactBlockTargetsOfExactBlocksTwoThroughFive
      P.blocksTwoThroughFive P.oneBlock

def toSmallKExactClosedPlacementSource
    (P : ExactBlockSourcePackage) :
    SmallKExactClosedPlacementSource where
  exactBlocks := P.toSmallLengthExactBlockTargets

theorem smallComplement_six
    (P : ExactBlockSourcePackage) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  P.toSmallKExactClosedPlacementSource.smallComplement_six

theorem smallComplement_two
    (P : ExactBlockSourcePackage) :
    SmallComplementExactBlocksW16.SmallComplement 2 :=
  ClosedPlacementSmallKCertificatesW19.smallComplement_two_of_concreteOneBlockCertificate
    P.oneBlock

end ExactBlockSourcePackage

structure CandidateSmallRowExactSourcePackage where
  period : PeriodCandidateFamily
  orientation : Fin 1 -> OrientationData.BlockOrientation
  oneBlock : ConcreteOneBlockCertificate orientation
  rows : CandidateSmallRowValueRows period

namespace CandidateSmallRowExactSourcePackage

def lengthOneValueMatrix
    (P : CandidateSmallRowExactSourcePackage) :
    NonConnectorValueMatrix
      P.period.toRoleHingedPeriodSearchFamily 1
      ConcreteValueCertificateExamples.onePositive :=
  ConcreteValueCertificateExamples.lengthOneMatrix
    P.period.toRoleHingedPeriodSearchFamily

theorem noUpperTrianglePosition_lengthOne
    (_P : CandidateSmallRowExactSourcePackage)
    (p : ConcreteValueCertificateExamples.UpperTrianglePosition 1) :
    False :=
  ConcreteValueCertificateExamples.noUpperTrianglePosition_length_one p

def exactBlocksTwoThroughFive
    (P : CandidateSmallRowExactSourcePackage) :
    ExactBlocksTwoThroughFive :=
  ExactBlocksTwoThroughFiveProducerW18.exactBlocksOfCandidateSmallRowValueRows
    P.rows

def toExactBlockSourcePackage
    (P : CandidateSmallRowExactSourcePackage) :
    ExactBlockSourcePackage where
  orientation := P.orientation
  oneBlock := P.oneBlock
  blocksTwoThroughFive := P.exactBlocksTwoThroughFive

def toSmallKExactClosedPlacementSource
    (P : CandidateSmallRowExactSourcePackage) :
    SmallKExactClosedPlacementSource :=
  P.toExactBlockSourcePackage.toSmallKExactClosedPlacementSource

theorem smallComplement_six
    (P : CandidateSmallRowExactSourcePackage) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  P.toSmallKExactClosedPlacementSource.smallComplement_six

theorem smallComplement_six_direct
    (P : CandidateSmallRowExactSourcePackage) :
    SmallComplement SmallComplementConcreteBlocksW17.blockThresholdSix :=
  ClosedPlacementSmallKCertificatesW19.smallComplement_six_of_candidateSmallRowValueRows
      P.rows P.oneBlock

end CandidateSmallRowExactSourcePackage

end

end SmallKClosedPlacementSourceW20
end PachToth
end ErdosProblems1066
