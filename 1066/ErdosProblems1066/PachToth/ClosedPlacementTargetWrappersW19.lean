import ErdosProblems1066.PachToth.ClosedChainReduction

set_option autoImplicit false

/-!
# W19 closed-placement target wrappers

This module is a thin exact-target facade for the explicit closed-placement
route.  It keeps the endpoint conditional on an actual producer of explicit
closed-placement certificates for every positive block count.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementTargetWrappersW19

open ClosedChainReduction

noncomputable section

abbrev ExplicitClosedPlacementCertificate (k : Nat) (hk : 0 < k) :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitClosedPlacementCertificateProducer : Type :=
  forall (k : Nat) (hk : 0 < k), ExplicitClosedPlacementCertificate k hk

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ExactBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

private theorem exactBlockTargetOfCertificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    ExactBlockTarget k := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificate
      C

/-- A concrete producer surface for exact closed-placement certificates. -/
structure ClosedPlacementCertificateProducer where
  certificate : ExplicitClosedPlacementCertificateProducer

namespace ClosedPlacementCertificateProducer

/-- The certificate produced at one positive block count gives the exact
`16 * k` target at that block count. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : ClosedPlacementCertificateProducer) (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k := by
  exact
    exactBlockTargetOfCertificate (P.certificate k hk)

/-- A producer of explicit closed-placement certificates for all positive
block counts gives the exact `16 * k` Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (P : ClosedPlacementCertificateProducer) :
    ExactTarget := by
  exact
    ClosedChainReduction.targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
      P.certificate

end ClosedPlacementCertificateProducer

/-- Repackage a raw certificate-producing function as the W19 producer
surface. -/
def producerOfExplicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateProducer) :
    ClosedPlacementCertificateProducer where
  certificate := H

/-- A single explicit closed-placement certificate gives the exact block
target at its block count. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (C : ExplicitClosedPlacementCertificate k hk) :
    ExactBlockTarget k := by
  exact
    exactBlockTargetOfCertificate C

/-- A raw producer function gives the exact block target at any positive
block count. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateProducer)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k := by
  exact
    (producerOfExplicitClosedPlacementCertificates H)
      |>.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact target wrapper from the concrete W19 certificate-producer surface. -/
theorem targetUpperConstructionFiveSixteen_of_certificateProducer
    (P : ClosedPlacementCertificateProducer) :
    ExactTarget := by
  exact P.targetUpperConstructionFiveSixteen

/-- Exact target wrapper from a raw producer of explicit closed-placement
certificates. -/
theorem targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
    (H : ExplicitClosedPlacementCertificateProducer) :
    ExactTarget := by
  exact
    ClosedChainReduction.targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
      H

/-- Alias for callers that name the dependency as a certificate producer. -/
theorem targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificateProducer
    (H : ExplicitClosedPlacementCertificateProducer) :
    ExactTarget := by
  exact targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates H

end

end ClosedPlacementTargetWrappersW19
end PachToth
end ErdosProblems1066
