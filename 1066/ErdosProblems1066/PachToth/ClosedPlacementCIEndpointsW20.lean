import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19
import ErdosProblems1066.PachToth.PachTothClosedPlacementAuditW19

set_option autoImplicit false

/-!
# W20 closed-placement CI endpoints

Alias-only theorem endpoints for the W19 explicit closed-placement route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementCIEndpointsW20

noncomputable section

open ClosedPlacementTargetWrappersW19
open PachTothClosedPlacementAuditW19

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_inputPackage :
    forall _ : ExplicitClosedPlacementProducerW19.InputPackage,
      forall k : Nat,
        0 < k -> ExplicitClosedPlacementProducerW19.ExactBlockTarget k :=
  ExplicitClosedPlacementProducerW19.InputPackage.targetUpperConstructionFiveSixteenAt_exactBlock

theorem targetUpperConstructionFiveSixteen_of_inputPackage :
    forall _ : ExplicitClosedPlacementProducerW19.InputPackage,
      ExplicitClosedPlacementProducerW19.ExactTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteen_of_inputPackage

theorem targetUpperConstructionFiveSixteenArbitrary_of_inputPackage :
    forall _ : ExplicitClosedPlacementProducerW19.InputPackage,
      ExplicitClosedPlacementProducerW19.ArbitraryTarget :=
  ExplicitClosedPlacementProducerW19.targetUpperConstructionFiveSixteenArbitrary_of_inputPackage

theorem targetUpperConstructionFiveSixteenAt_of_inputPackage :
    forall _ : ExplicitClosedPlacementProducerW19.InputPackage,
      forall n : Nat,
        ExplicitClosedPlacementProducerW19.FixedTarget n :=
  ExplicitClosedPlacementProducerW19.InputPackage.targetUpperConstructionFiveSixteenAt

theorem upper_bound_five_sixteen_arbitrary_of_inputPackage :
    forall _ : ExplicitClosedPlacementProducerW19.InputPackage,
      forall n : Nat,
        Exists fun C : _root_.UDConfig n =>
          forall s : Finset (Fin n), C.IsIndep s ->
            s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  ExplicitClosedPlacementProducerW19.InputPackage.upper_bound_five_sixteen_arbitrary

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_certificateFamily :
    forall _ :
        ClosedPlacementTargetWrappersW19.ExplicitClosedPlacementCertificateProducer,
      forall k : Nat,
        0 < k ->
          ClosedPlacementTargetWrappersW19.ExactBlockTarget k :=
  targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificates

theorem targetUpperConstructionFiveSixteen_of_certificateProducer :
    forall _ : ClosedPlacementTargetWrappersW19.ClosedPlacementCertificateProducer,
      ClosedPlacementTargetWrappersW19.ExactTarget :=
  w19_exact_target_of_certificate_producer

theorem targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates :
    forall _ :
        ClosedPlacementTargetWrappersW19.ExplicitClosedPlacementCertificateProducer,
      ClosedPlacementTargetWrappersW19.ExactTarget :=
  w19_exact_target_of_explicit_closed_placement_certificates

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates :
    forall _ :
        ArbitraryNClosedPlacementRouteW19.ExplicitClosedPlacementCertificateFamily,
      ArbitraryNClosedPlacementRouteW19.ArbitraryTarget :=
  w19_arbitrary_target_of_explicit_closed_placement_certificates

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitTransitionCertificates :
    forall _ :
        ArbitraryNClosedPlacementRouteW19.ExplicitTransitionClosedPlacementCertificateFamily,
      ArbitraryNClosedPlacementRouteW19.ArbitraryTarget :=
  w19_arbitrary_target_of_explicit_transition_closed_placement_certificates

theorem upper_bound_five_sixteen_arbitrary_of_explicitClosedPlacementCertificates :
    forall _ :
        ArbitraryNClosedPlacementRouteW19.ExplicitClosedPlacementCertificateFamily,
      forall n : Nat,
        Exists fun C : _root_.UDConfig n =>
          forall s : Finset (Fin n), C.IsIndep s ->
            s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  w19_upper_bound_arbitrary_of_explicit_closed_placement_certificates

theorem upper_bound_five_sixteen_arbitrary_of_explicitTransitionCertificates :
    forall _ :
        ArbitraryNClosedPlacementRouteW19.ExplicitTransitionClosedPlacementCertificateFamily,
      forall n : Nat,
        Exists fun C : _root_.UDConfig n =>
          forall s : Finset (Fin n), C.IsIndep s ->
            s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  w19_upper_bound_arbitrary_of_explicit_transition_closed_placement_certificates

end

end ClosedPlacementCIEndpointsW20
end PachToth
end ErdosProblems1066
