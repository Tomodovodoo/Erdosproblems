import ErdosProblems1066.W18IntegrationLedger
import ErdosProblems1066.PachToth.PachTothW18FinalGateAttempt
import ErdosProblems1066.PachToth.ArbitraryNClosedPlacementRouteW19
import ErdosProblems1066.PachToth.ClosedPlacementObstructionBypassW19
import ErdosProblems1066.PachToth.ClosedPlacementSameBlockEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementTargetWrappersW19

set_option autoImplicit false

namespace ErdosProblems1066
namespace PachToth
namespace PachTothClosedPlacementAuditW19

noncomputable section

open Arithmetic
open ArbitraryNClosedPlacementRouteW19
open ClosedPlacementObstructionBypassW19
open ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdgeCertificate
open ClosedPlacementTargetWrappersW19
open FiniteGraph
open PachTothW18FinalGateAttempt

theorem w18_final_inputs_exact_eventual_arbitrary
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateInputs) :
    PachTothW18FinalGateAttempt.ExactTarget /\
      PachTothW18FinalGateAttempt.EventualTarget /\
        PachTothW18FinalGateAttempt.ArbitraryTarget :=
  PachTothW18FinalGateAttempt.exact_eventual_arbitrary_of_allPositiveFinalCertificateInputs
    I

theorem w18_final_inputs_upper_bound_exact
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  PachTothW18FinalGateAttempt.upper_bound_five_sixteen_exact_of_allPositiveFinalCertificateInputs
    I k hk

theorem w18_final_inputs_upper_bound_arbitrary
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateInputs)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_allPositiveFinalCertificateInputs
    I n

theorem w18_final_value_inputs_exact_eventual_arbitrary
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateValueInputs) :
    PachTothW18FinalGateAttempt.ExactTarget /\
      PachTothW18FinalGateAttempt.EventualTarget /\
        PachTothW18FinalGateAttempt.ArbitraryTarget :=
  PachTothW18FinalGateAttempt.exact_eventual_arbitrary_of_allPositiveFinalCertificateValueInputs
    I

theorem w18_final_value_inputs_upper_bound_exact
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateValueInputs)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  upper_bound_five_sixteen_exact_of_allPositiveFinalCertificateValueInputs
    I k hk

theorem w18_final_value_inputs_upper_bound_arbitrary
    (I : PachTothW18FinalGateAttempt.AllPositiveFinalCertificateValueInputs)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_allPositiveFinalCertificateValueInputs
    I n

theorem w18_ledger_input_exact_eventual_arbitrary
    {K0 : Nat} (P : W18IntegrationLedger.InputPackage K0) :
    W18IntegrationLedger.ExactTarget /\
      W18IntegrationLedger.EventualTarget /\
        W18IntegrationLedger.ArbitraryTarget :=
  W18IntegrationLedger.exact_eventual_arbitrary_of_w18InputPackage P

theorem w18_ledger_input_upper_bound_exact
    {K0 : Nat} (P : W18IntegrationLedger.InputPackage K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  P.upper_bound_five_sixteen_exact k hk

theorem w18_ledger_input_upper_bound_arbitrary
    {K0 : Nat} (P : W18IntegrationLedger.InputPackage K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  W18IntegrationLedger.upper_bound_five_sixteen_arbitrary_of_w18InputPackage
    P n

theorem w18_ledger_value_input_exact_eventual_arbitrary
    {K0 : Nat} (P : W18IntegrationLedger.ValueInputPackage K0) :
    W18IntegrationLedger.ExactTarget /\
      W18IntegrationLedger.EventualTarget /\
        W18IntegrationLedger.ArbitraryTarget :=
  W18IntegrationLedger.exact_eventual_arbitrary_of_w18ValueInputPackage P

theorem w18_ledger_value_input_upper_bound_exact
    {K0 : Nat} (P : W18IntegrationLedger.ValueInputPackage K0)
    (k : Nat) (hk : 0 < k) :
    Exists fun C : _root_.UDConfig (16 * k) =>
      forall s : Finset (Fin (16 * k)), C.IsIndep s -> s.card <= 5 * k :=
  P.upper_bound_five_sixteen_exact k hk

theorem w18_ledger_value_input_upper_bound_arbitrary
    {K0 : Nat} (P : W18IntegrationLedger.ValueInputPackage K0)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  W18IntegrationLedger.upper_bound_five_sixteen_arbitrary_of_w18ValueInputPackage
    P n

theorem w19_exact_target_of_certificate_producer
    (P : ClosedPlacementTargetWrappersW19.ClosedPlacementCertificateProducer) :
    ClosedPlacementTargetWrappersW19.ExactTarget :=
  ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteen_of_certificateProducer
    P

theorem w19_exact_target_of_explicit_closed_placement_certificates
    (H :
      ClosedPlacementTargetWrappersW19.ExplicitClosedPlacementCertificateProducer) :
    ClosedPlacementTargetWrappersW19.ExactTarget :=
  targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificateProducer
    H

theorem w19_arbitrary_target_of_explicit_closed_placement_certificates
    (H :
      ArbitraryNClosedPlacementRouteW19.ExplicitClosedPlacementCertificateFamily) :
    ArbitraryNClosedPlacementRouteW19.ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
    H

theorem w19_arbitrary_target_of_explicit_transition_closed_placement_certificates
    (H :
      ArbitraryNClosedPlacementRouteW19.ExplicitTransitionClosedPlacementCertificateFamily) :
    ArbitraryNClosedPlacementRouteW19.ArbitraryTarget :=
  targetUpperConstructionFiveSixteenArbitrary_of_explicitTransitionClosedPlacementCertificates
    H

theorem w19_upper_bound_arbitrary_of_explicit_closed_placement_certificates
    (H :
      ArbitraryNClosedPlacementRouteW19.ExplicitClosedPlacementCertificateFamily)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_explicitClosedPlacementCertificates
    H n

theorem w19_upper_bound_arbitrary_of_explicit_transition_closed_placement_certificates
    (H :
      ArbitraryNClosedPlacementRouteW19.ExplicitTransitionClosedPlacementCertificateFamily)
    (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  upper_bound_five_sixteen_arbitrary_of_explicitTransitionClosedPlacementCertificates
    H n

theorem w19_same_block_exists_closed_placement
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> ClosedPlacementSameBlockEdgesW19.R2}
    (S :
      ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdgeCertificate point)
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v))
    (cross_connector_edges_unit :
      forall (i : Fin k) (u v : LocalVertex),
        CrossBlock.NextConnector u v ->
          _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = point :=
  exists_closedPlacement_of_sameBlockCertificate
    S separated cross_connector_edges_unit

theorem w19_same_block_transition_exists_closed_placement
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> ClosedPlacementSameBlockEdgesW19.R2}
    (S :
      ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdgeCertificate point)
    (transition :
      forall i : Fin k,
        OrientationData.TransitionCertificate
          (point i) (point (cyclicSucc hk i)))
    (separated :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) -> 1 <= _root_.eucDist (point i u) (point j v)) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = point :=
  exists_closedPlacement_of_sameBlockTransitionCertificate
    S transition separated

theorem w19_obstruction_bypass_gate
    {K0 : Nat} :
    Not (Nonempty ClosedPlacementObstructionBypassW19.BaseFixingCertificate) /\
      Not
        (Nonempty
          ClosedPlacementObstructionBypassW19.AllPositiveFinalCertificateInputs) /\
        Not
          (Nonempty
            ClosedPlacementObstructionBypassW19.AllPositiveFinalCertificateValueInputs) /\
          forall
            _ :
              ClosedPlacementObstructionBypassW19.ExplicitClosedPlacementRemainingGate
                K0,
            ClosedPlacementObstructionBypassW19.ExactTarget /\
              ClosedPlacementObstructionBypassW19.EventualTarget /\
                ClosedPlacementObstructionBypassW19.ArbitraryTarget :=
  w18_allPositive_baseFixing_blocked_explicitClosedPlacement_gate

end

end PachTothClosedPlacementAuditW19
end PachToth
end ErdosProblems1066
