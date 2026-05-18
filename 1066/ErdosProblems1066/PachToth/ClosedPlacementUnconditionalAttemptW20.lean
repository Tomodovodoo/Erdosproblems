import ErdosProblems1066.PachToth.ExplicitClosedPlacementProducerW19
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch
import ErdosProblems1066.PachToth.TranslatedEquationObstruction
import ErdosProblems1066.PachToth.TransitionAlternativeW13

set_option autoImplicit false

/-!
# W20 unconditional closed-placement attempt

The W19 closed-placement producer is constructive once supplied with one
generated-chain package: a generated family, closure equations for every
positive block count, and reduced metric hypotheses for that same family.

This file records that constructive route and proves that the available W18
and rigid/four-equation bypasses are dead.  Consequently the enumerated W20
route data is equivalent to the generated-chain package below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedPlacementUnconditionalAttemptW20

noncomputable section

open FiniteGraph

abbrev ExplicitClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) :=
  ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    ExplicitClosedPlacementCertificate k hk

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) :=
  ClosedPlacementClosure.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

/-- The exact generated-chain data missing from an unconditional W20
certificate family. -/
structure GeneratedChainData where
  family : GeneratedChainFamily
  closure : GeneratedChainFamilyClosures family
  reducedMetric : ReducedMetricHypotheses family

namespace GeneratedChainData

def toW19InputPackage
    (D : GeneratedChainData) :
    ExplicitClosedPlacementProducerW19.InputPackage where
  family := D.family
  closure := D.closure
  metric := D.reducedMetric

def toCertificateFamily
    (D : GeneratedChainData) :
    ExplicitClosedPlacementCertificateFamily :=
  ExplicitClosedPlacementProducerW19.explicitClosedPlacementCertificate
    D.toW19InputPackage

@[simp]
theorem toW19InputPackage_family
    (D : GeneratedChainData) :
    D.toW19InputPackage.family = D.family :=
  rfl

@[simp]
theorem toCertificateFamily_point
    (D : GeneratedChainData)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (D.toCertificateFamily k hk).point i v =
      GeneratedClosedChain.generatedPoint
        (D.family.O k hk) hk (D.family.base k hk)
        (D.family.orientation k hk) i v :=
  rfl

end GeneratedChainData

def generatedChainDataOfW19InputPackage
    (P : ExplicitClosedPlacementProducerW19.InputPackage) :
    GeneratedChainData where
  family := P.family
  closure := P.closure
  reducedMetric := P.metric

theorem nonempty_generatedChainData_iff_w19InputPackage :
    Nonempty GeneratedChainData <->
      Nonempty ExplicitClosedPlacementProducerW19.InputPackage := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | intro D =>
            exact Nonempty.intro D.toW19InputPackage)
      (fun h => by
        cases h with
        | intro P =>
            exact Nonempty.intro (generatedChainDataOfW19InputPackage P))

/-- Constructive positive route: generated-chain data gives the requested
explicit closed-placement certificates for every positive block count. -/
def explicitClosedPlacementCertificateFamily_of_generatedChainData
    (D : GeneratedChainData) :
    ExplicitClosedPlacementCertificateFamily :=
  D.toCertificateFamily

abbrev BaseFixingCertificate :=
  ClosedPlacementObstructionBypassW19.BaseFixingCertificate

abbrev AllPositiveFinalCertificateInputs :=
  ClosedPlacementObstructionBypassW19.AllPositiveFinalCertificateInputs

abbrev AllPositiveFinalCertificateValueInputs :=
  ClosedPlacementObstructionBypassW19.AllPositiveFinalCertificateValueInputs

abbrev StrongRoleHingeTransitionFacts :=
  RoleHingeTransitionSearch.RoleHingeTransitionFacts

abbrev SameOppositeStrongRoleHingeTransitionFacts :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts

abbrev FourEquationTranslatedRoute :=
  TranslatedEquationObstruction.FourEquationTranslatedRoute

abbrev SameOppositeFourEquationTranslatedRoute :=
  TranslatedEquationObstruction.SameOppositeFourEquationTranslatedRoute

abbrev ConcreteTransitionObligationsRestrictedExactBlockRouteData : Prop :=
  exists (k : Nat), exists (hk : 0 < k),
    exists (orientation : Fin k -> OrientationData.BlockOrientation),
      PeriodInterface.GeneratedClosureEquation
        TransitionAlternativeW13.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation /\
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        TransitionAlternativeW13.ConcreteTransitionObligations hk
        BaseTransitionRealization.exactBase orientation /\
      TransitionAlternativeW13.ConcreteOrbitSqDistances hk orientation

theorem not_nonempty_baseFixingCertificate :
    Not (Nonempty BaseFixingCertificate) :=
  ClosedPlacementObstructionBypassW19.not_nonempty_baseFixingCertificate

theorem not_nonempty_allPositiveFinalCertificateInputs :
    Not (Nonempty AllPositiveFinalCertificateInputs) :=
  ClosedPlacementObstructionBypassW19.not_nonempty_allPositiveFinalCertificateInputs

theorem not_nonempty_allPositiveFinalCertificateValueInputs :
    Not (Nonempty AllPositiveFinalCertificateValueInputs) :=
  ClosedPlacementObstructionBypassW19.not_nonempty_allPositiveFinalCertificateValueInputs

theorem not_nonempty_strongRoleHingeTransitionFacts :
    Not (Nonempty StrongRoleHingeTransitionFacts) :=
  RoleHingeTransitionSearch.not_nonempty_roleHingeTransitionFacts

theorem not_nonempty_sameOppositeStrongRoleHingeTransitionFacts :
    Not (Nonempty SameOppositeStrongRoleHingeTransitionFacts) :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts.not_nonempty_sameOppositeRoleHingeTransitionFacts

theorem not_nonempty_fourEquationTranslatedRoute :
    Not (Nonempty FourEquationTranslatedRoute) :=
  TranslatedEquationObstruction.no_fourEquationTranslatedRoute

theorem not_nonempty_sameOppositeFourEquationTranslatedRoute :
    Not (Nonempty SameOppositeFourEquationTranslatedRoute) :=
  TranslatedEquationObstruction.no_sameOppositeFourEquationTranslatedRoute

theorem not_concreteTransitionObligationsRestrictedExactBlockRouteData :
    Not ConcreteTransitionObligationsRestrictedExactBlockRouteData := by
  intro h
  cases h with
  | intro k h =>
      cases h with
      | intro hk h =>
          cases h with
          | intro orientation hdata =>
              exact
                TransitionAlternativeW13.concreteTransitionObligations_restrictedExactBlockRoute_blocked
                  hk orientation hdata

abbrev DeadRigidRouteData : Prop :=
  Nonempty BaseFixingCertificate \/
    Nonempty AllPositiveFinalCertificateInputs \/
    Nonempty AllPositiveFinalCertificateValueInputs \/
    Nonempty StrongRoleHingeTransitionFacts \/
    Nonempty SameOppositeStrongRoleHingeTransitionFacts \/
    Nonempty FourEquationTranslatedRoute \/
    Nonempty SameOppositeFourEquationTranslatedRoute \/
    ConcreteTransitionObligationsRestrictedExactBlockRouteData

theorem not_deadRigidRouteData :
    Not DeadRigidRouteData := by
  intro h
  cases h with
  | inl hbase =>
      exact not_nonempty_baseFixingCertificate hbase
  | inr h =>
      cases h with
      | inl hinputs =>
          exact not_nonempty_allPositiveFinalCertificateInputs hinputs
      | inr h =>
          cases h with
          | inl hvalues =>
              exact not_nonempty_allPositiveFinalCertificateValueInputs hvalues
          | inr h =>
              cases h with
              | inl hrole =>
                  exact not_nonempty_strongRoleHingeTransitionFacts hrole
              | inr h =>
                  cases h with
                  | inl hsameOppRole =>
                      exact
                        not_nonempty_sameOppositeStrongRoleHingeTransitionFacts
                          hsameOppRole
                  | inr h =>
                      cases h with
                      | inl hfour =>
                          exact not_nonempty_fourEquationTranslatedRoute hfour
                      | inr h =>
                          cases h with
                          | inl hsameOppFour =>
                              exact
                                not_nonempty_sameOppositeFourEquationTranslatedRoute
                                  hsameOppFour
                          | inr hconcrete =>
                              exact
                                not_concreteTransitionObligationsRestrictedExactBlockRouteData
                                  hconcrete

abbrev W20AvailableRouteData : Prop :=
  Nonempty GeneratedChainData \/ DeadRigidRouteData

/-- Among the enumerated W20 routes, every non-generated route is already
blocked; hence route data is exactly generated-chain data. -/
theorem w20AvailableRouteData_iff_generatedChainData :
    W20AvailableRouteData <-> Nonempty GeneratedChainData := by
  exact
    Iff.intro
      (fun h => by
        cases h with
        | inl hgenerated =>
            exact hgenerated
        | inr hdead =>
            exact False.elim (not_deadRigidRouteData hdead))
      (fun hgenerated => Or.inl hgenerated)

theorem w20AvailableRouteData_requires_generatedChainData
    (H : W20AvailableRouteData) :
    Nonempty GeneratedChainData :=
  w20AvailableRouteData_iff_generatedChainData.1 H

/-- Concrete no-go form: if the generated-chain package is absent, no
enumerated W20 route data remains. -/
theorem w20_no_go_without_generatedChainData
    (hmissing : Not (Nonempty GeneratedChainData)) :
    Not W20AvailableRouteData := by
  intro H
  exact hmissing (w20AvailableRouteData_requires_generatedChainData H)

end

end ClosedPlacementUnconditionalAttemptW20
end PachToth
end ErdosProblems1066
