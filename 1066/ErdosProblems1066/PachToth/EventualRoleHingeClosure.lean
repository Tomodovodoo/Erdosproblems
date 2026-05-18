import ErdosProblems1066.PachToth.GeneratedClosedChainEventualReduction
import ErdosProblems1066.PachToth.GeneratedMetricClosure
import ErdosProblems1066.PachToth.SmallCaseReduction

set_option autoImplicit false

/-!
# Eventual role-hinge closure

This module routes eventual role-hinged generated chains through the generated
closed-chain eventual reduction.  The large-period existence data and the
finite small cases remain explicit hypotheses.
-/

namespace ErdosProblems1066
namespace PachToth
namespace EventualRoleHingeClosure

open FiniteGraph
open GeneratedClosedChainEventualReduction

noncomputable section

abbrev R2 := Prod Real Real
abbrev RoleHingeTransitions := GeneratedMetricClosure.RoleHingeTransitions

/-- Eventual role-hinged generated-chain data, plus the finite small-case
callback used by the eventual reduction, implies the arbitrary-`n`
Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_small
    (K0 : Nat)
    (T : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedPeriod
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk))
    (separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_generated_chains_base_transitions
      K0
      (fun _k _hK _hk => T.toFigure2TransitionObligations)
      (fun _k _hK _hk => BaseTransitionRealization.exactBase)
      orientation
      period
      (fun k hK hk => separated k hK hk)
      (fun _k _hK _hk =>
        GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry)
      (fun _k _hK _hk =>
        GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances T)
      Hsmall

/-- Variant with the small cases supplied as exact-chain certificates for every
finite threshold requested by the eventual reduction. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_exactChainSmallCases
    (K0 : Nat)
    (T : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedPeriod
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk))
    (separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk))
    (smallCases :
      forall N0 : Nat, SmallCaseReduction.ExactChainSmallCaseCertificates N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_small
      K0 T orientation period separated
      (SmallCaseReduction.smallCaseCallback_of_exactChainCertificates
        smallCases)

/-- Large-period existence form: for every sufficiently large positive block
count, a role-hinged orientation is supplied together with its generated period
and generated global separation. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_exists_and_small
    (K0 : Nat)
    (T : RoleHingeTransitions)
    (Hlarge :
      forall (k : Nat), K0 <= k -> forall hk : 0 < k,
        exists orientation : Fin k -> OrientationData.BlockOrientation,
          And
            (GeneratedSeparationInterface.GeneratedPeriod
              T.toFigure2TransitionObligations hk
              BaseTransitionRealization.exactBase orientation)
            (GeneratedSeparationInterface.GeneratedGlobalSeparation
              T.toFigure2TransitionObligations hk
              BaseTransitionRealization.exactBase orientation))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let orientation :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation :=
    fun k hK hk => Classical.choose (Hlarge k hK hk)
  have period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedPeriod
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk) := by
    intro k hK hk
    exact (Classical.choose_spec (Hlarge k hK hk)).1
  have separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk) := by
    intro k hK hk
    exact (Classical.choose_spec (Hlarge k hK hk)).2
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_small
      K0 T orientation period separated Hsmall

/-- Large-period existence form with small cases supplied by exact-chain
certificates. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_exists_exactCases
    (K0 : Nat)
    (T : RoleHingeTransitions)
    (Hlarge :
      forall (k : Nat), K0 <= k -> forall hk : 0 < k,
        exists orientation : Fin k -> OrientationData.BlockOrientation,
          And
            (GeneratedSeparationInterface.GeneratedPeriod
              T.toFigure2TransitionObligations hk
              BaseTransitionRealization.exactBase orientation)
            (GeneratedSeparationInterface.GeneratedGlobalSeparation
              T.toFigure2TransitionObligations hk
              BaseTransitionRealization.exactBase orientation))
    (smallCases :
      forall N0 : Nat, SmallCaseReduction.ExactChainSmallCaseCertificates N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_exists_and_small
      K0 T Hlarge
      (SmallCaseReduction.smallCaseCallback_of_exactChainCertificates
        smallCases)

end

end EventualRoleHingeClosure
end PachToth
end ErdosProblems1066
