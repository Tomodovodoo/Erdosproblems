import ErdosProblems1066.PachToth.EventualRoleHingeClosure

set_option autoImplicit false

/-!
# Large closed-placement W12 bridge

This module records the sufficiently-large explicit closed-placement layer used
by the eventual Pach--Toth route.  The statements here are repackaging
theorems: large role-hinged generated-chain data is first forgotten to
`ExplicitClosedPlacementCertificate`, and the existing eventual
closed-placement wrappers then provide the target route.
-/

namespace ErdosProblems1066
namespace PachToth
namespace LargeClosedPlacementW12

open FiniteGraph
open ClosedChainReduction
open EventualRoleHingeClosure

noncomputable section

abbrev R2 := Prod Real Real
abbrev RoleHingeTransitions := EventualRoleHingeClosure.RoleHingeTransitions

/-- Forget the role-hinged transition certificate to the coordinate-level
explicit closed-placement certificate. -/
def explicitClosedPlacementCertificateOfRoleHinged
    (T : RoleHingeTransitions)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period :
      GeneratedSeparationInterface.GeneratedPeriod
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk :=
  (EventualRoleHingeClosure.explicitTransitionClosedPlacementCertificateOfRoleHinged
    T hk orientation period separated).toExplicitClosedPlacementCertificate

/-- A family of explicit closed-placement certificates available for every
positive block count from a threshold onward. -/
structure LargeExplicitClosedPlacementCertificates (K0 : Nat) where
  certificate :
    forall (k : Nat), K0 <= k -> forall hk : 0 < k,
      ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

namespace LargeExplicitClosedPlacementCertificates

/-- The exact-chain certificate extracted from a sufficiently-large explicit
closed placement. -/
def exactChainUpper
    {K0 : Nat} (C : LargeExplicitClosedPlacementCertificates K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    SplitSoundness.ExactChainUpper k :=
  ClosedChainReduction.exactChainUpperOfExplicitClosedPlacementCertificate
    (C.certificate k hK hk)

/-- Sufficiently-large explicit closed-placement certificates give the
source-faithful eventual target. -/
theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (C : LargeExplicitClosedPlacementCertificates K0) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    open ClosedChainReduction in
    targetUpperConstructionFiveSixteenEventually_of_eventualExplicitClosedPlacementCertificates
      K0 C.certificate

/-- Sufficiently-large explicit closed-placement certificates, plus the
matching finite-complement callback, give the arbitrary target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_small
    {K0 : Nat} (C : LargeExplicitClosedPlacementCertificates K0)
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    open ClosedChainReduction in
    targetUpperConstructionFiveSixteenArbitrary_of_eventualExplicitClosedPlacement_and_small
      K0 C.certificate Hsmall

/-- Sufficiently-large explicit closed placements, with exact-chain small-case
certificates supplying the finite complement. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactChainSmallCases
    {K0 : Nat} (C : LargeExplicitClosedPlacementCertificates K0)
    (smallCases :
      forall N0 : Nat, SmallCaseReduction.ExactChainSmallCaseCertificates N0) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    C.targetUpperConstructionFiveSixteenArbitrary_of_small
      (SmallCaseReduction.smallCaseCallback_of_exactChainCertificates
        smallCases)

end LargeExplicitClosedPlacementCertificates

/-- Role-hinged generated periods and separation from threshold `K0` onward
construct sufficiently-large explicit closed-placement certificates. -/
def largeExplicitClosedPlacementCertificatesOfRoleHinged
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
          (orientation k hK hk)) :
    LargeExplicitClosedPlacementCertificates K0 where
  certificate := fun k hK hk =>
    explicitClosedPlacementCertificateOfRoleHinged
      T hk (orientation k hK hk) (period k hK hk) (separated k hK hk)

/-- Role-hinged generated periods and separation give the eventual target via
the explicit closed-placement route. -/
theorem targetUpperConstructionFiveSixteenEventually_of_eventual_roleHinged_explicitClosed
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
          (orientation k hK hk)) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    (largeExplicitClosedPlacementCertificatesOfRoleHinged
      K0 T orientation period separated)
      |>.targetUpperConstructionFiveSixteenEventually

/-- Role-hinged generated periods and separation, plus the finite complement,
give the arbitrary target through the explicit closed-placement route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_explicitClosed_and_small
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
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (largeExplicitClosedPlacementCertificatesOfRoleHinged
      K0 T orientation period separated)
      |>.targetUpperConstructionFiveSixteenArbitrary_of_small Hsmall

/-- Closure-equation version of the sufficiently-large explicit
closed-placement construction. -/
def largeExplicitClosedPlacementCertificatesOfRoleHingedClosure
    (K0 : Nat)
    (T : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk))
    (separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk)) :
    LargeExplicitClosedPlacementCertificates K0 :=
  largeExplicitClosedPlacementCertificatesOfRoleHinged
    K0 T orientation
    (fun k hK hk =>
      PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase
        (orientation k hK hk)
        (closure k hK hk))
    separated

/-- Closure-equation data gives the eventual target via the explicit
closed-placement route. -/
theorem targetUpperConstructionFiveSixteenEventually_of_eventual_roleHingedClosure_explicitClosed
    (K0 : Nat)
    (T : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk))
    (separated :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk)) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    (largeExplicitClosedPlacementCertificatesOfRoleHingedClosure
      K0 T orientation closure separated)
      |>.targetUpperConstructionFiveSixteenEventually

/-- Closure-equation data and a finite-complement callback give the arbitrary
target through the explicit closed-placement route. -/
theorem
targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_explicitClosed_and_small
    (K0 : Nat)
    (T : RoleHingeTransitions)
    (orientation :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Fin k -> OrientationData.BlockOrientation)
    (closure :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedClosureEquation
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
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (largeExplicitClosedPlacementCertificatesOfRoleHingedClosure
      K0 T orientation closure separated)
      |>.targetUpperConstructionFiveSixteenArbitrary_of_small Hsmall

/-- The source-faithful finite-certificate obligations already contain exactly
the data needed to build sufficiently-large explicit closed placements. -/
def largeExplicitClosedPlacementCertificatesOfFiniteObligations
    {K0 : Nat}
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations K0) :
    LargeExplicitClosedPlacementCertificates K0 :=
  largeExplicitClosedPlacementCertificatesOfRoleHinged
    K0 O.transitions O.orientation O.period O.generatedSeparation

/-- Eventual finite-certificate obligations give the eventual target through
the explicit closed-placement route. -/
theorem targetUpperConstructionFiveSixteenEventually_of_finiteObligations_explicitClosed
    {K0 : Nat}
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations K0) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    (largeExplicitClosedPlacementCertificatesOfFiniteObligations O)
      |>.targetUpperConstructionFiveSixteenEventually

/-- Eventual finite-certificate obligations and exact-chain small cases give
the arbitrary target through the explicit closed-placement route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_finiteObligations_explicitClosed_exactCases
    {K0 : Nat}
    (O : EventualRoleHingeClosure.EventualFiniteCertificateObligations K0)
    (smallCases :
      forall N0 : Nat, SmallCaseReduction.ExactChainSmallCaseCertificates N0) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (largeExplicitClosedPlacementCertificatesOfFiniteObligations O)
      |>.targetUpperConstructionFiveSixteenArbitrary_of_exactChainSmallCases
        smallCases

end

end LargeClosedPlacementW12
end PachToth
end ErdosProblems1066
