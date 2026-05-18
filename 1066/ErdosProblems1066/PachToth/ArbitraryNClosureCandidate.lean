import ErdosProblems1066.PachToth.SmallCaseCertificates
import ErdosProblems1066.PachToth.SplitRealizationFinal
import ErdosProblems1066.PachToth.EventualRoleHingeClosure

set_option autoImplicit false

/-!
# Candidate arbitrary-`n` closure spine

This module records the reduced-hypothesis arbitrary-`n` Pach--Toth closure
shape shared by the small-case, split-realization, and eventual role-hinge
routes.  The point is to consume exactly the finite data still needed by an
eventual route: exact block targets below the eventual block threshold.  A
full exact target is handled separately by the translated-remainder split and
does not need a small-case callback.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ArbitraryNClosureCandidate

noncomputable section

open EventualRoleHingeClosure
open SmallCaseCertificates
open SplitRealizationFinal

/-- Exact block-form target data gives every fixed vertex count by taking the
div/mod exact chain and placing the checked remainder by translation. -/
theorem at_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) (n : Nat) :
    targetUpperConstructionFiveSixteenAt n := by
  exact
    targetUpperConstructionFiveSixteenAt_of_exactTarget_remainderFarApart
      Hexact n

/-- Exact block-form target data gives the arbitrary-`n` target without any
extra small-case hypothesis. -/
theorem arbitrary_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  intro n
  exact at_of_exactTarget Hexact n

/-- Exact block-form target data also supplies every finite small-case
complement requested by an eventual route. -/
theorem smallUpTo_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) (N0 : Nat) :
    targetUpperConstructionFiveSixteenSmallUpTo N0 := by
  intro n _hn
  exact at_of_exactTarget Hexact n

/-- An eventual vertex route with threshold `16 * K0` closes from exact block
targets only for the positive block counts below `K0`.  The checked remainder
split supplies the non-multiple-of-sixteen vertices. -/
theorem arbitrary_of_eventually_exactBlockSmallCases
    (K0 : Nat)
    (Hlarge :
      forall n : Nat, 16 * K0 <= n -> targetUpperConstructionFiveSixteenAt n)
    (exactBlock :
      forall k : Nat, k < K0 -> 0 < k ->
        targetUpperConstructionFiveSixteenAt (16 * k)) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * K0)
      Hlarge
      (targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
        K0 exactBlock)

/-- Eventual role-hinged period data plus exact block targets below the block
threshold is enough for the arbitrary-`n` target. -/
theorem arbitrary_of_roleHinged_exactBlockSmallCases
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
    (exactBlock :
      forall k : Nat, k < K0 -> 0 < k ->
        targetUpperConstructionFiveSixteenAt (16 * k)) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_smallUpTo
      K0 T orientation period separated
      (targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
        K0 exactBlock)

/-- Eventual role-hinged closure equations plus exact block targets below the
block threshold are enough for the arbitrary-`n` target. -/
theorem arbitrary_of_roleHingedClosure_exactBlockSmallCases
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
    (exactBlock :
      forall k : Nat, k < K0 -> 0 < k ->
        targetUpperConstructionFiveSixteenAt (16 * k)) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_and_smallUpTo
      K0 T orientation closure separated
      (targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
        K0 exactBlock)

/-- Compact eventual finite-certificate obligations close from exact block
targets below their block threshold. -/
theorem arbitrary_of_eventualFiniteCertificates_exactBlockSmallCases
    {K0 : Nat}
    (O : EventualFiniteCertificateObligations K0)
    (exactBlock :
      forall k : Nat, k < K0 -> 0 < k ->
        targetUpperConstructionFiveSixteenAt (16 * k)) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    O.targetUpperConstructionFiveSixteenArbitrary_of_smallUpTo
      (targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold_of_exactBlockTargets
        K0 exactBlock)

end

end ArbitraryNClosureCandidate
end PachToth
end ErdosProblems1066
