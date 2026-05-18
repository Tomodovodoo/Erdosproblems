import ErdosProblems1066.PachToth.GeneratedClosedChainEventualReduction
import ErdosProblems1066.PachToth.GeneratedMetricClosure
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.SmallCaseCertificates
import ErdosProblems1066.PachToth.SmallCaseReduction

set_option autoImplicit false

/-!
# Eventual role-hinge closure

This module routes eventual role-hinged generated chains through the generated
closed-chain eventual reduction.  The large-period existence data and the
finite small cases remain explicit hypotheses.  The direct wrappers below also
expose the sharp vertex threshold `16 * K0` induced by an eventual block-count
threshold `K0`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace EventualRoleHingeClosure

open FiniteGraph
open ClosedChainReduction
open GeneratedClosedChainEventualReduction
open GeneratedClosedChainReduction

noncomputable section

abbrev R2 := Prod Real Real
abbrev RoleHingeTransitions := GeneratedMetricClosure.RoleHingeTransitions

/-- If an eventual block threshold is at most one, then every positive block
count lies in the eventual range. -/
theorem threshold_le_of_atMostOne
    {K0 k : Nat} (hK0 : K0 <= 1) (hk : 0 < k) :
    K0 <= k := by
  exact le_trans hK0 (Nat.succ_le_of_lt hk)

/-- Package one role-hinged generated period and generated separation as the
transition-based closed-placement certificate consumed by the split route. -/
def explicitTransitionClosedPlacementCertificateOfRoleHinged
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
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk := by
  exact
    explicitTransitionClosedPlacementCertificateOfGenerated_reducedSameBlock
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      orientation
      period
      separated
      GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
      (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
        T)

/-- The exact-chain certificate extracted from one role-hinged generated
closed chain. -/
def exactChainUpperOfRoleHinged
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
    SplitSoundness.ExactChainUpper k := by
  exact
    ClosedChainReduction.exactChainUpperOfExplicitClosedPlacementCertificate
      ((explicitTransitionClosedPlacementCertificateOfRoleHinged
        T hk orientation period separated).toExplicitClosedPlacementCertificate)

/-- Eventual role-hinged generated-chain data gives every vertex target from
the explicit threshold `16 * K0` onward. -/
theorem targetUpperConstructionFiveSixteenAt_of_eventual_roleHinged_large
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
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have htarget :
      targetUpperConstructionFiveSixteenAt
        (16 * (n / 16) + n % 16) := by
    by_cases hk : 0 < n / 16
    case pos =>
      have hK : K0 <= n / 16 := by
        omega
      exact
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          (exactChainUpperOfRoleHinged T hk
            (orientation (n / 16) hK hk)
            (period (n / 16) hK hk)
            (separated (n / 16) hK hk))
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
    case neg =>
      have hk0 : n / 16 = 0 := Nat.eq_zero_of_not_pos hk
      have hzero :
          targetUpperConstructionFiveSixteenAt (16 * 0 + n % 16) :=
        RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
          hr
          SplitSoundness.emptyExactChainUpper
          (SplitSoundness.remainderUpperOfConstruction (n % 16))
      simpa [hk0] using hzero
  rw [hsplit]
  exact htarget

/-- Eventual role-hinged generated-chain data gives the source-faithful
eventual target with threshold `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenEventually_of_eventual_roleHinged
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
    targetUpperConstructionFiveSixteenEventually := by
  exact
    Exists.intro (16 * K0)
      (fun n hn =>
        targetUpperConstructionFiveSixteenAt_of_eventual_roleHinged_large
          K0 T orientation period separated hn)

/-- Eventual role-hinged period and separation data whose threshold is at most
one gives the exact block-form Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_eventual_roleHinged_atMostOne
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
    (hK0 : K0 <= 1) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_explicitTransitionClosedPlacementCertificates
      (fun k hk =>
        let hK : K0 <= k := threshold_le_of_atMostOne hK0 hk
        explicitTransitionClosedPlacementCertificateOfRoleHinged
          T hk (orientation k hK hk)
          (period k hK hk) (separated k hK hk))

/-- Eventual role-hinged period and separation data whose threshold is at most
one gives the arbitrary target via the exact target and checked remainders. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_atMostOne
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
    (hK0 : K0 <= 1) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    SmallCaseCertificates.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (targetUpperConstructionFiveSixteen_of_eventual_roleHinged_atMostOne
        K0 T orientation period separated hK0)

/-- Eventual role-hinged generated-chain data plus exactly the small cases
below the induced vertex threshold `16 * K0` gives the arbitrary target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_smallUpTo
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
    (Hsmall : targetUpperConstructionFiveSixteenSmallUpTo (16 * K0)) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * K0)
      (fun n hn =>
        targetUpperConstructionFiveSixteenAt_of_eventual_roleHinged_large
          K0 T orientation period separated hn)
      Hsmall

/-- If the eventual block threshold is at most one block, the checked
below-sixteen small cases discharge the finite complement. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_checkedSmallCases
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
    (hK0 : K0 <= 1) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_atMostOne
      K0 T orientation period separated hK0

/-- Eventual role-hinged generated-chain data plus exact-chain certificates for
the block counts below `K0` gives the arbitrary target.  The zero quotient is
discharged by the checked empty exact chain, so only positive small block
counts are requested. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_blockSmallCases
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
    (smallChains :
      forall k : Nat, k < K0 -> 0 < k -> SplitSoundness.ExactChainUpper k) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_smallUpTo
      K0 T orientation period separated
      (SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold
        K0 smallChains)

/-- Exact-block target data supplies the finite complement below the explicit
eventual threshold `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_exactTargetSmallCases
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
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_smallUpTo
      K0 T orientation period separated
      (SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_of_exactTarget
        Hexact (16 * K0))

/-- Closure-equation spelling of the large-threshold route. -/
theorem targetUpperConstructionFiveSixteenAt_of_eventual_roleHingedClosure_large
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
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n := by
  exact
    targetUpperConstructionFiveSixteenAt_of_eventual_roleHinged_large
      K0 T orientation
      (fun k hK hk =>
        PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk)
          (closure k hK hk))
      separated hn

/-- Closure-equation spelling of the exact block-form route when the eventual
threshold is at most one. -/
theorem targetUpperConstructionFiveSixteen_of_eventual_roleHingedClosure_atMostOne
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
    (hK0 : K0 <= 1) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_eventual_roleHinged_atMostOne
      K0 T orientation
      (fun k hK hk =>
        PeriodInterface.generatedPeriodEquation_of_generatedClosureEquation
          T.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase
          (orientation k hK hk)
          (closure k hK hk))
      separated hK0

/-- Closure-equation spelling with the exact finite complement below
`16 * K0`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_and_smallUpTo
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
    (Hsmall : targetUpperConstructionFiveSixteenSmallUpTo (16 * K0)) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * K0)
      (fun n hn =>
        targetUpperConstructionFiveSixteenAt_of_eventual_roleHingedClosure_large
          K0 T orientation closure separated hn)
      Hsmall

/-- Closure-equation spelling using the checked below-sixteen small cases when
the eventual block threshold is at most one. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_checkedSmallCases
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
    (hK0 : K0 <= 1) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    SmallCaseCertificates.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (targetUpperConstructionFiveSixteen_of_eventual_roleHingedClosure_atMostOne
        K0 T orientation closure separated hK0)

/-- Closure-equation spelling with exact-chain certificates for the block
counts below `K0`. -/
theorem targetArbitrary_of_eventual_roleHingedClosure_blockSmallCases
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
    (smallChains :
      forall k : Nat, k < K0 -> 0 < k -> SplitSoundness.ExactChainUpper k) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_and_smallUpTo
      K0 T orientation closure separated
      (SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold
        K0 smallChains)

/-- Closure-equation spelling using exact-block target data for the finite
small-case complement below `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_exactTarget
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
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_and_smallUpTo
      K0 T orientation closure separated
      (SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_of_exactTarget
        Hexact (16 * K0))

/-- Source-faithful eventual finite-certificate input.

For every positive block count from `K0` onward, the caller supplies one
finite orientation word, the sixteen exact algebraic period equations for that
word, and generated global separation. -/
structure EventualFiniteCertificateObligations (K0 : Nat) where
  transitions : RoleHingeTransitions
  word :
    forall (k : Nat), K0 <= k -> 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin 16),
      PeriodSearchInterface.AlgebraicVertexPeriodEquation
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hK hk))
        (BlockPartition.localVertexEquivFin16.symm i)
  separated :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hK hk).toFin)

namespace EventualFiniteCertificateObligations

/-- The generated-chain orientation extracted from the stored finite word. -/
def orientation
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (O.word k hK hk).toFin

@[simp]
theorem orientation_apply
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin k) :
    O.orientation k hK hk i = O.word k hK hk i :=
  rfl

/-- The finite period-search word at one eventual block count. -/
def finiteWord
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfWord hk
    (O.word k hK hk)

@[simp]
theorem finiteWord_length
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    (O.finiteWord k hK hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin k) :
    (O.finiteWord k hK hk).letter i = O.orientation k hK hk i :=
  rfl

/-- Repackage the stored sixteen algebraic equations as an indexed period
certificate. -/
def indexedCertificate
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      O.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (O.finiteWord k hK hk) where
  equation := O.equation k hK hk

/-- Algebraic closure equation projected from the stored finite equations. -/
def closure
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      O.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (O.orientation k hK hk) := by
  simpa [orientation, finiteWord] using
    (O.indexedCertificate k hK hk).toGeneratedClosureEquation

/-- Generated final-block period equation projected from the stored finite
equations. -/
def period
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedPeriod
      O.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (O.orientation k hK hk) := by
  simpa [orientation, finiteWord] using
    (O.indexedCertificate k hK hk).toGeneratedPeriod

/-- Generated global separation in the orientation spelling used by the
eventual role-hinge wrappers. -/
def generatedSeparation
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (k : Nat) (hK : K0 <= k) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (O.orientation k hK hk) := by
  exact O.separated k hK hk

/-- Eventual finite certificates give every vertex target from the explicit
threshold `16 * K0` onward. -/
theorem targetUpperConstructionFiveSixteenAt_large
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n := by
  exact
    targetUpperConstructionFiveSixteenAt_of_eventual_roleHinged_large
      K0 O.transitions O.orientation O.period O.generatedSeparation hn

/-- Eventual finite certificates give the source-faithful eventual target with
threshold `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    Exists.intro (16 * K0)
      (fun n hn => O.targetUpperConstructionFiveSixteenAt_large hn)

/-- Eventual finite certificates whose threshold is at most one give the exact
block-form target. -/
theorem targetUpperConstructionFiveSixteen_atMostOne
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (hK0 : K0 <= 1) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_eventual_roleHinged_atMostOne
      K0 O.transitions O.orientation O.period O.generatedSeparation hK0

/-- Eventual finite certificates plus exactly the small cases below
`16 * K0` give the arbitrary target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_smallUpTo
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (Hsmall : targetUpperConstructionFiveSixteenSmallUpTo (16 * K0)) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      (16 * K0)
      (fun n hn => O.targetUpperConstructionFiveSixteenAt_large hn)
      Hsmall

/-- If `K0 <= 1`, the checked below-sixteen cases discharge the entire
finite complement for eventual finite certificates. -/
theorem targetUpperConstructionFiveSixteenArbitrary_checkedSmallCases
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (hK0 : K0 <= 1) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    SmallCaseCertificates.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (O.targetUpperConstructionFiveSixteen_atMostOne hK0)

/-- Eventual finite certificates plus exact-chain certificates for the block
counts below `K0` give the arbitrary target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_blockSmallCases
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (smallChains :
      forall k : Nat, k < K0 -> 0 < k -> SplitSoundness.ExactChainUpper k) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    O.targetUpperConstructionFiveSixteenArbitrary_of_smallUpTo
      (SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_blockThreshold
        K0 smallChains)

/-- Eventual finite certificates whose threshold is at most one give the
arbitrary target through the exact block-form target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_atMostOne
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (hK0 : K0 <= 1) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    SmallCaseCertificates.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (O.targetUpperConstructionFiveSixteen_atMostOne hK0)

/-- The common `K0 = 1` specialization: eventual finite certificates from one
block onward plus the checked below-sixteen cases give the arbitrary target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_one_checkedSmallCases
    (O : EventualFiniteCertificateObligations 1) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact O.targetUpperConstructionFiveSixteenArbitrary_checkedSmallCases (by norm_num)

/-- Exact-block target data supplies the finite complement below `16 * K0` for
eventual finite certificates. -/
theorem targetUpperConstructionFiveSixteenArbitrary_exactTargetSmallCases
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0)
    (Hexact : targetUpperConstructionFiveSixteen) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    O.targetUpperConstructionFiveSixteenArbitrary_of_smallUpTo
      (SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_of_exactTarget
        Hexact (16 * K0))

/-- A concrete cross-block family already contains the transition package, all
positive period words/equations, and generated separation obtained from its
cross-block inequalities.  For any chosen eventual block threshold `K0`,
forget the all-positive data to the eventual finite-certificate interface. -/
def ofConcreteCrossBlockFamily
    (K0 : Nat) (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    EventualFiniteCertificateObligations K0 where
  transitions := F.periodSearch.transitions
  word := fun k _hK hk => F.periodSearch.word k hk
  equation := fun k _hK hk i => F.periodSearch.equation k hk i
  separated := fun k _hK hk => by
    simpa [ConcretePeriodSearchFamily.PeriodSearchData.orientation] using
      F.separated k hk

/-- Concrete cross-block-family data gives every vertex target from the explicit
eventual threshold `16 * K0` onward after forgetting to the eventual route. -/
theorem targetUpperConstructionFiveSixteenAt_large_of_concreteCrossBlockFamily
    (K0 : Nat) (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily)
    {n : Nat} (hn : 16 * K0 <= n) :
    targetUpperConstructionFiveSixteenAt n := by
  exact
    (ofConcreteCrossBlockFamily K0 F)
      |>.targetUpperConstructionFiveSixteenAt_large hn

/-- Concrete cross-block-family data gives the source-faithful eventual target
with the explicit threshold `16 * K0`. -/
theorem targetUpperConstructionFiveSixteenEventually_of_concreteCrossBlockFamily
    (K0 : Nat) (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    (ofConcreteCrossBlockFamily K0 F)
      |>.targetUpperConstructionFiveSixteenEventually

/-- Concrete cross-block-family data plus exactly the small cases below
`16 * K0` give the arbitrary target through the eventual route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteCrossBlockFamily_smallUpTo
    (K0 : Nat) (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily)
    (Hsmall : targetUpperConstructionFiveSixteenSmallUpTo (16 * K0)) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (ofConcreteCrossBlockFamily K0 F)
      |>.targetUpperConstructionFiveSixteenArbitrary_of_smallUpTo Hsmall

/-- If the selected eventual block threshold is at most one, the checked
below-sixteen small cases discharge the finite complement for concrete
cross-block-family data. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteCrossBlockFamily_checkedSmallCases
    (K0 : Nat) (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily)
    (hK0 : K0 <= 1) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    (ofConcreteCrossBlockFamily K0 F)
      |>.targetUpperConstructionFiveSixteenArbitrary_checkedSmallCases hK0

/-- The common `K0 = 1` spelling: concrete cross-block-family data routes
through eventual closure with threshold `16`, and the checked below-sixteen
certificates close the complement. -/
theorem targetUpperConstructionFiveSixteenArbitrary_one_of_concreteCrossBlockFamily
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_concreteCrossBlockFamily_checkedSmallCases
      1 F (by norm_num)

end EventualFiniteCertificateObligations

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
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHinged_and_smallUpTo
      K0 T orientation period separated
      (Hsmall (16 * K0)
        (fun n hn =>
          targetUpperConstructionFiveSixteenAt_of_eventual_roleHinged_large
            K0 T orientation period separated hn))

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
