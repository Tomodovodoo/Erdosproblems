import ErdosProblems1066.PachToth.PeriodSearchInterface
import ErdosProblems1066.PachToth.GeneratedMetricClosure
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart
import ErdosProblems1066.PachToth.ClosedPlacementClosure
import ErdosProblems1066.PachToth.SmallCaseCertificates

set_option autoImplicit false

/-!
# Exact generated-family closure

This module is the final conditional facade for the Pach-Toth generated-family
route.  The only geometric input is a generated family, algebraic closure for
each positive block count, and the reduced metric package for that same
family.  Period and separation remain local fields of the supplied data.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactFamilyClosure

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- A positive finite word in the exact length expected by a generated chain. -/
def finiteOrientationWord
    (k : Nat) (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    PeriodSearchInterface.FiniteOrientationWord where
  length := k
  positive_length := hk
  letter := orientation

/-- The smallest explicit bundle needed by the reduced generated-family route:
the generated family, its algebraic closure equations, and its reduced metric
data. -/
structure ExactFamilyHypotheses where
  family : GeneratedSeparationInterface.GeneratedChainFamily
  closure : ClosedPlacementClosure.GeneratedChainFamilyClosures family
  metric :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      family

namespace ExactFamilyHypotheses

/-- The closed placement obtained at a positive block count from the bundled
exact-family data. -/
def closedPlacement (H : ExactFamilyHypotheses)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacementFamily_of_generatedClosure_reduced
    H.family H.closure H.metric k hk

/-- The explicit closed-placement certificate obtained at a positive block
count from the bundled exact-family data. -/
def explicitClosedPlacementCertificate (H : ExactFamilyHypotheses)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk :=
  (ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure_reduced
    (H.family.O k hk) hk (H.family.base k hk)
    (H.family.orientation k hk) (H.closure k hk) (H.metric.metric k hk))
    |>.toExplicitClosedPlacementCertificate

end ExactFamilyHypotheses

/-- Bundled exact-family closure data gives the exact-block Pach-Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_exactFamilyHypotheses
    (H : ExactFamilyHypotheses) :
    targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family_reduced
      H.family H.closure H.metric

/-- The exact-block target gives the arbitrary target from vertex count
sixteen onward. -/
theorem targetUpperConstructionFiveSixteenAt_of_exactTarget_large
    (Hexact : targetUpperConstructionFiveSixteen)
    {n : Nat} (_hn : 16 <= n) :
    targetUpperConstructionFiveSixteenAt n := by
  have hr : n % 16 < 16 := Nat.mod_lt n (by norm_num)
  have hsplit : n = 16 * (n / 16) + n % 16 := by
    have h := Nat.mod_add_div n 16
    omega
  have htarget :
      targetUpperConstructionFiveSixteenAt (16 * (n / 16) + n % 16) :=
    RemainderPlacement.targetUpperConstructionFiveSixteenAt_of_exactChain_translatedRemainder
      hr
      (SplitSoundness.exactChainUpperOfTarget Hexact (n / 16))
      (SplitSoundness.remainderUpperOfConstruction (n % 16))
  rw [hsplit]
  exact htarget

/-- Exact-block target plus the checked small cases below sixteen gives the
arbitrary-`n` Pach-Toth target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
    (Hexact : targetUpperConstructionFiveSixteen) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
      16
      (fun n hn =>
        targetUpperConstructionFiveSixteenAt_of_exactTarget_large
          Hexact hn)
      SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_sixteen

/-- Bundled exact-family closure data gives the arbitrary-`n` Pach-Toth
target. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_exactFamilyHypotheses
    (H : ExactFamilyHypotheses) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (targetUpperConstructionFiveSixteen_of_exactFamilyHypotheses H)

/-- The exact target from the role-hinged generated-closure family interface. -/
theorem targetUpperConstructionFiveSixteen_of_roleHingedGeneratedClosureFamily
    (F : GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      F

/-- The arbitrary-`n` target from the role-hinged generated-closure family
interface and the checked small cases below sixteen. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_roleHingedGeneratedClosureFamily
    (F : GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (targetUpperConstructionFiveSixteen_of_roleHingedGeneratedClosureFamily F)

/-- Role-hinged exact-family data whose period equations come from finite
period-search certificates and whose generated separation comes from explicit
cross-block lower bounds. -/
structure RoleHingedPeriodSearchCrossBlockFamily where
  transitions : GeneratedMetricClosure.RoleHingeTransitions
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (finiteOrientationWord k hk (orientation k hk))
  lower :
    forall (k : Nat) (_hk : 0 < k),
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hk)
  lower_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)
        (lower k hk)

namespace RoleHingedPeriodSearchCrossBlockFamily

/-- The finite period-search certificate projected to the generated closure
equation for one exact block count. -/
def closure
    (F : RoleHingedPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.period k hk).toGeneratedClosureEquation

/-- The explicit cross-block lower bounds projected to generated global
separation for one exact block count. -/
def separated
    (F : RoleHingedPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions)
    (F.lower k hk) (F.lower_ge_one k hk) (F.lower_bound k hk)

/-- Forget the final period-search and lower-bound data to the role-hinged
generated-closure family interface. -/
def toRoleHingedGeneratedClosureFamily
    (F : RoleHingedPeriodSearchCrossBlockFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily where
  transitions := F.transitions
  orientation := F.orientation
  closure := F.closure
  separated := F.separated

end RoleHingedPeriodSearchCrossBlockFamily

/-- Exact Pach-Toth target from finite period-search certificates, role-hinged
metric data, and explicit cross-block lower bounds. -/
theorem targetUpperConstructionFiveSixteen_of_periodSearch_crossBlockLowerBounds
    (F : RoleHingedPeriodSearchCrossBlockFamily) :
    targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_roleHingedGeneratedClosureFamily
      F.toRoleHingedGeneratedClosureFamily

/-- Arbitrary-`n` Pach-Toth target from finite period-search certificates,
role-hinged metric data, explicit cross-block lower bounds, and the checked
small cases below sixteen. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearch_crossBlockLowerBounds
    (F : RoleHingedPeriodSearchCrossBlockFamily) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      (targetUpperConstructionFiveSixteen_of_periodSearch_crossBlockLowerBounds
        F)

end

end ExactFamilyClosure
end PachToth
end ErdosProblems1066
