import ErdosProblems1066.PachToth.FiniteSearchCertificate
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch

set_option autoImplicit false

/-!
# Role-hinge finite-family bridge

This module is the direct bridge from role-hinged finite-search data to the
existing exact `16 * k` Pach--Toth target.  It deliberately avoids the
translated-equation route: the remaining concrete inputs are the finite period
certificates and the cross-block lower-bound tables needed for separation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeFiniteFamilyBridge

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev TransitionFacts :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions
abbrev RoleHingedFiniteSearchFamily :=
  FiniteSearchCertificate.RoleHingedFiniteSearchFamily

/-- Direct bridge from the already-bundled finite-search family to the exact
Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_finiteSearchFamily
    (F : RoleHingedFiniteSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.targetUpperConstructionFiveSixteen

/-- One member of an already-bundled finite-search family gives the exact
target at its block multiple. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_finiteSearchFamily
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  F.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Search-facing role-hinge finite-family data.

The transition package is supplied as raw role-hinge transition facts.  The
period equations and cross-block lower-bound inequalities are still explicit
fields; this wrapper only projects them to
`FiniteSearchCertificate.RoleHingedFiniteSearchFamily`. -/
structure RoleHingeTransitionFactsFiniteSearchFamily where
  transitions : TransitionFacts
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
        transitions.toRoleHingeTransitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hk)
  lower_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        transitions.toRoleHingeTransitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hk).toFin)
        (lower k hk)

namespace RoleHingeTransitionFactsFiniteSearchFamily

/-- Project search-facing transition facts and explicit finite data to the
existing finite-search certificate family. -/
def toFiniteSearchFamily
    (F : RoleHingeTransitionFactsFiniteSearchFamily) :
    RoleHingedFiniteSearchFamily where
  transitions := F.transitions.toRoleHingeTransitions
  word := F.word
  period := F.period
  lower := F.lower
  lower_ge_one := F.lower_ge_one
  lower_bound := F.lower_bound

@[simp]
theorem toFiniteSearchFamily_transitions
    (F : RoleHingeTransitionFactsFiniteSearchFamily) :
    F.toFiniteSearchFamily.transitions =
      F.transitions.toRoleHingeTransitions :=
  rfl

@[simp]
theorem toFiniteSearchFamily_word
    (F : RoleHingeTransitionFactsFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    F.toFiniteSearchFamily.word k hk = F.word k hk :=
  rfl

@[simp]
theorem toFiniteSearchFamily_lower
    (F : RoleHingeTransitionFactsFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    F.toFiniteSearchFamily.lower k hk = F.lower k hk :=
  rfl

/-- The generated global separation obtained from the explicit lower-bound
fields for one positive block count. -/
def separated
    (F : RoleHingeTransitionFactsFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toRoleHingeTransitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      ((F.word k hk).toFin) :=
  F.toFiniteSearchFamily.separated k hk

/-- The generated closure equation obtained from the explicit finite period
certificate for one positive block count. -/
def closure
    (F : RoleHingeTransitionFactsFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toRoleHingeTransitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      ((F.word k hk).toFin) :=
  F.toFiniteSearchFamily.closure k hk

/-- Project to the generated-closure family used by the exact target facade. -/
def toRoleHingedGeneratedClosureFamily
    (F : RoleHingeTransitionFactsFiniteSearchFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  F.toFiniteSearchFamily.toRoleHingedGeneratedClosureFamily

/-- One member of the search-facing finite family gives the exact target at
its block multiple. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (F : RoleHingeTransitionFactsFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  F.toFiniteSearchFamily.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Search-facing role-hinge transition facts, finite period certificates, and
explicit cross-block lower bounds imply the exact Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (F : RoleHingeTransitionFactsFiniteSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toFiniteSearchFamily.targetUpperConstructionFiveSixteen

end RoleHingeTransitionFactsFiniteSearchFamily

/-- Raw-function spelling of the bridge when the caller already has a concrete
role-hinge transition realization package. -/
theorem targetUpperConstructionFiveSixteen_of_roleHingeTransitions
    (T : RoleHingeTransitions)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
          T.toFigure2TransitionObligations
          BaseTransitionRealization.exactBase
          (PeriodCertificateExamples.finiteOrientationWordOfWord hk
            (word k hk)))
    (lower :
      forall (k : Nat), 0 < k ->
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (lower_ge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
          (lower k hk))
    (lower_bound :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
          T.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          ((word k hk).toFin)
          (lower k hk)) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    targetUpperConstructionFiveSixteen_of_finiteSearchFamily
      { transitions := T
        word := word
        period := period
        lower := lower
        lower_ge_one := lower_ge_one
        lower_bound := lower_bound }

end

end RoleHingeFiniteFamilyBridge
end PachToth
end ErdosProblems1066
