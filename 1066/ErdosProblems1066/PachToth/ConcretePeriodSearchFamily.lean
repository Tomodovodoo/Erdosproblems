import ErdosProblems1066.PachToth.CrossBlockLowerBoundsInterface
import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.OrientationWord

set_option autoImplicit false

/-!
# Concrete role-hinged period-search families

This module gives a concrete, reusable input shape for the role-hinged
period-search route.  The data is intentionally explicit: an orientation word
for each positive block count and the indexed algebraic period equations for
that word.  It then projects that data to the existing
`CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily`.

The remaining cross-block inequalities are kept as separate fields in the
`ConcreteCrossBlockFamily` wrapper below.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcretePeriodSearchFamily

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions
abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily
abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F

/-- Concrete finite-word data for the role-hinged period-search family.

For every positive `k`, the fields supply a finite orientation word and the
exact indexed algebraic period equations for the corresponding generated
chain. -/
structure PeriodSearchData where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      PeriodSearchInterface.AlgebraicVertexPeriodEquation
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))
        (BlockPartition.localVertexEquivFin16.symm i)

namespace PeriodSearchData

/-- The raw generated-chain orientation function stored in a concrete family. -/
def orientation
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The finite period-search word attached to a concrete family member. -/
def finiteWord
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfWord hk (F.word k hk)

@[simp]
theorem finiteWord_length
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (F.finiteWord k hk).length = k :=
  rfl

@[simp]
theorem finiteWord_letter
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    (F.finiteWord k hk).letter i = F.orientation k hk i :=
  rfl

/-- Repackage the explicit indexed equations as the certificate expected by
`RoleHingedPeriodSearchFamily`. -/
def indexedCertificate
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      F.transitions.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (ExactFamilyClosure.finiteOrientationWord k hk
        (F.orientation k hk)) where
  equation := by
    intro i
    simpa [ExactFamilyClosure.finiteOrientationWord, finiteWord,
      PeriodCertificateExamples.finiteOrientationWordOfWord,
      orientation]
      using F.equation k hk i

/-- The generated closure equation obtained from the concrete period
certificate for one positive block count. -/
def closure
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (F.indexedCertificate k hk).toGeneratedClosureEquation

/-- The generated final-block period equation obtained from the concrete
algebraic certificate. -/
def periodEquation
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  (F.indexedCertificate k hk).toGeneratedPeriodEquation

/-- Project concrete word-and-equation data to the current role-hinged
period-search interface. -/
def toRoleHingedPeriodSearchFamily
    (F : PeriodSearchData) :
    RoleHingedPeriodSearchFamily where
  transitions := F.transitions
  orientation := F.orientation
  period := F.indexedCertificate

@[simp]
theorem toRoleHingedPeriodSearchFamily_transitions
    (F : PeriodSearchData) :
    F.toRoleHingedPeriodSearchFamily.transitions = F.transitions :=
  rfl

@[simp]
theorem toRoleHingedPeriodSearchFamily_orientation
    (F : PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    F.toRoleHingedPeriodSearchFamily.orientation k hk =
      F.orientation k hk :=
  rfl

/-- A concrete period-search family gives the role-hinged generated-closure
family once generated separation is supplied. -/
def toRoleHingedGeneratedClosureFamily
    (F : PeriodSearchData)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          F.transitions.toFigure2TransitionObligations
          hk
          BaseTransitionRealization.exactBase
          (F.orientation k hk)) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily where
  transitions := F.transitions
  orientation := F.orientation
  closure := F.closure
  separated := separated

end PeriodSearchData

/-- Concrete period-search data plus the remaining cross-block lower-bound
table and inequalities. -/
structure ConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j -> 1 <= lower k hk i u j v
  lower_bound :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          lower k hk i u j v <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint
                periodSearch.transitions.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (periodSearch.orientation k hk)
                i u)
              (GeneratedClosedChain.generatedPoint
                periodSearch.transitions.toFigure2TransitionObligations
                hk
                BaseTransitionRealization.exactBase
                (periodSearch.orientation k hk)
                j v)

namespace ConcreteCrossBlockFamily

/-- Forget concrete words to the period-search family expected by the
cross-block lower-bound interface. -/
def toRoleHingedPeriodSearchFamily
    (F : ConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  F.periodSearch.toRoleHingedPeriodSearchFamily

/-- Project the explicit concrete lower-bound fields to the existing
cross-block lower-bound interface. -/
def toCrossBlockLowerBounds
    (F : ConcreteCrossBlockFamily) :
    CrossBlockLowerBounds F.toRoleHingedPeriodSearchFamily where
  lower := F.lower
  lower_ge_one := F.lower_ge_one
  lower_bound := by
    intro k hk i u j v hij
    exact F.lower_bound k hk i u j v hij

/-- Generated global separation obtained from the explicit cross-block
lower-bound fields and the checked exact-base same-block facts. -/
def separated
    (F : ConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.periodSearch.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk) :=
  F.toCrossBlockLowerBounds.separated k hk

/-- The role-hinged generated-closure family obtained from the concrete
period-search and cross-block data. -/
def toRoleHingedGeneratedClosureFamily
    (F : ConcreteCrossBlockFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  F.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

/-- Exact-multiple Pach-Toth target from concrete period-search data and
explicit cross-block lower-bound inequalities. -/
theorem targetUpperConstructionFiveSixteen
    (F : ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach-Toth target from concrete period-search data,
explicit cross-block lower-bound inequalities, and the checked small cases
already imported by `ExactFamilyClosure`. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : ConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end ConcreteCrossBlockFamily

end

end ConcretePeriodSearchFamily
end PachToth
end ErdosProblems1066
