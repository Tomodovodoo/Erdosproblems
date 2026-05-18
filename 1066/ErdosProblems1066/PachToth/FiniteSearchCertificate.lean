import ErdosProblems1066.PachToth.PeriodCertificateExamples
import ErdosProblems1066.PachToth.GeneratedMetricClosure
import ErdosProblems1066.PachToth.GeneratedSeparationFarApart

set_option autoImplicit false

/-!
# Finite search certificate wrapper

This module is a Lean-side wrapper for finite search output.  It packages a
candidate orientation word, exact indexed period equations, and explicit
cross-block lower-bound data, then projects those fields to the generated
closure and separation interfaces already used downstream.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FiniteSearchCertificate

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev Orientation := OrientationWord.Orientation
abbrev RoleHingeTransitions := GeneratedMetricClosure.RoleHingeTransitions

/-- The period-search finite word associated to an `OrientationWord.SearchData`
candidate. -/
def finiteWordOfSearchData
    (D : OrientationWord.SearchData) :
    PeriodSearchInterface.FiniteOrientationWord :=
  PeriodCertificateExamples.finiteOrientationWordOfSearchData D

@[simp]
theorem finiteWordOfSearchData_length
    (D : OrientationWord.SearchData) :
    (finiteWordOfSearchData D).length = D.k :=
  rfl

@[simp]
theorem finiteWordOfSearchData_letter
    (D : OrientationWord.SearchData) (i : Fin D.k) :
    (finiteWordOfSearchData D).letter i = D.orientation i :=
  rfl

/-- One finite role-hinged certificate for a candidate period word.

The fields are exactly the remaining finite data: a positive orientation word,
the indexed algebraic period equations for the sixteen local vertices, and
cross-block lower bounds for distinct generated blocks. -/
structure RoleHingedCandidateCertificate
    (T : RoleHingeTransitions) where
  data : OrientationWord.SearchData
  period :
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase
      (finiteWordOfSearchData data)
  lower :
    Fin data.k -> LocalVertex -> Fin data.k -> LocalVertex -> Real
  lower_ge_one :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      lower
  lower_bound :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      T.toFigure2TransitionObligations
      data.hk
      BaseTransitionRealization.exactBase
      data.orientation
      lower

namespace RoleHingedCandidateCertificate

/-- The finite word consumed by `PeriodSearchInterface`. -/
def finiteWord
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodSearchInterface.FiniteOrientationWord :=
  finiteWordOfSearchData C.data

/-- Repackage the stored data as a standard period-search certificate. -/
def toPeriodSearchCertificate
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodSearchInterface.PeriodSearchCertificate
      T.toFigure2TransitionObligations
      BaseTransitionRealization.exactBase where
  word := C.finiteWord
  period := C.period

/-- The stored indexed algebraic equations imply generated closure for the
candidate word. -/
def closure
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodInterface.GeneratedClosureEquation
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation := by
  simpa [finiteWord, finiteWordOfSearchData] using
    C.period.toGeneratedClosureEquation

/-- The same indexed equations also imply the generated period equation. -/
def periodEquation
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    PeriodInterface.GeneratedPeriodEquation
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation := by
  simpa [finiteWord, finiteWordOfSearchData] using
    C.period.toGeneratedPeriodEquation

/-- Cross-block lower bounds plus the exact base metric supply global
generated separation for the candidate word. -/
def separated
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    T.toFigure2TransitionObligations
    C.data.hk
    BaseTransitionRealization.exactBase
    C.data.orientation
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances T)
    C.lower
    C.lower_ge_one
    C.lower_bound

/-- The reduced metric package associated to the candidate certificate. -/
def reducedMetricHypotheses
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      T.toFigure2TransitionObligations
      C.data.hk
      BaseTransitionRealization.exactBase
      C.data.orientation where
  separated := C.separated
  base_same_block_isometry :=
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances T

/-- Forget the candidate certificate to the generated-closure data wrapper. -/
def toRoleHingedGeneratedClosureData
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureData C.data.k C.data.hk
      where
  transitions := T
  orientation := C.data.orientation
  closure := C.closure
  separated := C.separated

/-- A finite candidate certificate gives the exact-block target at its period
length. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {T : RoleHingeTransitions}
    (C : RoleHingedCandidateCertificate T) :
    targetUpperConstructionFiveSixteenAt (16 * C.data.k) := by
  let G := C.toRoleHingedGeneratedClosureData
  exact G.targetUpperConstructionFiveSixteenAt_exactBlock

end RoleHingedCandidateCertificate

/-- A family version of the finite wrapper, with one role-hinged transition
package and one candidate word/lower-bound table for every positive length. -/
structure RoleHingedFiniteSearchFamily where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
        transitions.toFigure2TransitionObligations
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
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hk).toFin)
        (lower k hk)

namespace RoleHingedFiniteSearchFamily

/-- The raw orientation function expected by generated-chain APIs. -/
def orientation
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> Orientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i :=
  rfl

/-- The indexed period certificate projected to generated closure for one
positive length. -/
def closure
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) := by
  simpa [orientation, PeriodCertificateExamples.finiteOrientationWordOfWord]
    using (F.period k hk).toGeneratedClosureEquation

/-- The indexed period certificate projected to generated period for one
positive length. -/
def periodEquation
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) := by
  simpa [orientation, PeriodCertificateExamples.finiteOrientationWordOfWord]
    using (F.period k hk).toGeneratedPeriodEquation

/-- Cross-block lower bounds projected to generated global separation for one
positive length. -/
def separated
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
    (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions)
    (F.lower k hk)
    (F.lower_ge_one k hk)
    (F.lower_bound k hk)

/-- The reduced metric package obtained from one family member. -/
def reducedMetricHypotheses
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) where
  separated := F.separated k hk
  base_same_block_isometry :=
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances :=
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions

/-- Forget the finite search family to the generated-closure family facade. -/
def toRoleHingedGeneratedClosureFamily
    (F : RoleHingedFiniteSearchFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily where
  transitions := F.transitions
  orientation := F.orientation
  closure := F.closure
  separated := F.separated

/-- One member of the finite search family gives the exact-block target. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (F : RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  let G : GeneratedMetricClosure.RoleHingedGeneratedClosureData k hk :=
    { transitions := F.transitions
      orientation := F.orientation k hk
      closure := F.closure k hk
      separated := F.separated k hk }
  exact G.targetUpperConstructionFiveSixteenAt_exactBlock

/-- A finite search family for every positive period length gives the exact
Pach-Toth target. -/
theorem targetUpperConstructionFiveSixteen
    (F : RoleHingedFiniteSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen
      F.toRoleHingedGeneratedClosureFamily

end RoleHingedFiniteSearchFamily

end

end FiniteSearchCertificate
end PachToth
end ErdosProblems1066
