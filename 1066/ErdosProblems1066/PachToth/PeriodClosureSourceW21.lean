import ErdosProblems1066.PachToth.GeneratedChainClosureProducerW20
import ErdosProblems1066.PachToth.GeneratedChainFamilyProducerW20
import ErdosProblems1066.PachToth.ConcretePeriodCandidateSearch
import ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20

set_option autoImplicit false

/-!
# W21 period closure sources

This module is a W21 handoff layer for
`GeneratedChainClosureProducerW20.ClosureSource`.  It keeps ownership narrow:
period-search and certificate modules supply indexed algebraic equations,
and this file records the exact generated-chain closure source obtained from
those fields.

No external search success is asserted here.  The final section names the
remaining period-equation fields in their smallest reusable form.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodClosureSourceW21

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev GeneratedChainFamily :=
  GeneratedChainClosureProducerW20.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.GeneratedChainFamilyClosures F

abbrev ClosureSource
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainClosureProducerW20.ClosureSource F

abbrev TransitionObligations :=
  Figure2Certificate.SameOppositeTransitionObligations

/-! ## Generic period-equation candidate families -/

/-- The generated-chain family determined by a period-equation candidate
family for fixed transition obligations and base block. -/
def generatedChainFamilyOfPeriodEquationCandidateFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base) :
    GeneratedChainFamily where
  O := fun _k _hk => O
  base := fun _k _hk => base
  orientation := F.orientation

@[simp]
theorem generatedChainFamilyOfPeriodEquationCandidateFamily_O
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfPeriodEquationCandidateFamily O base F).O k hk =
      O :=
  rfl

@[simp]
theorem generatedChainFamilyOfPeriodEquationCandidateFamily_base
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfPeriodEquationCandidateFamily O base F).base k hk =
      base :=
  rfl

@[simp]
theorem generatedChainFamilyOfPeriodEquationCandidateFamily_orientation
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfPeriodEquationCandidateFamily O base F).orientation
        k hk =
      F.orientation k hk :=
  rfl

/-- Indexed algebraic period equations in a candidate family give the W20
generated-chain closure target. -/
def closuresOfPeriodEquationCandidateFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base) :
    GeneratedChainFamilyClosures
      (generatedChainFamilyOfPeriodEquationCandidateFamily O base F) :=
  fun k hk => F.generatedClosureEquation k hk

@[simp]
theorem closuresOfPeriodEquationCandidateFamily_apply
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base)
    (k : Nat) (hk : 0 < k) :
    closuresOfPeriodEquationCandidateFamily O base F k hk =
      F.generatedClosureEquation k hk :=
  rfl

/-- W20 closure source obtained from a generic all-positive period-equation
candidate family. -/
def sourceOfPeriodEquationCandidateFamily
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base) :
    ClosureSource
      (generatedChainFamilyOfPeriodEquationCandidateFamily O base F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (closuresOfPeriodEquationCandidateFamily O base F)

@[simp]
theorem sourceOfPeriodEquationCandidateFamily_closure
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (F :
      PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base) :
    (sourceOfPeriodEquationCandidateFamily O base F).closure =
      closuresOfPeriodEquationCandidateFamily O base F :=
  rfl

/-- Raw finite words plus exact `Fin 16` period equations are exactly enough
to produce a W20 closure source for the associated generated-chain family. -/
def sourceOfWordEquations
    (O : TransitionObligations)
    (base : LocalVertex -> R2)
    (word : forall (k : Nat), 0 < k -> OrientationWord.Word k)
    (equations :
      forall (k : Nat) (hk : 0 < k),
        PeriodEquationConcreteSearch.ExactPeriodEquations
          O hk base (word k hk)) :
    ClosureSource
      (generatedChainFamilyOfPeriodEquationCandidateFamily O base
        (PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.ofWordEquations
          word equations)) :=
  sourceOfPeriodEquationCandidateFamily O base
    (PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.ofWordEquations
      word equations)

/-! ## Concrete W20 period-search families -/

/-- Concrete period-search data gives a named W20 closure source for the
generated-chain family already used by `GeneratedChainClosureProducerW20`. -/
def sourceOfConcretePeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    ClosureSource
      (GeneratedChainClosureProducerW20.concretePeriodSearchGeneratedChainFamily
        F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (GeneratedChainClosureProducerW20.closuresOfConcretePeriodSearchData F)

@[simp]
theorem sourceOfConcretePeriodSearchData_closure
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    (sourceOfConcretePeriodSearchData F).closure =
      GeneratedChainClosureProducerW20.closuresOfConcretePeriodSearchData F :=
  rfl

/-- Concrete period-search data also supplies the family-level generated
period equations, so the W20 `ofPeriodEquations` constructor reaches the same
closure source target. -/
def periodEquationsOfConcretePeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    GeneratedChainClosureProducerW20.FamilyPeriodEquations
      (GeneratedChainClosureProducerW20.concretePeriodSearchGeneratedChainFamily
        F) :=
  fun k hk => F.periodEquation k hk

/-- Period-equation spelling of the same concrete period-search source. -/
def sourceOfConcretePeriodSearchDataViaPeriodEquations
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    ClosureSource
      (GeneratedChainClosureProducerW20.concretePeriodSearchGeneratedChainFamily
        F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofPeriodEquations
    (GeneratedChainClosureProducerW20.concretePeriodSearchGeneratedChainFamily
      F)
    (periodEquationsOfConcretePeriodSearchData F)

theorem sourceOfConcretePeriodSearchDataViaPeriodEquations_closure_eq
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    (sourceOfConcretePeriodSearchDataViaPeriodEquations F).closure =
      (sourceOfConcretePeriodSearchData F).closure := by
  funext k hk
  exact Subsingleton.elim _ _

/-- Concrete period-search plus cross-block data is the real W20 generated
family; the period equations alone already give its closure source. -/
def sourceOfConcreteCrossBlockFamily
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    ClosureSource F.toGeneratedChainFamily :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (GeneratedChainClosureProducerW20.closuresOfConcreteCrossBlockFamily F)

@[simp]
theorem sourceOfConcreteCrossBlockFamily_closure
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    (sourceOfConcreteCrossBlockFamily F).closure =
      GeneratedChainClosureProducerW20.closuresOfConcreteCrossBlockFamily F :=
  rfl

/-- Once the concrete cross-block lower-bound fields are present, the W20
closure source reaches the exact-family hypothesis package. -/
def exactFamilyHypothesesOfConcreteCrossBlockFamily
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    ExactFamilyClosure.ExactFamilyHypotheses :=
  (sourceOfConcreteCrossBlockFamily F).toExactFamilyHypotheses
    F.toReducedMetricHypotheses

@[simp]
theorem exactFamilyHypothesesOfConcreteCrossBlockFamily_family
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    (exactFamilyHypothesesOfConcreteCrossBlockFamily F).family =
      F.toGeneratedChainFamily :=
  by
    simp [exactFamilyHypothesesOfConcreteCrossBlockFamily]

@[simp]
theorem exactFamilyHypothesesOfConcreteCrossBlockFamily_closure
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    (exactFamilyHypothesesOfConcreteCrossBlockFamily F).closure =
      (sourceOfConcreteCrossBlockFamily F).toGeneratedChainFamilyClosures :=
  rfl

/-! ## Role-hinge candidate-search facades -/

/-- The generated-chain family determined by a role-hinge period-candidate
family before cross-block lower bounds are attached. -/
def generatedChainFamilyOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :
    GeneratedChainFamily where
  O := fun _k _hk =>
    ConcretePeriodCandidateSearch.transitionObligationsOfFacts F.transitions
  base := fun _k _hk => BaseTransitionRealization.exactBase
  orientation := F.orientation

/-- Role-hinge period-candidate families expose a W20 closure source directly
from their exact finite period-equation fields. -/
def sourceOfPeriodCandidateFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily) :
    ClosureSource (generatedChainFamilyOfPeriodCandidateFamily F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (show GeneratedChainFamilyClosures
        (generatedChainFamilyOfPeriodCandidateFamily F) from
      fun k hk => F.closure k hk)

@[simp]
theorem sourceOfPeriodCandidateFamily_closure_apply
    (F : ConcretePeriodCandidateSearch.PeriodCandidateFamily)
    (k : Nat) (hk : 0 < k) :
    (sourceOfPeriodCandidateFamily F).closure k hk =
      F.closure k hk :=
  rfl

/-- Period candidates plus cross-block lower bounds use the same closure
source while adding separation data elsewhere. -/
def sourceOfPeriodCandidateSearchFamily
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily) :
    ClosureSource
      (F.toRoleHingeTransitionFactsFiniteSearchFamily
        |>.toRoleHingedGeneratedClosureFamily
        |>.toGeneratedChainFamily) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (GeneratedChainClosureProducerW20.closuresOfRoleHingeTransitionFactsFiniteSearchFamily
      F.toRoleHingeTransitionFactsFiniteSearchFamily)

@[simp]
theorem sourceOfPeriodCandidateSearchFamily_closure_apply
    (F : ConcretePeriodCandidateSearch.PeriodCandidateSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (sourceOfPeriodCandidateSearchFamily F).closure k hk =
      F.closure k hk := by
  rfl

/-! ## All-positive finite-search certificate facades -/

/-- All-positive period-search data gives a W20 closure source before the
non-connector square-value tables are attached. -/
def sourceOfAllPositivePeriodSearchData
    (F : FiniteSearchCertificate.AllPositivePeriodSearchData) :
    ClosureSource
      (GeneratedChainClosureProducerW20.allPositivePeriodSearchGeneratedChainFamily
        F) :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (GeneratedChainClosureProducerW20.closuresOfAllPositivePeriodSearchData F)

@[simp]
theorem sourceOfAllPositivePeriodSearchData_closure
    (F : FiniteSearchCertificate.AllPositivePeriodSearchData) :
    (sourceOfAllPositivePeriodSearchData F).closure =
      GeneratedChainClosureProducerW20.closuresOfAllPositivePeriodSearchData F :=
  rfl

/-- The compact all-positive non-connector certificate exposes the same W20
closure source through the generated-closure family facade used downstream. -/
def sourceOfAllPositiveNonConnectorSqValueCertificate
    (C : FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate) :
    ClosureSource
      C.toRoleHingedGeneratedClosureFamily.toGeneratedChainFamily :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures
    (GeneratedChainClosureProducerW20.closuresOfAllPositiveNonConnectorSqValueCertificate
      C)

@[simp]
theorem sourceOfAllPositiveNonConnectorSqValueCertificate_closure_apply
    (C : FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    (sourceOfAllPositiveNonConnectorSqValueCertificate C).closure k hk =
      C.closure k hk :=
  rfl

/-! ## Minimal remaining period-equation fields -/

/-- A sharply reduced all-positive period-equation source: fixed transition
obligations and base block, one finite word for every positive length, and
the exact `Fin 16` algebraic period equations for those words. -/
structure PeriodEquationSourceFields
    (O : TransitionObligations)
    (base : LocalVertex -> R2) where
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equations :
    forall (k : Nat) (hk : 0 < k),
      PeriodEquationConcreteSearch.ExactPeriodEquations
        O hk base (word k hk)

namespace PeriodEquationSourceFields

/-- The reduced fields assemble to the reusable candidate-family record. -/
def toCandidateFamily
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : PeriodEquationSourceFields O base) :
    PeriodEquationConcreteSearch.PeriodEquationCandidateFamily O base :=
  PeriodEquationConcreteSearch.PeriodEquationCandidateFamily.ofWordEquations
    S.word S.equations

/-- Therefore these fields are sufficient for a W20 closure source. -/
def toClosureSource
    {O : TransitionObligations}
    {base : LocalVertex -> R2}
    (S : PeriodEquationSourceFields O base) :
    ClosureSource
      (generatedChainFamilyOfPeriodEquationCandidateFamily O base
        S.toCandidateFamily) :=
  sourceOfPeriodEquationCandidateFamily O base S.toCandidateFamily

end PeriodEquationSourceFields

/-- For the concrete W20 cross-block family, closure is already reduced to
the period-search subrecord; the remaining non-period fields are metric
separation data. -/
def concreteCrossBlockClosureDependsOnlyOnPeriodSearch
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    (sourceOfConcreteCrossBlockFamily F).closure =
      (sourceOfConcretePeriodSearchData F.periodSearch).closure :=
  rfl

end

end PeriodClosureSourceW21
end PachToth
end ErdosProblems1066
