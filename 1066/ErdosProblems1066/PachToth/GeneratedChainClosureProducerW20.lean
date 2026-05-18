import ErdosProblems1066.PachToth.ExactFamilyClosure
import ErdosProblems1066.PachToth.GeneratedPeriodClosure
import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.FiniteSearchCertificate
import ErdosProblems1066.PachToth.RoleHingeFiniteFamilyBridge

set_option autoImplicit false

/-!
# W20 generated-chain closure producer

This module is the W20 handoff for the generated-chain closure target

`ClosedPlacementClosure.GeneratedChainFamilyClosures F`.

It keeps the endpoint at the closure layer: no new target theorem is asserted
here.  Instead, the constructors below convert exact period-search data,
generated period equations, and role-hinged generated-family packages into the
closure family consumed by `ClosedPlacementClosure` and `ExactFamilyClosure`.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedChainClosureProducerW20

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  ClosedPlacementClosure.GeneratedChainFamilyClosures F

abbrev GeneratedChainFamilyPeriods
    (F : GeneratedChainFamily) : Prop :=
  GeneratedSeparationInterface.GeneratedChainFamily.Periods F

abbrev FamilyPeriodEquations
    (F : GeneratedChainFamily) : Prop :=
  GeneratedPeriodClosure.FamilyPeriodEquations F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

abbrev IndexedAlgebraicCertificateFamily
    (F : GeneratedChainFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    PeriodSearchInterface.IndexedAlgebraicPeriodCertificate
      (F.O k hk)
      (F.base k hk)
      (ExactFamilyClosure.finiteOrientationWord k hk (F.orientation k hk))

/-- Convert generated final-block period equations to algebraic generated
closure equations for every positive member of a generated-chain family. -/
def closuresOfPeriodEquations
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    GeneratedChainFamilyClosures F :=
  fun k hk =>
    PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
      (F.O k hk) hk (F.base k hk) (F.orientation k hk) (period k hk)

@[simp]
theorem closuresOfPeriodEquations_apply
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F)
    (k : Nat) (hk : 0 < k) :
    closuresOfPeriodEquations F period k hk =
      PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
        (period k hk) :=
  rfl

/-- The W20 period-equation constructor agrees with the existing
`GeneratedPeriodClosure` conversion. -/
theorem closuresOfPeriodEquations_eq_familyClosures
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    closuresOfPeriodEquations F period =
      GeneratedPeriodClosure.familyClosures_of_periodEquations F period := by
  funext k hk
  exact Subsingleton.elim _ _

/-- Convert generated-period hypotheses from `GeneratedSeparationInterface`
to the algebraic closure family required by `ClosedPlacementClosure`. -/
def closuresOfGeneratedPeriods
    (F : GeneratedChainFamily)
    (period : GeneratedChainFamilyPeriods F) :
    GeneratedChainFamilyClosures F :=
  fun k hk =>
    PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
      (F.O k hk) hk (F.base k hk) (F.orientation k hk) (period k hk)

@[simp]
theorem closuresOfGeneratedPeriods_apply
    (F : GeneratedChainFamily)
    (period : GeneratedChainFamilyPeriods F)
    (k : Nat) (hk : 0 < k) :
    closuresOfGeneratedPeriods F period k hk =
      PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
        (period k hk) :=
  rfl

/-- A finite indexed algebraic period-search certificate for every positive
block count supplies the exact generated closure family. -/
def closuresOfIndexedAlgebraicCertificates
    (F : GeneratedChainFamily)
    (certificates : IndexedAlgebraicCertificateFamily F) :
    GeneratedChainFamilyClosures F :=
  fun k hk => by
    simpa [ExactFamilyClosure.finiteOrientationWord] using
      (certificates k hk).toGeneratedClosureEquation

/-- Bundle an exact source for generated-chain closure equations.  The field
is intentionally the same target shape consumed by `ClosedPlacementClosure`;
the value can be produced by the constructors in this file. -/
structure ClosureSource (F : GeneratedChainFamily) where
  closure : GeneratedChainFamilyClosures F

namespace ClosureSource

/-- Forget a closure source to the closure family target. -/
def toGeneratedChainFamilyClosures
    {F : GeneratedChainFamily}
    (S : ClosureSource F) :
    GeneratedChainFamilyClosures F :=
  S.closure

@[simp]
theorem toGeneratedChainFamilyClosures_apply
    {F : GeneratedChainFamily}
    (S : ClosureSource F)
    (k : Nat) (hk : 0 < k) :
    S.toGeneratedChainFamilyClosures k hk = S.closure k hk :=
  rfl

/-- Build a closure source from already supplied generated-chain closures. -/
def ofClosures
    {F : GeneratedChainFamily}
    (closure : GeneratedChainFamilyClosures F) :
    ClosureSource F where
  closure := closure

@[simp]
theorem ofClosures_toGeneratedChainFamilyClosures
    {F : GeneratedChainFamily}
    (closure : GeneratedChainFamilyClosures F) :
    (ofClosures closure).toGeneratedChainFamilyClosures = closure :=
  rfl

/-- Build a closure source from generated final-block period equations. -/
def ofPeriodEquations
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    ClosureSource F where
  closure := closuresOfPeriodEquations F period

@[simp]
theorem ofPeriodEquations_toGeneratedChainFamilyClosures
    (F : GeneratedChainFamily)
    (period : FamilyPeriodEquations F) :
    (ofPeriodEquations F period).toGeneratedChainFamilyClosures =
      closuresOfPeriodEquations F period :=
  rfl

/-- Build a closure source from generated-period hypotheses. -/
def ofGeneratedPeriods
    (F : GeneratedChainFamily)
    (period : GeneratedChainFamilyPeriods F) :
    ClosureSource F where
  closure := closuresOfGeneratedPeriods F period

@[simp]
theorem ofGeneratedPeriods_toGeneratedChainFamilyClosures
    (F : GeneratedChainFamily)
    (period : GeneratedChainFamilyPeriods F) :
    (ofGeneratedPeriods F period).toGeneratedChainFamilyClosures =
      closuresOfGeneratedPeriods F period :=
  rfl

/-- Build a closure source from exact indexed algebraic period-search
certificates. -/
def ofIndexedAlgebraicCertificates
    (F : GeneratedChainFamily)
    (certificates : IndexedAlgebraicCertificateFamily F) :
    ClosureSource F where
  closure := closuresOfIndexedAlgebraicCertificates F certificates

@[simp]
theorem ofIndexedAlgebraicCertificates_toGeneratedChainFamilyClosures
    (F : GeneratedChainFamily)
    (certificates : IndexedAlgebraicCertificateFamily F) :
    (ofIndexedAlgebraicCertificates F certificates).toGeneratedChainFamilyClosures =
      closuresOfIndexedAlgebraicCertificates F certificates :=
  rfl

/-- Attach reduced metric data to a closure source to obtain the existing
`ExactFamilyClosure` input package. -/
def toExactFamilyHypotheses
    {F : GeneratedChainFamily}
    (S : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    ExactFamilyClosure.ExactFamilyHypotheses where
  family := F
  closure := S.toGeneratedChainFamilyClosures
  metric := metric

@[simp]
theorem toExactFamilyHypotheses_family
    {F : GeneratedChainFamily}
    (S : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    (S.toExactFamilyHypotheses metric).family = F :=
  rfl

@[simp]
theorem toExactFamilyHypotheses_closure
    {F : GeneratedChainFamily}
    (S : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    (S.toExactFamilyHypotheses metric).closure =
      S.toGeneratedChainFamilyClosures :=
  rfl

theorem toExactFamilyHypotheses_metric
    {F : GeneratedChainFamily}
    (S : ClosureSource F)
    (metric : ReducedMetricHypotheses F) :
    (S.toExactFamilyHypotheses metric).metric = metric :=
  rfl

end ClosureSource

/-- Public constructor name for the requested W20 target. -/
def generatedChainFamilyClosures
    {F : GeneratedChainFamily}
    (source : ClosureSource F) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures F :=
  source.toGeneratedChainFamilyClosures

@[simp]
theorem generatedChainFamilyClosures_apply
    {F : GeneratedChainFamily}
    (source : ClosureSource F)
    (k : Nat) (hk : 0 < k) :
    generatedChainFamilyClosures source k hk = source.closure k hk :=
  rfl

/-- Exact-family input packages already contain the requested closure target. -/
def closuresOfExactFamilyHypotheses
    (H : ExactFamilyClosure.ExactFamilyHypotheses) :
    GeneratedChainFamilyClosures H.family :=
  H.closure

@[simp]
theorem closuresOfExactFamilyHypotheses_apply
    (H : ExactFamilyClosure.ExactFamilyHypotheses)
    (k : Nat) (hk : 0 < k) :
    closuresOfExactFamilyHypotheses H k hk = H.closure k hk :=
  rfl

/-! ## Role-hinged and generated-family adapters -/

/-- Role-hinged generated-closure families project directly to generated-chain
closure families. -/
def closuresOfRoleHingedGeneratedClosureFamily
    (F : GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :
    GeneratedChainFamilyClosures F.toGeneratedChainFamily :=
  F.toGeneratedChainFamilyClosures

@[simp]
theorem closuresOfRoleHingedGeneratedClosureFamily_apply
    (F : GeneratedMetricClosure.RoleHingedGeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    closuresOfRoleHingedGeneratedClosureFamily F k hk =
      F.closure k hk :=
  rfl

/-- The corresponding closure source for a role-hinged generated-closure
family. -/
def sourceOfRoleHingedGeneratedClosureFamily
    (F : GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :
    ClosureSource F.toGeneratedChainFamily where
  closure := closuresOfRoleHingedGeneratedClosureFamily F

@[simp]
theorem sourceOfRoleHingedGeneratedClosureFamily_closure
    (F : GeneratedMetricClosure.RoleHingedGeneratedClosureFamily) :
    (sourceOfRoleHingedGeneratedClosureFamily F).closure =
      closuresOfRoleHingedGeneratedClosureFamily F :=
  rfl

/-- A bare role-hinged period-search family, before separation is attached,
still determines a generated-chain family. -/
def roleHingedPeriodSearchGeneratedChainFamily
    (F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily) :
    GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

@[simp]
theorem roleHingedPeriodSearchGeneratedChainFamily_O
    (F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (roleHingedPeriodSearchGeneratedChainFamily F).O k hk =
      F.transitions.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem roleHingedPeriodSearchGeneratedChainFamily_base
    (F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (roleHingedPeriodSearchGeneratedChainFamily F).base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem roleHingedPeriodSearchGeneratedChainFamily_orientation
    (F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (roleHingedPeriodSearchGeneratedChainFamily F).orientation k hk =
      F.orientation k hk :=
  rfl

/-- Exact indexed period-search certificates in a role-hinged period-search
family produce the requested generated-chain closure target. -/
def closuresOfRoleHingedPeriodSearchFamily
    (F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily) :
    GeneratedChainFamilyClosures
      (roleHingedPeriodSearchGeneratedChainFamily F) :=
  closuresOfIndexedAlgebraicCertificates
    (roleHingedPeriodSearchGeneratedChainFamily F) F.period

/-- Add explicit cross-block lower bounds to a period-search family and keep
the closure projection definitionally compatible with the role-hinged
generated-closure facade. -/
theorem closuresOfRoleHingedPeriodSearchFamily_eq_crossBlockRoute
    {F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily}
    (H : CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F) :
    closuresOfRoleHingedPeriodSearchFamily F =
      closuresOfRoleHingedGeneratedClosureFamily
        H.toRoleHingedGeneratedClosureFamily := by
  funext k hk
  exact Subsingleton.elim _ _

/-- The exact-family role-hinged period-search/cross-block package also
projects to generated-chain closures. -/
def closuresOfRoleHingedPeriodSearchCrossBlockFamily
    (F : ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily) :
    GeneratedChainFamilyClosures
      F.toRoleHingedGeneratedClosureFamily.toGeneratedChainFamily :=
  closuresOfRoleHingedGeneratedClosureFamily
    F.toRoleHingedGeneratedClosureFamily

@[simp]
theorem closuresOfRoleHingedPeriodSearchCrossBlockFamily_apply
    (F : ExactFamilyClosure.RoleHingedPeriodSearchCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    closuresOfRoleHingedPeriodSearchCrossBlockFamily F k hk =
      F.closure k hk :=
  rfl

/-! ## Concrete finite-search adapters -/

/-- Concrete period-search data alone determines a generated-chain family. -/
def concretePeriodSearchGeneratedChainFamily
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

@[simp]
theorem concretePeriodSearchGeneratedChainFamily_orientation
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    (concretePeriodSearchGeneratedChainFamily F).orientation k hk =
      F.orientation k hk :=
  rfl

/-- The exact equations in concrete period-search data produce generated-chain
closures before any separation data is added. -/
def closuresOfConcretePeriodSearchData
    (F : ConcretePeriodSearchFamily.PeriodSearchData) :
    GeneratedChainFamilyClosures
      (concretePeriodSearchGeneratedChainFamily F) :=
  fun k hk => F.closure k hk

@[simp]
theorem closuresOfConcretePeriodSearchData_apply
    (F : ConcretePeriodSearchFamily.PeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    closuresOfConcretePeriodSearchData F k hk = F.closure k hk :=
  rfl

/-- Concrete period-search plus cross-block data keeps the same closure source
while adding the metric data elsewhere. -/
def closuresOfConcreteCrossBlockFamily
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    GeneratedChainFamilyClosures F.toGeneratedChainFamily :=
  fun k hk => F.periodSearch.closure k hk

@[simp]
theorem closuresOfConcreteCrossBlockFamily_apply
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    closuresOfConcreteCrossBlockFamily F k hk =
      F.periodSearch.closure k hk :=
  rfl

/-- The concrete cross-block closure projection agrees with the role-hinged
generated-closure family projection. -/
theorem closuresOfConcreteCrossBlockFamily_eq_roleHinged
    (F : ConcretePeriodSearchFamily.ConcreteCrossBlockFamily) :
    closuresOfConcreteCrossBlockFamily F =
      closuresOfRoleHingedGeneratedClosureFamily
        F.toRoleHingedGeneratedClosureFamily := by
  funext k hk
  exact Subsingleton.elim _ _

/-- A finite role-hinged search family projects to the generated-chain family
of its role-hinged generated-closure facade. -/
def finiteSearchGeneratedChainFamily
    (F : FiniteSearchCertificate.RoleHingedFiniteSearchFamily) :
    GeneratedChainFamily :=
  F.toRoleHingedGeneratedClosureFamily.toGeneratedChainFamily

/-- The indexed algebraic certificates in a finite role-hinged search family
produce generated-chain closures. -/
def closuresOfFiniteSearchFamily
    (F : FiniteSearchCertificate.RoleHingedFiniteSearchFamily) :
    GeneratedChainFamilyClosures (finiteSearchGeneratedChainFamily F) :=
  F.toRoleHingedGeneratedClosureFamily.toGeneratedChainFamilyClosures

@[simp]
theorem closuresOfFiniteSearchFamily_apply
    (F : FiniteSearchCertificate.RoleHingedFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    closuresOfFiniteSearchFamily F k hk =
      F.closure k hk :=
  rfl

/-- Search-facing role-hinge transition facts project through their finite
search family to generated-chain closures. -/
def closuresOfRoleHingeTransitionFactsFiniteSearchFamily
    (F :
      RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily) :
    GeneratedChainFamilyClosures
      F.toRoleHingedGeneratedClosureFamily.toGeneratedChainFamily :=
  closuresOfRoleHingedGeneratedClosureFamily
    F.toRoleHingedGeneratedClosureFamily

@[simp]
theorem closuresOfRoleHingeTransitionFactsFiniteSearchFamily_apply
    (F :
      RoleHingeFiniteFamilyBridge.RoleHingeTransitionFactsFiniteSearchFamily)
    (k : Nat) (hk : 0 < k) :
    closuresOfRoleHingeTransitionFactsFiniteSearchFamily F k hk =
      F.closure k hk :=
  rfl

/-- All-positive period-search data determines a generated-chain family before
the non-connector square-value tables are attached. -/
def allPositivePeriodSearchGeneratedChainFamily
    (F : FiniteSearchCertificate.AllPositivePeriodSearchData) :
    GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

/-- The all-positive period-search equations produce generated-chain
closures directly. -/
def closuresOfAllPositivePeriodSearchData
    (F : FiniteSearchCertificate.AllPositivePeriodSearchData) :
    GeneratedChainFamilyClosures
      (allPositivePeriodSearchGeneratedChainFamily F) :=
  fun k hk => F.closure k hk

@[simp]
theorem closuresOfAllPositivePeriodSearchData_apply
    (F : FiniteSearchCertificate.AllPositivePeriodSearchData)
    (k : Nat) (hk : 0 < k) :
    closuresOfAllPositivePeriodSearchData F k hk =
      F.closure k hk :=
  rfl

/-- The compact all-positive non-connector certificate exposes the same
generated-chain closure source through its role-hinged generated facade. -/
def closuresOfAllPositiveNonConnectorSqValueCertificate
    (C : FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate) :
    GeneratedChainFamilyClosures
      C.toRoleHingedGeneratedClosureFamily.toGeneratedChainFamily :=
  closuresOfRoleHingedGeneratedClosureFamily
    C.toRoleHingedGeneratedClosureFamily

@[simp]
theorem closuresOfAllPositiveNonConnectorSqValueCertificate_apply
    (C : FiniteSearchCertificate.AllPositiveNonConnectorSqValueCertificate)
    (k : Nat) (hk : 0 < k) :
    closuresOfAllPositiveNonConnectorSqValueCertificate C k hk =
      C.closure k hk :=
  rfl

end

end GeneratedChainClosureProducerW20
end PachToth
end ErdosProblems1066
