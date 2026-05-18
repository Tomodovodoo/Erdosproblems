import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.NonConnectorInstantiationW13
import ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20
import ErdosProblems1066.PachToth.ExplicitClosedPlacementInputPackageW20

set_option autoImplicit false

/-!
# W21 concrete value-matrix handoff to the W19 input package

This file connects the concrete non-connector value-matrix route to
`ExplicitClosedPlacementProducerW19.InputPackage`.

The reduced-metric route alone supplies only a generated family plus its metric
hypotheses.  The extra field needed by the W19 producer is the generated
closure family.  For a concrete value-matrix family, that closure is already
present in the carried `periodSearch` data, so the full W19 package is
inhabited.  For reduced-metric packages without period-search data, this file
records the exact closure obligation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConcreteValueMatrixToInputPackageW21

noncomputable section

abbrev W19InputPackage : Type :=
  ExplicitClosedPlacementProducerW19.InputPackage

abbrev GeneratedChainFamily : Type :=
  ExplicitClosedPlacementProducerW19.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementProducerW19.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  ExplicitClosedPlacementProducerW19.ReducedMetricHypotheses F

abbrev ConcreteValueMatrixFamily : Type :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

abbrev RoleHingedPeriodSearchFamily : Type :=
  NonConnectorSeparationW12.RoleHingedPeriodSearchFamily

abbrev GeneratedNonConnectorSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily F

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily F

abbrev NonConnectorValueMatrixFamily
    (F : RoleHingedPeriodSearchFamily) : Type :=
  ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F

abbrev ProducedReducedMetricPackage : Type :=
  ReducedMetricHypothesesProducerW20.ProducedReducedMetricPackage

/-- A fixed-family, fixed-metric W19 package still needs exactly the generated
closure field. -/
structure InputPackageOver
    (F : GeneratedChainFamily)
    (metric : ReducedMetricHypotheses F) where
  closure : GeneratedChainFamilyClosures F

namespace InputPackageOver

/-- Convert a fixed-family package-with-closure to the public W19 input
package. -/
def toInputPackage
    {F : GeneratedChainFamily}
    {metric : ReducedMetricHypotheses F}
    (P : InputPackageOver F metric) :
    W19InputPackage where
  family := F
  closure := P.closure
  metric := metric

@[simp]
theorem toInputPackage_family
    {F : GeneratedChainFamily}
    {metric : ReducedMetricHypotheses F}
    (P : InputPackageOver F metric) :
    P.toInputPackage.family = F :=
  rfl

@[simp]
theorem toInputPackage_closure
    {F : GeneratedChainFamily}
    {metric : ReducedMetricHypotheses F}
    (P : InputPackageOver F metric) :
    P.toInputPackage.closure = P.closure :=
  rfl

@[simp]
theorem toInputPackage_metric
    {F : GeneratedChainFamily}
    {metric : ReducedMetricHypotheses F}
    (P : InputPackageOver F metric) :
    P.toInputPackage.metric = metric :=
  rfl

end InputPackageOver

/-- Exact blocker for the reduced-metric handoff: once family and metric are
fixed, nonempty W19 input data is equivalent to the missing closure family. -/
theorem nonempty_inputPackageOver_iff_closure
    (F : GeneratedChainFamily)
    (metric : ReducedMetricHypotheses F) :
    Nonempty (InputPackageOver F metric) ↔
      GeneratedChainFamilyClosures F := by
  constructor
  · intro h
    rcases h with ⟨P⟩
    exact P.closure
  · intro closure
    exact ⟨{ closure := closure }⟩

/-- Package a produced reduced-metric family when its missing closure data is
supplied. -/
def inputPackageOverOfProducedReducedMetricPackage
    (P : ProducedReducedMetricPackage)
    (closure : GeneratedChainFamilyClosures P.family) :
    InputPackageOver P.family P.metric where
  closure := closure

/-- Exact blocker for a produced reduced-metric package. -/
theorem producedReducedMetricPackage_nonempty_inputPackageOver_iff_closure
    (P : ProducedReducedMetricPackage) :
    Nonempty (InputPackageOver P.family P.metric) ↔
      GeneratedChainFamilyClosures P.family :=
  nonempty_inputPackageOver_iff_closure P.family P.metric

/-- Convert a produced reduced-metric package to the W19 input package once
the closure family is supplied. -/
def inputPackageOfProducedReducedMetricPackage
    (P : ProducedReducedMetricPackage)
    (closure : GeneratedChainFamilyClosures P.family) :
    W19InputPackage :=
  (inputPackageOverOfProducedReducedMetricPackage P closure).toInputPackage

/-- The generated-chain family used by the concrete value-matrix route. -/
def generatedChainFamilyOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    GeneratedChainFamily :=
  ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged
    C.toRoleHingedPeriodSearchFamily

@[simp]
theorem generatedChainFamilyOfConcreteValueMatrixFamily_O
    (C : ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfConcreteValueMatrixFamily C).O k hk =
      C.periodSearch.transitions.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem generatedChainFamilyOfConcreteValueMatrixFamily_base
    (C : ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfConcreteValueMatrixFamily C).base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem generatedChainFamilyOfConcreteValueMatrixFamily_orientation
    (C : ConcreteValueMatrixFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfConcreteValueMatrixFamily C).orientation k hk =
      C.periodSearch.orientation k hk :=
  rfl

/-- Concrete period-search data supplies the closure field missing from a bare
reduced-metric package. -/
def generatedChainFamilyClosuresOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    GeneratedChainFamilyClosures
      (generatedChainFamilyOfConcreteValueMatrixFamily C) := by
  intro k hk
  exact C.periodSearch.closure k hk

/-- The reduced metrics for the concrete value-matrix route, routed through
the W20 producer. -/
def reducedMetricHypothesesOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ReducedMetricHypotheses
      (generatedChainFamilyOfConcreteValueMatrixFamily C) :=
  ReducedMetricHypothesesProducerW20.ofConcreteValueMatrixFamily C

/-- Concrete value matrices inhabit the fixed-family input package because
their period-search component supplies closure. -/
def inputPackageOverOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    InputPackageOver
      (generatedChainFamilyOfConcreteValueMatrixFamily C)
      (reducedMetricHypothesesOfConcreteValueMatrixFamily C) where
  closure := generatedChainFamilyClosuresOfConcreteValueMatrixFamily C

/-- Actual W19 input package produced from concrete non-connector value
matrices. -/
def inputPackageOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    W19InputPackage :=
  (inputPackageOverOfConcreteValueMatrixFamily C).toInputPackage

@[simp]
theorem inputPackageOfConcreteValueMatrixFamily_family
    (C : ConcreteValueMatrixFamily) :
    (inputPackageOfConcreteValueMatrixFamily C).family =
      generatedChainFamilyOfConcreteValueMatrixFamily C :=
  rfl

@[simp]
theorem inputPackageOfConcreteValueMatrixFamily_closure
    (C : ConcreteValueMatrixFamily) :
    (inputPackageOfConcreteValueMatrixFamily C).closure =
      generatedChainFamilyClosuresOfConcreteValueMatrixFamily C :=
  rfl

@[simp]
theorem inputPackageOfConcreteValueMatrixFamily_metric
    (C : ConcreteValueMatrixFamily) :
    (inputPackageOfConcreteValueMatrixFamily C).metric =
      reducedMetricHypothesesOfConcreteValueMatrixFamily C :=
  rfl

/-- The metric field is exactly the W20 concrete-value-matrix route. -/
theorem inputPackageOfConcreteValueMatrixFamily_metric_eq_w20_route
    (C : ConcreteValueMatrixFamily) :
    (inputPackageOfConcreteValueMatrixFamily C).metric =
      ReducedMetricHypothesesProducerW20.ofConcreteValueMatrixFamily C :=
  rfl

/-- The metric field is also exactly the route through
`NonConnectorInstantiationW13.generatedTableFamilyOfConcreteValueMatrixFamily`.
-/
theorem inputPackageOfConcreteValueMatrixFamily_metric_eq_nonConnectorRoute
    (C : ConcreteValueMatrixFamily) :
    (inputPackageOfConcreteValueMatrixFamily C).metric =
      ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
        (NonConnectorInstantiationW13.generatedTableFamilyOfConcreteValueMatrixFamily
          C) :=
  rfl

/-- The W19 explicit closed-placement certificates obtained from concrete
value matrices. -/
def explicitClosedPlacementCertificateFamilyOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ExplicitClosedPlacementProducerW19.ExplicitClosedPlacementCertificateFamily :=
  (inputPackageOfConcreteValueMatrixFamily C)
    |>.explicitClosedPlacementCertificate

/-- Exact-block target routed through the actual W19 input package. -/
theorem targetUpperConstructionFiveSixteenOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (inputPackageOfConcreteValueMatrixFamily C)
    |>.targetUpperConstructionFiveSixteen

/-- Arbitrary-vertex target routed through the actual W19 input package. -/
theorem targetUpperConstructionFiveSixteenArbitraryOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (inputPackageOfConcreteValueMatrixFamily C)
    |>.targetUpperConstructionFiveSixteenArbitrary

/-- Exact closure blocker for the route beginning with generated
non-connector square-distance tables. -/
theorem generatedTableFamily_nonempty_inputPackageOver_iff_closure
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    Nonempty
      (InputPackageOver
        (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F)
        (ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
          T)) ↔
      GeneratedChainFamilyClosures
        (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F) :=
  nonempty_inputPackageOver_iff_closure
    (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F)
    (ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
      T)

/-- Exact closure blocker for the indexed-table route exported by
`NonConnectorInstantiationW13`. -/
theorem indexedTableFamily_nonempty_inputPackageOver_iff_closure
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    Nonempty
      (InputPackageOver
        (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F)
        (ReducedMetricHypothesesProducerW20.ofIndexedNonConnectorCrossBlockSqDistanceTableFamily
          T)) ↔
      GeneratedChainFamilyClosures
        (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F) :=
  nonempty_inputPackageOver_iff_closure
    (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F)
    (ReducedMetricHypothesesProducerW20.ofIndexedNonConnectorCrossBlockSqDistanceTableFamily
      T)

/-- Exact closure blocker for a value-matrix family when only its reduced
metric route is used and no period-search closure data is present. -/
theorem valueMatrixFamily_nonempty_inputPackageOver_iff_closure
    {F : RoleHingedPeriodSearchFamily}
    (M : NonConnectorValueMatrixFamily F) :
    Nonempty
      (InputPackageOver
        (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F)
        (ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
          (NonConnectorInstantiationW13.generatedTableFamilyOfValueMatrixFamily
            M))) ↔
      GeneratedChainFamilyClosures
        (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F) :=
  nonempty_inputPackageOver_iff_closure
    (ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F)
    (ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
      (NonConnectorInstantiationW13.generatedTableFamilyOfValueMatrixFamily M))

end

end ConcreteValueMatrixToInputPackageW21
end PachToth
end ErdosProblems1066
