import ErdosProblems1066.PachToth.DirectCrossBlockInputPackageW24
import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24

set_option autoImplicit false

/-!
# W25 direct full-metric source inhabitation

The W24 direct route reduced the full-metric source to concrete
non-connector lower tables plus exact-local preservation for the selected
role-hinge transitions.  Here the latter field is filled by the existing
exact-local geometry lemma for role-hinge transitions, so a concrete
lower-table package directly inhabits the exact-base full-metric source
surface and conditionally yields both target endpoints.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DirectFullMetricSourceInhabitationW25

open FiniteGraph

noncomputable section

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  DirectCrossBlockInputPackageW24.ConcreteValueMatrixRowPackage

abbrev ExactBaseFullMetricSourceFields : Type :=
  DirectCrossBlockInputPackageW24.ExactBaseFullMetricSourceFields

abbrev FullMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness

abbrev ExactLocalPreservation
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  DirectCrossBlockInputPackageW24.ExactLocalPreservation O

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! ## Concrete lower tables fill the exact-local field -/

def exactLocalPreservationOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactLocalPreservation
      C.periodSearch.transitions.toFigure2TransitionObligations :=
  GeneratedMetricClosure.roleHingeTransitions_preserveExactLocalSqDistances
    C.periodSearch.transitions

def fullMetricSourceFieldsOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactBaseFullMetricSourceFields :=
  DirectCrossBlockInputPackageW24.fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    C (exactLocalPreservationOfConcreteLowerTables C)

theorem nonempty_fullMetricSourceFields_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty ExactBaseFullMetricSourceFields :=
  Nonempty.intro (fullMetricSourceFieldsOfConcreteLowerTables C)

theorem nonempty_fullMetricSourceFields_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily ->
      Nonempty ExactBaseFullMetricSourceFields := by
  intro h
  cases h with
  | intro C =>
      exact nonempty_fullMetricSourceFields_of_concreteLowerTables C

def fullMetricClosedPlacementWitnessOfConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    FullMetricClosedPlacementWitness :=
  FullMetricClosedPlacementW24.fullMetricWitnessOfExactBaseSourceFields
    (fullMetricSourceFieldsOfConcreteLowerTables C)

/-! ## Exact iff/decomposition for the local direct package -/

structure DirectFullMetricSourcePackage where
  lowerTables : ConcreteNonConnectorLowerTableFamily
  exactLocal :
    ExactLocalPreservation
      lowerTables.periodSearch.transitions.toFigure2TransitionObligations

namespace DirectFullMetricSourcePackage

def ofConcreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    DirectFullMetricSourcePackage where
  lowerTables := C
  exactLocal := exactLocalPreservationOfConcreteLowerTables C

def sourceFields
    (P : DirectFullMetricSourcePackage) :
    ExactBaseFullMetricSourceFields :=
  DirectCrossBlockInputPackageW24.fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    P.lowerTables P.exactLocal

def closedPlacementWitness
    (P : DirectFullMetricSourcePackage) :
    FullMetricClosedPlacementWitness :=
  FullMetricClosedPlacementW24.fullMetricWitnessOfExactBaseSourceFields
    P.sourceFields

theorem targetUpperConstructionFiveSixteen
    (P : DirectFullMetricSourcePackage) :
    ExactTarget :=
  DirectCrossBlockInputPackageW24.targetUpperConstructionFiveSixteen_of_concreteLowerTables_exactLocal
    P.lowerTables P.exactLocal

theorem targetUpperConstructionFiveSixteenArbitrary
    (P : DirectFullMetricSourcePackage) :
    ArbitraryTarget :=
  DirectCrossBlockInputPackageW24.targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTables_exactLocal
    P.lowerTables P.exactLocal

theorem targetUpperConstructionFiveSixteenAt
    (P : DirectFullMetricSourcePackage) (n : Nat) :
    FixedTarget n :=
  P.targetUpperConstructionFiveSixteenArbitrary n

theorem targetUpperConstructionFiveSixteen_viaClosedPlacement
    (P : DirectFullMetricSourcePackage) :
    ExactTarget :=
  P.closedPlacementWitness.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_viaClosedPlacement
    (P : DirectFullMetricSourcePackage) :
    ArbitraryTarget :=
  P.closedPlacementWitness.targetUpperConstructionFiveSixteenArbitrary

end DirectFullMetricSourcePackage

abbrev DirectFullMetricSourcePackageFields : Prop :=
  Exists fun C : ConcreteNonConnectorLowerTableFamily =>
    ExactLocalPreservation
      C.periodSearch.transitions.toFigure2TransitionObligations

theorem nonempty_directFullMetricSourcePackage_iff_fields :
    Nonempty DirectFullMetricSourcePackage <->
      DirectFullMetricSourcePackageFields := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P =>
        exact Exists.intro P.lowerTables P.exactLocal
  case mpr =>
    intro h
    cases h with
    | intro C exactLocal =>
        exact Nonempty.intro
          { lowerTables := C
            exactLocal := exactLocal }

theorem directFullMetricSourcePackageFields_iff_concreteLowerTables :
    DirectFullMetricSourcePackageFields <->
      Nonempty ConcreteNonConnectorLowerTableFamily := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro C _ =>
        exact Nonempty.intro C
  case mpr =>
    intro h
    cases h with
    | intro C =>
        exact Exists.intro C (exactLocalPreservationOfConcreteLowerTables C)

theorem nonempty_directFullMetricSourcePackage_iff_concreteLowerTables :
    Nonempty DirectFullMetricSourcePackage <->
      Nonempty ConcreteNonConnectorLowerTableFamily :=
  Iff.trans nonempty_directFullMetricSourcePackage_iff_fields
    directFullMetricSourcePackageFields_iff_concreteLowerTables

theorem nonempty_fullMetricSourceFields_of_directPackage
    (H : Nonempty DirectFullMetricSourcePackage) :
    Nonempty ExactBaseFullMetricSourceFields := by
  cases H with
  | intro P =>
      exact Nonempty.intro P.sourceFields

theorem nonempty_fullMetricSourceFields_iff_directPackage :
    Nonempty DirectFullMetricSourcePackage ->
      Nonempty ExactBaseFullMetricSourceFields :=
  nonempty_fullMetricSourceFields_of_directPackage

/-! ## Concrete cross-block row package bridge -/

def concreteLowerTablesOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteNonConnectorLowerTableFamily :=
  DirectCrossBlockInputPackageW24.concreteLowerTablesOfRowPackage P

def directFullMetricSourcePackageOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    DirectFullMetricSourcePackage :=
  DirectFullMetricSourcePackage.ofConcreteLowerTables
    (concreteLowerTablesOfRowPackage P)

theorem nonempty_directFullMetricSourcePackage_of_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty DirectFullMetricSourcePackage := by
  intro h
  cases h with
  | intro P =>
      exact Nonempty.intro (directFullMetricSourcePackageOfRowPackage P)

theorem nonempty_fullMetricSourceFields_of_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty ExactBaseFullMetricSourceFields := by
  intro h
  exact
    nonempty_fullMetricSourceFields_of_directPackage
      (nonempty_directFullMetricSourcePackage_of_rowPackage h)

/-! ## Conditional exact and arbitrary target reductions -/

theorem targetUpperConstructionFiveSixteen_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ExactTarget :=
  DirectCrossBlockInputPackageW24.targetUpperConstructionFiveSixteen_of_concreteLowerTables_exactLocal
    C (exactLocalPreservationOfConcreteLowerTables C)

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) :
    ArbitraryTarget :=
  DirectCrossBlockInputPackageW24.targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTables_exactLocal
    C (exactLocalPreservationOfConcreteLowerTables C)

theorem targetUpperConstructionFiveSixteenAt_of_concreteLowerTables
    (C : ConcreteNonConnectorLowerTableFamily) (n : Nat) :
    FixedTarget n :=
  targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTables C n

theorem targetUpperConstructionFiveSixteen_of_directPackage
    (P : DirectFullMetricSourcePackage) :
    ExactTarget :=
  P.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_directPackage
    (P : DirectFullMetricSourcePackage) :
    ArbitraryTarget :=
  P.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_directPackage
    (P : DirectFullMetricSourcePackage) (n : Nat) :
    FixedTarget n :=
  P.targetUpperConstructionFiveSixteenAt n

theorem targetUpperConstructionFiveSixteen_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily -> ExactTarget := by
  intro h
  cases h with
  | intro C =>
      exact targetUpperConstructionFiveSixteen_of_concreteLowerTables C

theorem targetUpperConstructionFiveSixteenArbitrary_of_nonempty_concreteLowerTables :
    Nonempty ConcreteNonConnectorLowerTableFamily -> ArbitraryTarget := by
  intro h
  cases h with
  | intro C =>
      exact targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTables C

theorem targetUpperConstructionFiveSixteenAt_of_nonempty_concreteLowerTables
    (H : Nonempty ConcreteNonConnectorLowerTableFamily) (n : Nat) :
    FixedTarget n :=
  targetUpperConstructionFiveSixteenArbitrary_of_nonempty_concreteLowerTables H n

theorem targetUpperConstructionFiveSixteen_of_nonempty_directPackage :
    Nonempty DirectFullMetricSourcePackage -> ExactTarget := by
  intro h
  cases h with
  | intro P =>
      exact P.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_nonempty_directPackage :
    Nonempty DirectFullMetricSourcePackage -> ArbitraryTarget := by
  intro h
  cases h with
  | intro P =>
      exact P.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt_of_nonempty_directPackage
    (H : Nonempty DirectFullMetricSourcePackage) (n : Nat) :
    FixedTarget n :=
  targetUpperConstructionFiveSixteenArbitrary_of_nonempty_directPackage H n

theorem targetUpperConstructionFiveSixteen_of_rowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ExactTarget :=
  (directFullMetricSourcePackageOfRowPackage P).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_rowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ArbitraryTarget :=
  (directFullMetricSourcePackageOfRowPackage P).targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteen_of_nonempty_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage -> ExactTarget := by
  intro h
  cases h with
  | intro P =>
      exact targetUpperConstructionFiveSixteen_of_rowPackage P

theorem targetUpperConstructionFiveSixteenArbitrary_of_nonempty_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage -> ArbitraryTarget := by
  intro h
  cases h with
  | intro P =>
      exact targetUpperConstructionFiveSixteenArbitrary_of_rowPackage P

end

end DirectFullMetricSourceInhabitationW25
end PachToth
end ErdosProblems1066
