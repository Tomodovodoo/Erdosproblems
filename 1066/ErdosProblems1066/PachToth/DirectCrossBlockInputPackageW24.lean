import ErdosProblems1066.PachToth.ConcreteCrossBlockFamilyInhabitationW23
import ErdosProblems1066.PachToth.ExactBaseFullMetricConcreteW23
import ErdosProblems1066.PachToth.GeometricSoundness

set_option autoImplicit false

/-!
# W24 direct cross-block input-package attempt

This file records the direct route from concrete cross-block lower tables to
the generated-chain source surfaces.  The full-metric route closes from exact
local geometry.  The reduced W20 `SourceFields`/W19 `InputPackage` route has
one additional, explicitly named field: all selected transitions must preserve
same-block distances for arbitrary sources.
-/

namespace ErdosProblems1066
namespace PachToth
namespace DirectCrossBlockInputPackageW24

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev W19InputPackage : Type :=
  GeneratedChainFamilyProducerW20.InputPackage

abbrev W20SourceFields : Type :=
  GeneratedChainFamilyProducerW20.SourceFields

abbrev ExactBaseFullMetricSourceFields : Type :=
  ExactBaseFullMetricConcreteW23.ExactBaseFullMetricSourceFields

abbrev ConcreteNonConnectorLowerTableFamily : Type :=
  ConcreteCrossBlockInputPackageW22.ConcreteNonConnectorLowerTableFamily

abbrev ConcreteCrossBlockFamily : Type :=
  ConcreteCrossBlockFamilyInhabitationW23.ConcreteCrossBlockFamily

abbrev ConcreteValueMatrixRowPackage : Type :=
  ConcreteCrossBlockFamilyInhabitationW23.ConcreteValueMatrixRowPackage

abbrev RoleHingedPeriodSearchFamily : Type :=
  ConcreteCrossBlockLowerTable.RoleHingedPeriodSearchFamily

abbrev NonConnectorLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily F

abbrev ExactLocalPreservation
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  GeneratedMetricClosure.GeneratedTransitionsPreserveExactLocalSqDistances O

abbrev ReducedTransitionPreservation
    (O : Figure2Certificate.SameOppositeTransitionObligations) : Prop :=
  GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances O

abbrev DirectEdgeSoundness (k : Nat) (hk : 0 < k) : Type :=
  GeometricSoundness.ExplicitEdgeSoundness k hk

/-! ## Concrete lower tables as direct exact-base data -/

def concreteClosure
    (C : ConcreteNonConnectorLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      C.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.periodSearch.orientation k hk) :=
  C.periodSearch.closure k hk

def concreteSeparation
    (C : ConcreteNonConnectorLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      C.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.periodSearch.orientation k hk) :=
  C.separated k hk

def concreteSameBlockOfExactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      C.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (C.periodSearch.orientation k hk) :=
  GeneratedMetricClosure.generatedSameBlockIsometry_of_exactLocalSqDistances
    C.periodSearch.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (C.periodSearch.orientation k hk)
    GeneratedMetricClosure.exactBase_matchesExactLocalSqDistances
    exactLocal

def fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    ExactBaseFullMetricSourceFields where
  O := C.periodSearch.transitions.toFigure2TransitionObligations
  orientation := C.periodSearch.orientation
  closure := concreteClosure C
  metric := fun k hk =>
    { separated := concreteSeparation C k hk
      same_block_isometry :=
        concreteSameBlockOfExactLocal C exactLocal k hk }

theorem targetUpperConstructionFiveSixteen_of_concreteLowerTables_exactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    C exactLocal).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteLowerTables_exactLocal
    (C : ConcreteNonConnectorLowerTableFamily)
    (exactLocal :
      ExactLocalPreservation
        C.periodSearch.transitions.toFigure2TransitionObligations) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
    C exactLocal).targetUpperConstructionFiveSixteenArbitrary

/-! ## Reduced W20 fields and the precise extra direct field -/

abbrev MissingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) : Prop :=
  ReducedTransitionPreservation
    C.periodSearch.transitions.toFigure2TransitionObligations

structure DirectReducedSourceFieldsOver
    (C : ConcreteNonConnectorLowerTableFamily) where
  transition_preserves_same_block_distances :
    MissingDirectReducedInputField C

namespace DirectReducedSourceFieldsOver

def toSourceFields
    {C : ConcreteNonConnectorLowerTableFamily}
    (D : DirectReducedSourceFieldsOver C) :
    W20SourceFields where
  O := fun _ _ => C.periodSearch.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := C.periodSearch.orientation
  closure := concreteClosure C
  separated := concreteSeparation C
  base_same_block_isometry := fun _ _ =>
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances := fun _ _ =>
    D.transition_preserves_same_block_distances

def toInputPackage
    {C : ConcreteNonConnectorLowerTableFamily}
    (D : DirectReducedSourceFieldsOver C) :
    W19InputPackage :=
  D.toSourceFields.toInputPackage

theorem targetUpperConstructionFiveSixteen
    {C : ConcreteNonConnectorLowerTableFamily}
    (D : DirectReducedSourceFieldsOver C) :
    PachToth.targetUpperConstructionFiveSixteen :=
  D.toSourceFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    {C : ConcreteNonConnectorLowerTableFamily}
    (D : DirectReducedSourceFieldsOver C) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  D.toSourceFields.targetUpperConstructionFiveSixteenArbitrary

end DirectReducedSourceFieldsOver

theorem nonempty_directReducedSourceFieldsOver_iff_missingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) :
    Nonempty (DirectReducedSourceFieldsOver C) <->
      MissingDirectReducedInputField C := by
  constructor
  · intro h
    exact h.elim (fun D => D.transition_preserves_same_block_distances)
  · intro h
    exact Nonempty.intro
      { transition_preserves_same_block_distances := h }

theorem nonempty_w20SourceFields_of_missingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C -> Nonempty W20SourceFields := by
  intro h
  exact
    Nonempty.intro
      (({ transition_preserves_same_block_distances := h } :
          DirectReducedSourceFieldsOver C).toSourceFields)

theorem nonempty_w19InputPackage_of_missingDirectReducedInputField
    (C : ConcreteNonConnectorLowerTableFamily) :
    MissingDirectReducedInputField C -> Nonempty W19InputPackage := by
  intro h
  exact
    Nonempty.intro
      (({ transition_preserves_same_block_distances := h } :
          DirectReducedSourceFieldsOver C).toInputPackage)

/-! ## Bare table obstruction spelling -/

abbrev MissingBareLowerTableClosureField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)

abbrev MissingBareLowerTableReducedField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  ReducedTransitionPreservation F.transitions.toFigure2TransitionObligations

structure DirectReducedSourceFieldsOfBareLowerTables
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) where
  closure : MissingBareLowerTableClosureField F
  transition_preserves_same_block_distances :
    MissingBareLowerTableReducedField F

namespace DirectReducedSourceFieldsOfBareLowerTables

def toSourceFields
    {F : RoleHingedPeriodSearchFamily}
    {T : NonConnectorLowerTableFamily F}
    (D : DirectReducedSourceFieldsOfBareLowerTables T) :
    W20SourceFields where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation
  closure := D.closure
  separated := T.separated
  base_same_block_isometry := fun _ _ =>
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances := fun _ _ =>
    D.transition_preserves_same_block_distances

def toInputPackage
    {F : RoleHingedPeriodSearchFamily}
    {T : NonConnectorLowerTableFamily F}
    (D : DirectReducedSourceFieldsOfBareLowerTables T) :
    W19InputPackage :=
  D.toSourceFields.toInputPackage

end DirectReducedSourceFieldsOfBareLowerTables

theorem nonempty_directReducedSourceFieldsOfBareLowerTables_iff_missingFields
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorLowerTableFamily F) :
    Nonempty (DirectReducedSourceFieldsOfBareLowerTables T) <->
      MissingBareLowerTableClosureField F /\
        MissingBareLowerTableReducedField F := by
  constructor
  · intro h
    exact h.elim (fun D =>
      And.intro D.closure D.transition_preserves_same_block_distances)
  · intro h
    exact Nonempty.intro
      { closure := h.1
        transition_preserves_same_block_distances := h.2 }

/-! ## Concrete W23 source routes remain compatible -/

def concreteLowerTablesOfRowPackage
    (P : ConcreteValueMatrixRowPackage) :
    ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockFamilyInhabitationW23.concreteLowerTableFamilyOfRowPackage P

abbrev rowPackageTransitionObligations
    (P : ConcreteValueMatrixRowPackage) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  (concreteLowerTablesOfRowPackage P).periodSearch.transitions
    |>.toFigure2TransitionObligations

theorem nonempty_concreteLowerTables_of_rowPackage :
    Nonempty ConcreteValueMatrixRowPackage ->
      Nonempty ConcreteNonConnectorLowerTableFamily :=
  ConcreteCrossBlockFamilyInhabitationW23.nonempty_concreteLowerTableFamily_of_rowPackage

theorem nonempty_fullMetricSourceFields_of_rowPackage_exactLocal
    (P : ConcreteValueMatrixRowPackage)
    (exactLocal : ExactLocalPreservation (rowPackageTransitionObligations P)) :
    Nonempty ExactBaseFullMetricSourceFields :=
  Nonempty.intro
    (fullMetricSourceFieldsOfConcreteLowerTablesAndExactLocal
      (concreteLowerTablesOfRowPackage P) exactLocal)

/-! ## Geometric-soundness compatibility hook -/

def indexedRealizationOfEdgeSoundness
    {k : Nat} {hk : 0 < k}
    (G : DirectEdgeSoundness k hk) :
    IndexedChain.IndexedChainRealization k hk :=
  G.toIndexedChainRealization

end

end DirectCrossBlockInputPackageW24
end PachToth
end ErdosProblems1066
