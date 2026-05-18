import ErdosProblems1066.PachToth.AlternativeValueMatrixFamilyW24
import ErdosProblems1066.PachToth.FreePlacementSourceFieldsW24
import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24
import ErdosProblems1066.PachToth.DirectCrossBlockInputPackageW24
import ErdosProblems1066.PachToth.PachTothW23RouteAudit

set_option autoImplicit false

/-!
# W25 generated closure-metric package inhabitation

This file keeps the W23 live route explicit: a single generated family, a
same-family closure source, and same-family reduced metric fields.  The W24
non-role/direct/full-metric/free-placement surfaces are bridged to that
package exactly when they supply those same-family reduced fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedClosureMetricPackageInhabitationW25

noncomputable section

abbrev GeneratedChainFamily : Type :=
  PachTothW23RouteAudit.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainFamilyProducerW20.GeneratedChainFamilyClosures F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedChainFamilyProducerW20.ReducedMetricHypotheses F

abbrev ClosureSource
    (F : GeneratedChainFamily) :=
  PachTothW23RouteAudit.ClosureSource F

abbrev ReducedMetricFields
    (F : GeneratedChainFamily) :=
  PachTothW23RouteAudit.ReducedMetricFields F

abbrev RawSourceFields : Type :=
  PachTothW23RouteAudit.RawSourceFields

abbrev GeneratedClosureMetricRowPackage : Type :=
  PachTothW23RouteAudit.GeneratedClosureMetricRowPackage

abbrev KnownBoundsGate : Prop :=
  PachTothW23RouteAudit.KnownBoundsGate

def closureSourceOfClosures
    {F : GeneratedChainFamily}
    (closure : GeneratedChainFamilyClosures F) :
    ClosureSource F :=
  GeneratedChainClosureProducerW20.ClosureSource.ofClosures closure

def reducedMetricFieldsOfReducedMetricHypotheses
    {F : GeneratedChainFamily}
    (metric : ReducedMetricHypotheses F) :
    ReducedMetricFields F where
  separated := fun k hk => (metric.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (metric.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (metric.metric k hk).transition_preserves_same_block_distances

def generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields
    {F : GeneratedChainFamily}
    (closure : ClosureSource F)
    (metric : ReducedMetricFields F) :
    GeneratedClosureMetricRowPackage where
  family := F
  closureSource := closure
  reducedMetric := metric

@[simp]
theorem generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields_family
    {F : GeneratedChainFamily}
    (closure : ClosureSource F)
    (metric : ReducedMetricFields F) :
    (generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields
      closure metric).family = F :=
  rfl

def generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields
    (closureSourceOfClosures closure)
    (reducedMetricFieldsOfReducedMetricHypotheses metric)

@[simp]
theorem generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses_family
    (F : GeneratedChainFamily)
    (closure : GeneratedChainFamilyClosures F)
    (metric : ReducedMetricHypotheses F) :
    (generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
      F closure metric).family = F :=
  rfl

def generatedClosureMetricRowPackageOfRawSourceFields
    (S : RawSourceFields) :
    GeneratedClosureMetricRowPackage :=
  PachTothW23RouteAudit.generatedClosureMetricRowPackageOfRawSourceFields S

@[simp]
theorem generatedClosureMetricRowPackageOfRawSourceFields_family
    (S : RawSourceFields) :
    (generatedClosureMetricRowPackageOfRawSourceFields S).family = S.family :=
  rfl

theorem exists_generatedClosureMetricRowPackage_with_family_iff_closureSource_and_reducedMetricFields
    (F : GeneratedChainFamily) :
    (Exists fun P : GeneratedClosureMetricRowPackage => P.family = F) <->
      Nonempty (ClosureSource F) /\ Nonempty (ReducedMetricFields F) := by
  constructor
  · intro h
    cases h with
    | intro P hfamily =>
        cases hfamily
        exact
          And.intro
            (Nonempty.intro P.closureSource)
            (Nonempty.intro P.reducedMetric)
  · intro h
    cases h.1 with
    | intro closure =>
        cases h.2 with
        | intro metric =>
            exact
              Exists.intro
                (generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields
                  closure metric)
                rfl

theorem exists_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
    (F : GeneratedChainFamily) :
    (Exists fun P : GeneratedClosureMetricRowPackage => P.family = F) <->
      GeneratedChainFamilyClosures F /\ ReducedMetricHypotheses F := by
  constructor
  · intro h
    have hfields :=
      (exists_generatedClosureMetricRowPackage_with_family_iff_closureSource_and_reducedMetricFields
        F).1 h
    cases hfields.1 with
    | intro closure =>
        cases hfields.2 with
        | intro metric =>
            exact
              And.intro
                closure.toGeneratedChainFamilyClosures
                metric.toReducedMetricHypotheses
  · intro h
    exact
      (exists_generatedClosureMetricRowPackage_with_family_iff_closureSource_and_reducedMetricFields
        F).2
        (And.intro
          (Nonempty.intro (closureSourceOfClosures h.1))
          (Nonempty.intro
            (reducedMetricFieldsOfReducedMetricHypotheses h.2)))

theorem exists_generatedClosureMetricRowPackage_with_family_iff_rawSourceFields_with_family
    (F : GeneratedChainFamily) :
    (Exists fun P : GeneratedClosureMetricRowPackage => P.family = F) <->
      Exists fun S : RawSourceFields => S.family = F := by
  constructor
  · intro h
    have hfields :=
      (exists_generatedClosureMetricRowPackage_with_family_iff_closureSource_and_reducedMetricFields
        F).1 h
    exact
      (GeneratedChainSourceFieldsInhabitationW22.exists_sourceFields_with_family_iff_closureSource_and_reducedMetricFields
        F).2 hfields
  · intro h
    have hfields :=
      (GeneratedChainSourceFieldsInhabitationW22.exists_sourceFields_with_family_iff_closureSource_and_reducedMetricFields
        F).1 h
    exact
      (exists_generatedClosureMetricRowPackage_with_family_iff_closureSource_and_reducedMetricFields
        F).2 hfields

theorem nonempty_generatedClosureMetricRowPackage_iff_exists_closures_and_reducedMetricHypotheses :
    Nonempty GeneratedClosureMetricRowPackage <->
      Exists fun F : GeneratedChainFamily =>
        GeneratedChainFamilyClosures F /\ ReducedMetricHypotheses F := by
  constructor
  · intro h
    cases h with
    | intro P =>
        exact
          Exists.intro P.family
            ((exists_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
              P.family).1 (Exists.intro P rfl))
  · intro h
    cases h with
    | intro F hF =>
        exact
          let P :=
            generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
              F hF.1 hF.2
          Nonempty.intro P

theorem knownBoundsGate_iff_generatedClosureMetricRowPackage :
    KnownBoundsGate <-> Nonempty GeneratedClosureMetricRowPackage :=
  PachTothW23RouteAudit.knownBoundsGate_iff_generatedClosureMetricRowPackage

/-! ## Alternative value-matrix W24 package -/

def generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily
    (A : AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
    A.family A.closure A.toReducedMetricHypotheses

@[simp]
theorem generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily_family
    (A : AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily) :
    (generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily A).family =
      A.family :=
  rfl

theorem exists_alternativeValueMatrixFamily_with_family_iff_generatedClosureMetricRowPackage_with_family
    (F : GeneratedChainFamily) :
    (Exists fun A : AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily =>
      A.family = F) <->
      Exists fun P : GeneratedClosureMetricRowPackage => P.family = F := by
  constructor
  · intro h
    cases h with
    | intro A hfamily =>
        exact
          Exists.intro
            (generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily A)
            (by simp [hfamily])
  · intro h
    cases h with
    | intro P hfamily =>
        exact
          Exists.intro
            (AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.ofInputPackage
              P.toInputPackage)
            (by simpa [hfamily])

theorem nonempty_alternativeValueMatrixFamily_iff_generatedClosureMetricRowPackage :
    Nonempty AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily <->
      Nonempty GeneratedClosureMetricRowPackage := by
  constructor
  · intro h
    cases h with
    | intro A =>
        exact
          Nonempty.intro
            (generatedClosureMetricRowPackageOfAlternativeValueMatrixFamily A)
  · intro h
    cases h with
    | intro P =>
        exact
          Nonempty.intro
            (AlternativeValueMatrixFamilyW24.AlternativeValueMatrixFamily.ofInputPackage
              P.toInputPackage)

/-! ## Free-placement W24 source-field handoffs -/

def generatedClosureMetricRowPackageOfFreePlacementW20SourceFields
    (S : FreePlacementSourceFieldsW24.W20SourceFields) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfRawSourceFields S

@[simp]
theorem generatedClosureMetricRowPackageOfFreePlacementW20SourceFields_family
    (S : FreePlacementSourceFieldsW24.W20SourceFields) :
    (generatedClosureMetricRowPackageOfFreePlacementW20SourceFields S).family =
      S.family :=
  rfl

def generatedClosureMetricRowPackageOfFreePlacementW20ReducedSourceFields
    (S : FreePlacementSourceFieldsW24.W20ReducedSourceFields) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
    S.family S.closure S.reducedMetric

@[simp]
theorem generatedClosureMetricRowPackageOfFreePlacementW20ReducedSourceFields_family
    (S : FreePlacementSourceFieldsW24.W20ReducedSourceFields) :
    (generatedClosureMetricRowPackageOfFreePlacementW20ReducedSourceFields S).family =
      S.family :=
  rfl

theorem exists_freePlacementW20SourceFields_with_family_iff_generatedClosureMetricRowPackage_with_family
    (F : GeneratedChainFamily) :
    (Exists fun S : FreePlacementSourceFieldsW24.W20SourceFields =>
      S.family = F) <->
      Exists fun P : GeneratedClosureMetricRowPackage => P.family = F :=
  (exists_generatedClosureMetricRowPackage_with_family_iff_rawSourceFields_with_family
    F).symm

theorem exists_freePlacementW20ReducedSourceFields_with_family_iff_generatedClosureMetricRowPackage_with_family
    (F : GeneratedChainFamily) :
    (Exists fun S : FreePlacementSourceFieldsW24.W20ReducedSourceFields =>
      S.family = F) <->
      Exists fun P : GeneratedClosureMetricRowPackage => P.family = F := by
  constructor
  · intro h
    cases h with
    | intro S hfamily =>
        exact
          Exists.intro
            (generatedClosureMetricRowPackageOfFreePlacementW20ReducedSourceFields S)
            (by simp [hfamily])
  · intro h
    have hfields :=
      (exists_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
        F).1 h
    exact
      Exists.intro
        ({ family := F
           closure := hfields.1
           reducedMetric := hfields.2 } :
          FreePlacementSourceFieldsW24.W20ReducedSourceFields)
        rfl

/-! ## Full/reduced metric closed-placement W24 witnesses -/

def generatedClosureMetricRowPackageOfReducedMetricClosedPlacementWitness
    (W : FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
    W.family W.closure W.metric

@[simp]
theorem generatedClosureMetricRowPackageOfReducedMetricClosedPlacementWitness_family
    (W : FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness) :
    (generatedClosureMetricRowPackageOfReducedMetricClosedPlacementWitness W).family =
      W.family :=
  rfl

theorem exists_reducedMetricClosedPlacementWitness_with_family_iff_generatedClosureMetricRowPackage_with_family
    (F : GeneratedChainFamily) :
    (Exists fun W : FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness =>
      W.family = F) <->
      Exists fun P : GeneratedClosureMetricRowPackage => P.family = F := by
  constructor
  · intro h
    cases h with
    | intro W hfamily =>
        exact
          Exists.intro
            (generatedClosureMetricRowPackageOfReducedMetricClosedPlacementWitness W)
            (by simp [hfamily])
  · intro h
    have hfields :=
      (exists_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
        F).1 h
    exact
      Exists.intro
        ({ family := F
           closure := hfields.1
           metric := hfields.2 } :
          FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness)
        rfl

def generatedClosureMetricRowPackageOfFullMetricClosedPlacementWitnessAndReducedMetric
    (W : FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness)
    (metric : ReducedMetricHypotheses W.family) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfClosuresAndReducedMetricHypotheses
    W.family W.closure metric

@[simp]
theorem generatedClosureMetricRowPackageOfFullMetricClosedPlacementWitnessAndReducedMetric_family
    (W : FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness)
    (metric : ReducedMetricHypotheses W.family) :
    (generatedClosureMetricRowPackageOfFullMetricClosedPlacementWitnessAndReducedMetric
      W metric).family = W.family :=
  rfl

theorem exists_generatedClosureMetricRowPackage_with_fullMetricWitness_family_iff_reducedMetricFields
    (W : FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness) :
    (Exists fun P : GeneratedClosureMetricRowPackage => P.family = W.family) <->
      Nonempty (ReducedMetricFields W.family) := by
  constructor
  · intro h
    exact
      ((exists_generatedClosureMetricRowPackage_with_family_iff_closureSource_and_reducedMetricFields
        W.family).1 h).2
  · intro h
    cases h with
    | intro metric =>
        exact
          Exists.intro
            (generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields
              (closureSourceOfClosures W.closure) metric)
            rfl

/-! ## Direct cross-block W24 package -/

def directReducedGeneratedChainFamily
    (C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily) :
    GeneratedChainFamily where
  O := fun _ _ => C.periodSearch.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := C.periodSearch.orientation

def reducedMetricFieldsOfDirectMissingField
    (C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily)
    (h : DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C) :
    ReducedMetricFields (directReducedGeneratedChainFamily C) where
  separated := DirectCrossBlockInputPackageW24.concreteSeparation C
  base_same_block_isometry := fun _ _ =>
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances := fun _ _ => h

def generatedClosureMetricRowPackageOfDirectMissingField
    (C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily)
    (h : DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfClosureSourceAndReducedMetricFields
    (closureSourceOfClosures
      (fun k hk => DirectCrossBlockInputPackageW24.concreteClosure C k hk))
    (reducedMetricFieldsOfDirectMissingField C h)

@[simp]
theorem generatedClosureMetricRowPackageOfDirectMissingField_family
    (C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily)
    (h : DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C) :
    (generatedClosureMetricRowPackageOfDirectMissingField C h).family =
      directReducedGeneratedChainFamily C :=
  rfl

def generatedClosureMetricRowPackageOfDirectReducedSourceFieldsOver
    {C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily}
    (D : DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C) :
    GeneratedClosureMetricRowPackage :=
  generatedClosureMetricRowPackageOfDirectMissingField C
    D.transition_preserves_same_block_distances

@[simp]
theorem generatedClosureMetricRowPackageOfDirectReducedSourceFieldsOver_family
    {C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily}
    (D : DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C) :
    (generatedClosureMetricRowPackageOfDirectReducedSourceFieldsOver D).family =
      directReducedGeneratedChainFamily C :=
  rfl

theorem missingDirectReducedInputField_iff_reducedMetricFields_directFamily
    (C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily) :
    DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C <->
      Nonempty (ReducedMetricFields (directReducedGeneratedChainFamily C)) := by
  constructor
  · intro h
    exact Nonempty.intro (reducedMetricFieldsOfDirectMissingField C h)
  · intro h
    cases h with
    | intro metric =>
        simpa [directReducedGeneratedChainFamily,
          DirectCrossBlockInputPackageW24.MissingDirectReducedInputField]
          using metric.transition_preserves_same_block_distances 1
            (Nat.zero_lt_one)

theorem exists_generatedClosureMetricRowPackage_directFamily_iff_missingDirectReducedInputField
    (C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily) :
    (Exists fun P : GeneratedClosureMetricRowPackage =>
      P.family = directReducedGeneratedChainFamily C) <->
      DirectCrossBlockInputPackageW24.MissingDirectReducedInputField C := by
  constructor
  · intro h
    have hfields :=
      (exists_generatedClosureMetricRowPackage_with_family_iff_closureSource_and_reducedMetricFields
        (directReducedGeneratedChainFamily C)).1 h
    exact
      (missingDirectReducedInputField_iff_reducedMetricFields_directFamily
        C).2 hfields.2
  · intro h
    exact
      Exists.intro (generatedClosureMetricRowPackageOfDirectMissingField C h)
        rfl

theorem nonempty_directReducedSourceFieldsOver_iff_generatedClosureMetricRowPackage_directFamily
    (C : DirectCrossBlockInputPackageW24.ConcreteNonConnectorLowerTableFamily) :
    Nonempty (DirectCrossBlockInputPackageW24.DirectReducedSourceFieldsOver C) <->
      Exists fun P : GeneratedClosureMetricRowPackage =>
        P.family = directReducedGeneratedChainFamily C := by
  exact
    Iff.trans
      (DirectCrossBlockInputPackageW24.nonempty_directReducedSourceFieldsOver_iff_missingDirectReducedInputField
        C)
      (exists_generatedClosureMetricRowPackage_directFamily_iff_missingDirectReducedInputField
        C).symm

end

end GeneratedClosureMetricPackageInhabitationW25
end PachToth

namespace Verified

abbrev PachTothW25GeneratedClosureMetricRowPackage : Type :=
  PachToth.GeneratedClosureMetricPackageInhabitationW25.GeneratedClosureMetricRowPackage

abbrev PachTothW25GeneratedChainFamily : Type :=
  PachToth.GeneratedClosureMetricPackageInhabitationW25.GeneratedChainFamily

theorem pachtoth_w25_knownBoundsGate_iff_generatedClosureMetricRowPackage :
    PachToth.GeneratedClosureMetricPackageInhabitationW25.KnownBoundsGate <->
      Nonempty PachTothW25GeneratedClosureMetricRowPackage :=
  PachToth.GeneratedClosureMetricPackageInhabitationW25.knownBoundsGate_iff_generatedClosureMetricRowPackage

theorem pachtoth_w25_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
    (F : PachTothW25GeneratedChainFamily) :
    (Exists fun P : PachTothW25GeneratedClosureMetricRowPackage =>
      P.family = F) <->
      PachToth.GeneratedClosureMetricPackageInhabitationW25.GeneratedChainFamilyClosures F /\
        PachToth.GeneratedClosureMetricPackageInhabitationW25.ReducedMetricHypotheses F :=
  PachToth.GeneratedClosureMetricPackageInhabitationW25.exists_generatedClosureMetricRowPackage_with_family_iff_closures_and_reducedMetricHypotheses
    F

end Verified
end ErdosProblems1066
