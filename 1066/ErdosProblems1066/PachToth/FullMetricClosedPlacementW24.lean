import ErdosProblems1066.PachToth.ExactBaseFullMetricConcreteW23
import ErdosProblems1066.PachToth.GeneratedChainSourceFieldsConcreteClosureW23
import ErdosProblems1066.PachToth.TargetReduction

set_option autoImplicit false

/-!
# W24 full-metric closed-placement bridge

This file exposes the exact handoff from generated full metric data to
`DeformedPlacement.ClosedPlacement`, then records the downstream
`GeometricSoundness.ExplicitEdgeSoundness` and target reductions.  The
concrete generated-chain source route from W23 is reduced-metric rather than
full-metric, so it is kept in a separate reduced witness with the same exact
closed-placement endpoints.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FullMetricClosedPlacementW24

open FiniteGraph

noncomputable section

abbrev GeneratedChainFamily : Type :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev GeneratedChainFamilyClosures
    (F : GeneratedChainFamily) : Prop :=
  ClosedPlacementClosure.GeneratedChainFamilyClosures F

abbrev FullMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) : Prop :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

abbrev ExplicitClosedPlacementCertificateFamily : Type :=
  ArbitraryNClosedPlacementRouteW19.ExplicitClosedPlacementCertificateFamily

abbrev ExplicitTransitionClosedPlacementCertificateFamily : Type :=
  ArbitraryNClosedPlacementRouteW19.ExplicitTransitionClosedPlacementCertificateFamily

abbrev ClosedPlacementFamily : Type :=
  ArbitraryNClosedPlacementRouteW19.ClosedPlacementFamily

abbrev ExplicitEdgeSoundnessFamily : Type :=
  forall (k : Nat) (hk : 0 < k),
    GeometricSoundness.ExplicitEdgeSoundness k hk

abbrev ExactTarget : Prop :=
  targetUpperConstructionFiveSixteen

abbrev ArbitraryTarget : Prop :=
  targetUpperConstructionFiveSixteenArbitrary

abbrev ExactBlockTarget (k : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt (16 * k)

abbrev FixedTarget (n : Nat) : Prop :=
  targetUpperConstructionFiveSixteenAt n

/-- Minimal full-metric witness for the closed-placement route: one generated
family, algebraic closure for every positive block count, and full generated
metric hypotheses for that same family. -/
structure FullMetricClosedPlacementWitness where
  family : GeneratedChainFamily
  closure : GeneratedChainFamilyClosures family
  metric : FullMetricHypotheses family

namespace FullMetricClosedPlacementWitness

def transitionCertificateFamily
    (W : FullMetricClosedPlacementWitness) :
    ExplicitTransitionClosedPlacementCertificateFamily :=
  fun k hk =>
    ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure
      (W.family.O k hk) hk (W.family.base k hk) (W.family.orientation k hk)
      (W.closure k hk) (W.metric.metric k hk)

def explicitCertificateFamily
    (W : FullMetricClosedPlacementWitness) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => (W.transitionCertificateFamily k hk).toExplicitClosedPlacementCertificate

def closedPlacementFamily
    (W : FullMetricClosedPlacementWitness) :
    ClosedPlacementFamily :=
  fun k hk => (W.explicitCertificateFamily k hk).toClosedPlacement

def closedPlacement
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  W.closedPlacementFamily k hk

@[simp]
theorem closedPlacement_point
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (W.closedPlacement k hk).point i v =
      GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
        (W.family.base k hk) (W.family.orientation k hk) i v := by
  rfl

def explicitEdgeSoundness
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  (W.closedPlacement k hk).toExplicitEdgeSoundness

def explicitEdgeSoundnessFamily
    (W : FullMetricClosedPlacementWitness) :
    ExplicitEdgeSoundnessFamily :=
  fun k hk => W.explicitEdgeSoundness k hk

def indexedChainRealization
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    IndexedChain.IndexedChainRealization k hk :=
  (W.explicitEdgeSoundness k hk).toIndexedChainRealization

theorem exists_closedPlacement
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
          (W.family.base k hk) (W.family.orientation k hk) := by
  exact Exists.intro (W.closedPlacement k hk) rfl

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (W : FullMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k := by
  exact
    ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificate
      (W.explicitCertificateFamily k hk)

theorem targetUpperConstructionFiveSixteen
    (W : FullMetricClosedPlacementWitness) :
    ExactTarget := by
  exact
    ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
      W.explicitCertificateFamily

theorem targetUpperConstructionFiveSixteen_viaExplicitEdgeSoundness
    (W : FullMetricClosedPlacementWitness) :
    ExactTarget := by
  exact
    PachToth.targetUpperConstructionFiveSixteen_of_explicitEdgeSoundness
      W.explicitEdgeSoundnessFamily

theorem targetUpperConstructionFiveSixteen_viaClosedPlacement
    (W : FullMetricClosedPlacementWitness) :
    ExactTarget := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      W.closedPlacementFamily

theorem targetUpperConstructionFiveSixteenArbitrary
    (W : FullMetricClosedPlacementWitness) :
    ArbitraryTarget := by
  exact
    ArbitraryNClosedPlacementRouteW19.targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
      W.explicitCertificateFamily

theorem targetUpperConstructionFiveSixteenAt
    (W : FullMetricClosedPlacementWitness) (n : Nat) :
    FixedTarget n :=
  W.targetUpperConstructionFiveSixteenArbitrary n

theorem upper_bound_five_sixteen_arbitrary
    (W : FullMetricClosedPlacementWitness) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  W.targetUpperConstructionFiveSixteenAt n

end FullMetricClosedPlacementWitness

/-- Minimal reduced-metric witness for generated-chain source fields.  The W23
concrete value-matrix route supplies this shape, not the stronger full-metric
same-block-isometry field. -/
structure ReducedMetricClosedPlacementWitness where
  family : GeneratedChainFamily
  closure : GeneratedChainFamilyClosures family
  metric : ReducedMetricHypotheses family

namespace ReducedMetricClosedPlacementWitness

def transitionCertificateFamily
    (W : ReducedMetricClosedPlacementWitness) :
    ExplicitTransitionClosedPlacementCertificateFamily :=
  fun k hk =>
    ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure_reduced
      (W.family.O k hk) hk (W.family.base k hk) (W.family.orientation k hk)
      (W.closure k hk) (W.metric.metric k hk)

def explicitCertificateFamily
    (W : ReducedMetricClosedPlacementWitness) :
    ExplicitClosedPlacementCertificateFamily :=
  fun k hk => (W.transitionCertificateFamily k hk).toExplicitClosedPlacementCertificate

def closedPlacementFamily
    (W : ReducedMetricClosedPlacementWitness) :
    ClosedPlacementFamily :=
  fun k hk => (W.explicitCertificateFamily k hk).toClosedPlacement

def closedPlacement
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  W.closedPlacementFamily k hk

@[simp]
theorem closedPlacement_point
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (W.closedPlacement k hk).point i v =
      GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
        (W.family.base k hk) (W.family.orientation k hk) i v := by
  rfl

def explicitEdgeSoundness
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  (W.closedPlacement k hk).toExplicitEdgeSoundness

def explicitEdgeSoundnessFamily
    (W : ReducedMetricClosedPlacementWitness) :
    ExplicitEdgeSoundnessFamily :=
  fun k hk => W.explicitEdgeSoundness k hk

def indexedChainRealization
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    IndexedChain.IndexedChainRealization k hk :=
  (W.explicitEdgeSoundness k hk).toIndexedChainRealization

theorem exists_closedPlacement
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point =
        GeneratedClosedChain.generatedPoint (W.family.O k hk) hk
          (W.family.base k hk) (W.family.orientation k hk) := by
  exact Exists.intro (W.closedPlacement k hk) rfl

theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (W : ReducedMetricClosedPlacementWitness)
    (k : Nat) (hk : 0 < k) :
    ExactBlockTarget k := by
  exact
    ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitClosedPlacementCertificate
      (W.explicitCertificateFamily k hk)

theorem targetUpperConstructionFiveSixteen
    (W : ReducedMetricClosedPlacementWitness) :
    ExactTarget := by
  exact
    ClosedPlacementTargetWrappersW19.targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates
      W.explicitCertificateFamily

theorem targetUpperConstructionFiveSixteen_viaExplicitEdgeSoundness
    (W : ReducedMetricClosedPlacementWitness) :
    ExactTarget := by
  exact
    PachToth.targetUpperConstructionFiveSixteen_of_explicitEdgeSoundness
      W.explicitEdgeSoundnessFamily

theorem targetUpperConstructionFiveSixteen_viaClosedPlacement
    (W : ReducedMetricClosedPlacementWitness) :
    ExactTarget := by
  exact
    DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
      W.closedPlacementFamily

theorem targetUpperConstructionFiveSixteenArbitrary
    (W : ReducedMetricClosedPlacementWitness) :
    ArbitraryTarget := by
  exact
    ArbitraryNClosedPlacementRouteW19.targetUpperConstructionFiveSixteenArbitrary_of_explicitClosedPlacementCertificates
      W.explicitCertificateFamily

theorem targetUpperConstructionFiveSixteenAt
    (W : ReducedMetricClosedPlacementWitness) (n : Nat) :
    FixedTarget n :=
  W.targetUpperConstructionFiveSixteenArbitrary n

theorem upper_bound_five_sixteen_arbitrary
    (W : ReducedMetricClosedPlacementWitness) (n : Nat) :
    Exists fun C : _root_.UDConfig n =>
      forall s : Finset (Fin n), C.IsIndep s ->
        s.card <= Arithmetic.ceilDiv (5 * n) 16 :=
  W.targetUpperConstructionFiveSixteenAt n

end ReducedMetricClosedPlacementWitness

/-! ## Full-metric W23 adapters -/

def fullMetricWitnessOfExactBaseCore
    (C : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricCoreFields)
    (metric : ExactBaseFullMetricConcreteW23.RemainingFullMetricField C) :
    FullMetricClosedPlacementWitness where
  family := C.family
  closure := C.closures
  metric := C.metricHypotheses metric

def fullMetricWitnessOfExactBaseSourceFields
    (S : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricSourceFields) :
    FullMetricClosedPlacementWitness :=
  fullMetricWitnessOfExactBaseCore
    (ExactBaseFullMetricSourceInhabitationW22.exactBaseFullMetricCoreFieldsOfSource
      S)
    S.metric

def fullMetricWitnessOfExactBaseConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricConcreteCoreFields) :
    FullMetricClosedPlacementWitness :=
  fullMetricWitnessOfExactBaseCore D.core D.metric

def fullMetricWitnessOfConnectorConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ConnectorFullMetricConcreteCoreFields) :
    FullMetricClosedPlacementWitness :=
  fullMetricWitnessOfExactBaseCore D.core.toExactCore D.metric

def closedPlacementOfExactBaseConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricConcreteCoreFields)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  (fullMetricWitnessOfExactBaseConcreteCore D).closedPlacement k hk

def explicitEdgeSoundnessOfExactBaseConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricConcreteCoreFields)
    (k : Nat) (hk : 0 < k) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  (fullMetricWitnessOfExactBaseConcreteCore D).explicitEdgeSoundness k hk

theorem targetUpperConstructionFiveSixteen_of_exactBaseConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricConcreteCoreFields) :
    ExactTarget :=
  (fullMetricWitnessOfExactBaseConcreteCore D).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactBaseConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ExactBaseFullMetricConcreteCoreFields) :
    ArbitraryTarget :=
  (fullMetricWitnessOfExactBaseConcreteCore D).targetUpperConstructionFiveSixteenArbitrary

def closedPlacementOfConnectorConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ConnectorFullMetricConcreteCoreFields)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  (fullMetricWitnessOfConnectorConcreteCore D).closedPlacement k hk

def explicitEdgeSoundnessOfConnectorConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ConnectorFullMetricConcreteCoreFields)
    (k : Nat) (hk : 0 < k) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  (fullMetricWitnessOfConnectorConcreteCore D).explicitEdgeSoundness k hk

theorem targetUpperConstructionFiveSixteen_of_connectorConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ConnectorFullMetricConcreteCoreFields) :
    ExactTarget :=
  (fullMetricWitnessOfConnectorConcreteCore D).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_connectorConcreteCore
    (D : ExactBaseFullMetricConcreteW23.ConnectorFullMetricConcreteCoreFields) :
    ArbitraryTarget :=
  (fullMetricWitnessOfConnectorConcreteCore D).targetUpperConstructionFiveSixteenArbitrary

/-! ## Generated-chain W23 concrete-source adapters -/

def reducedWitnessOfSourceFields
    (S : GeneratedChainSourceFieldsConcreteClosureW23.SourceFields) :
    ReducedMetricClosedPlacementWitness where
  family := S.family
  closure := S.closures
  metric := S.reducedMetric

def reducedWitnessOfConcreteValueMatrixFamily
    (C : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixFamily) :
    ReducedMetricClosedPlacementWitness :=
  reducedWitnessOfSourceFields
    (GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixFamily
      C)

def reducedWitnessOfConcreteValueMatrixRowPackage
    (P : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixRowPackage) :
    ReducedMetricClosedPlacementWitness :=
  reducedWitnessOfSourceFields
    (GeneratedChainSourceFieldsConcreteClosureW23.sourceFieldsOfConcreteValueMatrixRowPackage
      P)

def closedPlacementOfConcreteValueMatrixRowPackage
    (P : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  (reducedWitnessOfConcreteValueMatrixRowPackage P).closedPlacement k hk

def explicitEdgeSoundnessOfConcreteValueMatrixRowPackage
    (P : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixRowPackage)
    (k : Nat) (hk : 0 < k) :
    GeometricSoundness.ExplicitEdgeSoundness k hk :=
  (reducedWitnessOfConcreteValueMatrixRowPackage P).explicitEdgeSoundness k hk

theorem targetUpperConstructionFiveSixteen_of_concreteValueMatrixRowPackage
    (P : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixRowPackage) :
    ExactTarget :=
  (reducedWitnessOfConcreteValueMatrixRowPackage P).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixRowPackage
    (P : GeneratedChainSourceFieldsConcreteClosureW23.ConcreteValueMatrixRowPackage) :
    ArbitraryTarget :=
  (reducedWitnessOfConcreteValueMatrixRowPackage P).targetUpperConstructionFiveSixteenArbitrary

end

end FullMetricClosedPlacementW24
end PachToth
end ErdosProblems1066
