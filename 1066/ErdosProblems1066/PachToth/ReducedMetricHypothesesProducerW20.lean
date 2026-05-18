import ErdosProblems1066.PachToth.ClosedPlacementCrossConnectorEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementSameBlockEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementSeparationW19
import ErdosProblems1066.PachToth.NonConnectorInstantiationW13

set_option autoImplicit false

/-!
# W20 reduced metric hypothesis producer

This module is the metric handoff for generated Pach--Toth chains.  It
constructs
`GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F`
from explicit separation, base same-block, and transition same-block fields,
and gives adapters from the W19 separation/same-block/cross-connector modules
and the existing non-connector separation tables.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ReducedMetricHypothesesProducerW20

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev ReducedMetricHypotheses
    (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

abbrev MetricAt
    (F : GeneratedChainFamily)
    (k : Nat) (hk : 0 < k) :=
  GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)

abbrev GeneratedPointAt
    (F : GeneratedChainFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> LocalVertex -> R2 :=
  GeneratedClosedChain.generatedPoint (F.O k hk) hk (F.base k hk)
    (F.orientation k hk)

abbrev GeneratedGlobalSeparationAt
    (F : GeneratedChainFamily)
    (k : Nat) (hk : 0 < k) : Prop :=
  GeneratedSeparationInterface.GeneratedGlobalSeparation
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)

/-- The exact fields needed to build reduced generated-family metric
hypotheses. -/
structure ReducedMetricFields (F : GeneratedChainFamily) where
  separated :
    forall (k : Nat) (hk : 0 < k), GeneratedGlobalSeparationAt F k hk
  base_same_block_isometry :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
        (F.base k hk)
  transition_preserves_same_block_distances :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        (F.O k hk)

namespace ReducedMetricFields

/-- Assemble the exact fields into the target generated-family reduced metric
interface. -/
def toReducedMetricHypotheses
    {F : GeneratedChainFamily}
    (D : ReducedMetricFields F) :
    ReducedMetricHypotheses F where
  metric := fun k hk =>
    { separated := D.separated k hk
      base_same_block_isometry := D.base_same_block_isometry k hk
      transition_preserves_same_block_distances :=
        D.transition_preserves_same_block_distances k hk }

@[simp]
theorem toReducedMetricHypotheses_metric_separated
    {F : GeneratedChainFamily}
    (D : ReducedMetricFields F)
    (k : Nat) (hk : 0 < k) :
    ((D.toReducedMetricHypotheses).metric k hk).separated =
      D.separated k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_baseSameBlock
    {F : GeneratedChainFamily}
    (D : ReducedMetricFields F)
    (k : Nat) (hk : 0 < k) :
    ((D.toReducedMetricHypotheses).metric k hk).base_same_block_isometry =
      D.base_same_block_isometry k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_transitionPreserves
    {F : GeneratedChainFamily}
    (D : ReducedMetricFields F)
    (k : Nat) (hk : 0 < k) :
    (((D.toReducedMetricHypotheses).metric k hk).transition_preserves_same_block_distances) =
      D.transition_preserves_same_block_distances k hk :=
  rfl

end ReducedMetricFields

/-- Public producer name for the requested target. -/
def reducedMetricHypotheses
    {F : GeneratedChainFamily}
    (D : ReducedMetricFields F) :
    GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
      F :=
  D.toReducedMetricHypotheses

/-- W19 separation-family certificates plus exact base/transition fields
produce reduced generated-family metric hypotheses. -/
structure W19SeparatedReducedMetricFields
    (F : GeneratedChainFamily) where
  separation : ClosedPlacementSeparationW19.SeparationFamilyCertificate
  point_eq :
    forall (k : Nat) (hk : 0 < k),
      separation.point k hk = GeneratedPointAt F k hk
  base_same_block_isometry :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
        (F.base k hk)
  transition_preserves_same_block_distances :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        (F.O k hk)

namespace W19SeparatedReducedMetricFields

/-- Convert W19 separated fields to the exact reduced-metric field package. -/
def toReducedMetricFields
    {F : GeneratedChainFamily}
    (D : W19SeparatedReducedMetricFields F) :
    ReducedMetricFields F where
  separated := by
    intro k hk i u j v hne
    simpa [GeneratedGlobalSeparationAt, GeneratedPointAt,
      ClosedPlacementSeparationW19.Separated, D.point_eq k hk] using
        D.separation.separated k hk i u j v hne
  base_same_block_isometry := D.base_same_block_isometry
  transition_preserves_same_block_distances :=
    D.transition_preserves_same_block_distances

/-- Convert W19 separated fields directly to the target reduced metric
interface. -/
def toReducedMetricHypotheses
    {F : GeneratedChainFamily}
    (D : W19SeparatedReducedMetricFields F) :
    ReducedMetricHypotheses F :=
  D.toReducedMetricFields.toReducedMetricHypotheses

@[simp]
theorem toReducedMetricHypotheses_metric_separated
    {F : GeneratedChainFamily}
    (D : W19SeparatedReducedMetricFields F)
    (k : Nat) (hk : 0 < k) :
    ((D.toReducedMetricHypotheses).metric k hk).separated =
      (D.toReducedMetricFields.separated k hk) :=
  rfl

end W19SeparatedReducedMetricFields

/-- A reduced metric family exposes its W19 separation certificate at each
block count. -/
def separationCertificateOfReducedMetric
    {F : GeneratedChainFamily}
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementSeparationW19.SeparationCertificate k hk :=
  ClosedPlacementSeparationW19.ofGeneratedReducedMetricHypotheses
    (F.O k hk) hk (F.base k hk) (F.orientation k hk) (H.metric k hk)

/-- A reduced metric family exposes the W19 same-block unit-edge certificate
for its generated point map. -/
def sameBlockUnitEdgeCertificateOfReducedMetric
    {F : GeneratedChainFamily}
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdgeCertificate
      (GeneratedPointAt F k hk) where
  unit_edges := by
    intro i u v _huv hadj
    calc
      _root_.eucDist (GeneratedPointAt F k hk i u)
          (GeneratedPointAt F k hk i v) =
        _root_.eucDist
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 u))
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 v)) := by
          exact
            GeneratedSeparationInterface.same_block_isometry_of_reduced
              (F.O k hk) hk (F.base k hk) (F.orientation k hk)
              (H.metric k hk) i u v
      _ = 1 :=
        OneBlockSoundness.oneBlockCertificate.same_block_edges_unit
          u v hadj

/-- Periods plus reduced metrics expose the W19 four-edge successor connector
certificate for every generated chain. -/
def crossConnectorUnitCertificateOfReducedMetric
    {F : GeneratedChainFamily}
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate
      hk (GeneratedPointAt F k hk) :=
  ClosedPlacementCrossConnectorEdgesW19.ofGeneratedPeriodReduced
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)
    (periods k hk) (H.metric k hk)

/-- Forget a role-hinged period-search family to the generated-chain family
interface used by the final reduced metric target. -/
def generatedChainFamilyOfRoleHinged
    (F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily) :
    GeneratedChainFamily where
  O := fun _k _hk => F.transitions.toFigure2TransitionObligations
  base := fun _k _hk => BaseTransitionRealization.exactBase
  orientation := F.orientation

@[simp]
theorem generatedChainFamilyOfRoleHinged_O
    (F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfRoleHinged F).O k hk =
      F.transitions.toFigure2TransitionObligations :=
  rfl

@[simp]
theorem generatedChainFamilyOfRoleHinged_base
    (F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfRoleHinged F).base k hk =
      BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem generatedChainFamilyOfRoleHinged_orientation
    (F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (generatedChainFamilyOfRoleHinged F).orientation k hk =
      F.orientation k hk :=
  rfl

/-- The exact same-block fields for role-hinged generated chains. -/
def roleHingedReducedMetricFields
    (F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily)
    (separated :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedGlobalSeparation
          F.transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (F.orientation k hk)) :
    ReducedMetricFields (generatedChainFamilyOfRoleHinged F) where
  separated := separated
  base_same_block_isometry := fun _k _hk =>
    GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
  transition_preserves_same_block_distances := fun _k _hk =>
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.transitions

/-- Existing generated non-connector square-distance table families produce
the target reduced metric hypotheses. -/
def ofGeneratedNonConnectorSqDistanceTableFamily
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily
      F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  (roleHingedReducedMetricFields F
    (fun k hk => T.separated k hk)).toReducedMetricHypotheses

/-- The same table route, expressed through the W19 separation-family adapter. -/
def ofGeneratedNonConnectorSqDistanceTableFamilyViaW19
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily
      F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  (W19SeparatedReducedMetricFields.toReducedMetricHypotheses
    { separation :=
        ClosedPlacementSeparationW19.SeparationFamilyCertificate.ofGeneratedNonConnectorSqDistanceTableFamily
          T
      point_eq := by
        intro _k _hk
        rfl
      base_same_block_isometry := fun _k _hk =>
        GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
      transition_preserves_same_block_distances := fun _k _hk =>
        GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
          F.transitions })

/-- Existing finite-index non-connector square-distance table families produce
the target reduced metric hypotheses. -/
def ofIndexedNonConnectorCrossBlockSqDistanceTableFamily
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T :
      NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily
        F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  ofGeneratedNonConnectorSqDistanceTableFamily
    (NonConnectorInstantiationW13.generatedTableFamilyOfIndexedTableFamily T)

/-- Existing cross-block lower-bound facades produce the target reduced metric
hypotheses. -/
def ofCrossBlockLowerBounds
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (H : NonConnectorSeparationW12.CrossBlockLowerBounds F) :
    ReducedMetricHypotheses (generatedChainFamilyOfRoleHinged F) :=
  (roleHingedReducedMetricFields F
    (fun k hk => H.separated k hk)).toReducedMetricHypotheses

/-- Concrete non-connector value matrices produce the target reduced metric
hypotheses for their generated-chain family. -/
def ofConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    ReducedMetricHypotheses
      (generatedChainFamilyOfRoleHinged C.toRoleHingedPeriodSearchFamily) :=
  ofGeneratedNonConnectorSqDistanceTableFamily
    (NonConnectorInstantiationW13.generatedTableFamilyOfConcreteValueMatrixFamily
      C)

/-- A package form for downstream producers that want the generated family and
its reduced metrics together. -/
structure ProducedReducedMetricPackage where
  family : GeneratedChainFamily
  metric : ReducedMetricHypotheses family

namespace ProducedReducedMetricPackage

/-- Build the package from generated non-connector square-distance tables. -/
def ofGeneratedNonConnectorSqDistanceTableFamily
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily
      F) :
    ProducedReducedMetricPackage where
  family := generatedChainFamilyOfRoleHinged F
  metric :=
    _root_.ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily
      T

/-- Build the package from finite-index non-connector square-distance tables. -/
def ofIndexedNonConnectorCrossBlockSqDistanceTableFamily
    {F : NonConnectorSeparationW12.RoleHingedPeriodSearchFamily}
    (T :
      NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily
        F) :
    ProducedReducedMetricPackage where
  family := generatedChainFamilyOfRoleHinged F
  metric :=
    _root_.ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20.ofIndexedNonConnectorCrossBlockSqDistanceTableFamily
      T

/-- Build the package from concrete value matrices. -/
def ofConcreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    ProducedReducedMetricPackage where
  family := generatedChainFamilyOfRoleHinged C.toRoleHingedPeriodSearchFamily
  metric :=
    _root_.ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20.ofConcreteValueMatrixFamily
      C

end ProducedReducedMetricPackage

end

end ReducedMetricHypothesesProducerW20
end PachToth
end ErdosProblems1066
