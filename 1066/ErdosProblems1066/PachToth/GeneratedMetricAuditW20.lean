import ErdosProblems1066.PachToth.ClosedPlacementCrossConnectorEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementSameBlockEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementSeparationW19
import ErdosProblems1066.PachToth.NonRigidClosedPlacementDataW19

set_option autoImplicit false

/-!
# W20 generated metric audit

This tiny audit module keeps the reduced generated-chain metric contract
visible for CI.  It records that
`GeneratedChainFamily.ReducedMetricHypotheses` is a family of rows whose
non-derived fields are exactly separation, base-block same-block isometry,
and same/opposite transition same-block distance preservation, then aliases
the W19 closed-placement certificate projections obtained from those fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedMetricAuditW20

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev GeneratedChainFamily :=
  GeneratedSeparationInterface.GeneratedChainFamily

abbrev ReducedMetricHypotheses (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses F

abbrev ReducedMetricRow
    (F : GeneratedChainFamily) (k : Nat) (hk : 0 < k) :=
  GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)

abbrev FullMetricHypotheses (F : GeneratedChainFamily) :=
  GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F

/-- The reduced family metric contract flattened into its three row fields. -/
structure ReducedMetricFieldFamily (F : GeneratedChainFamily) where
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
  base_same_block_isometry :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
        (F.base k hk)
  transition_preserves_same_block_distances :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        (F.O k hk)

namespace ReducedMetricFieldFamily

/-- Expand the bundled reduced metric hypotheses into the explicit field
family audited by this module. -/
def ofReducedMetricHypotheses
    {F : GeneratedChainFamily}
    (H : ReducedMetricHypotheses F) :
    ReducedMetricFieldFamily F where
  separated := fun k hk => (H.metric k hk).separated
  base_same_block_isometry := fun k hk =>
    (H.metric k hk).base_same_block_isometry
  transition_preserves_same_block_distances := fun k hk =>
    (H.metric k hk).transition_preserves_same_block_distances

/-- Rebundle the three audited row fields as reduced metric hypotheses. -/
def toReducedMetricHypotheses
    {F : GeneratedChainFamily}
    (A : ReducedMetricFieldFamily F) :
    ReducedMetricHypotheses F where
  metric := fun k hk =>
    { separated := A.separated k hk
      base_same_block_isometry := A.base_same_block_isometry k hk
      transition_preserves_same_block_distances :=
        A.transition_preserves_same_block_distances k hk }

@[simp]
theorem toReducedMetricHypotheses_metric_separated
    {F : GeneratedChainFamily}
    (A : ReducedMetricFieldFamily F)
    (k : Nat) (hk : 0 < k) :
    ((A.toReducedMetricHypotheses).metric k hk).separated =
      A.separated k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_baseSameBlock
    {F : GeneratedChainFamily}
    (A : ReducedMetricFieldFamily F)
    (k : Nat) (hk : 0 < k) :
    ((A.toReducedMetricHypotheses).metric k hk).base_same_block_isometry =
      A.base_same_block_isometry k hk :=
  rfl

@[simp]
theorem toReducedMetricHypotheses_metric_transitionPreserves
    {F : GeneratedChainFamily}
    (A : ReducedMetricFieldFamily F)
    (k : Nat) (hk : 0 < k) :
    (((A.toReducedMetricHypotheses).metric k hk).transition_preserves_same_block_distances) =
      A.transition_preserves_same_block_distances k hk :=
  rfl

@[simp]
theorem ofReducedMetricHypotheses_separated
    {F : GeneratedChainFamily}
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (ofReducedMetricHypotheses H).separated k hk =
      (H.metric k hk).separated :=
  rfl

@[simp]
theorem ofReducedMetricHypotheses_baseSameBlock
    {F : GeneratedChainFamily}
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (ofReducedMetricHypotheses H).base_same_block_isometry k hk =
      (H.metric k hk).base_same_block_isometry :=
  rfl

@[simp]
theorem ofReducedMetricHypotheses_transitionPreserves
    {F : GeneratedChainFamily}
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ((ofReducedMetricHypotheses H).transition_preserves_same_block_distances k hk) =
      (H.metric k hk).transition_preserves_same_block_distances :=
  rfl

end ReducedMetricFieldFamily

/-- CI-facing equivalence between the bundled reduced metric hypothesis and
the explicit field-family audit shape. -/
def reducedMetricFieldFamilyEquiv (F : GeneratedChainFamily) :
    ReducedMetricFieldFamily F ≃ ReducedMetricHypotheses F where
  toFun := ReducedMetricFieldFamily.toReducedMetricHypotheses
  invFun := ReducedMetricFieldFamily.ofReducedMetricHypotheses
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    intro H
    cases H
    rfl

theorem reducedMetric_separated
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      (F.O k hk) hk (F.base k hk) (F.orientation k hk) :=
  (H.metric k hk).separated

theorem reducedMetric_base_same_block_isometry
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
      (F.base k hk) :=
  (H.metric k hk).base_same_block_isometry

theorem reducedMetric_transition_preserves_same_block_distances
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      (F.O k hk) :=
  (H.metric k hk).transition_preserves_same_block_distances

/-- The only same-block fact derived from the reduced fields is the full
blockwise generated same-block isometry. -/
theorem same_block_isometry_of_reducedMetric
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      (F.O k hk) hk (F.base k hk) (F.orientation k hk) :=
  GeneratedSeparationInterface.same_block_isometry_of_reduced
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)
    (H.metric k hk)

/-- Repackage reduced family metric data as the full generated metric facade. -/
def fullMetricHypothesesOfReduced
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F) :
    FullMetricHypotheses F where
  metric := fun k hk =>
    { separated := (H.metric k hk).separated
      same_block_isometry :=
        same_block_isometry_of_reducedMetric F H k hk }

@[simp]
theorem fullMetricHypothesesOfReduced_metric_separated
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ((fullMetricHypothesesOfReduced F H).metric k hk).separated =
      (H.metric k hk).separated :=
  rfl

theorem fullMetricHypothesesOfReduced_metric_sameBlock
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ((fullMetricHypothesesOfReduced F H).metric k hk).same_block_isometry =
      same_block_isometry_of_reducedMetric F H k hk :=
  rfl

/-- W19 separated-field certificate obtained from a reduced metric row. -/
def separationCertificate
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementSeparationW19.SeparationCertificate k hk :=
  ClosedPlacementSeparationW19.ofGeneratedReducedMetricHypotheses
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)
    (H.metric k hk)

@[simp]
theorem separationCertificate_point
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (separationCertificate F H k hk).point =
      GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) :=
  rfl

@[simp]
theorem separationCertificate_separated
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (separationCertificate F H k hk).separated =
      (H.metric k hk).separated :=
  rfl

theorem separationCertificate_apply
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex)
    (hne : Ne (i, u) (j, v)) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint
          (F.O k hk) hk (F.base k hk) (F.orientation k hk) i u)
        (GeneratedClosedChain.generatedPoint
          (F.O k hk) hk (F.base k hk) (F.orientation k hk) j v) :=
  (separationCertificate F H k hk).separated i u j v hne

/-- W19 family-level separated-field certificate obtained from reduced
generated metric hypotheses. -/
def separationFamilyCertificate
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F) :
    ClosedPlacementSeparationW19.SeparationFamilyCertificate :=
  ClosedPlacementSeparationW19.SeparationFamilyCertificate.ofGeneratedFamilyReduced
    F H

@[simp]
theorem separationFamilyCertificate_point
    (F : GeneratedChainFamily)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (separationFamilyCertificate F H).point k hk =
      GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) :=
  rfl

/-- Direct W19 point/edge data from generated periods plus reduced metric
hypotheses.  Its fields are the separation, same-block unit-edge, and
successor connector certificates used downstream. -/
def explicitCyclicPointEdgeData
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface.ExplicitCyclicPointEdgeData
      k hk :=
  _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface.explicitCyclicPointEdgeData_of_generatedPeriod_reduced
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (periods k hk) (H.metric k hk)

@[simp]
theorem explicitCyclicPointEdgeData_point
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (explicitCyclicPointEdgeData F periods H k hk).point i v =
      GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i v :=
  by
    simp [explicitCyclicPointEdgeData]

/-- W19 same-block unit-edge certificate from generated periods plus reduced
metric hypotheses. -/
def sameBlockUnitEdgeCertificate
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdgeCertificate
      (GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)) where
  unit_edges := by
    intro i u v huv hadj
    simpa [explicitCyclicPointEdgeData] using
      (explicitCyclicPointEdgeData F periods H k hk).same_block_edges_unit
        i u v huv hadj

theorem sameBlockUnitEdges_apply
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u v : LocalVertex)
    (huv : Ne u v) (hadj : adj u v = true) :
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i u)
      (GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i v) = 1 :=
  (sameBlockUnitEdgeCertificate F periods H k hk).unit_edges
    i u v huv hadj

/-- W19 four-connector certificate from generated periods plus reduced
metric hypotheses. -/
def crossConnectorUnitCertificate
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate
      hk
      (GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)) :=
  ClosedPlacementCrossConnectorEdgesW19.ofGeneratedPeriodReduced
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)
    (periods k hk) (H.metric k hk)

theorem crossConnectorEdgesUnit_apply
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u v : LocalVertex)
    (hconn : CrossBlock.NextConnector u v) :
    _root_.eucDist
      (GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i u)
      (GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
        (Arithmetic.cyclicSucc hk i) v) = 1 :=
  (crossConnectorUnitCertificate F periods H k hk).crossConnectorEdgesUnit
    i u v hconn

/-- W19 family obligation record pairing periods with the reduced metric
family. -/
def reducedClosedPlacementFamilyObligations
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F) :
    _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementDataW19.GeneratedReducedClosedPlacementFamilyObligations
      F where
  periods := periods
  reducedMetric := H

@[simp]
theorem reducedClosedPlacementFamilyObligations_toOneChain_separated
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ((reducedClosedPlacementFamilyObligations F periods H).toOneChainObligations
      k hk).separated =
      (H.metric k hk).separated :=
  rfl

@[simp]
theorem reducedClosedPlacementFamilyObligations_toOneChain_baseSameBlock
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    ((reducedClosedPlacementFamilyObligations F periods H).toOneChainObligations
      k hk).base_same_block_isometry =
      (H.metric k hk).base_same_block_isometry :=
  rfl

@[simp]
theorem reducedClosedPlacementFamilyObligations_toOneChain_transitionPreserves
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) :
    (((reducedClosedPlacementFamilyObligations F periods H).toOneChainObligations
      k hk).transition_preserves_same_block_distances) =
      (H.metric k hk).transition_preserves_same_block_distances :=
  rfl

/-- W19 explicit certificate family obtained from periods and reduced metric
hypotheses. -/
def explicitClosedPlacementCertificateFamily
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F) :
    _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementDataW19.ExplicitClosedPlacementCertificateFamily :=
  _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementDataW19.certificateFamilyOfGeneratedPeriodFamily_reduced
    F periods H

@[simp]
theorem explicitClosedPlacementCertificateFamily_point
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (explicitClosedPlacementCertificateFamily F periods H k hk).point i v =
      GeneratedClosedChain.generatedPoint
        (F.O k hk) hk (F.base k hk) (F.orientation k hk) i v :=
  _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementDataW19.certificateOfGeneratedPeriod_reduced_point
    (F.O k hk) hk (F.base k hk) (F.orientation k hk)
    (periods k hk) (H.metric k hk) i v

theorem targetUpperConstructionFiveSixteen_of_reducedFamily
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F) :
    targetUpperConstructionFiveSixteen :=
  _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface.targetUpperConstructionFiveSixteen_of_generatedPeriodFamily_reduced
    F periods H

theorem targetUpperConstructionFiveSixteenArbitrary_of_reducedFamily
    (F : GeneratedChainFamily)
    (periods : F.Periods)
    (H : ReducedMetricHypotheses F) :
    targetUpperConstructionFiveSixteenArbitrary :=
  _root_.ErdosProblems1066.PachToth.NonRigidClosedPlacementInterface.targetUpperConstructionFiveSixteenArbitrary_of_generatedPeriodFamily_reduced
    F periods H

end

end GeneratedMetricAuditW20
end PachToth
end ErdosProblems1066
