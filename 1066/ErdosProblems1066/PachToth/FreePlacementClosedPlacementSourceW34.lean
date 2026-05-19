import ErdosProblems1066.PachToth.DeformedPlacementConstructionW33
import ErdosProblems1066.PachToth.FreePlacementFieldsInhabitationW25
import ErdosProblems1066.PachToth.FullMetricClosedPlacementW24

set_option autoImplicit false

/-!
# W34 free-placement source lane

This file routes the W24 free-placement fields into the W33
`ClosedPlacementMetricFieldFamily` endpoint.  The only connector conversion
needed is the checked W19 finite bridge from the quantified
`CrossBlock.NextConnector` unit field to the four named successor-connector
unit equations expected by the W33 endpoint.
-/

namespace ErdosProblems1066
namespace PachToth
namespace FreePlacementClosedPlacementSourceW34

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev MinimalFreePlacementFields : Type :=
  FreePlacementSourceFieldsW24.MinimalFreePlacementFields

abbrev ClosedPlacementFamily : Type :=
  forall (k : Nat) (hk : 0 < k), DeformedPlacement.ClosedPlacement k hk

abbrev ClosedPlacementMetricFields (k : Nat) (hk : 0 < k) : Type :=
  DeformedPlacement.ClosedPlacementMetricFields k hk

abbrev ClosedPlacementMetricFieldFamily : Type :=
  DeformedPlacement.ClosedPlacementMetricFieldFamily

abbrev FullMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.FullMetricClosedPlacementWitness

abbrev ReducedMetricClosedPlacementWitness : Type :=
  FullMetricClosedPlacementW24.ReducedMetricClosedPlacementWitness

/-- The quantified W24 successor-connector field supplies the four named W19
connector equations expected by the W33 metric-field endpoint. -/
def namedConnectorCertificateOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate
      hk (S.point k hk) where
  t2_2_t1_1 := fun i =>
    S.cross_connector_edges_unit k hk i T2_2 T1_1
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T2_2_T1_1
  t2_2_t1_2 := fun i =>
    S.cross_connector_edges_unit k hk i T2_2 T1_2
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T2_2_T1_2
  t4_0_t0_0 := fun i =>
    S.cross_connector_edges_unit k hk i T4_0 T0_0
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T4_0_T0_0
  t4_0_t0_2 := fun i =>
    S.cross_connector_edges_unit k hk i T4_0 T0_2
      ClosedPlacementCrossConnectorEdgesW19.nextConnector_T4_0_T0_2

/-- W24 free-placement fields, repackaged as one W33 metric-field object at a
fixed positive block count. -/
def metricFieldsOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementMetricFields k hk where
  point := S.point k hk
  separated := S.separated k hk
  same_block_edges_unit := S.same_block_edges_unit k hk
  cross_connector_named_units :=
    namedConnectorCertificateOfMinimalFreePlacementFields S k hk

@[simp]
theorem metricFieldsOfMinimalFreePlacementFields_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (metricFieldsOfMinimalFreePlacementFields S k hk).point i v =
      S.point k hk i v := by
  rfl

/-- W24 free-placement fields supply the complete W33 metric-field family. -/
def metricFieldFamilyOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    ClosedPlacementMetricFieldFamily :=
  fun k hk => metricFieldsOfMinimalFreePlacementFields S k hk

@[simp]
theorem metricFieldFamilyOfMinimalFreePlacementFields_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (metricFieldFamilyOfMinimalFreePlacementFields S k hk).point i v =
      S.point k hk i v := by
  rfl

/-- The W33 endpoint gives checked closed placements from the W24 source lane. -/
def closedPlacementOfMinimalFreePlacementFields
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) :
    DeformedPlacement.ClosedPlacement k hk :=
  DeformedPlacement.closedPlacement_of_metricFieldFamily
    (metricFieldFamilyOfMinimalFreePlacementFields S) k hk

@[simp]
theorem closedPlacementOfMinimalFreePlacementFields_point
    (S : MinimalFreePlacementFields)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (closedPlacementOfMinimalFreePlacementFields S k hk).point i v =
      S.point k hk i v := by
  rfl

/-- Any family of checked closed placements can be re-exposed through the W33
metric-field endpoint by first forgetting to W24 free-placement fields. -/
def metricFieldFamilyOfClosedPlacementFamily
    (H : ClosedPlacementFamily) :
    ClosedPlacementMetricFieldFamily :=
  metricFieldFamilyOfMinimalFreePlacementFields
    (FreePlacementSourceFieldsW24.ofClosedPlacements H)

@[simp]
theorem metricFieldFamilyOfClosedPlacementFamily_point
    (H : ClosedPlacementFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (metricFieldFamilyOfClosedPlacementFamily H k hk).point i v =
      (H k hk).point i v := by
  rfl

/-- A full-metric W24 witness also lands in the W33 metric-field endpoint. -/
def metricFieldFamilyOfFullMetricWitness
    (W : FullMetricClosedPlacementWitness) :
    ClosedPlacementMetricFieldFamily :=
  metricFieldFamilyOfClosedPlacementFamily W.closedPlacementFamily

/-- A reduced-metric W24 witness also lands in the W33 metric-field endpoint. -/
def metricFieldFamilyOfReducedMetricWitness
    (W : ReducedMetricClosedPlacementWitness) :
    ClosedPlacementMetricFieldFamily :=
  metricFieldFamilyOfClosedPlacementFamily W.closedPlacementFamily

/-- Conversely, a W33 metric-field family already gives W24 free-placement
fields by using the checked W33 closed-placement conversion. -/
def minimalFreePlacementFieldsOfMetricFieldFamily
    (F : ClosedPlacementMetricFieldFamily) :
    MinimalFreePlacementFields :=
  FreePlacementSourceFieldsW24.ofClosedPlacements
    (fun k hk => DeformedPlacement.closedPlacement_of_metricFieldFamily F k hk)

@[simp]
theorem minimalFreePlacementFieldsOfMetricFieldFamily_point
    (F : ClosedPlacementMetricFieldFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) (v : LocalVertex) :
    (minimalFreePlacementFieldsOfMetricFieldFamily F).point k hk i v =
      (F k hk).point i v := by
  rfl

theorem nonempty_metricFieldFamily_of_minimalFreePlacementFields :
    Nonempty MinimalFreePlacementFields ->
      Nonempty ClosedPlacementMetricFieldFamily := by
  rintro ⟨S⟩
  exact ⟨metricFieldFamilyOfMinimalFreePlacementFields S⟩

theorem nonempty_minimalFreePlacementFields_of_metricFieldFamily :
    Nonempty ClosedPlacementMetricFieldFamily ->
      Nonempty MinimalFreePlacementFields := by
  rintro ⟨F⟩
  exact ⟨minimalFreePlacementFieldsOfMetricFieldFamily F⟩

/-- The W24 source surface and the W33 metric-field endpoint are equivalent
at the nonempty/source-gate level. -/
theorem nonempty_minimalFreePlacementFields_iff_metricFieldFamily :
    Nonempty MinimalFreePlacementFields <->
      Nonempty ClosedPlacementMetricFieldFamily := by
  constructor
  · exact nonempty_metricFieldFamily_of_minimalFreePlacementFields
  · exact nonempty_minimalFreePlacementFields_of_metricFieldFamily

theorem nonempty_metricFieldFamily_of_closedPlacementFamily :
    Nonempty ClosedPlacementFamily ->
      Nonempty ClosedPlacementMetricFieldFamily := by
  rintro ⟨H⟩
  exact ⟨metricFieldFamilyOfClosedPlacementFamily H⟩

theorem targetUpperConstructionFiveSixteen_of_metricFieldFamily
    (F : ClosedPlacementMetricFieldFamily) :
    targetUpperConstructionFiveSixteen :=
  DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
    (fun k hk => DeformedPlacement.closedPlacement_of_metricFieldFamily F k hk)

theorem targetUpperConstructionFiveSixteen_of_metricFieldFamilyGate
    (H : Nonempty ClosedPlacementMetricFieldFamily) :
    targetUpperConstructionFiveSixteen := by
  rcases H with ⟨F⟩
  exact targetUpperConstructionFiveSixteen_of_metricFieldFamily F

theorem targetUpperConstructionFiveSixteen_of_minimalFreePlacementFields
    (S : MinimalFreePlacementFields) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_metricFieldFamily
    (metricFieldFamilyOfMinimalFreePlacementFields S)

theorem targetUpperConstructionFiveSixteen_of_minimalFreePlacementFieldsGate
    (H : Nonempty MinimalFreePlacementFields) :
    targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_metricFieldFamilyGate
    (nonempty_metricFieldFamily_of_minimalFreePlacementFields H)

end

end FreePlacementClosedPlacementSourceW34
end PachToth

namespace Verified

open PachToth.FreePlacementClosedPlacementSourceW34

abbrev PachTothW34ClosedPlacementMetricFieldFamily : Type :=
  ClosedPlacementMetricFieldFamily

abbrev PachTothW34FreePlacementSourceFields : Type :=
  MinimalFreePlacementFields

theorem pachtoth_w34_freePlacementSourceFields_iff_metricFieldFamily :
    Nonempty PachTothW34FreePlacementSourceFields <->
      Nonempty PachTothW34ClosedPlacementMetricFieldFamily :=
  nonempty_minimalFreePlacementFields_iff_metricFieldFamily

theorem targetUpperConstructionFiveSixteen_of_pachtoth_w34_metricFieldFamily
    (F : PachTothW34ClosedPlacementMetricFieldFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_metricFieldFamily F

theorem targetUpperConstructionFiveSixteen_of_pachtoth_w34_freePlacementSourceFields
    (H : Nonempty PachTothW34FreePlacementSourceFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_minimalFreePlacementFieldsGate H

end Verified
end ErdosProblems1066
