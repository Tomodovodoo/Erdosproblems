import ErdosProblems1066.PachToth.ReducedMetricHypothesesProducerW20

set_option autoImplicit false

/-!
# W21 reduced metric source fields

This file keeps the reduced-metric source for the concrete role-hinged
generated-chain family honest.  For
`ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F`, the
base-block and transition same-block metric fields are already canonical; the
only remaining metric field is global separation.  Existing W19 separation
certificates and non-connector tables feed that single field.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ReducedMetricSourceFieldsW21

open FiniteGraph

noncomputable section

abbrev GeneratedChainFamily :=
  ReducedMetricHypothesesProducerW20.GeneratedChainFamily

abbrev RoleHingedPeriodSearchFamily :=
  NonConnectorSeparationW12.RoleHingedPeriodSearchFamily

abbrev ConcreteValueMatrixFamily :=
  ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily

/-- The concrete generated-chain family used by the reduced role-hinged
non-connector route. -/
abbrev roleHingedGeneratedChainFamily
    (F : RoleHingedPeriodSearchFamily) :
    GeneratedChainFamily :=
  ReducedMetricHypothesesProducerW20.generatedChainFamilyOfRoleHinged F

/-- For the role-hinged generated family, this is the only remaining
non-canonical reduced-metric field. -/
abbrev RemainingSeparationField
    (F : RoleHingedPeriodSearchFamily) : Prop :=
  forall (k : Nat) (hk : 0 < k),
    ReducedMetricHypothesesProducerW20.GeneratedGlobalSeparationAt
      (roleHingedGeneratedChainFamily F) k hk

/-- Build the W20 reduced-metric field package from the single remaining
separation field. -/
def fieldsOfSeparation
    (F : RoleHingedPeriodSearchFamily)
    (separated : RemainingSeparationField F) :
    ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  ReducedMetricHypothesesProducerW20.roleHingedReducedMetricFields F separated

/-- Forget the canonical fields and retain the only source field that is not
already fixed by the role-hinged generated-chain construction. -/
def separationOfFields
    {F : RoleHingedPeriodSearchFamily}
    (D : ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F)) :
    RemainingSeparationField F :=
  D.separated

@[simp]
theorem separationOfFields_fieldsOfSeparation
    (F : RoleHingedPeriodSearchFamily)
    (separated : RemainingSeparationField F) :
    separationOfFields (fieldsOfSeparation F separated) = separated :=
  rfl

/-- Exact nonemptiness reduction: for the concrete role-hinged generated
family, inhabiting W20 `ReducedMetricFields` is precisely the same as proving
the remaining separation field. -/
theorem nonempty_reducedMetricFields_iff_remainingSeparation
    (F : RoleHingedPeriodSearchFamily) :
    Nonempty (ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F)) <->
      RemainingSeparationField F := by
  constructor
  · intro h
    exact h.elim (fun D => separationOfFields D)
  · intro h
    exact ⟨fieldsOfSeparation F h⟩

/-- The same reduction in the forward direction, as a compact constructor. -/
theorem nonempty_reducedMetricFields_of_remainingSeparation
    (F : RoleHingedPeriodSearchFamily)
    (separated : RemainingSeparationField F) :
    Nonempty (ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F)) :=
  (nonempty_reducedMetricFields_iff_remainingSeparation F).2 separated

/-- W19 separation-family certificates provide the remaining separation field
when their point map is the generated point map of the concrete family. -/
def fieldsOfW19SeparationFamily
    {F : RoleHingedPeriodSearchFamily}
    (S : ClosedPlacementSeparationW19.SeparationFamilyCertificate)
    (point_eq :
      forall (k : Nat) (hk : 0 < k),
        S.point k hk =
          ReducedMetricHypothesesProducerW20.GeneratedPointAt (roleHingedGeneratedChainFamily F) k hk) :
    ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  ReducedMetricHypothesesProducerW20.W19SeparatedReducedMetricFields.toReducedMetricFields
    { separation := S
      point_eq := point_eq
      base_same_block_isometry := fun _k _hk =>
        GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
      transition_preserves_same_block_distances := fun _k _hk =>
        GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
          F.transitions }

/-- Existing generated non-connector square-distance table families inhabit
the W20 reduced-metric fields for the concrete role-hinged generated family. -/
def fieldsOfGeneratedNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily
      F) :
    ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  fieldsOfSeparation F (fun k hk => T.separated k hk)

@[simp]
theorem fieldsOfGeneratedNonConnectorSqDistanceTableFamily_separated
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily
      F)
    (k : Nat) (hk : 0 < k) :
    (fieldsOfGeneratedNonConnectorSqDistanceTableFamily T).separated k hk =
      T.separated k hk :=
  rfl

/-- The generated-table field constructor agrees with the W20 reduced-metric
hypothesis producer after bundling the fields. -/
theorem fieldsOfGeneratedNonConnectorSqDistanceTableFamily_toReducedMetricHypotheses
    {F : RoleHingedPeriodSearchFamily}
    (T : NonConnectorSeparationW12.GeneratedNonConnectorSqDistanceTableFamily
      F) :
    (fieldsOfGeneratedNonConnectorSqDistanceTableFamily T).toReducedMetricHypotheses =
      ReducedMetricHypothesesProducerW20.ofGeneratedNonConnectorSqDistanceTableFamily T :=
  rfl

/-- Existing indexed non-connector square-distance table families inhabit the
same reduced-metric field package. -/
def fieldsOfIndexedNonConnectorCrossBlockSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T :
      NonConnectorSeparationW12.IndexedNonConnectorCrossBlockSqDistanceTableFamily
        F) :
    ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  fieldsOfGeneratedNonConnectorSqDistanceTableFamily
    (NonConnectorInstantiationW13.generatedTableFamilyOfIndexedTableFamily T)

/-- Existing cross-block lower-bound facades inhabit the reduced-metric field
package by supplying the remaining separation field. -/
def fieldsOfCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (H : NonConnectorSeparationW12.CrossBlockLowerBounds F) :
    ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F) :=
  fieldsOfSeparation F (fun k hk => H.separated k hk)

/-- Concrete non-connector value matrices give the requested field inhabitant
for their concrete generated-chain family. -/
def fieldsOfConcreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    ReducedMetricHypothesesProducerW20.ReducedMetricFields
      (roleHingedGeneratedChainFamily C.toRoleHingedPeriodSearchFamily) :=
  fieldsOfGeneratedNonConnectorSqDistanceTableFamily
    (NonConnectorInstantiationW13.generatedTableFamilyOfConcreteValueMatrixFamily
      C)

theorem nonempty_reducedMetricFields_of_concreteValueMatrixFamily
    (C : ConcreteValueMatrixFamily) :
    Nonempty
      (ReducedMetricHypothesesProducerW20.ReducedMetricFields
        (roleHingedGeneratedChainFamily C.toRoleHingedPeriodSearchFamily)) :=
  ⟨fieldsOfConcreteValueMatrixFamily C⟩

/-- Bundling the concrete value-matrix field inhabitant is definitionally the
W20 concrete value-matrix reduced-metric route. -/
theorem fieldsOfConcreteValueMatrixFamily_toReducedMetricHypotheses
    (C : ConcreteValueMatrixFamily) :
    (fieldsOfConcreteValueMatrixFamily C).toReducedMetricHypotheses =
      ReducedMetricHypothesesProducerW20.ofConcreteValueMatrixFamily C :=
  rfl

/-- The W19 same-block unit-edge certificate projected from W20 reduced
metric fields. -/
def sameBlockUnitEdgeCertificateOfFields
    {F : RoleHingedPeriodSearchFamily}
    (D : ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F))
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdgeCertificate
      (ReducedMetricHypothesesProducerW20.GeneratedPointAt (roleHingedGeneratedChainFamily F) k hk) :=
  ReducedMetricHypothesesProducerW20.sameBlockUnitEdgeCertificateOfReducedMetric
    D.toReducedMetricHypotheses k hk

/-- Generated periods plus W20 reduced metric fields give the W19
cross-connector four-edge certificate. -/
def crossConnectorUnitCertificateOfFields
    {F : RoleHingedPeriodSearchFamily}
    (periods : (roleHingedGeneratedChainFamily F).Periods)
    (D : ReducedMetricHypothesesProducerW20.ReducedMetricFields (roleHingedGeneratedChainFamily F))
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementCrossConnectorEdgesW19.ExactCrossConnectorUnitCertificate
      hk (ReducedMetricHypothesesProducerW20.GeneratedPointAt (roleHingedGeneratedChainFamily F) k hk) :=
  ReducedMetricHypothesesProducerW20.crossConnectorUnitCertificateOfReducedMetric
    periods D.toReducedMetricHypotheses k hk

end

end ReducedMetricSourceFieldsW21
end PachToth
end ErdosProblems1066
