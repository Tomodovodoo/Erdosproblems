import ErdosProblems1066.PachToth.OrbitSqDistancesW12

set_option autoImplicit false

/-!
# W13 restricted exact-block certificates

The concrete two-block all-same orbit is obstructed in `OrbitSqDistancesW12`.
This file records the smallest positive replacement that is currently
provable without changing the transition maps: a one-block generated orbit
has the exact local same-block square-distance table whenever its base block
has that table.  For the exact base, global separation is also inherited from
the checked one-block realization.  The final closure equation remains the
explicit certificate field routed to the exact-block target.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ExactBlockCertificateW13

open FiniteGraph

abbrev R2 := Prod Real Real
abbrev ConcreteTransitionObligations :=
  OrbitSqDistancesW12.ConcreteTransitionObligations

theorem oneBlockPositive : 0 < 1 := by
  decide

theorem finOne_val_eq_zero (i : Fin 1) : i.val = 0 := by
  omega

/-- A one-block generated orbit exposes only the base block, so its
exact-local square-distance invariant is exactly the base invariant. -/
theorem oneBlock_generatedOrbitMatchesExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (base : LocalVertex -> R2)
    (orientation : Fin 1 -> OrientationData.BlockOrientation)
    (hbase : RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances base) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      O oneBlockPositive base orientation := by
  intro i
  have hi : i.val = 0 := finOne_val_eq_zero i
  simpa [RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances,
    GeneratedClosedChain.generatedPoint, hi] using hbase

/-- Exact-base specialization of the one-block orbit square-distance
certificate. -/
theorem oneBlock_exactBase_generatedOrbitMatchesExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      O oneBlockPositive BaseTransitionRealization.exactBase orientation := by
  exact
    oneBlock_generatedOrbitMatchesExactLocalSqDistances
      O BaseTransitionRealization.exactBase orientation
      (by
        simpa [BaseTransitionRealization.exactBase] using
          RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances)

/-- A one-block exact-base generated orbit is globally separated by the
checked one-block realization. -/
theorem oneBlock_exactBase_generatedGlobalSeparation
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O oneBlockPositive BaseTransitionRealization.exactBase orientation := by
  intro i u j v hne
  have hi : i = j := by
    apply Fin.ext
    rw [finOne_val_eq_zero i, finOne_val_eq_zero j]
  have huv : Ne u v := by
    intro huv
    apply hne
    cases hi
    cases huv
    rfl
  have huv_fin :
      Ne (BlockPartition.localVertexEquivFin16 u)
        (BlockPartition.localVertexEquivFin16 v) := by
    intro h
    exact huv (BlockPartition.localVertexEquivFin16.injective h)
  have hsep :=
    OneBlockSoundness.oneBlockCertificate.separated
      (BlockPartition.localVertexEquivFin16 u)
      (BlockPartition.localVertexEquivFin16 v) huv_fin
  have hbase :
      _root_.eucDist
          (BaseTransitionRealization.exactBase u)
          (BaseTransitionRealization.exactBase v) =
        _root_.eucDist
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 u))
          (OneBlockSoundness.oneBlockCertificate.config.pts
            (BlockPartition.localVertexEquivFin16 v)) :=
    BaseTransitionRealization.exactBase_same_block_isometry u v
  have hgoal :
      1 <=
        _root_.eucDist
          (BaseTransitionRealization.exactBase u)
          (BaseTransitionRealization.exactBase v) := by
    rw [hbase]
    exact hsep
  have hi0 : i.val = 0 := finOne_val_eq_zero i
  have hj0 : j.val = 0 := finOne_val_eq_zero j
  simpa [GeneratedClosedChain.generatedPoint, hi0, hj0] using hgoal

/-- A restricted one-block exact-block certificate.  The orbit same-block
metric and global separation are proved in this file; closure is the remaining
honest geometric input. -/
structure ExactOneBlockCertificate
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (orientation : Fin 1 -> OrientationData.BlockOrientation) where
  closure :
    PeriodInterface.GeneratedClosureEquation O oneBlockPositive
      BaseTransitionRealization.exactBase orientation

namespace ExactOneBlockCertificate

variable {O : Figure2Certificate.SameOppositeTransitionObligations}
variable {orientation : Fin 1 -> OrientationData.BlockOrientation}

/-- The proved orbit square-distance component of a one-block certificate. -/
theorem orbitSqDistances
    (_C : ExactOneBlockCertificate O orientation) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      O oneBlockPositive BaseTransitionRealization.exactBase orientation :=
  oneBlock_exactBase_generatedOrbitMatchesExactLocalSqDistances O orientation

/-- The proved global separation component of a one-block exact-base
certificate. -/
theorem separated
    (_C : ExactOneBlockCertificate O orientation) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation O oneBlockPositive
      BaseTransitionRealization.exactBase orientation :=
  oneBlock_exactBase_generatedGlobalSeparation O orientation

/-- Package the one-block certificate as the orbit-square-distance metric
hypotheses consumed by the generated-chain bridge. -/
def toOrbitSqDistanceMetricHypotheses
    (C : ExactOneBlockCertificate O orientation) :
    RoleHingeInterfaceRefinement.GeneratedOrbitSqDistanceMetricHypotheses
      O oneBlockPositive BaseTransitionRealization.exactBase orientation where
  separated := C.separated
  orbit_sq_distances := C.orbitSqDistances

/-- A one-block exact-block certificate routes to the exact target at `16`. -/
theorem targetUpperConstructionFiveSixteenAt_of_certificate
    (C : ExactOneBlockCertificate O orientation) :
    targetUpperConstructionFiveSixteenAt 16 := by
  have htarget : targetUpperConstructionFiveSixteenAt (16 * 1) :=
    RoleHingeInterfaceRefinement.targetUpperConstructionFiveSixteenAt_exactBlock_of_orbitSqDistances
      O oneBlockPositive BaseTransitionRealization.exactBase orientation
      C.closure C.separated C.orbitSqDistances
  simpa using htarget

end ExactOneBlockCertificate

/-- One-block certificate type specialized to the current concrete
connector-only transition obligations. -/
abbrev ConcreteOneBlockCertificate
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :=
  ExactOneBlockCertificate ConcreteTransitionObligations orientation

/-- The concrete connector-only obligations have the one-block exact-base
orbit square-distance invariant.  This does not assert any two-block or
fully quantified orbit theorem. -/
theorem concrete_oneBlock_generatedOrbitMatchesExactLocalSqDistances
    (orientation : Fin 1 -> OrientationData.BlockOrientation) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      ConcreteTransitionObligations oneBlockPositive
      BaseTransitionRealization.exactBase orientation :=
  oneBlock_exactBase_generatedOrbitMatchesExactLocalSqDistances
    ConcreteTransitionObligations orientation

/-- Concrete one-block certificates feed the W12 restricted exact-block
bridge; closure is kept as the certificate field. -/
theorem targetUpperConstructionFiveSixteenAt_of_concreteOneBlockCertificate
    {orientation : Fin 1 -> OrientationData.BlockOrientation}
    (C : ConcreteOneBlockCertificate orientation) :
    targetUpperConstructionFiveSixteenAt 16 := by
  have htarget : targetUpperConstructionFiveSixteenAt (16 * 1) :=
    OrbitSqDistancesW12.exactBlockTarget_of_concreteTransitionObligations_orbitSqDistances
      oneBlockPositive orientation C.closure C.separated
      (concrete_oneBlock_generatedOrbitMatchesExactLocalSqDistances orientation)
  simpa using htarget

end ExactBlockCertificateW13
end PachToth
end ErdosProblems1066

end
