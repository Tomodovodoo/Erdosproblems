import ErdosProblems1066.Swanepoel.BoundaryAngleTargetFinalW11
import ErdosProblems1066.Swanepoel.BoundaryAngleFinalIntegratedW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11
import ErdosProblems1066.Swanepoel.TargetConsistencyVerifiedFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Final W11 boundary-angle route summary

This leaf module records the final boundary-angle route ledgers, names the
uniform final boundary-angle matrix input, and exposes only target projections
that still require that input.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryAngleRouteSummaryFinalW11

open MinimalGraphFacts

universe u

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev FinalMatrixInput : Type (u + 1) :=
  BoundaryAngleTargetFinalW11.FinalMatrixInput.{u}

abbrev FinalRow
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) : Type (u + 1) :=
  BoundaryAngleTargetFinalW11.FinalRow.{u} C hmin

/-! ## Checked ledgers -/

/-- Checked final W11 ledgers summarized by this boundary-angle route. -/
structure CheckedLedgers where
  boundaryAngleTarget :
    BoundaryAngleTargetFinalW11.Matrix.{u}
  boundaryAngleFinal :
    BoundaryAngleFinalIntegratedW11.Matrix.{u}

/-- Imported checked ledgers used by the summary. -/
def checkedLedgers : CheckedLedgers where
  boundaryAngleTarget := BoundaryAngleTargetFinalW11.matrix
  boundaryAngleFinal := BoundaryAngleFinalIntegratedW11.matrix

/-! ## Explicit final matrix input -/

/-- The explicit final boundary-angle input surface retained by this summary.

The summary records the row and uniform matrix shapes only; it does not
construct an inhabitant of the uniform matrix. -/
structure ExplicitFinalMatrixInput : Type (u + 2) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n),
      IsMinimalClearedFailure C -> Type (u + 1)
  uniform :
    Type (u + 1)

/-- Displayed final boundary-angle input surface. -/
def explicitFinalMatrixInput :
    ExplicitFinalMatrixInput.{u} where
  row := fun C hmin => FinalRow.{u} C hmin
  uniform := FinalMatrixInput.{u}

/-! ## Conditional target projections -/

/-- Target projections from a supplied final boundary-angle matrix. -/
structure ConditionalTargetProjections : Type (u + 1) where
  finalIntegratedDirect :
    FinalMatrixInput.{u} -> Target
  finalIntegratedK23 :
    FinalMatrixInput.{u} -> Target
  finalIntegratedCommonNeighbor :
    FinalMatrixInput.{u} -> Target
  targetLayerDirect :
    FinalMatrixInput.{u} -> Target
  targetLayerK23 :
    FinalMatrixInput.{u} -> Target
  targetLayerCommonNeighbor :
    FinalMatrixInput.{u} -> Target
  brokenLatticeDirect :
    FinalMatrixInput.{u} -> Target
  brokenLatticeK23 :
    FinalMatrixInput.{u} -> Target
  brokenLatticeCommonNeighbor :
    FinalMatrixInput.{u} -> Target
  targetConsistencyDirect :
    FinalMatrixInput.{u} -> Target
  targetConsistencyK23 :
    FinalMatrixInput.{u} -> Target
  targetConsistencyCommonNeighbor :
    FinalMatrixInput.{u} -> Target
  aggregateBoundaryAngleDirect :
    SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u} -> Target
  aggregateBoundaryAngleK23 :
    SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u} -> Target
  aggregateBoundaryAngleCommonNeighbor :
    SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u} -> Target
  verifiedDirectField :
    TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u} -> Target
  verifiedK23Field :
    TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u} -> Target
  verifiedCommonNeighborField :
    TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u} -> Target

/-- Checked conditional target projections from the final matrix input. -/
def conditionalTargetProjections :
    ConditionalTargetProjections.{u} where
  finalIntegratedDirect :=
    BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_direct
  finalIntegratedK23 :=
    BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_k23
  finalIntegratedCommonNeighbor :=
    BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_commonNeighbor
  targetLayerDirect :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_direct
  targetLayerK23 :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_k23
  targetLayerCommonNeighbor :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
  brokenLatticeDirect :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeDirect
  brokenLatticeK23 :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeK23
  brokenLatticeCommonNeighbor :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeCommonNeighbor
  targetConsistencyDirect :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyDirect
  targetConsistencyK23 :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyK23
  targetConsistencyCommonNeighbor :=
    BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyCommonNeighbor
  aggregateBoundaryAngleDirect :=
    SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_direct
  aggregateBoundaryAngleK23 :=
    SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_k23
  aggregateBoundaryAngleCommonNeighbor :=
    SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_commonNeighbor
  verifiedDirectField :=
    TargetConsistencyVerifiedFinalW11.target_of_directField
  verifiedK23Field :=
    TargetConsistencyVerifiedFinalW11.target_of_k23Field
  verifiedCommonNeighborField :=
    TargetConsistencyVerifiedFinalW11.target_of_commonNeighborField

/-! ## Final summary matrix -/

/-- Concise final boundary-angle route summary.

The matrix stores checked ledgers, the explicit final matrix surface, and
conditional target projections. -/
structure Matrix where
  checked :
    CheckedLedgers
  input :
    ExplicitFinalMatrixInput.{u}
  projections :
    ConditionalTargetProjections.{u}

/-- The checked final boundary-angle route summary matrix. -/
def matrix :
    Matrix where
  checked := checkedLedgers
  input := explicitFinalMatrixInput
  projections := conditionalTargetProjections

theorem matrix_nonempty :
    Nonempty Matrix :=
  Nonempty.intro matrix

theorem checked_boundaryAngleTarget :
    matrix.checked.boundaryAngleTarget =
      BoundaryAngleTargetFinalW11.matrix := by
  rfl

theorem checked_boundaryAngleFinal :
    matrix.checked.boundaryAngleFinal =
      BoundaryAngleFinalIntegratedW11.matrix := by
  rfl

/-! ## Public conditional projections -/

theorem target_of_finalMatrix_via_finalIntegratedDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_direct M

theorem target_of_finalMatrix_via_finalIntegratedK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_k23 M

theorem target_of_finalMatrix_via_finalIntegratedCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleFinalIntegratedW11.target_of_finalMatrix_via_commonNeighbor M

theorem target_of_finalMatrix_via_targetLayerDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_direct M

theorem target_of_finalMatrix_via_targetLayerK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_k23 M

theorem target_of_finalMatrix_via_targetLayerCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_commonNeighbor
    M

theorem target_of_finalMatrix_via_brokenLatticeDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeDirect
    M

theorem target_of_finalMatrix_via_brokenLatticeK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeK23
    M

theorem target_of_finalMatrix_via_brokenLatticeCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_brokenLatticeCommonNeighbor
    M

theorem target_of_finalMatrix_via_targetConsistencyDirect
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyDirect
    M

theorem target_of_finalMatrix_via_targetConsistencyK23
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyK23
    M

theorem target_of_finalMatrix_via_targetConsistencyCommonNeighbor
    (M : FinalMatrixInput.{u}) :
    Target :=
  BoundaryAngleTargetFinalW11.swanepoelTarget_of_finalMatrix_via_targetConsistencyCommonNeighbor
    M

theorem target_of_aggregateBoundaryAngle_via_direct
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_direct M

theorem target_of_aggregateBoundaryAngle_via_k23
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_k23 M

theorem target_of_aggregateBoundaryAngle_via_commonNeighbor
    (M : SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices.{u}) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_boundaryAngle_commonNeighbor M

theorem target_of_verifiedConsistency_via_directField
    (M : TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyVerifiedFinalW11.target_of_directField M

theorem target_of_verifiedConsistency_via_k23Field
    (M : TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyVerifiedFinalW11.target_of_k23Field M

theorem target_of_verifiedConsistency_via_commonNeighborField
    (M : TargetConsistencyVerifiedFinalW11.ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyVerifiedFinalW11.target_of_commonNeighborField M

end

end BoundaryAngleRouteSummaryFinalW11
end Swanepoel
end ErdosProblems1066
