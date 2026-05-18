import ErdosProblems1066.Swanepoel.TargetConsistencyFinalW11
import ErdosProblems1066.Swanepoel.NoEarlyTargetFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelW11FinalConsistency
import ErdosProblems1066.Swanepoel.TargetIntegratedMatrixW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Verified final W11 Swanepoel target consistency layer

This file is a small terminal layer over the checked W11 target modules.  It
records imported ledgers, names the visible matrix hypotheses, and exposes
target projections only from those hypotheses.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace TargetConsistencyVerifiedFinalW11

universe u

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

/-! ## Checked imports -/

/-- Checked W11 ledgers imported by this layer. -/
structure ImportedLedgers : Type (u + 3) where
  targetConsistency :
    TargetConsistencyFinalW11.Matrix.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.Matrix.{u}
  swanepoelFinalOmissions :
    SwanepoelW11FinalConsistency.KnownImportOmissions
  targetIntegrated :
    TargetIntegratedMatrixW11.Matrix.{u}

/-- The checked imported ledgers. -/
def importedLedgers : ImportedLedgers.{u} where
  targetConsistency := TargetConsistencyFinalW11.matrix
  noEarlyTargetFinal := NoEarlyTargetFinalW11.matrix
  swanepoelFinalOmissions :=
    SwanepoelW11FinalConsistency.knownImportOmissions
  targetIntegrated := TargetIntegratedMatrixW11.matrix

/-! ## Explicit required matrices -/

/-- Source-facing matrices used by the integrated target routes. -/
structure SourceRequiredMatrices : Type (u + 1) where
  directField :
    BrokenLatticeIntegratedW11.DirectFieldMatrix.{u}
  k23Field :
    BrokenLatticeIntegratedW11.K23FieldMatrix.{u}
  commonNeighborField :
    BrokenLatticeIntegratedW11.CommonNeighborFieldMatrix.{u}
  noEarlyRows :
    WindowNoEarlyRowsW11.NoEarlyMatrix.{u}
  noStartRows :
    WindowNoEarlyRowsW11.NoStartMatrix.{u}

/-- Target-facing matrices used by the final target consistency routes. -/
structure TargetFacingRequiredMatrices : Type (u + 1) where
  geometryDirect :
    GeometryTargetIntegratedW11.DirectTargetMatrix.{u}
  geometryK23 :
    GeometryTargetIntegratedW11.K23TargetMatrix.{u}
  geometryCommonNeighbor :
    GeometryTargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  k23 :
    K23TargetIntegratedW11.K23TargetMatrix.{u}
  commonNeighbor :
    K23TargetIntegratedW11.CommonNeighborTargetMatrix.{u}
  explicitNoEarly :
    NoEarlyTargetFinalW11.ExplicitNoEarlyMatrix.{u}
  explicitNoStart :
    NoEarlyTargetFinalW11.ExplicitNoStartMatrix.{u}
  explicitNoStartNoEarly :
    NoEarlyTargetFinalW11.ExplicitNoStartNoEarlyMatrix.{u}

/-- All explicit matrix hypotheses consumed by this verified layer. -/
structure ExplicitRequiredMatrices : Type (u + 1) where
  source :
    SourceRequiredMatrices.{u}
  targetFacing :
    TargetFacingRequiredMatrices.{u}
  noEarlyFinal :
    NoEarlyTargetFinalW11.FinalMatrixInput.{u}
  boundaryLabelIntegrated :
    BoundaryLabelIntegratedW11.Matrix.{u}

/-- Type-level requirements inherited from the checked target layers. -/
structure RequiredMatrixTypes : Type (u + 3) where
  targetConsistency :
    TargetConsistencyFinalW11.RequiredInputMatrices.{u}
  noEarlyTargetFinal :
    NoEarlyTargetFinalW11.ExplicitInputLedger.{u}
  source :
    Type (u + 1)
  targetFacing :
    Type (u + 1)
  all :
    Type (u + 1)

/-- The required matrix surfaces recorded without constructing inhabitants. -/
def requiredMatrixTypes : RequiredMatrixTypes.{u} where
  targetConsistency := TargetConsistencyFinalW11.requiredInputMatrices
  noEarlyTargetFinal := NoEarlyTargetFinalW11.explicitInputLedger
  source := SourceRequiredMatrices.{u}
  targetFacing := TargetFacingRequiredMatrices.{u}
  all := ExplicitRequiredMatrices.{u}

/-! ## Conditional projection ledger -/

/-- Target projections exposed by this layer. -/
structure ConditionalTargetProjections : Type (u + 1) where
  directField :
    ExplicitRequiredMatrices.{u} -> Target
  k23Field :
    ExplicitRequiredMatrices.{u} -> Target
  commonNeighborField :
    ExplicitRequiredMatrices.{u} -> Target
  noEarlyRows :
    ExplicitRequiredMatrices.{u} -> Target
  noStartRows :
    ExplicitRequiredMatrices.{u} -> Target
  geometryDirect :
    ExplicitRequiredMatrices.{u} -> Target
  geometryK23 :
    ExplicitRequiredMatrices.{u} -> Target
  geometryCommonNeighbor :
    ExplicitRequiredMatrices.{u} -> Target
  k23 :
    ExplicitRequiredMatrices.{u} -> Target
  commonNeighbor :
    ExplicitRequiredMatrices.{u} -> Target
  explicitNoEarly :
    ExplicitRequiredMatrices.{u} -> Target
  explicitNoStart :
    ExplicitRequiredMatrices.{u} -> Target
  explicitNoStartNoEarly :
    ExplicitRequiredMatrices.{u} -> Target
  noEarlyFinal :
    ExplicitRequiredMatrices.{u} -> Target
  noStartFinal :
    ExplicitRequiredMatrices.{u} -> Target
  boundaryLabelIntegrated :
    ExplicitRequiredMatrices.{u} -> Target

/-! ## Verified matrix -/

/-- Final verified W11 target consistency matrix.

The matrix stores checked ledgers, required matrix surfaces, and conditional
projection functions.  It supplies no inhabitants of the required matrices.
-/
structure Matrix : Type (u + 3) where
  imported :
    ImportedLedgers.{u}
  requirements :
    RequiredMatrixTypes.{u}
  projections :
    ConditionalTargetProjections.{u}

/-! ## Public conditional projections -/

theorem target_of_directField
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_directFieldMatrix
    M.source.directField

theorem target_of_k23Field
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_k23FieldMatrix
    M.source.k23Field

theorem target_of_commonNeighborField
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_commonNeighborFieldMatrix
    M.source.commonNeighborField

theorem target_of_noEarlyRows
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noEarlyMatrix
    M.source.noEarlyRows

theorem target_of_noStartRows
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetIntegratedMatrixW11.targetClosure_of_noStartMatrix
    M.source.noStartRows

theorem target_of_geometryDirect
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryDirectTargetMatrix
    M.targetFacing.geometryDirect

theorem target_of_geometryK23
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryK23TargetMatrix
    M.targetFacing.geometryK23

theorem target_of_geometryCommonNeighbor
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_geometryCommonNeighborTargetMatrix
    M.targetFacing.geometryCommonNeighbor

theorem target_of_k23
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_k23ExplicitTargetMatrix
    M.targetFacing.k23

theorem target_of_commonNeighbor
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_commonNeighborExplicitTargetMatrix
    M.targetFacing.commonNeighbor

theorem target_of_explicitNoEarly
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_noEarlyTargetMatrix
    M.targetFacing.explicitNoEarly

theorem target_of_explicitNoStart
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_noStartTargetMatrix
    M.targetFacing.explicitNoStart

theorem target_of_explicitNoStartNoEarly
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_noStartNoEarlyTargetMatrix
    M.targetFacing.explicitNoStartNoEarly

theorem target_of_noEarlyFinal
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noEarly
    M.noEarlyFinal

theorem target_of_noStartFinal
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  NoEarlyTargetFinalW11.target_of_finalMatrix_via_noStart
    M.noEarlyFinal

theorem target_of_boundaryLabelIntegrated
    (M : ExplicitRequiredMatrices.{u}) :
    Target :=
  TargetConsistencyFinalW11.target_of_boundaryLabelIntegratedMatrix
    M.boundaryLabelIntegrated

/-- The checked conditional target projection functions. -/
def conditionalTargetProjections :
    ConditionalTargetProjections.{u} where
  directField := target_of_directField
  k23Field := target_of_k23Field
  commonNeighborField := target_of_commonNeighborField
  noEarlyRows := target_of_noEarlyRows
  noStartRows := target_of_noStartRows
  geometryDirect := target_of_geometryDirect
  geometryK23 := target_of_geometryK23
  geometryCommonNeighbor := target_of_geometryCommonNeighbor
  k23 := target_of_k23
  commonNeighbor := target_of_commonNeighbor
  explicitNoEarly := target_of_explicitNoEarly
  explicitNoStart := target_of_explicitNoStart
  explicitNoStartNoEarly := target_of_explicitNoStartNoEarly
  noEarlyFinal := target_of_noEarlyFinal
  noStartFinal := target_of_noStartFinal
  boundaryLabelIntegrated := target_of_boundaryLabelIntegrated

/-- The checked verified final target consistency layer. -/
def matrix : Matrix.{u} where
  imported := importedLedgers
  requirements := requiredMatrixTypes
  projections := conditionalTargetProjections

theorem matrix_nonempty :
    Nonempty Matrix.{u} :=
  Nonempty.intro matrix

theorem checked_targetConsistency :
    matrix.{u}.imported.targetConsistency =
      TargetConsistencyFinalW11.matrix := by
  rfl

theorem checked_noEarlyTargetFinal :
    matrix.{u}.imported.noEarlyTargetFinal =
      NoEarlyTargetFinalW11.matrix := by
  rfl

theorem checked_swanepoelFinalConsistency_omissions :
    matrix.{u}.imported.swanepoelFinalOmissions =
      SwanepoelW11FinalConsistency.knownImportOmissions := by
  rfl

theorem checked_targetIntegrated :
    matrix.{u}.imported.targetIntegrated =
      TargetIntegratedMatrixW11.matrix := by
  rfl

end

end TargetConsistencyVerifiedFinalW11
end Swanepoel
end ErdosProblems1066
