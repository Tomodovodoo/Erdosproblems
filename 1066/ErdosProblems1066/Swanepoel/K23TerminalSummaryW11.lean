import ErdosProblems1066.Swanepoel.K23RouteSummaryFinalW11
import ErdosProblems1066.Swanepoel.K23BrokenTargetFinalW11
import ErdosProblems1066.Swanepoel.SwanepoelTargetFinalAggregateW11
import ErdosProblems1066.Swanepoel.SwanepoelRouteLedgerFinalW11

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Terminal W11 K23/common-neighbor summary

This file is the terminal K23/common-neighbor ledger over the checked W11
route-summary, broken-target, target-aggregate, and Swanepoel route-ledger
files.  This file keeps the required input matrices explicit and exposes
target projections only from caller-supplied matrix packages.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace K23TerminalSummaryW11

universe u v

noncomputable section

abbrev Target : Prop :=
  TargetIntegratedMatrixW11.Target

abbrev RouteSummaryMatrices :=
  K23RouteSummaryFinalW11.ExplicitMatrices

abbrev BrokenTargetMatrices :=
  K23BrokenTargetFinalW11.ExplicitMatrices

abbrev TargetAggregateCoreMatrices :=
  SwanepoelTargetFinalAggregateW11.CoreInputMatrices

abbrev TargetAggregateBranchMatrices :=
  SwanepoelTargetFinalAggregateW11.FinalBranchInputMatrices

abbrev TargetAggregateAllMatrices :=
  SwanepoelTargetFinalAggregateW11.ExplicitInputMatrices

/-! ## Imported terminal ledgers -/

/-- Availability status for the optional Swanepoel route ledger. -/
inductive OptionalRouteLedgerStatus where
  | present
  | absent
deriving DecidableEq

/-- Optional terminal ledgers mentioned by the W11 task. -/
structure OptionalTerminalLedgers where
  swanepoelRouteLedger : OptionalRouteLedgerStatus

/-- Optional-ledger availability in this checkout. -/
def optionalTerminalLedgers : OptionalTerminalLedgers where
  swanepoelRouteLedger := OptionalRouteLedgerStatus.present

theorem swanepoelRouteLedger_present :
    optionalTerminalLedgers.swanepoelRouteLedger =
      OptionalRouteLedgerStatus.present := by
  rfl

/-- Checked endpoint ledgers used by the terminal K23/common-neighbor summary. -/
structure CheckedEndpointLedgers where
  routeSummary :
    K23RouteSummaryFinalW11.Matrix.{u}
  brokenTarget :
    K23BrokenTargetFinalW11.Matrix.{u}
  targetAggregate :
    True
  routeLedger :
    SwanepoelRouteLedgerFinalW11.Matrix.{u}
  optional :
    OptionalTerminalLedgers

/-- Imported checked endpoint ledgers. -/
def checkedEndpointLedgers :
    CheckedEndpointLedgers where
  routeSummary := K23RouteSummaryFinalW11.matrix
  brokenTarget := K23BrokenTargetFinalW11.matrix
  targetAggregate := True.intro
  routeLedger := SwanepoelRouteLedgerFinalW11.matrix
  optional := optionalTerminalLedgers

/-! ## Explicit input matrices -/

/-- Explicit matrix surfaces retained by the imported ledgers. -/
structure ExplicitInputMatrixSurfaces where
  routeSummary :
    K23RouteSummaryFinalW11.ExplicitMatrixSurface.{u}
  brokenTarget :
    K23BrokenTargetFinalW11.ExplicitMatrixSurface.{u}
  targetAggregate :
    True
  routeLedger :
    SwanepoelRouteLedgerFinalW11.ExplicitInputMatrixLedger.{u}
  optional :
    OptionalTerminalLedgers

/-- Checked surface ledger for the explicit matrix inputs. -/
def explicitInputMatrixSurfaces :
    ExplicitInputMatrixSurfaces where
  routeSummary := K23RouteSummaryFinalW11.explicitMatrixSurface
  brokenTarget := K23BrokenTargetFinalW11.explicitMatrixSurface
  targetAggregate := True.intro
  routeLedger := SwanepoelRouteLedgerFinalW11.explicitInputMatrixLedger
  optional := optionalTerminalLedgers

/-- Caller-supplied matrix package for every terminal K23/common-neighbor row. -/
structure ExplicitInputMatrices where
  routeSummary :
    RouteSummaryMatrices.{u}
  brokenTarget :
    BrokenTargetMatrices.{u}
  targetCore :
    TargetAggregateCoreMatrices.{u}
  targetBranches :
    TargetAggregateBranchMatrices.{u}
  targetAll :
    TargetAggregateAllMatrices.{u}

namespace ExplicitInputMatrices

/-- K23/common-neighbor final matrix carried by the route-summary input. -/
def routeFinal
    (M : ExplicitInputMatrices) :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} :=
  M.routeSummary.final

/-- K23/common-neighbor final matrix carried by the broken-target input. -/
def brokenTargetFinal
    (M : ExplicitInputMatrices) :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} :=
  M.brokenTarget.k23CommonNeighbor

/-- K23/common-neighbor final matrix carried by the target-aggregate branch input. -/
def branchFinal
    (M : ExplicitInputMatrices) :
    K23FinalIntegratedW11.K23CommonNeighborFinalMatrix.{u} :=
  M.targetBranches.k23Final

/-- Core matrices carried by the combined target-aggregate input. -/
def coreFromAll
    (M : ExplicitInputMatrices) :
    TargetAggregateCoreMatrices.{u} :=
  M.targetAll.core

/-- Final-branch matrices carried by the combined target-aggregate input. -/
def branchesFromAll
    (M : ExplicitInputMatrices) :
    TargetAggregateBranchMatrices.{u} :=
  M.targetAll.finalBranches

@[simp]
theorem routeFinal_eq
    (M : ExplicitInputMatrices) :
    M.routeFinal = M.routeSummary.final := by
  rfl

@[simp]
theorem brokenTargetFinal_eq
    (M : ExplicitInputMatrices) :
    M.brokenTargetFinal = M.brokenTarget.k23CommonNeighbor := by
  rfl

@[simp]
theorem branchFinal_eq
    (M : ExplicitInputMatrices) :
    M.branchFinal = M.targetBranches.k23Final := by
  rfl

@[simp]
theorem coreFromAll_eq
    (M : ExplicitInputMatrices) :
    M.coreFromAll = M.targetAll.core := by
  rfl

@[simp]
theorem branchesFromAll_eq
    (M : ExplicitInputMatrices) :
    M.branchesFromAll = M.targetAll.finalBranches := by
  rfl

end ExplicitInputMatrices

/-! ## Conditional target projections -/

/-- A target projection indexed by an explicit input package. -/
structure ConditionalTargetProjection (alpha : Type v) where
  target : alpha -> Target

/-- Target projections inherited from the final K23 route summary. -/
structure RouteSummaryTargetProjections where
  k23Final :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})
  commonNeighborFinal :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})
  brokenFieldsK23 :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})
  brokenFieldsCommonNeighbor :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})
  brokenTargetK23 :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})
  brokenTargetCommonNeighbor :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})
  finalBranchesK23 :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})
  finalBranchesCommonNeighbor :
    ConditionalTargetProjection (RouteSummaryMatrices.{u})

/-- Checked route-summary target projections. -/
def routeSummaryTargetProjections :
    RouteSummaryTargetProjections where
  k23Final := {
    target := K23RouteSummaryFinalW11.target_of_explicitMatrices_via_k23Final
  }
  commonNeighborFinal := {
    target :=
      K23RouteSummaryFinalW11.target_of_explicitMatrices_via_commonNeighborFinal
  }
  brokenFieldsK23 := {
    target :=
      K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenFields_k23
  }
  brokenFieldsCommonNeighbor := {
    target :=
      K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenFields_commonNeighbor
  }
  brokenTargetK23 := {
    target :=
      K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenTarget_k23
  }
  brokenTargetCommonNeighbor := {
    target :=
      K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenTarget_commonNeighbor
  }
  finalBranchesK23 := {
    target :=
      K23RouteSummaryFinalW11.target_of_explicitMatrices_via_finalBranch_k23
  }
  finalBranchesCommonNeighbor := {
    target :=
      K23RouteSummaryFinalW11.target_of_explicitMatrices_via_finalBranch_commonNeighbor
  }

/-- Target projections inherited from the K23 broken-target final layer. -/
structure BrokenTargetProjections where
  k23Final :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})
  commonNeighborFinal :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})
  k23BrokenLattice :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})
  commonNeighborBrokenLattice :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})
  k23TargetClosure :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})
  commonNeighborTargetClosure :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})
  k23Geometry :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})
  commonNeighborGeometry :
    ConditionalTargetProjection (BrokenTargetMatrices.{u})

/-- Checked K23 broken-target projections. -/
def brokenTargetProjections :
    BrokenTargetProjections where
  k23Final := {
    target := K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23Final
  }
  commonNeighborFinal := {
    target :=
      K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborFinal
  }
  k23BrokenLattice := {
    target :=
      K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23BrokenLattice
  }
  commonNeighborBrokenLattice := {
    target :=
      K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborBrokenLattice
  }
  k23TargetClosure := {
    target :=
      K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23TargetClosure
  }
  commonNeighborTargetClosure := {
    target :=
      K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborTargetClosure
  }
  k23Geometry := {
    target :=
      K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23Geometry
  }
  commonNeighborGeometry := {
    target :=
      K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborGeometry
  }

/-- K23/common-neighbor projections inherited from the target aggregate. -/
structure TargetAggregateProjections where
  coreK23Integrated :
    ConditionalTargetProjection (TargetAggregateCoreMatrices.{u})
  coreCommonNeighborIntegrated :
    ConditionalTargetProjection (TargetAggregateCoreMatrices.{u})
  branchK23Final :
    ConditionalTargetProjection (TargetAggregateBranchMatrices.{u})
  branchCommonNeighborFinal :
    ConditionalTargetProjection (TargetAggregateBranchMatrices.{u})
  allK23Final :
    ConditionalTargetProjection (TargetAggregateAllMatrices.{u})

/-- Checked target-aggregate projections. -/
def targetAggregateProjections :
    TargetAggregateProjections where
  coreK23Integrated := {
    target := SwanepoelTargetFinalAggregateW11.target_via_core_k23Integrated
  }
  coreCommonNeighborIntegrated := {
    target :=
      SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborIntegrated
  }
  branchK23Final := {
    target := SwanepoelTargetFinalAggregateW11.target_via_k23Final
  }
  branchCommonNeighborFinal := {
    target := SwanepoelTargetFinalAggregateW11.target_via_k23Final_commonNeighbor
  }
  allK23Final := {
    target := SwanepoelTargetFinalAggregateW11.target_via_all_k23Final
  }

/-- Collected conditional target projections for this terminal K23 summary. -/
structure ConditionalProjectionLedger where
  routeSummary :
    RouteSummaryTargetProjections
  brokenTarget :
    BrokenTargetProjections
  targetAggregate :
    TargetAggregateProjections

/-- Checked conditional target projections. -/
def conditionalProjectionLedger :
    ConditionalProjectionLedger where
  routeSummary := routeSummaryTargetProjections
  brokenTarget := brokenTargetProjections
  targetAggregate := targetAggregateProjections

/-! ## Final terminal matrix -/

/-- Terminal checked K23/common-neighbor summary.

The matrix stores checked endpoint ledgers, explicit input surfaces, and
conditional target projections.  It provides no target theorem without a
caller-supplied input matrix.
-/
structure Matrix where
  checked :
    CheckedEndpointLedgers
  inputs :
    ExplicitInputMatrixSurfaces
  projections :
    ConditionalProjectionLedger
  omissions :
    SwanepoelW11FinalConsistency.KnownImportOmissions

/-- The checked terminal K23/common-neighbor summary matrix. -/
def matrix :
    Matrix where
  checked := checkedEndpointLedgers
  inputs := explicitInputMatrixSurfaces
  projections := conditionalProjectionLedger
  omissions := SwanepoelW11FinalConsistency.knownImportOmissions

theorem matrix_nonempty :
    Nonempty Matrix :=
  Nonempty.intro matrix

theorem checked_routeSummary :
    matrix.checked.routeSummary = K23RouteSummaryFinalW11.matrix := by
  rfl

theorem checked_brokenTarget :
    matrix.checked.brokenTarget = K23BrokenTargetFinalW11.matrix := by
  rfl

theorem checked_targetAggregate :
    matrix.checked.targetAggregate =
      True.intro := by
  rfl

theorem checked_optionalRouteLedgerStatus :
    matrix.checked.optional.swanepoelRouteLedger =
      OptionalRouteLedgerStatus.present := by
  rfl

theorem checked_routeLedger :
    matrix.checked.routeLedger = SwanepoelRouteLedgerFinalW11.matrix := by
  rfl

/-! ## Public conditional target projections -/

theorem target_of_inputs_via_routeSummary_k23Final
    (M : ExplicitInputMatrices) :
    Target :=
  K23RouteSummaryFinalW11.target_of_explicitMatrices_via_k23Final
    M.routeSummary

theorem target_of_inputs_via_routeSummary_commonNeighborFinal
    (M : ExplicitInputMatrices) :
    Target :=
  K23RouteSummaryFinalW11.target_of_explicitMatrices_via_commonNeighborFinal
    M.routeSummary

theorem target_of_inputs_via_routeSummary_brokenFieldsK23
    (M : ExplicitInputMatrices) :
    Target :=
  K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenFields_k23
    M.routeSummary

theorem target_of_inputs_via_routeSummary_brokenFieldsCommonNeighbor
    (M : ExplicitInputMatrices) :
    Target :=
  K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenFields_commonNeighbor
    M.routeSummary

theorem target_of_inputs_via_routeSummary_brokenTargetK23
    (M : ExplicitInputMatrices) :
    Target :=
  K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenTarget_k23
    M.routeSummary

theorem target_of_inputs_via_routeSummary_brokenTargetCommonNeighbor
    (M : ExplicitInputMatrices) :
    Target :=
  K23RouteSummaryFinalW11.target_of_explicitMatrices_via_brokenTarget_commonNeighbor
    M.routeSummary

theorem target_of_inputs_via_brokenTarget_k23Final
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23Final
    M.brokenTarget

theorem target_of_inputs_via_brokenTarget_commonNeighborFinal
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborFinal
    M.brokenTarget

theorem target_of_inputs_via_brokenTarget_k23BrokenLattice
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23BrokenLattice
    M.brokenTarget

theorem target_of_inputs_via_brokenTarget_commonNeighborBrokenLattice
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborBrokenLattice
    M.brokenTarget

theorem target_of_inputs_via_brokenTarget_k23TargetClosure
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23TargetClosure
    M.brokenTarget

theorem target_of_inputs_via_brokenTarget_commonNeighborTargetClosure
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborTargetClosure
    M.brokenTarget

theorem target_of_inputs_via_brokenTarget_k23Geometry
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_k23Geometry
    M.brokenTarget

theorem target_of_inputs_via_brokenTarget_commonNeighborGeometry
    (M : ExplicitInputMatrices) :
    Target :=
  K23BrokenTargetFinalW11.target_of_matrices_via_k23Broken_commonNeighborGeometry
    M.brokenTarget

theorem target_of_inputs_via_targetAggregate_coreK23Integrated
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_k23Integrated
    M.targetCore

theorem target_of_inputs_via_targetAggregate_coreCommonNeighborIntegrated
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_core_commonNeighborIntegrated
    M.targetCore

theorem target_of_inputs_via_targetAggregate_branchK23Final
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_k23Final
    M.targetBranches

theorem target_of_inputs_via_targetAggregate_branchCommonNeighborFinal
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_k23Final_commonNeighbor
    M.targetBranches

theorem target_of_inputs_via_targetAggregate_allK23Final
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelTargetFinalAggregateW11.target_via_all_k23Final
    M.targetAll

theorem target_of_inputs_via_routeLedger_coreK23Integrated
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_core_k23Integrated
    M.targetCore

theorem target_of_inputs_via_routeLedger_coreCommonNeighborIntegrated
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_core_commonNeighborIntegrated
    M.targetCore

theorem target_of_inputs_via_routeLedger_branchK23Final
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_finalBranches_k23Final
    M.targetBranches

theorem target_of_inputs_via_routeLedger_branchCommonNeighborFinal
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_finalBranches_commonNeighborFinal
    M.targetBranches

theorem target_of_inputs_via_routeLedger_allK23Final
    (M : ExplicitInputMatrices) :
    Target :=
  SwanepoelRouteLedgerFinalW11.target_of_all_k23Final
    M.targetAll

end

end K23TerminalSummaryW11
end Swanepoel
end ErdosProblems1066
