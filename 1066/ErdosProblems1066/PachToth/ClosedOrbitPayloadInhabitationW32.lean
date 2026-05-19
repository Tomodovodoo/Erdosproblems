import ErdosProblems1066.PachToth.ClosedOrbitConcreteBranchW31
import ErdosProblems1066.PachToth.ClosedOrbitBranchSourceW30
import ErdosProblems1066.PachToth.CompletionRowsInhabitationW31
import ErdosProblems1066.PachToth.ClosedPlacementCrossConnectorEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementSameBlockEdgesW19
import ErdosProblems1066.PachToth.ClosedPlacementSeparationW19

set_option autoImplicit false

/-!
# W32 closed-orbit payload inhabitation

This file is a source-only bridge from W31 completion-row inhabitants to the
W31 closed-orbit branch payload surface.  The completion rows remain the real
source requirements: cyclic displacement closure, square-distance separation,
and square-distance same-block unit rows.  Once those rows exist, the
successor cross-connector square-unit rows are derived from the generated
transition package and the closure equation.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedOrbitPayloadInhabitationW32

open Arithmetic
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-! ## W31 source vocabulary -/

abbrev GeneratedOrbitSkeleton : Type :=
  ClosedOrbitConcreteBranchW31.GeneratedOrbitSkeleton

abbrev DisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedDisplacementClosureRows G

abbrev SeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedSeparationRows G

abbrev SameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedSameBlockUnitRows G

abbrev CompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedCompletionRows G

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedCompletionRowsGate G

abbrev GeneratedCompletionPayloads
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedCompletionPayloads G

abbrev GeneratedCompletionPayloadBlocker
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedCompletionPayloadBlocker G

abbrev CompletionRowData
    (G : GeneratedOrbitSkeleton) : Prop :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowData G

abbrev CompletionRowSource : Type :=
  CompletionRowsInhabitationW31.GeneratedCompletionRowSource

abbrev SquaredOrbitClosureSourceRows : Type :=
  ClosedOrbitConcreteBranchW31.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  ClosedOrbitConcreteBranchW31.SquaredOrbitClosureSourceRowsGate

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  ClosedOrbitConcreteBranchW31.SquaredMinimalFieldsWithOrbitClosure

abbrev SquaredOrbitClosureGate : Prop :=
  ClosedOrbitConcreteBranchW31.SquaredOrbitClosureGate

abbrev ConcreteClosedOrbitFamily : Type :=
  ClosedOrbitConcreteBranchW31.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  ClosedOrbitConcreteBranchW31.ConcreteClosedOrbitFamilyGate

abbrev W27SquaredMetricClosureRowsGate : Prop :=
  ClosedOrbitConcreteBranchW31.W27SquaredMetricClosureRowsGate

abbrev MinimalFieldsWithOrbitClosure : Type :=
  ClosedOrbitConcreteBranchW31.MinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  ClosedOrbitConcreteBranchW31.MinimalFieldsWithOrbitClosureGate

abbrev ClosedOrbitBranchGate : Prop :=
  ClosedOrbitConcreteBranchW31.ClosedOrbitBranchGate

abbrev GeneratedClosureMetricGate : Prop :=
  ClosedOrbitConcreteBranchW31.GeneratedClosureMetricGate

abbrev GeneratedClosureMetricRowPackage : Type :=
  ClosedOrbitConcreteBranchW31.GeneratedClosureMetricRowPackage

abbrev MissingDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.MissingDisplacementClosureRows G

abbrev MissingSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.MissingSeparationRows G

abbrev MissingSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  ClosedOrbitConcreteBranchW31.MissingSameBlockUnitRows G

/-! ## Completion-row payloads and W31 row-data inhabitants -/

def completionRowDataOfPayloads
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionPayloads G) :
    CompletionRowData G where
  closure := H.1
  separated_sq := H.2.1
  same_block_edges_sq_unit := H.2.2

theorem payloads_of_completionRowData
    {G : GeneratedOrbitSkeleton}
    (D : CompletionRowData G) :
    GeneratedCompletionPayloads G :=
  And.intro D.closure
    (And.intro D.separated_sq D.same_block_edges_sq_unit)

theorem nonempty_completionRowData_iff_payloads
    (G : GeneratedOrbitSkeleton) :
    Nonempty (CompletionRowData G) <->
      GeneratedCompletionPayloads G := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro D =>
        exact payloads_of_completionRowData D
  case mpr =>
    intro h
    exact Nonempty.intro (completionRowDataOfPayloads h)

theorem completionRowsGate_iff_completionRowData
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionRowsGate G <->
      Nonempty (CompletionRowData G) :=
  CompletionRowsInhabitationW31.completionRowsGate_iff_generatedCompletionRowData
    G

theorem completionRowsGate_iff_payloads
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionRowsGate G <->
      GeneratedCompletionPayloads G :=
  ClosedOrbitConcreteBranchW31.generatedCompletionRowsGate_iff_payloads G

def completionRowsOfCompletionRowData
    {G : GeneratedOrbitSkeleton}
    (D : CompletionRowData G) :
    CompletionRows G :=
  D.toCompletionRows

def sourceRowsOfCompletionRowData
    {G : GeneratedOrbitSkeleton}
    (D : CompletionRowData G) :
    SquaredOrbitClosureSourceRows :=
  D.toSourceRows

theorem sourceRowsGate_of_completionRowData
    {G : GeneratedOrbitSkeleton}
    (D : CompletionRowData G) :
    SquaredOrbitClosureSourceRowsGate :=
  Nonempty.intro (sourceRowsOfCompletionRowData D)

theorem sourceRowsGate_of_completionRowDataGate
    {G : GeneratedOrbitSkeleton}
    (H : Nonempty (CompletionRowData G)) :
    SquaredOrbitClosureSourceRowsGate := by
  cases H with
  | intro D =>
      exact sourceRowsGate_of_completionRowData D

theorem closedOrbitBranchGate_of_payloads
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionPayloads G) :
    ClosedOrbitBranchGate :=
  ClosedOrbitConcreteBranchW31.closedOrbitBranchGate_of_payloads
    H.1 H.2.1 H.2.2

theorem closedOrbitBranchGate_of_completionRowData
    {G : GeneratedOrbitSkeleton}
    (D : CompletionRowData G) :
    ClosedOrbitBranchGate :=
  ClosedOrbitConcreteBranchW31.closedOrbitBranchGate_of_completionRows
    (completionRowsOfCompletionRowData D)

theorem closedOrbitBranchGate_of_completionRowDataGate
    {G : GeneratedOrbitSkeleton}
    (H : Nonempty (CompletionRowData G)) :
    ClosedOrbitBranchGate := by
  cases H with
  | intro D =>
      exact closedOrbitBranchGate_of_completionRowData D

theorem closedOrbitBranchGate_of_completionRowSource
    (S : CompletionRowSource) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_completionRowData S.data

theorem closedOrbitBranchGate_of_completionRowSourceGate
    (H : Nonempty CompletionRowSource) :
    ClosedOrbitBranchGate := by
  cases H with
  | intro S =>
      exact closedOrbitBranchGate_of_completionRowSource S

theorem closedOrbitBranchGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ClosedOrbitBranchGate :=
  ClosedOrbitConcreteBranchW31.closedOrbitBranchGate_of_generatedClosureMetricGate
    H

theorem w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    W27SquaredMetricClosureRowsGate :=
  ClosedOrbitConcreteBranchW31.w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate
    H

theorem closedOrbitBranchGate_of_w27SquaredMetricClosureRowsGate
    (H : W27SquaredMetricClosureRowsGate) :
    ClosedOrbitBranchGate :=
  ClosedOrbitConcreteBranchW31.closedOrbitBranchGate_of_w27SquaredMetricClosureRowsGate
    H

/-! ## Same-block and cross-connector square-unit rows -/

abbrev sqDist (p q : R2) : Real :=
  SquaredOrbitClosureSourceW28.sqDist p q

abbrev CrossConnectorSqUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u v : LocalVertex),
    CrossBlock.NextConnector u v ->
      sqDist (G.point k hk i u)
        (G.point k hk (cyclicSucc hk i) v) = 1

abbrev SameBlockAndCrossConnectorSqUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  SameBlockUnitRows G /\ CrossConnectorSqUnitRows G

theorem crossConnectorSqUnitRows_of_sourceRows
    (S : SquaredOrbitClosureSourceRows) :
    CrossConnectorSqUnitRows S.skeleton := by
  intro k hk i u v hconn
  exact S.crossConnectorSqUnit k hk i u v hconn

theorem crossConnectorSqUnitRows_of_completionRowData
    {G : GeneratedOrbitSkeleton}
    (D : CompletionRowData G) :
    CrossConnectorSqUnitRows G := by
  simpa [sourceRowsOfCompletionRowData] using
    crossConnectorSqUnitRows_of_sourceRows
      (sourceRowsOfCompletionRowData D)

theorem crossConnectorSqUnitRows_of_payloads
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionPayloads G) :
    CrossConnectorSqUnitRows G :=
  crossConnectorSqUnitRows_of_completionRowData
    (completionRowDataOfPayloads H)

theorem sameBlockAndCrossConnectorSqUnitRows_of_completionRowData
    {G : GeneratedOrbitSkeleton}
    (D : CompletionRowData G) :
    SameBlockAndCrossConnectorSqUnitRows G :=
  And.intro D.same_block_edges_sq_unit
    (crossConnectorSqUnitRows_of_completionRowData D)

theorem sameBlockAndCrossConnectorSqUnitRows_of_payloads
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionPayloads G) :
    SameBlockAndCrossConnectorSqUnitRows G :=
  And.intro H.2.2 (crossConnectorSqUnitRows_of_payloads H)

/-! ## Sharp source-row blockers -/

abbrev MissingCrossConnectorSqUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  Not (CrossConnectorSqUnitRows G)

theorem missingDisplacementClosureRows_blocks_payloads
    {G : GeneratedOrbitSkeleton}
    (B : MissingDisplacementClosureRows G) :
    Not (GeneratedCompletionPayloads G) := by
  intro h
  exact B.no_rows h.1

theorem missingSeparationRows_blocks_payloads
    {G : GeneratedOrbitSkeleton}
    (B : MissingSeparationRows G) :
    Not (GeneratedCompletionPayloads G) := by
  intro h
  exact B.no_rows h.2.1

theorem missingSameBlockUnitRows_blocks_payloads
    {G : GeneratedOrbitSkeleton}
    (B : MissingSameBlockUnitRows G) :
    Not (GeneratedCompletionPayloads G) := by
  intro h
  exact B.no_rows h.2.2

theorem missingCrossConnectorSqUnitRows_blocks_payloads
    {G : GeneratedOrbitSkeleton}
    (B : MissingCrossConnectorSqUnitRows G) :
    Not (GeneratedCompletionPayloads G) := by
  intro h
  exact B (crossConnectorSqUnitRows_of_payloads h)

theorem missingDisplacementClosureRows_blocks_completionRowData
    {G : GeneratedOrbitSkeleton}
    (B : MissingDisplacementClosureRows G) :
    Not (Nonempty (CompletionRowData G)) := by
  intro h
  cases h with
  | intro D =>
      exact
        missingDisplacementClosureRows_blocks_payloads B
          (payloads_of_completionRowData D)

theorem missingSeparationRows_blocks_completionRowData
    {G : GeneratedOrbitSkeleton}
    (B : MissingSeparationRows G) :
    Not (Nonempty (CompletionRowData G)) := by
  intro h
  cases h with
  | intro D =>
      exact
        missingSeparationRows_blocks_payloads B
          (payloads_of_completionRowData D)

theorem missingSameBlockUnitRows_blocks_completionRowData
    {G : GeneratedOrbitSkeleton}
    (B : MissingSameBlockUnitRows G) :
    Not (Nonempty (CompletionRowData G)) := by
  intro h
  cases h with
  | intro D =>
      exact
        missingSameBlockUnitRows_blocks_payloads B
          (payloads_of_completionRowData D)

theorem missingCrossConnectorSqUnitRows_blocks_completionRowData
    {G : GeneratedOrbitSkeleton}
    (B : MissingCrossConnectorSqUnitRows G) :
    Not (Nonempty (CompletionRowData G)) := by
  intro h
  cases h with
  | intro D =>
      exact B (crossConnectorSqUnitRows_of_completionRowData D)

theorem missingDisplacementClosureRows_blocks_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : MissingDisplacementClosureRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  ClosedOrbitConcreteBranchW31.missingDisplacementClosureRows_blocks_completionRowsGate
    B

theorem missingSeparationRows_blocks_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : MissingSeparationRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  ClosedOrbitConcreteBranchW31.missingSeparationRows_blocks_completionRowsGate
    B

theorem missingSameBlockUnitRows_blocks_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : MissingSameBlockUnitRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  ClosedOrbitConcreteBranchW31.missingSameBlockUnitRows_blocks_completionRowsGate
    B

theorem missingCrossConnectorSqUnitRows_blocks_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : MissingCrossConnectorSqUnitRows G) :
    Not (GeneratedCompletionRowsGate G) := by
  intro h
  exact
    missingCrossConnectorSqUnitRows_blocks_payloads B
      ((completionRowsGate_iff_payloads G).1 h)

theorem sameBlockUnitRows_blocker_of_missingSameBlock
    {G : GeneratedOrbitSkeleton}
    (B : MissingSameBlockUnitRows G) :
    Not (SameBlockAndCrossConnectorSqUnitRows G) := by
  intro h
  exact B.no_rows h.1

/-! ## Root-distance placement payloads -/

abbrev CrossConnectorUnitRows
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2) : Prop :=
  forall (i : Fin k) (u v : LocalVertex),
    CrossBlock.NextConnector u v ->
      _root_.eucDist (point i u) (point (cyclicSucc hk i) v) = 1

abbrev DeformedPlacementPayload
    {k : Nat} (hk : 0 < k)
    (point : Fin k -> LocalVertex -> R2) : Prop :=
  ClosedPlacementSeparationW19.Separated point /\
    ClosedPlacementSameBlockEdgesW19.SameBlockUnitEdges point /\
      CrossConnectorUnitRows hk point

theorem deformedPlacementPayload_of_closedPlacement
    {k : Nat} {hk : 0 < k}
    (P : DeformedPlacement.ClosedPlacement k hk) :
    DeformedPlacementPayload hk P.point :=
  And.intro P.separated
    (And.intro P.same_block_edges_unit
      P.cross_connector_edges_unit)

def closedPlacementOfDeformedPayload
    {k : Nat} {hk : 0 < k}
    {point : Fin k -> LocalVertex -> R2}
    (H : DeformedPlacementPayload hk point) :
    DeformedPlacement.ClosedPlacement k hk where
  point := point
  separated := H.1
  same_block_edges_unit := H.2.1
  cross_connector_edges_unit := H.2.2

theorem exists_closedPlacement_eq_iff_deformedPayload
    {k : Nat} {hk : 0 < k}
    (point : Fin k -> LocalVertex -> R2) :
    (exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = point) <->
        DeformedPlacementPayload hk point := by
  constructor
  case mp =>
    intro h
    cases h with
    | intro P hP =>
        simpa [hP] using deformedPlacementPayload_of_closedPlacement P
  case mpr =>
    intro h
    exact Exists.intro (closedPlacementOfDeformedPayload h) rfl

/-! ## Compact W32 certificate -/

structure CompletionPayloadBlockerCertificate : Prop where
  rowsGateIffPayloads :
    forall G : GeneratedOrbitSkeleton,
      GeneratedCompletionRowsGate G <->
        GeneratedCompletionPayloads G
  noPayloadsIffNoRowsGate :
    forall G : GeneratedOrbitSkeleton,
      GeneratedCompletionPayloadBlocker G <->
        Not (GeneratedCompletionRowsGate G)
  missingDisplacement :
    forall G : GeneratedOrbitSkeleton,
      MissingDisplacementClosureRows G ->
        Not (GeneratedCompletionRowsGate G)
  missingSeparation :
    forall G : GeneratedOrbitSkeleton,
      MissingSeparationRows G ->
        Not (GeneratedCompletionRowsGate G)
  missingSameBlockUnit :
    forall G : GeneratedOrbitSkeleton,
      MissingSameBlockUnitRows G ->
        Not (GeneratedCompletionRowsGate G)
  missingCrossConnector :
    forall G : GeneratedOrbitSkeleton,
      MissingCrossConnectorSqUnitRows G ->
        Not (GeneratedCompletionRowsGate G)

theorem completionPayloadBlockerCertificate :
    CompletionPayloadBlockerCertificate where
  rowsGateIffPayloads := completionRowsGate_iff_payloads
  noPayloadsIffNoRowsGate :=
    ClosedOrbitConcreteBranchW31.generatedCompletionPayloadBlocker_iff_not_gate
  missingDisplacement := by
    intro G B
    exact missingDisplacementClosureRows_blocks_completionRowsGate B
  missingSeparation := by
    intro G B
    exact missingSeparationRows_blocks_completionRowsGate B
  missingSameBlockUnit := by
    intro G B
    exact missingSameBlockUnitRows_blocks_completionRowsGate B
  missingCrossConnector := by
    intro G B
    exact missingCrossConnectorSqUnitRows_blocks_completionRowsGate B

structure ClosedOrbitPayloadInhabitationCertificate : Prop where
  rowDataIffPayloads :
    forall G : GeneratedOrbitSkeleton,
      Nonempty (CompletionRowData G) <->
        GeneratedCompletionPayloads G
  rowsGateIffRowData :
    forall G : GeneratedOrbitSkeleton,
      GeneratedCompletionRowsGate G <->
        Nonempty (CompletionRowData G)
  payloadsFeedSourceRows :
    forall G : GeneratedOrbitSkeleton,
      GeneratedCompletionPayloads G ->
        SquaredOrbitClosureSourceRowsGate
  rowDataFeedsBranch :
    forall G : GeneratedOrbitSkeleton,
      Nonempty (CompletionRowData G) ->
        ClosedOrbitBranchGate
  payloadsFeedBranch :
    forall G : GeneratedOrbitSkeleton,
      GeneratedCompletionPayloads G ->
        ClosedOrbitBranchGate
  payloadsFeedSameAndCross :
    forall G : GeneratedOrbitSkeleton,
      GeneratedCompletionPayloads G ->
        SameBlockAndCrossConnectorSqUnitRows G
  generatedMetricFeedsBranch :
    GeneratedClosureMetricGate -> ClosedOrbitBranchGate
  concreteFamilyFeedsW27Rows :
    ConcreteClosedOrbitFamilyGate -> W27SquaredMetricClosureRowsGate
  w27RowsFeedBranch :
    W27SquaredMetricClosureRowsGate -> ClosedOrbitBranchGate
  blockers :
    CompletionPayloadBlockerCertificate
  deformedPayloadIffClosedPlacement :
    forall {k : Nat} (hk : 0 < k)
      (point : Fin k -> LocalVertex -> R2),
      (exists P : DeformedPlacement.ClosedPlacement k hk,
        P.point = point) <->
          DeformedPlacementPayload hk point

theorem closedOrbitPayloadInhabitationCertificate :
    ClosedOrbitPayloadInhabitationCertificate where
  rowDataIffPayloads := nonempty_completionRowData_iff_payloads
  rowsGateIffRowData := completionRowsGate_iff_completionRowData
  payloadsFeedSourceRows := by
    intro G H
    exact sourceRowsGate_of_completionRowData
      (completionRowDataOfPayloads H)
  rowDataFeedsBranch := by
    intro G H
    exact closedOrbitBranchGate_of_completionRowDataGate H
  payloadsFeedBranch := by
    intro G H
    exact closedOrbitBranchGate_of_payloads H
  payloadsFeedSameAndCross := by
    intro G H
    exact sameBlockAndCrossConnectorSqUnitRows_of_payloads H
  generatedMetricFeedsBranch :=
    closedOrbitBranchGate_of_generatedClosureMetricGate
  concreteFamilyFeedsW27Rows :=
    w27SquaredMetricClosureRowsGate_of_concreteClosedOrbitFamilyGate
  w27RowsFeedBranch :=
    closedOrbitBranchGate_of_w27SquaredMetricClosureRowsGate
  blockers :=
    completionPayloadBlockerCertificate
  deformedPayloadIffClosedPlacement := by
    intro k hk point
    exact exists_closedPlacement_eq_iff_deformedPayload point

end

end ClosedOrbitPayloadInhabitationW32
end PachToth

namespace Verified

open PachToth.ClosedOrbitPayloadInhabitationW32

abbrev PachTothW32ClosedOrbitPayloadInhabitationCertificate : Prop :=
  PachToth.ClosedOrbitPayloadInhabitationW32.ClosedOrbitPayloadInhabitationCertificate

abbrev PachTothW32CompletionPayloadBlockerCertificate : Prop :=
  PachToth.ClosedOrbitPayloadInhabitationW32.CompletionPayloadBlockerCertificate

theorem pachtoth_w32_closedOrbitBranchGate_of_completionRowSource
    (S : PachToth.ClosedOrbitPayloadInhabitationW32.CompletionRowSource) :
    PachToth.ClosedOrbitPayloadInhabitationW32.ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_completionRowSource S

theorem pachtoth_w32_closedOrbitBranchGate_of_w27SquaredMetricClosureRowsGate
    (H :
      PachToth.ClosedOrbitPayloadInhabitationW32.W27SquaredMetricClosureRowsGate) :
    PachToth.ClosedOrbitPayloadInhabitationW32.ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_w27SquaredMetricClosureRowsGate H

theorem pachtoth_w32_completionPayloadBlockerCertificate :
    PachTothW32CompletionPayloadBlockerCertificate :=
  completionPayloadBlockerCertificate

theorem pachtoth_w32_closedOrbitPayloadInhabitationCertificate :
    PachTothW32ClosedOrbitPayloadInhabitationCertificate :=
  closedOrbitPayloadInhabitationCertificate

end Verified
end ErdosProblems1066
