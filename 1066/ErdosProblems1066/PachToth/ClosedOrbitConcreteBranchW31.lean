import ErdosProblems1066.PachToth.ClosedOrbitBranchAssemblyW29
import ErdosProblems1066.PachToth.ClosedOrbitBranchSourceW30

set_option autoImplicit false

/-!
# W31 concrete closed-orbit branch

This file keeps the W30 closed-orbit branch source-facing.  It exposes actual
constructors from completion rows, squared orbit-closure source rows, squared
minimal fields, concrete closed-orbit families, and minimal orbit-closure
fields into the current W29/W30 closed-orbit gate.

It also records the exact blockers for the branch payloads.  No declaration
below routes from an endpoint target back into source data.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ClosedOrbitConcreteBranchW31

noncomputable section

/-! ## Current branch vocabulary -/

abbrev GeneratedOrbitSkeleton : Type :=
  PachTothW29RouteAudit.GeneratedOrbitSkeleton

abbrev GeneratedCompletionRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedCompletionRows G

abbrev GeneratedCompletionRowsGate
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedCompletionRowsGate G

abbrev GeneratedDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedDisplacementClosureRows G

abbrev GeneratedSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedSeparationRows G

abbrev GeneratedSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.GeneratedSameBlockUnitRows G

abbrev MissingDisplacementClosureRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.MissingDisplacementClosureRows G

abbrev MissingSeparationRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.MissingSeparationRows G

abbrev MissingSameBlockUnitRows
    (G : GeneratedOrbitSkeleton) : Prop :=
  PachTothW29RouteAudit.MissingSameBlockUnitRows G

abbrev SquaredOrbitClosureSourceRows : Type :=
  PachTothW29RouteAudit.SquaredOrbitClosureSourceRows

abbrev SquaredOrbitClosureSourceRowsGate : Prop :=
  PachTothW29RouteAudit.SquaredOrbitClosureSourceRowsGate

abbrev SquaredMinimalFieldsWithOrbitClosure : Type :=
  PachTothW29RouteAudit.SquaredMinimalFieldsWithOrbitClosure

abbrev SquaredOrbitClosureGate : Prop :=
  PachTothW29RouteAudit.SquaredOrbitClosureGate

abbrev ConcreteClosedOrbitFamily : Type :=
  PachTothW29RouteAudit.ConcreteClosedOrbitFamily

abbrev ConcreteClosedOrbitFamilyGate : Prop :=
  PachTothW29RouteAudit.ConcreteClosedOrbitFamilyGate

abbrev MinimalFieldsWithOrbitClosure : Type :=
  PachTothW29RouteAudit.MinimalFieldsWithOrbitClosure

abbrev MinimalFieldsWithOrbitClosureGate : Prop :=
  PachTothW29RouteAudit.MinimalFieldsWithOrbitClosureGate

abbrev ClosedOrbitBranchGate : Prop :=
  PachTothW29RouteAudit.ClosedOrbitBranchGate

abbrev GeneratedClosureMetricRowPackage : Type :=
  PachTothW29RouteAudit.GeneratedClosureMetricRowPackage

abbrev GeneratedClosureMetricGate : Prop :=
  PachTothW29RouteAudit.GeneratedClosureMetricGate

/-! ## Concrete constructors into the branch -/

def completionRowsOfPayloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    GeneratedCompletionRows G where
  closure := closure
  separated_sq := separated_sq
  same_block_edges_sq_unit := same_block_edges_sq_unit

def sourceRowsOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : GeneratedCompletionRows G) :
    SquaredOrbitClosureSourceRows :=
  PachTothW29RouteAudit.squaredOrbitClosureSourceRowsOfCompletionRows G R

def sourceRowsOfPayloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    SquaredOrbitClosureSourceRows :=
  sourceRowsOfCompletionRows G
    (completionRowsOfPayloads
      closure separated_sq same_block_edges_sq_unit)

def squaredMinimalFieldsWithOrbitClosureOfSourceRows
    (S : SquaredOrbitClosureSourceRows) :
    SquaredMinimalFieldsWithOrbitClosure :=
  S.toSquaredMinimalFieldsWithOrbitClosure

def concreteClosedOrbitFamilyOfSourceRows
    (S : SquaredOrbitClosureSourceRows) :
    ConcreteClosedOrbitFamily :=
  S.toConcreteClosedOrbitFamily

def squaredMinimalFieldsWithOrbitClosureOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : GeneratedCompletionRows G) :
    SquaredMinimalFieldsWithOrbitClosure :=
  squaredMinimalFieldsWithOrbitClosureOfSourceRows
    (sourceRowsOfCompletionRows G R)

def concreteClosedOrbitFamilyOfCompletionRows
    (G : GeneratedOrbitSkeleton)
    (R : GeneratedCompletionRows G) :
    ConcreteClosedOrbitFamily :=
  concreteClosedOrbitFamilyOfSourceRows
    (sourceRowsOfCompletionRows G R)

def squaredMinimalFieldsWithOrbitClosureOfPayloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    SquaredMinimalFieldsWithOrbitClosure :=
  squaredMinimalFieldsWithOrbitClosureOfSourceRows
    (sourceRowsOfPayloads
      closure separated_sq same_block_edges_sq_unit)

def concreteClosedOrbitFamilyOfPayloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    ConcreteClosedOrbitFamily :=
  concreteClosedOrbitFamilyOfSourceRows
    (sourceRowsOfPayloads
      closure separated_sq same_block_edges_sq_unit)

def sourceRowsOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SquaredOrbitClosureSourceRows :=
  SquaredOrbitClosureCompletionRowsW29.sourceRowsOfGeneratedClosureMetricRowPackage
    P

def squaredMinimalFieldsWithOrbitClosureOfGeneratedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SquaredMinimalFieldsWithOrbitClosure :=
  squaredMinimalFieldsWithOrbitClosureOfSourceRows
    (sourceRowsOfGeneratedClosureMetricRowPackage P)

theorem generatedCompletionRowsGate_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (R : GeneratedCompletionRows G) :
    GeneratedCompletionRowsGate G :=
  Nonempty.intro R

theorem generatedCompletionRowsGate_of_payloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    GeneratedCompletionRowsGate G :=
  Nonempty.intro
    (completionRowsOfPayloads
      closure separated_sq same_block_edges_sq_unit)

theorem sourceRowsGate_of_sourceRows
    (S : SquaredOrbitClosureSourceRows) :
    SquaredOrbitClosureSourceRowsGate :=
  Nonempty.intro S

theorem sourceRowsGate_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (R : GeneratedCompletionRows G) :
    SquaredOrbitClosureSourceRowsGate :=
  sourceRowsGate_of_sourceRows (sourceRowsOfCompletionRows G R)

theorem sourceRowsGate_of_payloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    SquaredOrbitClosureSourceRowsGate :=
  sourceRowsGate_of_sourceRows
    (sourceRowsOfPayloads
      closure separated_sq same_block_edges_sq_unit)

theorem squaredOrbitClosureGate_of_squaredMinimalFieldsWithOrbitClosure
    (S : SquaredMinimalFieldsWithOrbitClosure) :
    SquaredOrbitClosureGate :=
  Nonempty.intro S

theorem squaredOrbitClosureGate_of_sourceRows
    (S : SquaredOrbitClosureSourceRows) :
    SquaredOrbitClosureGate :=
  squaredOrbitClosureGate_of_squaredMinimalFieldsWithOrbitClosure
    (squaredMinimalFieldsWithOrbitClosureOfSourceRows S)

theorem squaredOrbitClosureGate_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (R : GeneratedCompletionRows G) :
    SquaredOrbitClosureGate :=
  squaredOrbitClosureGate_of_sourceRows
    (sourceRowsOfCompletionRows G R)

theorem squaredOrbitClosureGate_of_payloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    SquaredOrbitClosureGate :=
  squaredOrbitClosureGate_of_sourceRows
    (sourceRowsOfPayloads
      closure separated_sq same_block_edges_sq_unit)

theorem squaredOrbitClosureGate_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    SquaredOrbitClosureGate :=
  squaredOrbitClosureGate_of_sourceRows
    (sourceRowsOfGeneratedClosureMetricRowPackage P)

theorem closedOrbitBranchGate_of_squaredOrbitClosureGate
    (H : SquaredOrbitClosureGate) :
    ClosedOrbitBranchGate :=
  Or.inl H

theorem closedOrbitBranchGate_of_squaredMinimalFieldsWithOrbitClosure
    (S : SquaredMinimalFieldsWithOrbitClosure) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_squaredOrbitClosureGate
    (squaredOrbitClosureGate_of_squaredMinimalFieldsWithOrbitClosure S)

theorem closedOrbitBranchGate_of_sourceRows
    (S : SquaredOrbitClosureSourceRows) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_squaredOrbitClosureGate
    (squaredOrbitClosureGate_of_sourceRows S)

theorem closedOrbitBranchGate_of_sourceRowsGate
    (H : SquaredOrbitClosureSourceRowsGate) :
    ClosedOrbitBranchGate := by
  cases H with
  | intro S =>
      exact closedOrbitBranchGate_of_sourceRows S

theorem closedOrbitBranchGate_of_completionRows
    {G : GeneratedOrbitSkeleton}
    (R : GeneratedCompletionRows G) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_sourceRows
    (sourceRowsOfCompletionRows G R)

theorem closedOrbitBranchGate_of_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (H : GeneratedCompletionRowsGate G) :
    ClosedOrbitBranchGate := by
  cases H with
  | intro R =>
      exact closedOrbitBranchGate_of_completionRows R

theorem closedOrbitBranchGate_of_payloads
    {G : GeneratedOrbitSkeleton}
    (closure : GeneratedDisplacementClosureRows G)
    (separated_sq : GeneratedSeparationRows G)
    (same_block_edges_sq_unit : GeneratedSameBlockUnitRows G) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_sourceRows
    (sourceRowsOfPayloads
      closure separated_sq same_block_edges_sq_unit)

theorem closedOrbitBranchGate_of_generatedClosureMetricRowPackage
    (P : GeneratedClosureMetricRowPackage) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_squaredOrbitClosureGate
    (squaredOrbitClosureGate_of_generatedClosureMetricRowPackage P)

theorem closedOrbitBranchGate_of_generatedClosureMetricGate
    (H : GeneratedClosureMetricGate) :
    ClosedOrbitBranchGate := by
  cases H with
  | intro P =>
      exact closedOrbitBranchGate_of_generatedClosureMetricRowPackage P

theorem closedOrbitBranchGate_of_concreteClosedOrbitFamilyGate
    (H : ConcreteClosedOrbitFamilyGate) :
    ClosedOrbitBranchGate :=
  Or.inr (Or.inl H)

theorem closedOrbitBranchGate_of_concreteClosedOrbitFamily
    (F : ConcreteClosedOrbitFamily) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_concreteClosedOrbitFamilyGate
    (Nonempty.intro F)

theorem closedOrbitBranchGate_of_minimalFieldsWithOrbitClosureGate
    (H : MinimalFieldsWithOrbitClosureGate) :
    ClosedOrbitBranchGate :=
  Or.inr (Or.inr H)

theorem closedOrbitBranchGate_of_minimalFieldsWithOrbitClosure
    (M : MinimalFieldsWithOrbitClosure) :
    ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_minimalFieldsWithOrbitClosureGate
    (Nonempty.intro M)

/-! ## Exact blockers for missing payloads -/

abbrev GeneratedCompletionPayloads
    (G : GeneratedOrbitSkeleton) : Prop :=
  GeneratedDisplacementClosureRows G /\
    GeneratedSeparationRows G /\
      GeneratedSameBlockUnitRows G

abbrev GeneratedCompletionPayloadBlocker
    (G : GeneratedOrbitSkeleton) : Prop :=
  Not (GeneratedCompletionPayloads G)

theorem generatedCompletionRowsGate_iff_payloads
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionRowsGate G <-> GeneratedCompletionPayloads G :=
  PachTothW29RouteAudit.generatedCompletionRowsGate_iff_source_rows G

theorem generatedCompletionPayloadBlocker_iff_not_gate
    (G : GeneratedOrbitSkeleton) :
    GeneratedCompletionPayloadBlocker G <->
      Not (GeneratedCompletionRowsGate G) := by
  constructor
  case mp =>
    intro hPayload hGate
    exact hPayload ((generatedCompletionRowsGate_iff_payloads G).1 hGate)
  case mpr =>
    intro hGate hPayload
    exact hGate ((generatedCompletionRowsGate_iff_payloads G).2 hPayload)

theorem missingDisplacementClosureRows_blocks_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : MissingDisplacementClosureRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  PachTothW29RouteAudit.missingDisplacementClosureRows_blocks_generatedCompletionRows
    B

theorem missingSeparationRows_blocks_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : MissingSeparationRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  PachTothW29RouteAudit.missingSeparationRows_blocks_generatedCompletionRows
    B

theorem missingSameBlockUnitRows_blocks_completionRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : MissingSameBlockUnitRows G) :
    Not (GeneratedCompletionRowsGate G) :=
  PachTothW29RouteAudit.missingSameBlockUnitRows_blocks_generatedCompletionRows
    B

theorem no_sourceRowsGate_of_no_squaredOrbitClosureGate
    (B : Not SquaredOrbitClosureGate) :
    Not SquaredOrbitClosureSourceRowsGate := by
  intro hSource
  cases hSource with
  | intro S =>
      exact B (squaredOrbitClosureGate_of_sourceRows S)

theorem no_completionRowsGate_of_no_sourceRowsGate
    {G : GeneratedOrbitSkeleton}
    (B : Not SquaredOrbitClosureSourceRowsGate) :
    Not (GeneratedCompletionRowsGate G) := by
  intro hRows
  cases hRows with
  | intro R =>
      exact B (sourceRowsGate_of_completionRows R)

structure ClosedOrbitBranchPayloadBlockers : Prop where
  no_squared : Not SquaredOrbitClosureGate
  no_concrete : Not ConcreteClosedOrbitFamilyGate
  no_minimal : Not MinimalFieldsWithOrbitClosureGate

theorem not_closedOrbitBranchGate_of_payloadBlockers
    (B : ClosedOrbitBranchPayloadBlockers) :
    Not ClosedOrbitBranchGate := by
  intro hBranch
  cases hBranch with
  | inl hSquared =>
      exact B.no_squared hSquared
  | inr hRest =>
      cases hRest with
      | inl hConcrete =>
          exact B.no_concrete hConcrete
      | inr hMinimal =>
          exact B.no_minimal hMinimal

theorem payloadBlockers_of_not_closedOrbitBranchGate
    (B : Not ClosedOrbitBranchGate) :
    ClosedOrbitBranchPayloadBlockers where
  no_squared := fun hSquared => B (Or.inl hSquared)
  no_concrete := fun hConcrete => B (Or.inr (Or.inl hConcrete))
  no_minimal := fun hMinimal => B (Or.inr (Or.inr hMinimal))

theorem not_closedOrbitBranchGate_iff_payloadBlockers :
    Not ClosedOrbitBranchGate <-> ClosedOrbitBranchPayloadBlockers := by
  constructor
  case mp =>
    exact payloadBlockers_of_not_closedOrbitBranchGate
  case mpr =>
    exact not_closedOrbitBranchGate_of_payloadBlockers

theorem closedOrbitBranchGate_iff_payloadAvailable :
    ClosedOrbitBranchGate <->
      SquaredOrbitClosureGate \/
        ConcreteClosedOrbitFamilyGate \/
          MinimalFieldsWithOrbitClosureGate :=
  Iff.rfl

theorem branchReductionSummary :
    (forall G : GeneratedOrbitSkeleton,
        GeneratedCompletionRowsGate G <-> GeneratedCompletionPayloads G) /\
      (forall G : GeneratedOrbitSkeleton,
        GeneratedCompletionPayloadBlocker G <->
          Not (GeneratedCompletionRowsGate G)) /\
        (SquaredOrbitClosureSourceRows -> ClosedOrbitBranchGate) /\
          (SquaredMinimalFieldsWithOrbitClosure -> ClosedOrbitBranchGate) /\
            (MinimalFieldsWithOrbitClosure -> ClosedOrbitBranchGate) /\
              (ConcreteClosedOrbitFamily -> ClosedOrbitBranchGate) /\
                (Not ClosedOrbitBranchGate <->
                  ClosedOrbitBranchPayloadBlockers) := by
  exact
    And.intro generatedCompletionRowsGate_iff_payloads
      (And.intro generatedCompletionPayloadBlocker_iff_not_gate
        (And.intro closedOrbitBranchGate_of_sourceRows
          (And.intro closedOrbitBranchGate_of_squaredMinimalFieldsWithOrbitClosure
            (And.intro closedOrbitBranchGate_of_minimalFieldsWithOrbitClosure
              (And.intro closedOrbitBranchGate_of_concreteClosedOrbitFamily
                not_closedOrbitBranchGate_iff_payloadBlockers)))))

end

end ClosedOrbitConcreteBranchW31
end PachToth

namespace Verified

open PachToth.ClosedOrbitConcreteBranchW31

abbrev PachTothW31ClosedOrbitBranchGate : Prop :=
  PachToth.ClosedOrbitConcreteBranchW31.ClosedOrbitBranchGate

abbrev PachTothW31ClosedOrbitBranchPayloadBlockers : Prop :=
  PachToth.ClosedOrbitConcreteBranchW31.ClosedOrbitBranchPayloadBlockers

theorem pachtoth_w31_closedOrbitBranchGate_of_sourceRows
    (S : PachToth.ClosedOrbitConcreteBranchW31.SquaredOrbitClosureSourceRows) :
    PachTothW31ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_sourceRows S

theorem pachtoth_w31_closedOrbitBranchGate_of_squaredMinimalFields
    (S :
      PachToth.ClosedOrbitConcreteBranchW31.SquaredMinimalFieldsWithOrbitClosure) :
    PachTothW31ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_squaredMinimalFieldsWithOrbitClosure S

theorem pachtoth_w31_closedOrbitBranchGate_of_minimalFields
    (M :
      PachToth.ClosedOrbitConcreteBranchW31.MinimalFieldsWithOrbitClosure) :
    PachTothW31ClosedOrbitBranchGate :=
  closedOrbitBranchGate_of_minimalFieldsWithOrbitClosure M

theorem pachtoth_w31_not_closedOrbitBranchGate_iff_payloadBlockers :
    Not PachTothW31ClosedOrbitBranchGate <->
      PachTothW31ClosedOrbitBranchPayloadBlockers :=
  not_closedOrbitBranchGate_iff_payloadBlockers

end Verified
end ErdosProblems1066
