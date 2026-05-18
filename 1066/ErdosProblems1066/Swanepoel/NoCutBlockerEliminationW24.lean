import ErdosProblems1066.Swanepoel.NoCutSourceConcreteW23
import ErdosProblems1066.Swanepoel.NoCutSourceInhabitationW21
import ErdosProblems1066.Swanepoel.NoCutMinimalitySourceInhabitationW22
import ErdosProblems1066.Swanepoel.RemainingObligationLedgerW20
import ErdosProblems1066.Swanepoel.PayForCutProducerFamilyW20
import ErdosProblems1066.Swanepoel.SwanepoelSourcePackageW20
import ErdosProblems1066.Swanepoel.NoCutFromMinimalityW16
import ErdosProblems1066.Swanepoel.NoCutMinimalityProofW15
import ErdosProblems1066.Swanepoel.NoCutMinimalityClosureW19
import ErdosProblems1066.Swanepoel.CutVertexInterface
import ErdosProblems1066.Swanepoel.CutVertexFinal
import ErdosProblems1066.Swanepoel.CutVertexSlackFromDeletion
import ErdosProblems1066.Swanepoel.CutVertexSideCardFromMinimality
import ErdosProblems1066.Swanepoel.MinimalGraphFacts
import ErdosProblems1066.Swanepoel.CounterexamplePipeline

set_option autoImplicit false

/-!
# W24 no-cut blocker elimination facade

This file records the strongest current elimination statement for
`NoCutSourceConcreteW23.MinimalCutVertexBlocker`.

No unconditional cut-vertex contradiction is available from the imported
facts.  The checked result is sharper than a new conditional source: the
blocker is absent exactly when every cut-vertex partition of every minimal
cleared failure is contradictory.  The same condition is equivalent to the
W19/W20/W22 no-cut source, the final remaining no-cut slack family, and the
deletion-side slack/cardinality interfaces.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutBlockerEliminationW24

open CutVertexInterface
open MinimalGraphFacts

noncomputable section

abbrev MinimalCutVertexBlocker : Type :=
  NoCutSourceConcreteW23.MinimalCutVertexBlocker

abbrev MinimalCutVertexBlockerExists : Prop :=
  Nonempty MinimalCutVertexBlocker

abbrev SmallestMissingMinimalityNoCutTheorem : Prop :=
  NoCutSourceConcreteW23.SmallestMissingMinimalityNoCutTheorem

abbrev LedgerPayForCutSource : Type 1 :=
  NoCutSourceConcreteW23.LedgerPayForCutSource

abbrev W20PayForCutSource : Type 1 :=
  NoCutSourceConcreteW23.W20PayForCutSource

/-- Uniform no-cut over minimal cleared failures. -/
abbrev MinimalFailureNoCutVertexFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> NoCutVertex C

/-- The exact partition-level contradiction still missing for an unconditional
blocker elimination. -/
abbrev MinimalFailureCutVertexContradictionFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C -> CutVertexPartition C -> False

/-- Final API spelling of the same no-cut content. -/
abbrev MinimalFailureRemainingSlackFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C ->
      Nonempty (CutVertexFinal.RemainingNoCutSlackFact C)

/-- Deletion/slack API spelling of the same no-cut content. -/
abbrev MinimalFailureDeletionSlackFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n),
    IsMinimalClearedFailure C ->
      CutVertexSlackFromDeletion.CutVertexDeletionSlackFact C

/-- The missing arithmetic/cardinality statement for the side witnesses chosen
from minimality. -/
abbrev MinimalFailureMissingArithmeticFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      CutVertexSlackFromDeletion.CutVertexDeletionMissingArithmetic hmin

/-- Wrapper-free side-cardinality spelling of the same partition contradiction
boundary. -/
abbrev MinimalFailureSideCardExactFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      CutVertexSlackFromDeletion.CutVertexDeletionSideCardExactFact hmin

variable {n : Nat} {C : _root_.UDConfig n}

/-- A blocker is exactly a minimal cleared failure with a supplied cut-vertex
partition. -/
theorem blocker_exists_iff_exists_minimalFailure_cutPartition :
    MinimalCutVertexBlockerExists <->
      Exists fun n : Nat =>
        Exists fun C : _root_.UDConfig n =>
          IsMinimalClearedFailure C /\ Nonempty (CutVertexPartition C) := by
  constructor
  case mp =>
    rintro ⟨B⟩
    exact ⟨B.n, B.C, B.minimal, Nonempty.intro B.cut⟩
  case mpr =>
    rintro ⟨n, C, hmin, hcut⟩
    rcases hcut with ⟨P⟩
    exact
      Nonempty.intro
        (NoCutSourceConcreteW23.MinimalCutVertexBlocker.of_cutVertexPartition
          (C := C) hmin P)

/-- Classical complement form: blockers exist exactly when some minimal
failure is not known to be no-cut. -/
theorem blocker_exists_iff_exists_minimalFailure_not_noCutVertex :
    MinimalCutVertexBlockerExists <->
      Exists fun n : Nat =>
        Exists fun C : _root_.UDConfig n =>
          IsMinimalClearedFailure C /\ Not (NoCutVertex C) := by
  classical
  constructor
  case mp =>
    rintro ⟨B⟩
    exact ⟨B.n, B.C, B.minimal, fun hno => hno (Nonempty.intro B.cut)⟩
  case mpr =>
    rintro ⟨n, C, hmin, hnotNoCut⟩
    have hcut : Nonempty (CutVertexPartition C) := by
      exact Classical.not_not.mp (by simpa [NoCutVertex] using hnotNoCut)
    exact
      blocker_exists_iff_exists_minimalFailure_cutPartition.2
        ⟨n, C, hmin, hcut⟩

/-- The W23 source boundary, restated with the W24 blocker alias. -/
theorem not_blocker_iff_smallestMissing :
    Not MinimalCutVertexBlockerExists <->
      SmallestMissingMinimalityNoCutTheorem :=
  NoCutSourceConcreteW23.smallestMissing_iff_not_blocker.symm

theorem blocker_iff_not_smallestMissing :
    MinimalCutVertexBlockerExists <->
      Not SmallestMissingMinimalityNoCutTheorem :=
  NoCutSourceConcreteW23.not_smallestMissing_iff_blocker.symm

/-- Current strongest elimination theorem: removing the concrete blocker is
exactly proving uniform no-cut for minimal cleared failures. -/
theorem not_blocker_iff_noCutVertexFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro hNoBlocker n C hmin
    exact NoCutSourceConcreteW23.noCutVertex_of_not_blocker
      (C := C) hNoBlocker hmin
  case mpr =>
    intro H hBlocker
    rcases hBlocker with ⟨B⟩
    exact H B.C B.minimal (Nonempty.intro B.cut)

/-- Equivalent partition-level form exposing the exact remaining
cut-vertex contradiction. -/
theorem noCutVertexFamily_iff_cutVertexContradictionFamily :
    MinimalFailureNoCutVertexFamily <->
      MinimalFailureCutVertexContradictionFamily := by
  constructor
  case mp =>
    intro H n C hmin P
    exact H C hmin (Nonempty.intro P)
  case mpr =>
    intro H n C hmin hcut
    rcases hcut with ⟨P⟩
    exact H C hmin P

/-- The blocker is eliminated exactly by the missing partition contradiction:
for each minimal cleared failure, every supplied cut partition must be false. -/
theorem not_blocker_iff_cutVertexContradictionFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureCutVertexContradictionFamily :=
  not_blocker_iff_noCutVertexFamily.trans
    noCutVertexFamily_iff_cutVertexContradictionFamily

theorem not_blocker_of_cutVertexContradictionFamily
    (H : MinimalFailureCutVertexContradictionFamily) :
    Not MinimalCutVertexBlockerExists :=
  not_blocker_iff_cutVertexContradictionFamily.2 H

theorem blocker_false_of_cutVertexContradictionFamily
    (H : MinimalFailureCutVertexContradictionFamily)
    (B : MinimalCutVertexBlocker) :
    False :=
  H B.C B.minimal B.cut

/-- A full minimal-cleared-failure eliminator is still more than enough to
remove blockers. -/
theorem not_blocker_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    Not MinimalCutVertexBlockerExists :=
  NoCutSourceConcreteW23.not_blocker_of_minimalClearedFailureEliminator hElim

theorem cutVertexContradictionFamily_of_minimalClearedFailureEliminator
    (hElim : MinimalClearedFailureEliminator) :
    MinimalFailureCutVertexContradictionFamily := by
  intro n C hmin _P
  exact hElim C hmin

/-- The final remaining-slack family is equivalent to blocker elimination. -/
theorem remainingSlackFamily_iff_noCutVertexFamily :
    MinimalFailureRemainingSlackFamily <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro H n C hmin
    exact
      (CutVertexFinal.remainingNoCutSlackFact_nonempty_iff_noCutVertex_of_minimalFailure
        (C := C) hmin).1 (H C hmin)
  case mpr =>
    intro H n C hmin
    exact
      (CutVertexFinal.remainingNoCutSlackFact_nonempty_iff_noCutVertex_of_minimalFailure
        (C := C) hmin).2 (H C hmin)

theorem not_blocker_iff_remainingSlackFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureRemainingSlackFamily :=
  not_blocker_iff_noCutVertexFamily.trans
    remainingSlackFamily_iff_noCutVertexFamily.symm

theorem not_blocker_of_remainingSlackFamily
    (H : MinimalFailureRemainingSlackFamily) :
    Not MinimalCutVertexBlockerExists :=
  not_blocker_iff_remainingSlackFamily.2 H

/-- The Prop-valued deletion slack family has the same content as no-cut, in
minimal cleared failures. -/
theorem deletionSlackFamily_iff_noCutVertexFamily :
    MinimalFailureDeletionSlackFamily <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro H n C hmin
    exact
      (CutVertexSlackFromDeletion.deletionSlackFact_iff_noCutVertex_of_minimalFailure
        (C := C) hmin).1 (H C hmin)
  case mpr =>
    intro H n C hmin
    exact
      (CutVertexSlackFromDeletion.deletionSlackFact_iff_noCutVertex_of_minimalFailure
        (C := C) hmin).2 (H C hmin)

theorem not_blocker_iff_deletionSlackFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureDeletionSlackFamily :=
  not_blocker_iff_noCutVertexFamily.trans
    deletionSlackFamily_iff_noCutVertexFamily.symm

theorem not_blocker_of_deletionSlackFamily
    (H : MinimalFailureDeletionSlackFamily) :
    Not MinimalCutVertexBlockerExists :=
  not_blocker_iff_deletionSlackFamily.2 H

/-- If there is no supplied cut partition, the missing arithmetic is vacuous. -/
theorem missingArithmetic_of_noCutVertex
    (hmin : IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    CutVertexSlackFromDeletion.CutVertexDeletionMissingArithmetic hmin := by
  intro P
  exact False.elim (hno (Nonempty.intro P))

theorem missingArithmetic_iff_noCutVertex_of_minimalFailure
    (hmin : IsMinimalClearedFailure C) :
    CutVertexSlackFromDeletion.CutVertexDeletionMissingArithmetic hmin <->
      NoCutVertex C := by
  constructor
  case mp =>
    exact CutVertexSlackFromDeletion.noCutVertex_of_minimalFailure_missingArithmetic_core
      (C := C) hmin
  case mpr =>
    exact missingArithmetic_of_noCutVertex (C := C) hmin

theorem missingArithmeticFamily_iff_noCutVertexFamily :
    MinimalFailureMissingArithmeticFamily <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro H n C hmin
    exact (missingArithmetic_iff_noCutVertex_of_minimalFailure
      (C := C) hmin).1 (H C hmin)
  case mpr =>
    intro H n C hmin
    exact (missingArithmetic_iff_noCutVertex_of_minimalFailure
      (C := C) hmin).2 (H C hmin)

theorem not_blocker_iff_missingArithmeticFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureMissingArithmeticFamily :=
  not_blocker_iff_noCutVertexFamily.trans
    missingArithmeticFamily_iff_noCutVertexFamily.symm

/-- If there is no supplied cut partition, the side-cardinality fact is also
vacuous. -/
theorem sideCardExactFact_of_noCutVertex
    (hmin : IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    CutVertexSlackFromDeletion.CutVertexDeletionSideCardExactFact hmin := by
  intro P
  exact False.elim (hno (Nonempty.intro P))

theorem sideCardExactFact_iff_noCutVertex_of_minimalFailure
    (hmin : IsMinimalClearedFailure C) :
    CutVertexSlackFromDeletion.CutVertexDeletionSideCardExactFact hmin <->
      NoCutVertex C := by
  constructor
  case mp =>
    exact CutVertexSlackFromDeletion.noCutVertex_of_minimalFailure_sideCardExactFact
      (C := C) hmin
  case mpr =>
    exact sideCardExactFact_of_noCutVertex (C := C) hmin

theorem sideCardExactFamily_iff_noCutVertexFamily :
    MinimalFailureSideCardExactFamily <->
      MinimalFailureNoCutVertexFamily := by
  constructor
  case mp =>
    intro H n C hmin
    exact (sideCardExactFact_iff_noCutVertex_of_minimalFailure
      (C := C) hmin).1 (H C hmin)
  case mpr =>
    intro H n C hmin
    exact (sideCardExactFact_iff_noCutVertex_of_minimalFailure
      (C := C) hmin).2 (H C hmin)

theorem not_blocker_iff_sideCardExactFamily :
    Not MinimalCutVertexBlockerExists <->
      MinimalFailureSideCardExactFamily :=
  not_blocker_iff_noCutVertexFamily.trans
    sideCardExactFamily_iff_noCutVertexFamily.symm

/-- W20 producer nonemptiness is equivalent to blocker elimination. -/
theorem nonempty_w20PayForCutSource_iff_not_blocker :
    Nonempty W20PayForCutSource <->
      Not MinimalCutVertexBlockerExists :=
  NoCutSourceConcreteW23.nonempty_w20PayForCutSource_iff_not_blocker

theorem nonempty_w20PayForCutSource_iff_cutVertexContradictionFamily :
    Nonempty W20PayForCutSource <->
      MinimalFailureCutVertexContradictionFamily :=
  nonempty_w20PayForCutSource_iff_not_blocker.trans
    not_blocker_iff_cutVertexContradictionFamily

/-- Ledger producer nonemptiness is equivalent to blocker elimination. -/
theorem nonempty_ledgerPayForCutSource_iff_not_blocker :
    Nonempty LedgerPayForCutSource <->
      Not MinimalCutVertexBlockerExists :=
  NoCutSourceConcreteW23.nonempty_ledgerPayForCutSource_iff_not_blocker

theorem nonempty_ledgerPayForCutSource_iff_cutVertexContradictionFamily :
    Nonempty LedgerPayForCutSource <->
      MinimalFailureCutVertexContradictionFamily :=
  nonempty_ledgerPayForCutSource_iff_not_blocker.trans
    not_blocker_iff_cutVertexContradictionFamily

/-- Negative producer form: failure to inhabit the W20 no-cut/pay-for-cut
source is exactly the concrete blocker. -/
theorem not_nonempty_w20PayForCutSource_iff_blocker :
    Not (Nonempty W20PayForCutSource) <->
      MinimalCutVertexBlockerExists :=
  NoCutSourceConcreteW23.not_nonempty_w20PayForCutSource_iff_blocker

theorem not_nonempty_ledgerPayForCutSource_iff_blocker :
    Not (Nonempty LedgerPayForCutSource) <->
      MinimalCutVertexBlockerExists :=
  NoCutSourceConcreteW23.not_nonempty_ledgerPayForCutSource_iff_blocker

/-- Exact statement requested by the W24 task: an unconditional proof of this
left-hand side is the same as proving the partition contradiction family on
the right. -/
theorem not_nonempty_minimalCutVertexBlocker_iff_partitionContradiction :
    Not (Nonempty MinimalCutVertexBlocker) <->
      MinimalFailureCutVertexContradictionFamily :=
  not_blocker_iff_cutVertexContradictionFamily

end

end NoCutBlockerEliminationW24
end Swanepoel
end ErdosProblems1066
