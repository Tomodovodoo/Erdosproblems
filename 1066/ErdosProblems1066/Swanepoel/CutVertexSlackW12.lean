import ErdosProblems1066.Swanepoel.CutVertexSideCardFromMinimality

set_option autoImplicit false

/-!
# W12 cut-vertex slack blocker ledger

This file records the honest W12 status of the cut-vertex slack route.

The requested side-cardinality and deletion-slack targets do not follow from
the current minimality interface alone: existing lemmas show that any supplied
cut partition makes the concrete minimality-selected side-card bound
contradict the ambient uncleared assumption.  What remains is therefore an
extraction of `NoCutVertex C`, or additional graph data producing genuine
per-partition pay-for-cut witnesses.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexSlackW12

open CutVertexInterface
open CutVertexSlackFromDeletion

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

/-- Target-shaped conditional side-card theorem: once no supplied cut
partition exists, the universal side-card fact is vacuous. -/
theorem cutVertexDeletionSideCardExactFact_of_minimalFailure_of_noCutVertex
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    CutVertexDeletionSideCardExactFact hmin := by
  intro P
  exact False.elim (hno (Nonempty.intro P))

/-- In a minimal failure, the side-cardinality target is equivalent to no
supplied cut-vertex partition.  The forward direction is already the checked
contradiction route; the reverse direction is vacuous. -/
theorem cutVertexDeletionSideCardExactFact_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <-> NoCutVertex C := by
  constructor
  case mp =>
    exact
      CutVertexSlackFromDeletion.noCutVertex_of_minimalFailure_sideCardExactFact
        hmin
  case mpr =>
    exact cutVertexDeletionSideCardExactFact_of_minimalFailure_of_noCutVertex
      hmin

/-- Target-shaped conditional deletion-slack theorem: after no-cut extraction,
the deletion slack fact is vacuous. -/
theorem cutVertexDeletionSlackFact_of_minimalFailure_of_noCutVertex
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    CutVertexDeletionSlackFact C := by
  intro P
  exact False.elim (hno (Nonempty.intro P))

/-- In a minimal failure, deletion slack is equivalent to no supplied
cut-vertex partition. -/
theorem cutVertexDeletionSlackFact_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSlackFact C <-> NoCutVertex C := by
  constructor
  case mp =>
    exact
      CutVertexSlackFromDeletion.noCutVertex_of_minimalFailure_deletionSlackFact_direct
        hmin
  case mpr =>
    exact cutVertexDeletionSlackFact_of_minimalFailure_of_noCutVertex hmin

/-- Target-shaped conditional final remaining-slack theorem: after no-cut
extraction, the data-valued final slack package is vacuous. -/
def remainingNoCutSlackFact_of_minimalFailure_of_noCutVertex
    (_hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    CutVertexFinal.RemainingNoCutSlackFact C where
  gluingData := fun P => False.elim (hno (Nonempty.intro P))

/-- In a minimal failure, the final remaining-slack package is equivalent to
no supplied cut-vertex partition. -/
theorem remainingNoCutSlackFact_nonempty_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Nonempty (CutVertexFinal.RemainingNoCutSlackFact C) <-> NoCutVertex C := by
  constructor
  case mp =>
    intro hslack
    cases hslack with
    | intro H =>
        exact
          ({ minimalFailure := hmin
             cutVertexSlack := H } :
              CutVertexClosure.MinimalFailureCutVertexSlackData C).noCutVertex
  case mpr =>
    intro hno
    exact Nonempty.intro
      (remainingNoCutSlackFact_of_minimalFailure_of_noCutVertex hmin hno)

/-- The side-cardinality target and final remaining-slack target have the
same remaining blocker under minimality. -/
theorem cutVertexDeletionSideCardExactFact_iff_remainingNoCutSlackFact_nonempty
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <->
      Nonempty (CutVertexFinal.RemainingNoCutSlackFact C) :=
  (cutVertexDeletionSideCardExactFact_iff_noCutVertex_of_minimalFailure
    hmin).trans
    (remainingNoCutSlackFact_nonempty_iff_noCutVertex_of_minimalFailure
      hmin).symm

end

end CutVertexSlackW12
end Swanepoel
end ErdosProblems1066
