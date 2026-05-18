import ErdosProblems1066.Swanepoel.CutVertexPayForCutArithmetic

set_option autoImplicit false

/-!
# Cut-vertex side cardinality from minimality

Minimality supplies cleared witnesses on the two proper sides of a supplied
cut-vertex partition.  The existing deletion/minimality API does not determine
that the particular witnesses chosen by `sideSurplusData_of_minimalFailure`
have enough combined cardinality to pay for the deleted cut vertex.

This file therefore isolates that remaining graph/cardinality input in its
most direct form and routes it through the existing pay-for-cut arithmetic.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexSlackFromDeletion

open CounterexamplePipeline
open CutVertexInterface

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

/-- The exact cardinal fact still needed for the concrete side witnesses
chosen from minimality: for every cut-vertex partition, their combined size
already satisfies the ambient `8 / 31` bound. -/
def CutVertexDeletionSideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    8 * n <=
      31 *
        ((sideSurplusData_of_minimalFailure hmin P).leftSet.carrier.card +
          (sideSurplusData_of_minimalFailure hmin P).rightSet.carrier.card)

/-- The exact cardinal statement is precisely the paper-level side-cardinality
fact expressed without the `AmbientCardBound` wrapper. -/
theorem sideCardPaperFact_of_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : CutVertexDeletionSideCardExactFact hmin) :
    CutVertexDeletionSideCardPaperFact hmin := by
  intro P
  simpa [CutVertexDeletionSideCardExactFact,
    CutVertexSideSurplusData.AmbientCardBound]
    using hcard P

/-- The wrapper-free exact cardinal statement follows back from the existing
paper-level side-cardinality fact. -/
theorem sideCardExactFact_of_sideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hpaper : CutVertexDeletionSideCardPaperFact hmin) :
    CutVertexDeletionSideCardExactFact hmin := by
  intro P
  simpa [CutVertexDeletionSideCardExactFact,
    CutVertexSideSurplusData.AmbientCardBound]
    using hpaper P

/-- The isolated exact cardinal fact is equivalent to the existing paper-level
side-cardinality interface. -/
theorem sideCardExactFact_iff_sideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexDeletionSideCardExactFact hmin <->
      CutVertexDeletionSideCardPaperFact hmin := by
  constructor
  case mp =>
    exact sideCardPaperFact_of_sideCardExactFact hmin
  case mpr =>
    exact sideCardExactFact_of_sideCardPaperFact hmin

/-- The exact per-partition cardinal fact supplies the remaining deletion
slack fact used by the cut-vertex closure route. -/
theorem deletionSlackFact_of_minimalFailure_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hcard : CutVertexDeletionSideCardExactFact hmin) :
    CutVertexDeletionSlackFact C :=
  deletionSlackFact_of_minimalFailure_sideCardPaperFact hmin
    (sideCardPaperFact_of_sideCardExactFact hmin hcard)

end

end CutVertexSlackFromDeletion
end Swanepoel
end ErdosProblems1066
