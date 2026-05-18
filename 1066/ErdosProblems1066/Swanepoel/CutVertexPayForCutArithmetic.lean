import ErdosProblems1066.Swanepoel.CutVertexSlackFromDeletion

set_option autoImplicit false

/-!
# Cut-vertex pay-for-cut arithmetic

This file isolates the arithmetic that converts retained side surpluses into
the `8 <= leftSurplus + rightSurplus` field needed for cut-vertex gluing.

The existing deletion/minimality layer gives exact side surpluses.  The only
paper-level input retained here is the combined cardinal inequality saying
that the two chosen side independent sets are large enough for the ambient
`8 / 31` bound after the cut vertex is reinserted.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexSlackFromDeletion

open CounterexamplePipeline
open CutVertexInterface

noncomputable section

namespace SideSurplusData

variable {m : Nat} {Csmall : _root_.UDConfig m}

/-- Exact retained surplus turns the inequality stored in
`SlackIndependentSet` into an equality. -/
theorem slack_eq_of_exact (D : SideSurplusData Csmall)
    (hexact : D.ExactSurplus) :
    8 * m + D.surplus = 31 * D.set.carrier.card := by
  have hbound := D.set.surplus_bound
  unfold ExactSurplus at hexact
  omega

/-- Exact retained surplus, in the orientation useful for linear arithmetic. -/
theorem exact_add_slack_eq (D : SideSurplusData Csmall)
    (hexact : D.ExactSurplus) :
    31 * D.set.carrier.card = 8 * m + D.surplus := by
  exact (D.slack_eq_of_exact hexact).symm

end SideSurplusData

namespace CutVertexSideSurplusData

variable {n : Nat} {C : _root_.UDConfig n} {P : CutVertexPartition C}

/-- The side surplus fields are exactly the retained cleared slack of their
carriers. -/
def ExactSideSurpluses (D : CutVertexSideSurplusData P) : Prop :=
  D.leftSurplus = 31 * D.leftSet.carrier.card - 8 * P.left.card ∧
    D.rightSurplus = 31 * D.rightSet.carrier.card - 8 * P.right.card

/-- The combined side independent sets satisfy the ambient cardinal inequality
after the deleted cut vertex is reinserted.  This is the minimal paper-level
fact needed by the arithmetic below. -/
def AmbientCardBound (D : CutVertexSideSurplusData P) : Prop :=
  8 * n <= 31 * (D.leftSet.carrier.card + D.rightSet.carrier.card)

/-- The same combined cardinal inequality, with the ambient cardinal expanded
using the cut-vertex partition. -/
def ExpandedCardBound (D : CutVertexSideSurplusData P) : Prop :=
  8 * (P.left.card + P.right.card + 1) <=
    31 * (D.leftSet.carrier.card + D.rightSet.carrier.card)

/-- Expand the ambient cardinal in the paper-level cardinal bound. -/
theorem expandedCardBound_of_ambientCardBound
    (D : CutVertexSideSurplusData P)
    (hbound : D.AmbientCardBound) :
    D.ExpandedCardBound := by
  have hcard := P.card_eq_left_add_right_add_one
  unfold AmbientCardBound ExpandedCardBound at *
  omega

/-- Compress the expanded cardinal bound back to the ambient form. -/
theorem ambientCardBound_of_expandedCardBound
    (D : CutVertexSideSurplusData P)
    (hbound : D.ExpandedCardBound) :
    D.AmbientCardBound := by
  have hcard := P.card_eq_left_add_right_add_one
  unfold AmbientCardBound ExpandedCardBound at *
  omega

/-- Exact side surplus equations supply exact slack equalities for each side. -/
theorem side_slack_eqs_of_exactSideSurpluses
    (D : CutVertexSideSurplusData P)
    (hexact : D.ExactSideSurpluses) :
    8 * P.left.card + D.leftSurplus = 31 * D.leftSet.carrier.card ∧
      8 * P.right.card + D.rightSurplus = 31 * D.rightSet.carrier.card := by
  rcases hexact with ⟨hleft, hright⟩
  have hleft_bound := D.leftSet.surplus_bound
  have hright_bound := D.rightSet.surplus_bound
  constructor <;> omega

/-- The expanded combined cardinal bound is exactly what is needed to make the
two exact side surpluses pay for the deleted cut vertex. -/
theorem paysCut_of_exactSideSurpluses_of_expandedCardBound
    (D : CutVertexSideSurplusData P)
    (hexact : D.ExactSideSurpluses)
    (hbound : D.ExpandedCardBound) :
    D.PaysCut := by
  rcases D.side_slack_eqs_of_exactSideSurpluses hexact with
    ⟨hleft, hright⟩
  unfold PaysCut
  unfold ExpandedCardBound at hbound
  omega

/-- Ambient-cardinality form of the pay-for-cut arithmetic. -/
theorem paysCut_of_exactSideSurpluses_of_ambientCardBound
    (D : CutVertexSideSurplusData P)
    (hexact : D.ExactSideSurpluses)
    (hbound : D.AmbientCardBound) :
    D.PaysCut :=
  D.paysCut_of_exactSideSurpluses_of_expandedCardBound hexact
    (D.expandedCardBound_of_ambientCardBound hbound)

end CutVertexSideSurplusData

variable {n : Nat} {C : _root_.UDConfig n}

/-- The side-surplus data constructed from minimality has exact side
surpluses by construction. -/
theorem sideSurplusData_of_minimalFailure_exactSideSurpluses
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    (sideSurplusData_of_minimalFailure hmin P).ExactSideSurpluses := by
  constructor <;> rfl

/-- The minimal paper fact needed to finish the deletion route: for every
cut-vertex partition, the two minimality-supplied side independent sets have
enough combined cardinality for the ambient `8 / 31` bound. -/
def CutVertexDeletionSideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    (sideSurplusData_of_minimalFailure hmin P).AmbientCardBound

/-- The paper-level combined-cardinality fact implies the exact missing
`PaysCut` arithmetic required by `CutVertexSlackFromDeletion`. -/
theorem missingArithmetic_of_sideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hpaper : CutVertexDeletionSideCardPaperFact hmin) :
    CutVertexDeletionMissingArithmetic hmin := by
  intro P
  let D := sideSurplusData_of_minimalFailure hmin P
  exact D.paysCut_of_exactSideSurpluses_of_ambientCardBound
    (sideSurplusData_of_minimalFailure_exactSideSurpluses hmin P)
    (hpaper P)

/-- Bridge from the minimal paper-level side-cardinality fact to the existing
Prop-level cut-vertex deletion slack fact. -/
theorem deletionSlackFact_of_minimalFailure_sideCardPaperFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hpaper : CutVertexDeletionSideCardPaperFact hmin) :
    CutVertexDeletionSlackFact C :=
  deletionSlackFact_of_minimalFailure_missingArithmetic hmin
    (missingArithmetic_of_sideCardPaperFact hmin hpaper)

end

end CutVertexSlackFromDeletion
end Swanepoel
end ErdosProblems1066
