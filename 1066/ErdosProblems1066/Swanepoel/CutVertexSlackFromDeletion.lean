import ErdosProblems1066.Swanepoel.CutVertexFinal

set_option autoImplicit false

/-!
# Cut-vertex slack from deletion data

This file records the current status of the cut-vertex slack route.

Minimality already supplies cleared independent sets on the two proper sides
of a supplied cut-vertex partition.  The deletion/reinsertion APIs currently
do not retain enough numerical surplus to prove that the two side bounds pay
for the omitted cut vertex.  The remaining honest input is therefore exactly a
per-partition slack-gluing witness.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexSlackFromDeletion

open CounterexamplePipeline
open CutVertexInterface

noncomputable section

/-! ## What minimality already gives on the two cut sides -/

variable {n : Nat} {C : _root_.UDConfig n}

/-- Minimality clears the left induced side of any supplied cut-vertex
partition, since that side has strictly fewer vertices than the ambient
configuration. -/
theorem leftSide_hasCleared_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    HasClearedEightThirtyOneIndependentSet P.leftInduced.config :=
  MinimalGraphFacts.smaller_hasCleared_of_minimalClearedFailure
    hmin P.leftInduced.config P.left_card_lt

/-- Minimality clears the right induced side of any supplied cut-vertex
partition, since that side has strictly fewer vertices than the ambient
configuration. -/
theorem rightSide_hasCleared_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    HasClearedEightThirtyOneIndependentSet P.rightInduced.config :=
  MinimalGraphFacts.smaller_hasCleared_of_minimalClearedFailure
    hmin P.rightInduced.config P.right_card_lt

/-! ## The exact remaining slack input -/

/-- The remaining cut-vertex slack fact after the deletion/minimality
reduction: every supplied cut partition has side independent sets whose
combined cleared surplus pays for the deleted cut vertex.

This is deliberately `Prop`-valued.  It is the smallest interface needed to
recover the data-valued `AllCutVertexSlackGluingData` by choice, without
claiming the surplus is derivable from the present deletion/reinsertion API. -/
def CutVertexDeletionSlackFact {n : Nat} (C : _root_.UDConfig n) : Prop :=
  forall P : CutVertexPartition C,
    Nonempty (CutVertexPartition.CutVertexSlackGluingData P)

/-- Data projection from the Prop-level remaining slack fact to the uniform
cut-vertex slack package used by `CutVertexClosure`. -/
def allCutVertexSlackGluingData_of_deletionSlackFact
    (hslack : CutVertexDeletionSlackFact C) :
    CutVertexClosure.AllCutVertexSlackGluingData C where
  gluingData := fun P => Classical.choice (hslack P)

/-- The same projection, named for the final cut-vertex API. -/
def remainingNoCutSlackFact_of_deletionSlackFact
    (hslack : CutVertexDeletionSlackFact C) :
    CutVertexFinal.RemainingNoCutSlackFact C :=
  allCutVertexSlackGluingData_of_deletionSlackFact hslack

/-- If the data-valued all-cut slack package is already available, it gives
the Prop-level deletion slack fact. -/
theorem deletionSlackFact_of_allCutVertexSlackGluingData
    (hslack : CutVertexClosure.AllCutVertexSlackGluingData C) :
    CutVertexDeletionSlackFact C := by
  intro P
  exact ⟨hslack.forPartition P⟩

/-- The Prop-level deletion slack fact is equivalent to the final remaining
no-cut slack input, up to the expected data/Prop projection. -/
theorem deletionSlackFact_iff_remainingNoCutSlackFact :
    CutVertexDeletionSlackFact C <->
      Nonempty (CutVertexFinal.RemainingNoCutSlackFact C) := by
  constructor
  · intro hslack
    exact ⟨remainingNoCutSlackFact_of_deletionSlackFact hslack⟩
  · rintro ⟨hslack⟩
    exact deletionSlackFact_of_allCutVertexSlackGluingData hslack

/-! ## Projections into `CutVertexFinal` -/

/-- Conditional no-cut projection through the final API, using exactly the
remaining deletion slack fact. -/
theorem noCutVertex_of_minimalFailure_deletionSlackFact
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexDeletionSlackFact C) :
    CutVertexInterface.NoCutVertex C :=
  CutVertexFinal.noCutVertex_of_minimalFailure_remainingSlack
    (C := C) hn hmin
    (remainingNoCutSlackFact_of_deletionSlackFact hslack)

/-- Projection to the connected/no-cut certificate from
`CutVertexFromConnectedness`, again through the final remaining slack alias. -/
theorem cutVertexFromConnectednessCertificate_of_minimalFailure_deletionSlackFact
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexDeletionSlackFact C) :
    CutVertexFromConnectedness.ConnectedNoCutVertexCertificate C :=
  CutVertexFinal.cutVertexFromConnectednessCertificate_of_minimalFailure_remainingSlack
    (C := C) hn hmin
    (remainingNoCutSlackFact_of_deletionSlackFact hslack)

/-- Final connected/no-cut/degree-range package from minimality plus the exact
remaining per-partition deletion slack fact. -/
theorem connectedNoCutDegreeRangeCertificate_of_minimalFailure_deletionSlackFact
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexDeletionSlackFact C) :
    CutVertexFinal.ConnectedNoCutDegreeRangeCertificate C :=
  CutVertexFinal.connectedNoCutDegreeRangeCertificate_of_minimalFailure_remainingSlack
    (C := C) hn hmin
    (remainingNoCutSlackFact_of_deletionSlackFact hslack)

end

end CutVertexSlackFromDeletion
end Swanepoel
end ErdosProblems1066
