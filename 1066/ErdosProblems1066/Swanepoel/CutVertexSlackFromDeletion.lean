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

/-! ## Side-specific surplus retained from the cleared witnesses -/

/-- A cleared side witness with its exact numerical surplus retained. -/
structure SideSurplusData {m : Nat} (Csmall : _root_.UDConfig m) where
  surplus : Nat
  set : CutVertexPartition.SlackIndependentSet Csmall surplus

namespace SideSurplusData

variable {m : Nat} {Csmall : _root_.UDConfig m}

/-- The retained surplus is exactly the cleared slack of its carrier. -/
def ExactSurplus (D : SideSurplusData Csmall) : Prop :=
  D.surplus = 31 * D.set.carrier.card - 8 * m

/-- Projection to the weaker cleared-side statement. -/
theorem hasCleared (D : SideSurplusData Csmall) :
    HasClearedEightThirtyOneIndependentSet Csmall :=
  D.set.hasCleared

end SideSurplusData

/-- Any cleared witness can be repackaged with its exact arithmetic surplus
`31 * |s| - 8 * m`. -/
def sideSurplusData_of_hasCleared {m : Nat} {Csmall : _root_.UDConfig m}
    (hcleared : HasClearedEightThirtyOneIndependentSet Csmall) :
    SideSurplusData Csmall :=
  let s : Finset (Fin m) := Classical.choose hcleared
  let hspec := Classical.choose_spec hcleared
  { surplus := 31 * s.card - 8 * m
    set :=
      { carrier := s
        indep := hspec.1
        surplus_bound := by
          have hbound : 8 * m <= 31 * s.card := by
            simpa [MinimalCounterexample.ClearedEightThirtyOneBound, s]
              using hspec.2
          omega } }

theorem sideSurplusData_of_hasCleared_exact {m : Nat}
    {Csmall : _root_.UDConfig m}
    (hcleared : HasClearedEightThirtyOneIndependentSet Csmall) :
    (sideSurplusData_of_hasCleared hcleared).ExactSurplus := by
  rfl

/-- Minimality gives a left-side cleared witness with its exact surplus
retained. -/
def leftSide_surplusData_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    SideSurplusData P.leftInduced.config :=
  sideSurplusData_of_hasCleared
    (leftSide_hasCleared_of_minimalFailure hmin P)

/-- Minimality gives a right-side cleared witness with its exact surplus
retained. -/
def rightSide_surplusData_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    SideSurplusData P.rightInduced.config :=
  sideSurplusData_of_hasCleared
    (rightSide_hasCleared_of_minimalFailure hmin P)

theorem leftSide_surplusData_exact_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    (leftSide_surplusData_of_minimalFailure hmin P).ExactSurplus := by
  rfl

theorem rightSide_surplusData_exact_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    (rightSide_surplusData_of_minimalFailure hmin P).ExactSurplus := by
  rfl

/-! ## The isolated missing arithmetic -/

/-- Side surplus data for a cut partition before the final pay-for-cut
inequality is supplied. -/
structure CutVertexSideSurplusData (P : CutVertexPartition C) where
  leftSurplus : Nat
  rightSurplus : Nat
  leftSet : CutVertexPartition.SlackIndependentSet
    P.leftInduced.config leftSurplus
  rightSet : CutVertexPartition.SlackIndependentSet
    P.rightInduced.config rightSurplus

namespace CutVertexSideSurplusData

variable {P : CutVertexPartition C}

/-- The only arithmetic still needed to turn side surplus data into gluing
data. -/
def PaysCut (D : CutVertexSideSurplusData P) : Prop :=
  8 <= D.leftSurplus + D.rightSurplus

/-- Once the side surplus pays for the deleted cut vertex, it is exactly the
gluing data consumed by the cut-vertex closure API. -/
def toGluingData (D : CutVertexSideSurplusData P) (hpay : D.PaysCut) :
    CutVertexPartition.CutVertexSlackGluingData P where
  leftSurplus := D.leftSurplus
  rightSurplus := D.rightSurplus
  leftSet := D.leftSet
  rightSet := D.rightSet
  pays_cut_vertex := hpay

end CutVertexSideSurplusData

/-- Minimality supplies both side-specific surplus witnesses; only the final
sum-of-surpluses arithmetic is not supplied by the current deletion API. -/
def sideSurplusData_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    CutVertexSideSurplusData P :=
  let L := leftSide_surplusData_of_minimalFailure hmin P
  let R := rightSide_surplusData_of_minimalFailure hmin P
  { leftSurplus := L.surplus
    rightSurplus := R.surplus
    leftSet := L.set
    rightSet := R.set }

/-- The exact arithmetic still missing after retaining the side-specific
surpluses supplied by minimality. -/
def CutVertexDeletionMissingArithmetic
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    (sideSurplusData_of_minimalFailure hmin P).PaysCut

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

/-- If the isolated pay-for-cut arithmetic is supplied for the side-specific
minimality witnesses, the original deletion slack fact follows. -/
theorem deletionSlackFact_of_minimalFailure_missingArithmetic
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (harith : CutVertexDeletionMissingArithmetic hmin) :
    CutVertexDeletionSlackFact C := by
  intro P
  exact Nonempty.intro
    ((sideSurplusData_of_minimalFailure hmin P).toGluingData (harith P))

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

/-- Symmetric form of `deletionSlackFact_iff_remainingNoCutSlackFact` for
downstream files that start from the final remaining-slack alias. -/
theorem remainingNoCutSlackFact_iff_deletionSlackFact :
    Nonempty (CutVertexFinal.RemainingNoCutSlackFact C) <->
      CutVertexDeletionSlackFact C :=
  deletionSlackFact_iff_remainingNoCutSlackFact.symm

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
