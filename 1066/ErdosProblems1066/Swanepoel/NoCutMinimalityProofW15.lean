import ErdosProblems1066.Swanepoel.NoCutVertexExtractionW13
import ErdosProblems1066.Swanepoel.CutVertexFromConnectedness
import ErdosProblems1066.Swanepoel.MinimalConnectednessClosure
import ErdosProblems1066.Swanepoel.RemainingInputFamilyBuilderW14

set_option autoImplicit false

/-!
# W15 no-cut minimality localization

Minimality closes connectedness, and it supplies cleared witnesses on both
sides of any supplied cut-vertex partition.  The present interface still needs
one genuinely cut-vertex-specific step: those two minimality-selected side
surpluses must pay for the omitted cut vertex.

This file keeps that step explicit.  It proves the exact equivalence between
the missing pay-for-cut statement and `NoCutVertex`, and records the
partition-level obstruction showing why this is the sharp remaining argument.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutMinimalityProofW15

open CutVertexInterface
open CutVertexSlackFromDeletion

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}

/-- The local pay-for-cut statement for one supplied cut-vertex partition,
using exactly the side surplus witnesses selected from minimality. -/
def MinimalitySelectedPartitionPaysCut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) : Prop :=
  (sideSurplusData_of_minimalFailure hmin P).PaysCut

/-- The uniform missing cut-vertex argument: every supplied cut partition has
minimality-selected side surplus large enough to pay for the deleted cut
vertex. -/
def MinimalitySelectedPayForCut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) : Prop :=
  forall P : CutVertexPartition C,
    MinimalitySelectedPartitionPaysCut hmin P

/-- The W15 name is definitionally the W13/W12 isolated missing arithmetic. -/
theorem minimalitySelectedPayForCut_iff_missingArithmetic
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionMissingArithmetic hmin := by
  rfl

/-- One supplied partition cannot both exist in a minimal cleared failure and
have the minimality-selected side surplus pay for the omitted cut vertex. -/
theorem not_minimalitySelectedPartitionPaysCut_of_minimalFailure_partition
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (MinimalitySelectedPartitionPaysCut hmin P) := by
  intro hpay
  exact MinimalGraphFacts.not_hasCleared_of_minimalClearedFailure hmin
    (CutVertexPartition.hasCleared_of_cutVertexSlack P
      ((sideSurplusData_of_minimalFailure hmin P).toGluingData hpay))

/-- Any concrete cut partition obstructs the uniform W15 pay-for-cut input. -/
theorem cutVertexPartition_obstructs_minimalitySelectedPayForCut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : CutVertexPartition C) :
    Not (MinimalitySelectedPayForCut hmin) := by
  intro hpay
  exact
    not_minimalitySelectedPartitionPaysCut_of_minimalFailure_partition hmin P
      (hpay P)

/-- The exact checked localization: under minimal cleared failure, proving the
uniform minimality-selected pay-for-cut statement is equivalent to proving
there is no supplied cut-vertex partition. -/
theorem minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <-> NoCutVertex C := by
  simpa [MinimalitySelectedPayForCut,
    MinimalitySelectedPartitionPaysCut] using
    NoCutVertexExtractionW13.missingArithmetic_iff_noCutVertex_of_minimalFailure
      hmin

/-- Forward form of the localized missing argument.  This is the strongest
non-vacuous route currently available in this interface: the extra hypothesis
is exactly the partition-level pay-for-cut theorem above. -/
theorem noCutVertex_of_minimalFailure_minimalitySelectedPayForCut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hpay : MinimalitySelectedPayForCut hmin) :
    NoCutVertex C :=
  (minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure hmin).1 hpay

/-- Reverse form: once no cut partition is known, the W15 pay-for-cut
statement is vacuous. -/
theorem minimalitySelectedPayForCut_of_minimalFailure_noCutVertex
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    MinimalitySelectedPayForCut hmin :=
  (minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure hmin).2 hno

/-- Minimality alone closes the connectedness part of the no-cut/connectedness
package. -/
theorem connected_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (GraphBridge.unitDistanceSimpleGraph C).Connected :=
  MinimalConnectednessClosure.unitDistanceSimpleGraph_connected_of_minimalClearedFailure
    hmin

/-- Minimality plus the exact W15 pay-for-cut argument gives the connected and
no-cut conclusions, without introducing any unconditional no-cut assumption. -/
theorem connected_and_noCutVertex_of_minimalFailure_minimalitySelectedPayForCut
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hpay : MinimalitySelectedPayForCut hmin) :
    And
      ((GraphBridge.unitDistanceSimpleGraph C).Connected)
      (NoCutVertex C) :=
  And.intro
    (connected_of_minimalFailure hmin)
    (noCutVertex_of_minimalFailure_minimalitySelectedPayForCut hmin hpay)

/-- Equivalence form including the already-closed connectedness contribution:
for a minimal cleared failure, the whole connected/no-cut pair is equivalent
to the exact W15 pay-for-cut argument. -/
theorem minimalitySelectedPayForCut_iff_connected_and_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      And
        ((GraphBridge.unitDistanceSimpleGraph C).Connected)
        (NoCutVertex C) := by
  constructor
  case mp =>
    intro hpay
    exact
      connected_and_noCutVertex_of_minimalFailure_minimalitySelectedPayForCut
        hmin hpay
  case mpr =>
    intro H
    exact
      minimalitySelectedPayForCut_of_minimalFailure_noCutVertex hmin H.2

end

end NoCutMinimalityProofW15
end Swanepoel
end ErdosProblems1066
