import ErdosProblems1066.Swanepoel.CutVertexInterface
import ErdosProblems1066.Swanepoel.MinimalConnectedness

set_option autoImplicit false

/-!
# Conditional cut-vertex closure

This module is the honest closure layer above `CutVertexInterface`.  It does
not extract a cut partition from graph theory and it does not prove a no-cut
theorem from minimality alone.  Instead it records the exact conditional route:
uniform cut-vertex slack data turns any supplied cut partition into a cleared
independent set, contradicting minimal cleared failure.  Consequently, a
minimal cleared failure with such uniform slack data has no supplied
`CutVertexPartition`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexClosure

open CounterexamplePipeline
open CutVertexInterface
open GraphBridge
open MinimalGraphFacts

noncomputable section

/-! ## Named cut-vertex assumptions -/

/-- Slack gluing data available for every labelled cut-vertex partition of
`C`.  This is data, not a proof that such partitions exist. -/
structure AllCutVertexSlackGluingData {n : Nat}
    (C : _root_.UDConfig n) where
  gluingData :
    forall (P : CutVertexPartition C),
      CutVertexPartition.CutVertexSlackGluingData P

/-- A named cut-vertex branch: an actual supplied cut-vertex partition. -/
structure CutVertexCaseData {n : Nat} (C : _root_.UDConfig n) where
  partition : CutVertexPartition C

/-- Minimal-failure data together with uniform cut-vertex slack gluing data. -/
structure MinimalFailureCutVertexSlackData {n : Nat}
    (C : _root_.UDConfig n) where
  minimalFailure : IsMinimalClearedFailure C
  cutVertexSlack : AllCutVertexSlackGluingData C

/-- The connected no-cut package obtainable from honest separator extraction
and uniform cut-vertex slack. -/
structure ConnectedNoCutVertexClosureData {n : Nat}
    (C : _root_.UDConfig n) where
  minimalFailure : IsMinimalClearedFailure C
  separatorExtraction :
    MinimalConnectedness.HonestAnticompleteSeparatorExtraction C
  cutVertexSlack : AllCutVertexSlackGluingData C

/-- The proposition-level closure conclusion: preconnectedness and absence of
supplied cut-vertex partitions. -/
structure PreconnectedNoCutVertexCertificate {n : Nat}
    (C : _root_.UDConfig n) : Prop where
  preconnected : (unitDistanceSimpleGraph C).Preconnected
  noCutVertex : NoCutVertex C

namespace AllCutVertexSlackGluingData

variable {n : Nat} {C : _root_.UDConfig n}

/-- Project the slack package to a particular cut partition. -/
def forPartition (H : AllCutVertexSlackGluingData C)
    (P : CutVertexPartition C) :
    CutVertexPartition.CutVertexSlackGluingData P :=
  H.gluingData P

/-- Uniform slack data clears the ambient configuration on any supplied
cut-vertex branch. -/
theorem hasCleared_of_partition
    (H : AllCutVertexSlackGluingData C)
    (P : CutVertexPartition C) :
    HasClearedEightThirtyOneIndependentSet C :=
  CutVertexPartition.hasCleared_of_cutVertexSlack P (H.forPartition P)

/-- Structure-valued version of `hasCleared_of_partition`. -/
theorem hasCleared_of_cutVertexCase
    (H : AllCutVertexSlackGluingData C)
    (K : CutVertexCaseData C) :
    HasClearedEightThirtyOneIndependentSet C :=
  H.hasCleared_of_partition K.partition

/-- Contradiction-routing form for an ambient configuration already known not
to satisfy the cleared bound. -/
theorem contradiction_of_partition
    (H : AllCutVertexSlackGluingData C)
    (hC : Not (HasClearedEightThirtyOneIndependentSet C))
    (P : CutVertexPartition C) :
    False :=
  hC (H.hasCleared_of_partition P)

/-- Structure-valued contradiction-routing form. -/
theorem contradiction_of_cutVertexCase
    (H : AllCutVertexSlackGluingData C)
    (hC : Not (HasClearedEightThirtyOneIndependentSet C))
    (K : CutVertexCaseData C) :
    False :=
  H.contradiction_of_partition hC K.partition

end AllCutVertexSlackGluingData

namespace MinimalFailureCutVertexSlackData

variable {n : Nat} {C : _root_.UDConfig n}

/-- The uncleared side of the packaged minimal-failure assumption. -/
theorem not_hasCleared (H : MinimalFailureCutVertexSlackData C) :
    Not (HasClearedEightThirtyOneIndependentSet C) :=
  not_hasCleared_of_minimalClearedFailure H.minimalFailure

/-- If the cut-vertex branch is supplied, the uniform slack data constructs a
cleared independent set in the original configuration. -/
theorem hasCleared_of_partition
    (H : MinimalFailureCutVertexSlackData C)
    (P : CutVertexPartition C) :
    HasClearedEightThirtyOneIndependentSet C :=
  H.cutVertexSlack.hasCleared_of_partition P

/-- Structure-valued version of `hasCleared_of_partition`. -/
theorem hasCleared_of_cutVertexCase
    (H : MinimalFailureCutVertexSlackData C)
    (K : CutVertexCaseData C) :
    HasClearedEightThirtyOneIndependentSet C :=
  H.hasCleared_of_partition K.partition

/-- A minimal cleared failure with uniform cut-vertex slack cannot be in a
supplied cut-vertex branch. -/
theorem contradiction_of_partition
    (H : MinimalFailureCutVertexSlackData C)
    (P : CutVertexPartition C) :
    False :=
  H.not_hasCleared (H.hasCleared_of_partition P)

/-- Structure-valued contradiction theorem for the cut-vertex branch. -/
theorem contradiction_of_cutVertexCase
    (H : MinimalFailureCutVertexSlackData C)
    (K : CutVertexCaseData C) :
    False :=
  H.contradiction_of_partition K.partition

/-- Contradiction from a nonempty collection of supplied cut partitions. -/
theorem contradiction_of_nonempty_partition
    (H : MinimalFailureCutVertexSlackData C)
    (hcut : Nonempty (CutVertexPartition C)) :
    False := by
  cases hcut with
  | intro P => exact H.contradiction_of_partition P

/-- The strongest no-cut conclusion currently available from the honest
cut-vertex interface: no `CutVertexPartition` can be supplied. -/
theorem noCutVertex
    (H : MinimalFailureCutVertexSlackData C) :
    NoCutVertex C := by
  intro hcut
  exact H.contradiction_of_nonempty_partition hcut

/-- Certificate form of `noCutVertex`. -/
theorem noCutVertexCertificate
    (H : MinimalFailureCutVertexSlackData C) :
    NoCutVertexCertificate C where
  no_cut_vertex := H.noCutVertex

end MinimalFailureCutVertexSlackData

namespace ConnectedNoCutVertexClosureData

variable {n : Nat} {C : _root_.UDConfig n}

/-- Forget the connectedness extraction and keep the cut-vertex closure
package. -/
def minimalFailureCutVertexSlack
    (H : ConnectedNoCutVertexClosureData C) :
    MinimalFailureCutVertexSlackData C where
  minimalFailure := H.minimalFailure
  cutVertexSlack := H.cutVertexSlack

/-- The connectedness contribution supplied by `MinimalConnectedness`. -/
theorem preconnected
    (H : ConnectedNoCutVertexClosureData C) :
    (unitDistanceSimpleGraph C).Preconnected :=
  MinimalConnectedness.preconnected_of_minimalClearedFailure_of_separatorExtraction
    H.minimalFailure H.separatorExtraction

/-- The cut-vertex contribution supplied by uniform slack gluing. -/
theorem noCutVertex
    (H : ConnectedNoCutVertexClosureData C) :
    NoCutVertex C :=
  H.minimalFailureCutVertexSlack.noCutVertex

/-- Pack the two honest conclusions together. -/
theorem preconnectedNoCutVertexCertificate
    (H : ConnectedNoCutVertexClosureData C) :
    PreconnectedNoCutVertexCertificate C where
  preconnected := H.preconnected
  noCutVertex := H.noCutVertex

/-- Nonempty connectedness version of the closure package. -/
theorem connected
    (H : ConnectedNoCutVertexClosureData C)
    [Nonempty (Fin n)] :
    (unitDistanceSimpleGraph C).Connected :=
  MinimalConnectedness.connected_of_minimalClearedFailure_of_separatorExtraction
    H.minimalFailure H.separatorExtraction

/-- A supplied cut-vertex branch is still contradictory in the connected
package. -/
theorem contradiction_of_cutVertexCase
    (H : ConnectedNoCutVertexClosureData C)
    (K : CutVertexCaseData C) :
    False :=
  H.minimalFailureCutVertexSlack.contradiction_of_cutVertexCase K

end ConnectedNoCutVertexClosureData

/-! ## Direct theorem forms -/

/-- Direct positive form: all cut partitions have slack data, and this
particular cut partition is supplied, so the original configuration is cleared. -/
theorem hasCleared_of_allCutVertexSlack_of_cutVertexCase
    {n : Nat} {C : _root_.UDConfig n}
    (Hslack : AllCutVertexSlackGluingData C)
    (K : CutVertexCaseData C) :
    HasClearedEightThirtyOneIndependentSet C :=
  Hslack.hasCleared_of_cutVertexCase K

/-- Direct minimal-failure contradiction form. -/
theorem contradiction_of_minimalFailure_allCutVertexSlack_of_cutVertexCase
    {n : Nat} {C : _root_.UDConfig n}
    (H : MinimalFailureCutVertexSlackData C)
    (K : CutVertexCaseData C) :
    False :=
  H.contradiction_of_cutVertexCase K

/-- Direct no-cut certificate form. -/
theorem noCutVertexCertificate_of_minimalFailure_allCutVertexSlack
    {n : Nat} {C : _root_.UDConfig n}
    (H : MinimalFailureCutVertexSlackData C) :
    NoCutVertexCertificate C :=
  H.noCutVertexCertificate

end

end CutVertexClosure
end Swanepoel
end ErdosProblems1066
