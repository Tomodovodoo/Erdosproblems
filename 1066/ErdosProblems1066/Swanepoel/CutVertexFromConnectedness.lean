import ErdosProblems1066.Swanepoel.ConnectednessExtractionClosure
import ErdosProblems1066.Swanepoel.CutVertexClosure
import ErdosProblems1066.Swanepoel.MinimumDegree
import ErdosProblems1066.Swanepoel.MinimalFailureDegreeRange

set_option autoImplicit false

/-!
# Connectedness plus conditional cut-vertex closure

This file is only a packaging layer.  It combines the checked connectedness
extraction, the conditional cut-vertex slack closure, and the minimal-failure
degree range into one certificate theorem.

The no-cut-vertex conclusion remains conditional on explicit slack data for
every supplied cut-vertex partition.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexFromConnectedness

open GraphBridge
open MinimalFailureDegreeRange

noncomputable section

/-- The explicit data used by this closure layer.

The `allCutVertexSlack` field is the essential cut-vertex input: no theorem in
this file derives it from minimality. -/
structure MinimalFailureAllCutSlackData {n : Nat}
    (C : _root_.UDConfig n) where
  positiveCard : 0 < n
  minimalFailure : MinimalGraphFacts.IsMinimalClearedFailure C
  allCutVertexSlack : CutVertexClosure.AllCutVertexSlackGluingData C

/-- The combined certificate supplied by minimality plus explicit all-cut
slack data. -/
structure ConnectedNoCutVertexCertificate {n : Nat}
    (C : _root_.UDConfig n) : Prop where
  connected : (unitDistanceSimpleGraph C).Connected
  noCutVertex : CutVertexInterface.NoCutVertex C
  minimumDegree :
    forall v : Fin n,
      3 <= (DegreePipeline.unitDistanceNeighborSet C v).card
  degreeRange :
    forall v : Fin n,
      And
        (3 <= (DegreePipeline.unitDistanceNeighborSet C v).card)
        ((DegreePipeline.unitDistanceNeighborSet C v).card <= 6)

namespace MinimalFailureAllCutSlackData

variable {n : Nat} {C : _root_.UDConfig n}

/-- Forget to the conditional cut-vertex package from `CutVertexClosure`. -/
def minimalFailureCutVertexSlackData
    (H : MinimalFailureAllCutSlackData C) :
    CutVertexClosure.MinimalFailureCutVertexSlackData C where
  minimalFailure := H.minimalFailure
  cutVertexSlack := H.allCutVertexSlack

/-- The connected/no-cut closure package with the concrete separator
extraction filled in. -/
def connectedNoCutVertexClosureData
    (H : MinimalFailureAllCutSlackData C) :
    CutVertexClosure.ConnectedNoCutVertexClosureData C where
  minimalFailure := H.minimalFailure
  separatorExtraction :=
    ConnectednessExtractionClosure.honestAnticompleteSeparatorExtraction C
  cutVertexSlack := H.allCutVertexSlack

/-- Connectedness of the unit-distance graph. -/
theorem connected
    (H : MinimalFailureAllCutSlackData C) :
    (unitDistanceSimpleGraph C).Connected := by
  haveI : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 H.positiveCard)
  exact H.connectedNoCutVertexClosureData.connected

/-- Conditional no-cut-vertex conclusion from explicit all-cut slack data. -/
theorem noCutVertex
    (H : MinimalFailureAllCutSlackData C) :
    CutVertexInterface.NoCutVertex C :=
  H.minimalFailureCutVertexSlackData.noCutVertex

/-- Minimum unit-distance degree supplied by the minimal-failure degree
pipeline. -/
theorem minimumDegree
    (H : MinimalFailureAllCutSlackData C)
    (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  MinimumDegree.unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
    H.minimalFailure v

/-- The full checked degree range for each vertex. -/
theorem degreeRange
    (H : MinimalFailureAllCutSlackData C)
    (v : Fin n) :
    And
      (3 <= (DegreePipeline.unitDistanceNeighborSet C v).card)
      ((DegreePipeline.unitDistanceNeighborSet C v).card <= 6) :=
  unitDistanceNeighborSet_card_between_three_and_six_of_minimalClearedFailure
    H.minimalFailure v

/-- Pack the connectedness, conditional no-cut, and degree conclusions. -/
theorem connectedNoCutVertexCertificate
    (H : MinimalFailureAllCutSlackData C) :
    ConnectedNoCutVertexCertificate C where
  connected := H.connected
  noCutVertex := H.noCutVertex
  minimumDegree := H.minimumDegree
  degreeRange := H.degreeRange

end MinimalFailureAllCutSlackData

/-! ## Direct theorem forms -/

/-- Clean conditional theorem: a nonempty minimal cleared failure with explicit
slack gluing data for every supplied cut-vertex partition has a connected
unit-distance graph and no supplied cut-vertex partition.  The certificate also
records the available minimal-failure degree facts. -/
theorem connectedNoCutVertexCertificate_of_minimalFailure_allCutVertexSlack
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexClosure.AllCutVertexSlackGluingData C) :
    ConnectedNoCutVertexCertificate C :=
  ({ positiveCard := hn
     minimalFailure := hmin
     allCutVertexSlack := hslack } :
      MinimalFailureAllCutSlackData C).connectedNoCutVertexCertificate

/-- Pair-valued convenience form of
`connectedNoCutVertexCertificate_of_minimalFailure_allCutVertexSlack`. -/
theorem connected_and_noCutVertex_of_minimalFailure_allCutVertexSlack
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexClosure.AllCutVertexSlackGluingData C) :
    And
      ((unitDistanceSimpleGraph C).Connected)
      (CutVertexInterface.NoCutVertex C) := by
  have H :=
    connectedNoCutVertexCertificate_of_minimalFailure_allCutVertexSlack
      (C := C) hn hmin hslack
  exact And.intro H.connected H.noCutVertex

/-- Conditional no-cut projection.  The explicit all-cut slack data is still
required. -/
theorem noCutVertex_of_minimalFailure_allCutVertexSlack
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : CutVertexClosure.AllCutVertexSlackGluingData C) :
    CutVertexInterface.NoCutVertex C :=
  (connectedNoCutVertexCertificate_of_minimalFailure_allCutVertexSlack
    (C := C) hn hmin hslack).noCutVertex

end

end CutVertexFromConnectedness
end Swanepoel
end ErdosProblems1066
