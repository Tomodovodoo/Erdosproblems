import ErdosProblems1066.Swanepoel.CutVertexFromConnectedness

set_option autoImplicit false

/-!
# Final cut-vertex route package

This file is a small final API for the checked connectedness/no-cut/min-degree
route.

The connectedness and degree-range conclusions use only minimal cleared
failure.  The no-cut-vertex conclusion is intentionally conditional on the
uniform all-cut-vertex slack package from `CutVertexClosure`.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace CutVertexFinal

open GraphBridge
open CutVertexFromConnectedness
open MinimalFailureDegreeRange

noncomputable section

/-- The exact remaining cut-vertex input needed by the current no-cut route. -/
abbrev RemainingNoCutSlackFact {n : Nat} (C : _root_.UDConfig n) :=
  CutVertexClosure.AllCutVertexSlackGluingData C

/-- The unconditional part of the current minimal-failure route: connectedness
and the checked unit-distance degree range. -/
structure ConnectedDegreeRangeCertificate {n : Nat}
    (C : _root_.UDConfig n) : Prop where
  connected : (unitDistanceSimpleGraph C).Connected
  minimumDegree :
    forall v : Fin n,
      3 <= (DegreePipeline.unitDistanceNeighborSet C v).card
  maximumDegree :
    forall v : Fin n,
      (DegreePipeline.unitDistanceNeighborSet C v).card <= 6
  degreeRange :
    forall v : Fin n,
      And
        (3 <= (DegreePipeline.unitDistanceNeighborSet C v).card)
        ((DegreePipeline.unitDistanceNeighborSet C v).card <= 6)

/-- The strongest final package available here: connectedness, conditional
absence of supplied cut-vertex partitions, and the checked degree range. -/
structure ConnectedNoCutDegreeRangeCertificate {n : Nat}
    (C : _root_.UDConfig n) : Prop where
  connected : (unitDistanceSimpleGraph C).Connected
  noCutVertex : CutVertexInterface.NoCutVertex C
  minimumDegree :
    forall v : Fin n,
      3 <= (DegreePipeline.unitDistanceNeighborSet C v).card
  maximumDegree :
    forall v : Fin n,
      (DegreePipeline.unitDistanceNeighborSet C v).card <= 6
  degreeRange :
    forall v : Fin n,
      And
        (3 <= (DegreePipeline.unitDistanceNeighborSet C v).card)
        ((DegreePipeline.unitDistanceNeighborSet C v).card <= 6)

/-- Minimal cleared failure alone gives connectedness and degree range. -/
theorem connectedDegreeRangeCertificate_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    ConnectedDegreeRangeCertificate C where
  connected :=
    ConnectednessExtractionClosure.connected_of_minimalClearedFailure
      (C := C) hn hmin
  minimumDegree :=
    unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure hmin
  maximumDegree :=
    unitDistanceNeighborSet_card_le_six C
  degreeRange :=
    unitDistanceNeighborSet_card_between_three_and_six_of_minimalClearedFailure
      hmin

/-- Projection theorem for the connectedness part of minimal failure. -/
theorem connected_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    (unitDistanceSimpleGraph C).Connected :=
  (connectedDegreeRangeCertificate_of_minimalFailure
    (C := C) hn hmin).connected

/-- Projection theorem for the lower degree bound from minimal failure. -/
theorem minimumDegree_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card :=
  unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure hmin v

/-- Projection theorem for the upper degree bound. -/
theorem maximumDegree
    {n : Nat} (C : _root_.UDConfig n)
    (v : Fin n) :
    (DegreePipeline.unitDistanceNeighborSet C v).card <= 6 :=
  unitDistanceNeighborSet_card_le_six C v

/-- Projection theorem for the full degree range from minimal failure. -/
theorem degreeRange_of_minimalFailure
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (v : Fin n) :
    And
      (3 <= (DegreePipeline.unitDistanceNeighborSet C v).card)
      ((DegreePipeline.unitDistanceNeighborSet C v).card <= 6) :=
  unitDistanceNeighborSet_card_between_three_and_six_of_minimalClearedFailure
    hmin v

/-- Conditional no-cut projection.  The uniform slack fact is the remaining
cut-vertex payload; it is not derived from minimality in this file. -/
theorem noCutVertex_of_minimalFailure_remainingSlack
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : RemainingNoCutSlackFact C) :
    CutVertexInterface.NoCutVertex C :=
  noCutVertex_of_minimalFailure_allCutVertexSlack
    (C := C) hn hmin hslack

/-- Compatibility projection to the certificate from
`CutVertexFromConnectedness`. -/
theorem cutVertexFromConnectednessCertificate_of_minimalFailure_remainingSlack
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : RemainingNoCutSlackFact C) :
    ConnectedNoCutVertexCertificate C :=
  connectedNoCutVertexCertificate_of_minimalFailure_allCutVertexSlack
    (C := C) hn hmin hslack

/-- Combined final conditional package. -/
theorem connectedNoCutDegreeRangeCertificate_of_minimalFailure_remainingSlack
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : RemainingNoCutSlackFact C) :
    ConnectedNoCutDegreeRangeCertificate C := by
  exact
    { connected := connected_of_minimalFailure (C := C) hn hmin
      noCutVertex :=
        noCutVertex_of_minimalFailure_remainingSlack
          (C := C) hn hmin hslack
      minimumDegree := minimumDegree_of_minimalFailure hmin
      maximumDegree := maximumDegree C
      degreeRange := degreeRange_of_minimalFailure hmin }

/- Name-compatible namespace for downstream files that group these results as
connected no-cut vertices. -/
namespace ConnectedNoCutVertices

/-- Alias for the final connected/no-cut/degree certificate. -/
abbrev Certificate {n : Nat} (C : _root_.UDConfig n) : Prop :=
  ConnectedNoCutDegreeRangeCertificate C

/-- Final conditional theorem in the `ConnectedNoCutVertices` namespace. -/
theorem of_minimalFailure_remainingSlack
    {n : Nat} {C : _root_.UDConfig n}
    (hn : 0 < n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (hslack : RemainingNoCutSlackFact C) :
    Certificate C :=
  connectedNoCutDegreeRangeCertificate_of_minimalFailure_remainingSlack
    (C := C) hn hmin hslack

end ConnectedNoCutVertices

end

end CutVertexFinal
end Swanepoel
end ErdosProblems1066
