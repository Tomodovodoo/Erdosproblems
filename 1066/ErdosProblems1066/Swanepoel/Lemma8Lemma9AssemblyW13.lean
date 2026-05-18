import ErdosProblems1066.Swanepoel.BoundaryArcW12
import ErdosProblems1066.Swanepoel.E22E23BridgeW12
import ErdosProblems1066.Swanepoel.Lemma8WitnessW12
import ErdosProblems1066.Swanepoel.Lemma9NoStartConcrete

set_option autoImplicit false

/-!
# W13 Lemma 8 / Lemma 9 assembly

This module is a checked bridge layer between the W12 Lemma 8 witness
extraction and the Lemma 9 no-start adapters.

The boundary side keeps the selected arc data honest: the finite `p/q` spine
is obtained from `BoundaryArcW12.M8BoundaryArcCertificate`, so the first and
last labels are the recorded arc endpoints.  The Lemma 8 fields then extract
the actual `r_i, s_i` witnesses from that spine.

The Lemma 9 side takes the five explicit no-start fields and exposes the
concrete no-early predicate, the construction late-triples package, the honest
late-triples predicate, and the window/no-early package used immediately
before the E22/E23 bridge.
-/

noncomputable section

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8Lemma9AssemblyW13

open BoundaryArcW12
open BoundaryFaceCountingToM8
open BoundaryLabelCertificateAssembly
open BoundarySpineFiniteCertificate
open CutVertexClosure
open E22E23BridgeW12
open GraphBridge
open LateTriplesInterface
open Lemma8ExistenceConcrete
open Lemma8NeighborExtractionConcrete
open Lemma8WitnessW12
open Lemma9NoStartConcrete
open Lemma10AnalyticBridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8LateTriplesFromNoEarly
open M8PipelineClosure
open M8WindowContainmentConcrete
open MinimalGraphFacts
open NoEarlyTripleConcrete

universe u

variable {n : Nat} {C : _root_.UDConfig n}
variable {Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
  (CanonicalUDGraph C)}
variable {connectedNoCut : PreconnectedNoCutVertexCertificate C}
variable {hmin : IsMinimalClearedFailure C}

/-! ## Boundary arc data to Lemma 8 witness data -/

/--
Boundary-arc data plus the local Lemma 8 witness hypotheses for the finite
spine obtained from that arc.
-/
structure M8ArcLemma8WitnessData
    (Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) where
  arc : M8BoundaryArcCertificate Dplanar
  centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree
        (arc.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin) i = 6
  forbiddenFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (arc.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin) i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix forbiddenFrame).r i)
        ((arc.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin).prevQ i)
        ((arc.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin).leftP i)
        ((arc.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin).rightP i)
        ((arc.toFinitePQSpineCertificate.toM8BoundarySpine
          connectedNoCut hmin).nextQ i)

namespace M8ArcLemma8WitnessData

variable (W : M8ArcLemma8WitnessData Dplanar connectedNoCut hmin)

/-- The finite `p/q` spine certificate obtained from the real boundary arc. -/
def finiteLabels : M8FinitePQSpineCertificate Dplanar :=
  W.arc.toFinitePQSpineCertificate

/-- The boundary spine obtained from the arc-derived finite certificate. -/
def spine :
    M8BoundarySpine
      (W.finiteLabels.context connectedNoCut hmin) :=
  W.finiteLabels.toM8BoundarySpine connectedNoCut hmin

/-- Forget the arc metadata to the W12 finite Lemma 8 witness package. -/
def toFiniteBoundaryLemma8WitnessData :
    M8FiniteBoundaryLemma8WitnessData Dplanar connectedNoCut hmin where
  finiteLabels := W.finiteLabels
  centerDegreeSix := W.centerDegreeSix
  forbiddenFrame := W.forbiddenFrame
  positiveCyclicOrderAt := W.positiveCyclicOrderAt
  positiveCyclicOrder := W.positiveCyclicOrder

/-- The extracted non-cyclic `r_i, s_i` data. -/
def extraNeighborData :
    M8ExtraNeighborData W.spine :=
  W.toFiniteBoundaryLemma8WitnessData.extraNeighborData

/-- The extracted Lemma 8 combinatorics package. -/
def toLemma8Combinatorics :
    M8Lemma8Combinatorics W.spine :=
  W.toFiniteBoundaryLemma8WitnessData.toLemma8Combinatorics

/-- The finite boundary-label certificate assembled from arc labels and
Lemma 8 witnesses. -/
def toFiniteBoundaryLabelCertificate :
    M8FiniteBoundaryLabelCertificate Dplanar connectedNoCut hmin :=
  W.toFiniteBoundaryLemma8WitnessData.toFiniteBoundaryLabelCertificate

/-- The boundary-label package assembled from arc labels and Lemma 8
witnesses. -/
def toBoundaryLabelPackage : M8BoundaryLabelPackage C :=
  W.toFiniteBoundaryLemma8WitnessData.toBoundaryLabelPackage

/-- The local M8 labels assembled from arc labels and Lemma 8 witnesses. -/
def localLabels : M8LocalLabels C :=
  W.toBoundaryLabelPackage.toM8LocalLabels

@[simp]
theorem finiteLabels_eq :
    W.finiteLabels = W.arc.toFinitePQSpineCertificate :=
  rfl

@[simp]
theorem finiteLabels_firstEndpoint :
    W.finiteLabels.pIndex m8ArcFirstBoundaryIndex = W.arc.leftEndpoint :=
  W.arc.leftEndpoint_eq_p0

@[simp]
theorem finiteLabels_lastEndpoint :
    W.finiteLabels.pIndex m8ArcLastBoundaryIndex = W.arc.rightEndpoint :=
  W.arc.rightEndpoint_eq_p13

@[simp]
theorem toLemma8Combinatorics_r (i : M8ExtraIndex) :
    W.toLemma8Combinatorics.r i = W.extraNeighborData.r i :=
  rfl

@[simp]
theorem toLemma8Combinatorics_s (i : M8ExtraIndex) :
    W.toLemma8Combinatorics.s i = W.extraNeighborData.s i :=
  rfl

/-- The arc-derived local label at the first endpoint is the recorded first
boundary vertex. -/
theorem localLabels_p_first :
    W.localLabels.labels.p m8ArcFirstBoundaryIndex =
      W.arc.leftEndpointVertex := by
  calc
    W.localLabels.labels.p m8ArcFirstBoundaryIndex =
        W.toFiniteBoundaryLabelCertificate.toM8LocalLabels.labels.p
          m8ArcFirstBoundaryIndex := rfl
    _ = W.finiteLabels.p m8ArcFirstBoundaryIndex :=
        W.toFiniteBoundaryLabelCertificate.labels_p m8ArcFirstBoundaryIndex
    _ = W.arc.leftEndpointVertex := by
        simp [finiteLabels, M8BoundaryArcCertificate.leftEndpointVertex,
          M8BoundaryArcCertificate.p]

/-- The arc-derived local label at the last endpoint is the recorded last
boundary vertex. -/
theorem localLabels_p_last :
    W.localLabels.labels.p m8ArcLastBoundaryIndex =
      W.arc.rightEndpointVertex := by
  calc
    W.localLabels.labels.p m8ArcLastBoundaryIndex =
        W.toFiniteBoundaryLabelCertificate.toM8LocalLabels.labels.p
          m8ArcLastBoundaryIndex := rfl
    _ = W.finiteLabels.p m8ArcLastBoundaryIndex :=
        W.toFiniteBoundaryLabelCertificate.labels_p m8ArcLastBoundaryIndex
    _ = W.arc.rightEndpointVertex := by
        simp [finiteLabels, M8BoundaryArcCertificate.rightEndpointVertex,
          M8BoundaryArcCertificate.p]

/-- Projection of the extracted `r_i` adjacency from the arc route. -/
theorem r_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (W.spine.centerQ i) (W.extraNeighborData.r i) :=
  W.toFiniteBoundaryLemma8WitnessData.r_neighbor i

/-- Projection of the extracted `s_i` adjacency from the arc route. -/
theorem s_neighbor (i : M8ExtraIndex) :
    (unitDistanceLocalGraph C).Adj
      (W.spine.centerQ i) (W.extraNeighborData.s i) :=
  W.toFiniteBoundaryLemma8WitnessData.s_neighbor i

/-- The arc route preserves the local extra-neighbor predicate required by
downstream broken-lattice labels. -/
theorem localLabels_extraNeighborWitness (i : M8ExtraIndex) :
    W.localLabels.predicates.data.extraNeighborWitness i :=
  W.toBoundaryLabelPackage.extraNeighborWitness i

end M8ArcLemma8WitnessData

/-! ## Lemma 8 witness data plus Lemma 9 no-start data -/

/--
Finite Lemma 8 witness data paired with the exact five Lemma 9 no-start
fields for the local labels produced by those witnesses.
-/
structure M8FiniteLemma8NoStartData
    (Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) where
  witness :
    M8FiniteBoundaryLemma8WitnessData Dplanar connectedNoCut hmin
  noStart :
    M8ConstructionExplicitNoStartFields
      witness.toBoundaryLabelPackage.toM8LocalLabels

namespace M8FiniteLemma8NoStartData

variable (D : M8FiniteLemma8NoStartData Dplanar connectedNoCut hmin)

/-- The finite boundary-label certificate supplied by Lemma 8 witness data. -/
def finiteBoundaryLabelCertificate :
    M8FiniteBoundaryLabelCertificate Dplanar connectedNoCut hmin :=
  D.witness.toFiniteBoundaryLabelCertificate

/-- The boundary-label package supplied by Lemma 8 witness data. -/
def boundaryLabelPackage : M8BoundaryLabelPackage C :=
  D.witness.toBoundaryLabelPackage

/-- The local labels on which the Lemma 9 no-start fields are stated. -/
def localLabels : M8LocalLabels C :=
  D.boundaryLabelPackage.toM8LocalLabels

/-- The five no-start fields as concrete no-early triple exclusions. -/
def concreteNoEarlyTripleEquality :
    M8ConcreteNoEarlyTripleEquality D.localLabels.predicates.data :=
  D.noStart.toConcreteNoEarlyTripleEquality

/-- The abstract no-early predicate consumed by the late-triples bridge. -/
theorem noEarlyTripleEquality :
    M8NoEarlyTripleEquality D.localLabels.predicates.data :=
  D.concreteNoEarlyTripleEquality.toNoEarlyTripleEquality

/-- Construction-interface no-early triples from the five no-start fields. -/
def constructionNoEarlyTriples :
    M8ConstructionNoEarlyTriples D.localLabels :=
  D.noStart.constructionNoEarlyTriples

/-- Pipeline no-early triples from the same five no-start fields. -/
def pipelineNoEarlyTriples :
    M8PipelineNoEarlyTriples D.localLabels.predicates where
  noEarlyTripleEquality := D.noEarlyTripleEquality

/-- Construction-interface late triples obtained from Lemma 9 no-start data. -/
def lateTriples :
    M8LateTriples D.localLabels :=
  D.noStart.lateTriples

/-- Honest predicate-level late triples obtained from Lemma 9 no-start data. -/
theorem honestLateTriples :
    D.localLabels.predicates.LateTriples :=
  D.noStart.honestLateTriples

/-- Separated pipeline late-triples field obtained from Lemma 9 no-start
data. -/
def pipelineLateTriplesField :
    M8LateTriplesField D.localLabels.predicates :=
  D.pipelineNoEarlyTriples.toM8LateTriplesField

@[simp]
theorem concreteNoEarlyTripleEquality_no_start1 :
    D.concreteNoEarlyTripleEquality.no_start1 = D.noStart.no_start1 :=
  rfl

@[simp]
theorem concreteNoEarlyTripleEquality_no_start2 :
    D.concreteNoEarlyTripleEquality.no_start2 = D.noStart.no_start2 :=
  rfl

@[simp]
theorem concreteNoEarlyTripleEquality_no_start3 :
    D.concreteNoEarlyTripleEquality.no_start3 = D.noStart.no_start3 :=
  rfl

@[simp]
theorem concreteNoEarlyTripleEquality_no_start4 :
    D.concreteNoEarlyTripleEquality.no_start4 = D.noStart.no_start4 :=
  rfl

@[simp]
theorem concreteNoEarlyTripleEquality_no_start5 :
    D.concreteNoEarlyTripleEquality.no_start5 = D.noStart.no_start5 :=
  rfl

end M8FiniteLemma8NoStartData

/-- Arc Lemma 8 witness data plus no-start fields, expressed as the finite
Lemma 8/no-start bridge. -/
def M8ArcLemma8WitnessData.toFiniteLemma8NoStartData
    (W : M8ArcLemma8WitnessData Dplanar connectedNoCut hmin)
    (noStart : M8ConstructionExplicitNoStartFields W.localLabels) :
    M8FiniteLemma8NoStartData Dplanar connectedNoCut hmin where
  witness := W.toFiniteBoundaryLemma8WitnessData
  noStart := noStart

/-! ## Window/no-early fields before E22/E23 -/

/--
Finite Lemma 8 witness data, Lemma 9 no-start fields, turn bounds, and
Figure-containment window fields packaged at the point just before E22/E23 is
applied.
-/
structure M8FiniteLemma8NoStartWindowData
    (Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) where
  noStartData :
    M8FiniteLemma8NoStartData Dplanar connectedNoCut hmin
  turnBounds : M8TurnBounds
  windowFields :
    M8LocalWindowContainmentFields noStartData.localLabels turnBounds

namespace M8FiniteLemma8NoStartWindowData

variable (R :
  M8FiniteLemma8NoStartWindowData Dplanar connectedNoCut hmin)

/-- The local labels assembled from Lemma 8 witness data. -/
def localLabels : M8LocalLabels C :=
  R.noStartData.localLabels

/-- The no-early predicate obtained from Lemma 9 no-start data. -/
theorem noEarlyTripleEquality :
    M8NoEarlyTripleEquality R.localLabels.predicates.data :=
  R.noStartData.noEarlyTripleEquality

/-- Construction-interface late triples obtained before entering E22/E23. -/
def lateTriples : M8LateTriples R.localLabels :=
  R.noStartData.lateTriples

/-- Honest late triples obtained before entering E22/E23. -/
theorem honestLateTriples :
    R.localLabels.predicates.LateTriples :=
  R.noStartData.honestLateTriples

/-- Construction-interface window geometry from the supplied containment
fields. -/
def windowGeometry :
    M8WindowGeometry R.localLabels R.turnBounds :=
  R.windowFields.toM8WindowGeometry

/-- The same turn bounds in the separated pipeline format. -/
def pipelineTurnBounds :
    M8PipelineClosure.M8TurnBounds R.turnBounds.turn :=
  M8PipelineClosure.turnBounds_of_m8TurnBounds R.turnBounds

/-- The same window geometry in the separated pipeline format. -/
def pipelineWindowGeometry :
    M8PipelineClosure.M8WindowGeometry
      R.localLabels.predicates R.turnBounds.turn where
  figure8_separated := R.windowFields.figure8WindowGeometry
  figure9_adjacent_left := R.windowFields.figure9LeftWindowGeometry

/-- The strongest pre-E22/E23 package: window geometry plus no-early triples.
-/
def toM8WindowNoEarlyConstructionFields :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin where
  predicates := R.localLabels.predicates
  turn := R.turnBounds.turn
  turnBounds := R.pipelineTurnBounds
  windowGeometry := R.pipelineWindowGeometry
  noEarlyTripleEquality := R.noEarlyTripleEquality

/-- Forget the window/no-early package to direct E22/E23 plus no-early fields.
-/
def toM8E22E23NoEarlyConstructionFields :
    M8PipelineClosure.M8E22E23NoEarlyConstructionFields C hmin :=
  R.toM8WindowNoEarlyConstructionFields.toE22E23NoEarlyConstructionFields

/-- Forget the window/no-early package to separated construction fields. -/
def toM8SeparatedConstructionFields :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  R.toM8WindowNoEarlyConstructionFields.toSeparatedConstructionFields

/-- Clean construction-interface data using late triples derived from
Lemma 9 no-start fields. -/
def toM8ConstructionData :
    M8ConstructionData C hmin where
  localLabels := R.localLabels
  turnBounds := R.turnBounds
  lateTriples := R.lateTriples
  windowGeometry := R.windowGeometry

/-- The supplied containment fields give the honest E22/E23 hypotheses by the
checked W12 bridge. -/
theorem honestE22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        R.localLabels.predicates R.turnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        R.localLabels.predicates R.turnBounds.turn :=
  E22E23BridgeW12.honestE22_E23_of_localWindowContainmentFields
    R.windowFields

/-- A fixed minimal failure with the assembled window/no-early fields is
contradictory by the existing pipeline closure. -/
theorem contradiction
    (R :
      M8FiniteLemma8NoStartWindowData Dplanar connectedNoCut hmin) :
    False :=
  M8PipelineClosure.M8WindowNoEarlyConstructionFields.contradiction
    (toM8WindowNoEarlyConstructionFields R)

end M8FiniteLemma8NoStartWindowData

/--
Arc Lemma 8 witness data, Lemma 9 no-start fields, turn bounds, and window
fields packaged just before E22/E23.
-/
structure M8ArcLemma8NoStartWindowData
    (Dplanar : PlanarBoundaryClosure.PlanarBoundaryData.{u}
      (CanonicalUDGraph C))
    (connectedNoCut : PreconnectedNoCutVertexCertificate C)
    (hmin : IsMinimalClearedFailure C) where
  witness : M8ArcLemma8WitnessData Dplanar connectedNoCut hmin
  noStart : M8ConstructionExplicitNoStartFields witness.localLabels
  turnBounds : M8TurnBounds
  windowFields : M8LocalWindowContainmentFields witness.localLabels turnBounds

namespace M8ArcLemma8NoStartWindowData

variable (R :
  M8ArcLemma8NoStartWindowData Dplanar connectedNoCut hmin)

/-- Forget the boundary-arc metadata after it has produced the finite witness
and no-start bridge. -/
def toFiniteLemma8NoStartWindowData :
    M8FiniteLemma8NoStartWindowData Dplanar connectedNoCut hmin where
  noStartData := R.witness.toFiniteLemma8NoStartData R.noStart
  turnBounds := R.turnBounds
  windowFields := R.windowFields

/-- The arc-derived first endpoint remains the first local boundary label. -/
theorem localLabels_p_first :
    R.witness.localLabels.labels.p m8ArcFirstBoundaryIndex =
      R.witness.arc.leftEndpointVertex :=
  R.witness.localLabels_p_first

/-- The arc-derived last endpoint remains the last local boundary label. -/
theorem localLabels_p_last :
    R.witness.localLabels.labels.p m8ArcLastBoundaryIndex =
      R.witness.arc.rightEndpointVertex :=
  R.witness.localLabels_p_last

/-- Lemma 9 no-start fields give the construction-interface late triples. -/
def lateTriples :
    M8LateTriples R.witness.localLabels :=
  R.toFiniteLemma8NoStartWindowData.lateTriples

/-- Lemma 9 no-start fields give the honest late-triples predicate. -/
theorem honestLateTriples :
    R.witness.localLabels.predicates.LateTriples :=
  R.toFiniteLemma8NoStartWindowData.honestLateTriples

/-- Arc, Lemma 8, Lemma 9, and window containment give the pre-E22/E23
window/no-early package. -/
def toM8WindowNoEarlyConstructionFields :
    M8PipelineClosure.M8WindowNoEarlyConstructionFields C hmin :=
  R.toFiniteLemma8NoStartWindowData.toM8WindowNoEarlyConstructionFields

/-- Arc, Lemma 8, Lemma 9, and window containment give direct E22/E23 plus
no-early fields. -/
def toM8E22E23NoEarlyConstructionFields :
    M8PipelineClosure.M8E22E23NoEarlyConstructionFields C hmin :=
  R.toFiniteLemma8NoStartWindowData.toM8E22E23NoEarlyConstructionFields

/-- Arc, Lemma 8, Lemma 9, and window containment give clean construction
data. -/
def toM8ConstructionData :
    M8ConstructionData C hmin :=
  R.toFiniteLemma8NoStartWindowData.toM8ConstructionData

end M8ArcLemma8NoStartWindowData

end Lemma8Lemma9AssemblyW13
end Swanepoel
end ErdosProblems1066

end
