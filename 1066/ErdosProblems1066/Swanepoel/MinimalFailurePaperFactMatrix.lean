import ErdosProblems1066.Swanepoel.MinimalFailureComponentPackage

set_option autoImplicit false

/-!
# Matrix of remaining minimal-failure paper facts

This file is build-checked documentation for the remaining Swanepoel
minimal-failure inputs.  It does not assert that those inputs exist.

The matrix has two levels:

* `FixedReducerMatrix` records, for one fixed minimal cleared failure, the
  currently checked reducers that consume the supplied paper fields.
* `UniformReducerMatrix` records the uniform family route to the existing
  conditional target.

The projection lemmas below keep the rows honest: each reducer is tied back to
the field of `MinimalFailureM8PaperFacts` or
`MinimalFailureM8PaperFactsFamily` that it actually consumes.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailurePaperFactMatrix

open MinimalFailureComponentPackage
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- Local abbreviation for the one-failure package whose fields remain
paper-supplied. -/
abbrev PaperFacts (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  MinimalFailureM8PaperFacts C hmin

/-- Local abbreviation for the uniform package of remaining paper-supplied
facts. -/
abbrev PaperFactsFamily :=
  MinimalFailureM8PaperFactsFamily

/-! ## Fixed minimal-failure matrix -/

/--
For one fixed minimal cleared failure, the current checked reducers consume
the supplied paper facts into these downstream packages.

This is a matrix row bundle, not a constructor for the missing geometry: the
only constructor provided here, `ofPaperFacts`, requires the original
`MinimalFailureM8PaperFacts` package first.
-/
structure FixedReducerMatrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  paper : PaperFacts C hmin
  connectedDegreeRange : CutVertexFinal.ConnectedDegreeRangeCertificate C
  connectedNoCutDegreeRange :
    CutVertexFinal.ConnectedNoCutDegreeRangeCertificate C
  preconnectedNoCut :
    CutVertexClosure.PreconnectedNoCutVertexCertificate C
  concreteFaceCountingData :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      paper.planarBoundary
  faceCountingTheorems :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      paper.planarBoundary
  boundaryLabels : M8BoundaryLabelsConcrete.M8BoundaryLabelPackage C
  localLabels : M8ConstructionInterface.M8LocalLabels C
  turnBounds : M8ConstructionInterface.M8TurnBounds
  lateTriples : M8ConstructionInterface.M8LateTriples localLabels
  windowGeometry :
    M8ConstructionInterface.M8WindowGeometry localLabels turnBounds
  constructionData : M8ConstructionInterface.M8ConstructionData C hmin
  componentPackage :
    M8SeparatedConstructionConcrete.M8SeparatedConstructionComponentPackage
      C hmin
  separatedFields : M8PipelineClosure.M8SeparatedConstructionFields C hmin

namespace FixedReducerMatrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Build the fixed matrix from the explicit one-failure paper package. -/
def ofPaperFacts (P : PaperFacts C hmin) :
    FixedReducerMatrix C hmin where
  paper := P
  connectedDegreeRange := P.cutVertex.connectedDegreeRange
  connectedNoCutDegreeRange := P.connectedNoCutDegreeRange
  preconnectedNoCut := P.cutVertex.preconnectedNoCut
  concreteFaceCountingData := P.concreteFaceCountingData
  faceCountingTheorems := P.faceCountingTheorems
  boundaryLabels := P.boundaryLabels
  localLabels := P.localLabels
  turnBounds := P.turnBounds
  lateTriples := P.lateTriples
  windowGeometry := P.windowGeometry
  constructionData := P.toM8ConstructionData
  componentPackage := P.toM8SeparatedConstructionComponentPackage
  separatedFields := P.toM8SeparatedConstructionFields

@[simp]
theorem ofPaperFacts_paper (P : PaperFacts C hmin) :
    (ofPaperFacts P).paper = P :=
  rfl

@[simp]
theorem ofPaperFacts_componentPackage (P : PaperFacts C hmin) :
    (ofPaperFacts P).componentPackage =
      P.toM8SeparatedConstructionComponentPackage :=
  rfl

@[simp]
theorem ofPaperFacts_separatedFields (P : PaperFacts C hmin) :
    (ofPaperFacts P).separatedFields =
      P.toM8SeparatedConstructionFields :=
  rfl

end FixedReducerMatrix

/-! ## Checked consumer rows for the fixed package -/

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The connected/degree reducer uses the positive-cardinality field of the
cut-vertex row. -/
theorem connectedDegreeRange_consumes_positiveCard
    (K : MinimalFailureCutVertexFacts C hmin) :
    K.connectedDegreeRange =
      CutVertexFinal.connectedDegreeRangeCertificate_of_minimalFailure
        (C := C) K.positiveCard hmin :=
  rfl

/-- The connected/no-cut/degree reducer uses the positive-cardinality field and
the remaining cut-vertex slack field. -/
theorem connectedNoCutDegreeRange_consumes_remainingSlack
    (K : MinimalFailureCutVertexFacts C hmin) :
    K.connectedNoCutDegreeRange =
      CutVertexFinal.connectedNoCutDegreeRangeCertificate_of_minimalFailure_remainingSlack
        (C := C) K.positiveCard hmin K.remainingSlack :=
  rfl

/-- The preconnected/no-cut reducer is the projection of the checked
connected/no-cut/degree package. -/
theorem preconnectedNoCut_consumes_connectedNoCutDegreeRange
    (K : MinimalFailureCutVertexFacts C hmin) :
    K.preconnectedNoCut.noCutVertex =
      K.connectedNoCutDegreeRange.noCutVertex :=
  rfl

/-- The face-counting data reducer consumes the planar-boundary field. -/
theorem concreteFaceCountingData_consumes_planarBoundary
    (P : PaperFacts C hmin) :
    P.concreteFaceCountingData =
      PlanarBoundaryFinal.PlanarBoundaryData.concreteFaceCountingData
        P.planarBoundary :=
  rfl

/-- The proposition-valued face-counting reducer consumes the same
planar-boundary field. -/
theorem faceCountingTheorems_consumes_planarBoundary
    (P : PaperFacts C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      P.planarBoundary :=
  P.faceCountingTheorems

/-- Boundary labels consume the planar boundary core, the cut-vertex/no-cut
projection, the boundary spine, and the Lemma 8 combinatorics field. -/
theorem boundaryLabels_consumes_boundary_spine_lemma8
    (P : PaperFacts C hmin) :
    P.boundaryLabels =
      M8BoundaryLabelsConcrete.M8BoundaryLabelPackage.ofMinimalClearedFailure
        P.planarBoundary.core P.cutVertex.preconnectedNoCut hmin
        P.spine P.lemma8 :=
  rfl

/-- Local labels are the local-label projection of the boundary-label row. -/
theorem localLabels_consumes_boundaryLabels
    (P : PaperFacts C hmin) :
    P.localLabels = P.boundaryLabels.toM8LocalLabels :=
  rfl

/-- The turn-bound reducer consumes the nonconcave-arc field. -/
theorem turnBounds_consumes_arc
    (P : PaperFacts C hmin) :
    P.turnBounds = M8TurnBoundsConcrete.m8TurnBounds P.arc :=
  rfl

/-- The late-triples reducer consumes the no-early-triples field. -/
theorem lateTriples_consumes_noEarlyTriples
    (P : PaperFacts C hmin) :
    M8ConstructionInterface.M8LateTriples P.localLabels :=
  P.noEarlyTriples.toM8LateTriples

/-- The window-geometry reducer consumes the Figure 8/Figure 9 containment
field. -/
theorem windowGeometry_consumes_windowContainment
    (P : PaperFacts C hmin) :
    M8ConstructionInterface.M8WindowGeometry P.localLabels P.turnBounds :=
  P.windowContainment.toM8WindowGeometry

/-- The construction-data reducer consumes the label, turn, late-triples, and
window-geometry reducers. -/
theorem constructionData_consumes_reducer_outputs
    (P : PaperFacts C hmin) :
    P.toM8ConstructionData =
      P.boundaryLabels.toM8ConstructionData
        P.turnBounds P.lateTriples P.windowGeometry :=
  rfl

/-- The separated component package keeps exactly the boundary-label, arc,
no-early-triples, and containment rows. -/
theorem componentPackage_consumes_explicit_fields
    (P : PaperFacts C hmin) :
    P.toM8SeparatedConstructionComponentPackage =
      { labels := P.boundaryLabels.toLabelsFromBoundaryData
        arc := P.arc
        noEarlyTriples := P.noEarlyTriples
        windowContainment := P.windowContainment } :=
  rfl

@[simp]
theorem componentPackage_labels
    (P : PaperFacts C hmin) :
    P.toM8SeparatedConstructionComponentPackage.labels =
      P.boundaryLabels.toLabelsFromBoundaryData :=
  rfl

@[simp]
theorem componentPackage_arc
    (P : PaperFacts C hmin) :
    P.toM8SeparatedConstructionComponentPackage.arc = P.arc :=
  rfl

/-- The separated fields consumed by the final pipeline are obtained from the
component package, not from any hidden theorem. -/
theorem separatedFields_consumes_componentPackage
    (P : PaperFacts C hmin) :
    P.toM8SeparatedConstructionFields =
      P.toM8SeparatedConstructionComponentPackage.toM8SeparatedConstructionFields :=
  rfl

@[simp]
theorem separatedFields_predicates
    (P : PaperFacts C hmin) :
    P.toM8SeparatedConstructionFields.predicates =
      P.localLabels.predicates :=
  rfl

@[simp]
theorem separatedFields_turn
    (P : PaperFacts C hmin) :
    P.toM8SeparatedConstructionFields.turn = P.arc.turn :=
  rfl

/-- The no-early-triples field also supplies the honest late-triples field
appearing in the separated pipeline. -/
theorem separatedFields_lateTriples_consumes_noEarlyTriples
    (P : PaperFacts C hmin) :
    P.localLabels.predicates.LateTriples :=
  P.noEarlyTriples.toHonestLateTriples

/-! ## Uniform minimal-failure matrix -/

/--
The uniform matrix records the checked reducers available from a uniform
supplier of the remaining paper facts.

As above, this is conditional documentation: `ofFamily` requires the family of
paper facts and then records the checked consumers.
-/
structure UniformReducerMatrix where
  family : PaperFactsFamily
  separatedComponents :
    M8SeparatedConstructionConcrete.M8SeparatedConstructionComponents
  noMinimalClearedFailure :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C)
  targetLowerBoundEightThirtyOne :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

namespace UniformReducerMatrix

/-- Build the uniform matrix from the uniform paper-fact family. -/
def ofFamily (H : PaperFactsFamily) : UniformReducerMatrix where
  family := H
  separatedComponents := H.toSeparatedConstructionComponents
  noMinimalClearedFailure := H.no_minimalClearedFailure
  targetLowerBoundEightThirtyOne := H.targetLowerBoundEightThirtyOne

@[simp]
theorem ofFamily_family (H : PaperFactsFamily) :
    (ofFamily H).family = H :=
  rfl

@[simp]
theorem ofFamily_separatedComponents (H : PaperFactsFamily) :
    (ofFamily H).separatedComponents =
      H.toSeparatedConstructionComponents :=
  rfl

end UniformReducerMatrix

/-- The uniform component reducer consumes the `facts` field pointwise. -/
theorem family_componentPackage_consumes_facts
    (H : PaperFactsFamily) {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    H.toSeparatedConstructionComponents.componentPackage C hmin =
      (H.facts C hmin).toM8SeparatedConstructionComponentPackage :=
  rfl

/-- The uniform no-minimal-failure reducer consumes the component-family
reducer. -/
theorem family_noMinimalClearedFailure_consumes_facts
    (H : PaperFactsFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

/-- The current final conditional Swanepoel target consumes the same uniform
paper-fact family through the component reducer. -/
theorem family_target_consumes_facts
    (H : PaperFactsFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

end

end MinimalFailurePaperFactMatrix
end Swanepoel
end ErdosProblems1066
