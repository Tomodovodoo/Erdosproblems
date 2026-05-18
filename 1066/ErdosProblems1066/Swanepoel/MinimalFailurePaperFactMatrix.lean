import ErdosProblems1066.Swanepoel.M8PaperFactsAssemblyRefined

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
* `RefinedReducerMatrix` and `RefinedUniformReducerMatrix` record the current
  source-refined third-wave theorem surfaces.

The projection lemmas below keep the rows honest: each reducer is tied back to
the field of `MinimalFailureM8PaperFacts` or
`MinimalFailureM8PaperFactsFamily`, or to the refined/remaining family
adapters that it actually consumes.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailurePaperFactMatrix

open MinimalFailureComponentPackage
open MinimalGraphFacts
open M8PaperFactsAssemblyRefined

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

/-- Local abbreviation for the concrete remaining package, where the no-early
triple field is the five concrete exclusions. -/
abbrev RemainingPaperFacts (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  MinimalFailureFactsFamilyConcrete.MinimalFailureM8RemainingPaperFacts C hmin

/-- Local abbreviation for the concrete remaining-facts family. -/
abbrev RemainingPaperFactsFamily :=
  MinimalFailureFactsFamilyConcrete.MinimalFailureM8RemainingPaperFactsFamily

/-- Local abbreviation for the shortest current source-facing fixed package:
the eight refined inputs remaining for one minimal cleared failure. -/
abbrev RefinedPaperFacts (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts C hmin

/-- Local abbreviation for the shortest current source-facing uniform package.

For each minimal cleared failure, this family supplies exactly the refined
input row:
`positiveCard`, `remainingNoCutSlack`, `arcBoundaryBudget`,
`spineCertificate`, `lemma8Existence`, `lemma9FiveStartLateFacts`,
`figure8EuclideanFacts`, and `figure9EuclideanFacts`.
-/
abbrev RefinedPaperFactsFamily :=
  M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily

/-- The shortest exact remaining input family currently known to imply the
conditional Swanepoel `8 / 31` target. -/
abbrev TargetLowerBoundEightThirtyOneInputs :=
  RefinedPaperFactsFamily

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

/-! ## Concrete remaining-facts matrix -/

/--
For one fixed minimal cleared failure, the concrete remaining-facts row records
the checked adapter from the five no-early triple exclusions into the older
paper-facts package.
-/
structure RemainingReducerMatrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  remaining : RemainingPaperFacts C hmin
  noEarlyTriples :
    M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples
      remaining.localLabels
  paper : PaperFacts C hmin
  componentPackage :
    M8SeparatedConstructionConcrete.M8SeparatedConstructionComponentPackage
      C hmin
  separatedFields : M8PipelineClosure.M8SeparatedConstructionFields C hmin

namespace RemainingReducerMatrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Build the concrete remaining-facts matrix from the explicit concrete
remaining package. -/
def ofRemainingPaperFacts (P : RemainingPaperFacts C hmin) :
    RemainingReducerMatrix C hmin where
  remaining := P
  noEarlyTriples := P.noEarlyTriples
  paper := P.toMinimalFailureM8PaperFacts
  componentPackage :=
    P.toMinimalFailureM8PaperFacts.toM8SeparatedConstructionComponentPackage
  separatedFields :=
    P.toMinimalFailureM8PaperFacts.toM8SeparatedConstructionFields

@[simp]
theorem ofRemainingPaperFacts_remaining
    (P : RemainingPaperFacts C hmin) :
    (ofRemainingPaperFacts P).remaining = P :=
  rfl

@[simp]
theorem ofRemainingPaperFacts_paper
    (P : RemainingPaperFacts C hmin) :
    (ofRemainingPaperFacts P).paper =
      P.toMinimalFailureM8PaperFacts :=
  rfl

end RemainingReducerMatrix

/-- The concrete no-early row consumes exactly the five-exclusion field. -/
theorem remaining_noEarlyTriples_consumes_concreteNoEarly
    (P : RemainingPaperFacts C hmin) :
    P.noEarlyTriples.noEarlyTripleEquality =
      P.noEarlyTripleEquality.toNoEarlyTripleEquality :=
  rfl

/-- Forgetting the concrete remaining row to the older paper-facts row keeps
the converted no-early-triples package and no extra input. -/
theorem remaining_toPaperFacts_consumes_noEarlyTriples
    (P : RemainingPaperFacts C hmin) :
    P.toMinimalFailureM8PaperFacts.noEarlyTriples =
      P.noEarlyTriples :=
  rfl

/-- A concrete remaining row closes a fixed minimal failure through the older
paper-facts contradiction adapter. -/
theorem remaining_contradiction_consumes_toPaperFacts
    (P : RemainingPaperFacts C hmin) :
    False :=
  P.toMinimalFailureM8PaperFacts.contradiction

/-! ## Source-refined third-wave matrix -/

/--
For one fixed minimal cleared failure, the refined matrix records the current
third-wave theorem surfaces and their checked direct adapter into
`M8ConstructionData`.
-/
structure RefinedReducerMatrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  refined : RefinedPaperFacts C hmin
  cutVertex : MinimalFailureCutVertexFacts C hmin
  spine :
    M8LabelsFromBoundaryInterface.M8BoundarySpine
      (M8LabelsFromBoundaryInterface.M8BoundaryCutDegreeContext.of_minimalClearedFailure
        refined.planarBoundary.core refined.cutVertex.preconnectedNoCut hmin)
  lemma8 : M8LabelsFromBoundaryInterface.M8Lemma8Combinatorics spine
  arc : M8TurnBoundsFromArc.NonconcaveArcTurnData
  turnBounds : M8ConstructionInterface.M8TurnBounds
  noEarlyTripleEquality :
    NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
      refined.localLabels.predicates.data
  noEarlyTriples :
    M8LateTriplesFromNoEarly.M8ConstructionNoEarlyTriples
      refined.localLabels
  lateTriples : M8ConstructionInterface.M8LateTriples refined.localLabels
  windowGeometry :
    M8ConstructionInterface.M8WindowGeometry refined.localLabels turnBounds
  constructionData : M8ConstructionInterface.M8ConstructionData C hmin

namespace RefinedReducerMatrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Build the refined matrix from the explicit source-refined paper package. -/
def ofRefinedPaperFacts (P : RefinedPaperFacts C hmin) :
    RefinedReducerMatrix C hmin where
  refined := P
  cutVertex := P.cutVertex
  spine := P.spine
  lemma8 := P.lemma8
  arc := P.arc
  turnBounds := P.turnBounds
  noEarlyTripleEquality := P.noEarlyTripleEquality
  noEarlyTriples := P.noEarlyTriples
  lateTriples := P.lateTriples
  windowGeometry := P.windowGeometry
  constructionData := P.toM8ConstructionData

@[simp]
theorem ofRefinedPaperFacts_refined
    (P : RefinedPaperFacts C hmin) :
    (ofRefinedPaperFacts P).refined = P :=
  rfl

@[simp]
theorem ofRefinedPaperFacts_constructionData
    (P : RefinedPaperFacts C hmin) :
    (ofRefinedPaperFacts P).constructionData =
      P.toM8ConstructionData :=
  rfl

end RefinedReducerMatrix

/-- The refined cut-vertex row consumes only positive cardinality and the
remaining no-cut slack input. -/
theorem refined_cutVertex_consumes_positiveCard_remainingSlack
    (P : RefinedPaperFacts C hmin) :
    P.cutVertex =
      { positiveCard := P.positiveCard
        remainingSlack := P.remainingNoCutSlack } :=
  rfl

/-- The refined boundary-spine row consumes the finite `p/q` spine
certificate. -/
theorem refined_spine_consumes_spineCertificate
    (P : RefinedPaperFacts C hmin) :
    P.spine =
      P.spineCertificate.toM8BoundarySpine
        P.cutVertex.preconnectedNoCut hmin :=
  rfl

/-- The refined Lemma 8 row consumes the current missing-existence package. -/
theorem refined_lemma8_consumes_lemma8Existence
    (P : RefinedPaperFacts C hmin) :
    P.lemma8 = P.lemma8Existence.toLemma8Combinatorics :=
  rfl

/-- The refined nonconcave-arc row consumes the geometric angle-facts package.
-/
theorem refined_arc_consumes_arcBoundaryBudget
    (P : RefinedPaperFacts C hmin) :
    P.arc = P.arcBoundaryBudget.toNonconcaveArcTurnData :=
  rfl

/-- The refined turn-bound row consumes the boundary-attached nonconcave arc
budget. -/
theorem refined_turnBounds_consumes_arcBoundaryBudget
    (P : RefinedPaperFacts C hmin) :
    P.turnBounds = P.arcBoundaryBudget.toM8TurnBounds :=
  rfl

/-- The refined no-early-triples row consumes the Lemma 9 five-start late
facts. -/
theorem refined_noEarly_consumes_lemma9FiveStartLateFacts
    (P : RefinedPaperFacts C hmin) :
    P.noEarlyTripleEquality =
      P.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality :=
  rfl

/-- The refined no-early-triples interface consumes the five concrete
exclusions. -/
theorem refined_noEarlyTriples_consumes_noEarlyTripleEquality
    (P : RefinedPaperFacts C hmin) :
    P.noEarlyTriples.noEarlyTripleEquality =
      P.noEarlyTripleEquality.toNoEarlyTripleEquality :=
  rfl

/-- The refined late-triples row consumes the no-early-triples interface. -/
theorem refined_lateTriples_consumes_noEarlyTriples
    (P : RefinedPaperFacts C hmin) :
    P.lateTriples = P.noEarlyTriples.toM8LateTriples :=
  rfl

/-- The refined window-geometry row consumes exactly the Figure 8 and Figure 9
Euclidean fact packages. -/
theorem refined_windowGeometry_consumes_figure8_figure9
    (P : RefinedPaperFacts C hmin) :
    P.windowGeometry =
      { figure8 :=
          MinimalFailureM8RefinedPaperFacts.figure8WindowGeometry_of_explicitEuclideanFacts
            (localLabels := P.localLabels) (turnBounds := P.turnBounds)
            P.figure8EuclideanFacts
        figure9_left :=
          MinimalFailureM8RefinedPaperFacts.figure9WindowGeometry_of_euclideanFactWitnesses
            (localLabels := P.localLabels) (turnBounds := P.turnBounds)
            P.figure9EuclideanFacts } :=
  rfl

/-- The refined construction-data row consumes labels, turn bounds,
late triples, and window geometry directly. -/
theorem refined_toM8ConstructionData_consumes_refined_outputs
    (P : RefinedPaperFacts C hmin) :
    P.toM8ConstructionData =
      { localLabels := P.localLabels
        turnBounds := P.turnBounds
        lateTriples := P.lateTriples
        windowGeometry := P.windowGeometry } :=
  rfl

/-- A refined row closes a fixed minimal failure through the checked
construction-data adapter. -/
theorem refined_contradiction_consumes_constructionData
    (P : RefinedPaperFacts C hmin) :
    False :=
  P.contradiction

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

/-! ## Uniform third-wave target matrix -/

/-- The concrete remaining-facts family consumes its `facts` field pointwise
when it forgets to the older paper-facts family. -/
theorem remaining_family_to_paperFamily_consumes_facts
    (H : RemainingPaperFactsFamily) {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    H.toMinimalFailureM8PaperFactsFamily.facts C hmin =
      (H.facts C hmin).toMinimalFailureM8PaperFacts :=
  rfl

/-- The refined family consumes its `facts` field pointwise when it builds the
construction-data eliminator. -/
theorem refined_family_to_constructionEliminator_consumes_facts
    (H : RefinedPaperFactsFamily) {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    H.toM8ConstructionEliminator C hmin =
      Nonempty.intro
        ((H.facts C hmin).toM8ConstructionData.toBrokenLatticeMinimalFailure) :=
  rfl

/-- The refined family rules out minimal cleared failures through the
construction-data eliminator. -/
theorem refined_family_noMinimalClearedFailure_consumes_eliminator
    (H : RefinedPaperFactsFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

/--
The uniform refined matrix records the currently shortest source-facing input
family and the checked construction-data adapter down to the final conditional
target.
-/
structure RefinedUniformReducerMatrix where
  inputs : TargetLowerBoundEightThirtyOneInputs
  constructionEliminator :
    BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator
  noMinimalClearedFailure :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C)
  targetLowerBoundEightThirtyOne :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne

namespace RefinedUniformReducerMatrix

/-- Build the third-wave uniform matrix from the exact remaining target-input
family. -/
def ofInputs
    (H : TargetLowerBoundEightThirtyOneInputs) :
    RefinedUniformReducerMatrix where
  inputs := H
  constructionEliminator := H.toM8ConstructionEliminator
  noMinimalClearedFailure := H.no_minimalClearedFailure
  targetLowerBoundEightThirtyOne := H.targetLowerBoundEightThirtyOne

@[simp]
theorem ofInputs_inputs
    (H : TargetLowerBoundEightThirtyOneInputs) :
    (ofInputs H).inputs = H :=
  rfl

@[simp]
theorem ofInputs_constructionEliminator
    (H : TargetLowerBoundEightThirtyOneInputs) {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    (ofInputs H).constructionEliminator C hmin =
      H.toM8ConstructionEliminator C hmin :=
  rfl

end RefinedUniformReducerMatrix

/-- The exact remaining target-input family is the refined family; the final
target remains conditional on supplying that family. -/
theorem targetLowerBoundEightThirtyOne_consumes_exact_inputs
    (H : TargetLowerBoundEightThirtyOneInputs) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

/-- Pointwise form of the exact remaining target-input list. -/
def targetLowerBoundEightThirtyOne_inputs_pointwise
    (H : TargetLowerBoundEightThirtyOneInputs) {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts C hmin :=
  H.facts C hmin

end

end MinimalFailurePaperFactMatrix
end Swanepoel
end ErdosProblems1066
