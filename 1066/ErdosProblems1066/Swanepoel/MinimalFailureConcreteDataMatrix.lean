import ErdosProblems1066.Swanepoel.M8PaperFactsAssemblyRefined
import ErdosProblems1066.Swanepoel.MinimalConnectednessClosure

set_option autoImplicit false

/-!
# Concrete minimal-failure data matrix

This file is an audit layer for the current Swanepoel minimal-failure route.
It separates the data that is already derivable from a minimal cleared failure
from the remaining source facts that still have to be supplied.

The only source-facing obligations in this file are:

* remaining no-cut slack;
* boundary-attached nonconcave-arc budget data;
* a finite boundary-spine certificate;
* Lemma 8 existence data;
* Lemma 9 five-start late facts;
* Figure 8 Euclidean facts;
* Figure 9 Euclidean facts.

The positive-cardinality field is not an obligation here: it is proved from
minimality.  All other fields in `ConcreteDerivedFieldMatrix` are checked
projections from those obligations through the existing refined assembly.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureConcreteDataMatrix

open BoundarySpineFiniteCertificate
open CutVertexFinal
open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open Lemma8ExistenceConcrete
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8LateTriplesFromNoEarly
open M8PaperFactsAssemblyRefined
open M8TurnBoundsFromArc
open MinimalFailureComponentPackage
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-- Local abbreviation for the canonical graph attached to a configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  M8PaperFactsAssemblyRefined.CanonicalGraph C

/-- Local abbreviation for the refined one-failure row consumed downstream. -/
abbrev RefinedPaperFacts (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :=
  M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts C hmin

/-- Local abbreviation for the refined uniform family consumed downstream. -/
abbrev RefinedPaperFactsFamily :=
  M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily

/-! ## Derived minimality field -/

/-- The positive-cardinality field appearing in the refined row. -/
abbrev PositiveCardField (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) : Prop :=
  0 < n

/-- A minimal cleared failure has positive cardinality, so this field is
derivable and is not listed as a remaining paper obligation below. -/
theorem positiveCard_of_minimalClearedFailure
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C) :
    PositiveCardField C hmin := by
  cases n with
  | zero =>
      have hfin : Nonempty (Fin 0) :=
        MinimalConnectednessClosure.fin_nonempty_of_minimalClearedFailure
          (C := C) hmin
      cases hfin with
      | intro i => exact Fin.elim0 i
  | succ n =>
      exact Nat.succ_pos n

/-! ## Named source obligations -/

/-- Obligation S8.1: the exact no-cut slack package still needed by the
cut-vertex route. -/
abbrev RemainingNoCutSlackObligation (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) :=
  CutVertexFinal.RemainingNoCutSlackFact C

/-- Obligation S8.2: boundary data together with the selected nonconcave arc
and its angle budget. -/
abbrev ArcBoundaryBudgetObligation (C : _root_.UDConfig n)
    (_hmin : IsMinimalClearedFailure C) :=
  NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C)

/-- The cut-vertex package derived from minimality and the remaining no-cut
slack obligation. -/
def cutVertexOfObligations {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard := positiveCard_of_minimalClearedFailure hmin
  remainingSlack := remainingNoCutSlack

/-- Obligation S8.3: a finite `p/q` spine certificate for the supplied
boundary-budget row. -/
abbrev SpineCertificateObligation {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin) :=
  M8FinitePQSpineCertificate arcBoundaryBudget.planarBoundary

/-- Boundary spine derived from the finite certificate, positive-cardinality
proof, and no-cut slack obligation. -/
def spineOfObligations {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        arcBoundaryBudget.planarBoundary.core
        (cutVertexOfObligations hmin remainingNoCutSlack).preconnectedNoCut
        hmin) :=
  spineCertificate.toM8BoundarySpine
    (cutVertexOfObligations hmin remainingNoCutSlack).preconnectedNoCut hmin

/-- Obligation S8.4: the remaining Lemma 8 existence package for the derived
boundary spine. -/
abbrev Lemma8ExistenceObligation {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget) :=
  M8Lemma8MissingExistenceConditions
    (spineOfObligations hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate)

/-- Lemma 8 combinatorics derived from the Lemma 8 existence obligation. -/
def lemma8OfObligations {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget)
    (lemma8Existence :
      Lemma8ExistenceObligation hmin remainingNoCutSlack
        arcBoundaryBudget spineCertificate) :
    M8Lemma8Combinatorics
      (spineOfObligations hmin remainingNoCutSlack arcBoundaryBudget
        spineCertificate) :=
  lemma8Existence.toLemma8Combinatorics

/-- Boundary labels derived from the boundary, spine, and Lemma 8 rows. -/
def boundaryLabelsOfObligations {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget)
    (lemma8Existence :
      Lemma8ExistenceObligation hmin remainingNoCutSlack
        arcBoundaryBudget spineCertificate) :
    M8BoundaryLabelPackage C :=
  M8BoundaryLabelPackage.ofMinimalClearedFailure
    arcBoundaryBudget.planarBoundary.core
    (cutVertexOfObligations hmin remainingNoCutSlack).preconnectedNoCut hmin
    (spineOfObligations hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate)
    (lemma8OfObligations hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate lemma8Existence)

/-- Local labels derived from the boundary-label package. -/
def localLabelsOfObligations {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget)
    (lemma8Existence :
      Lemma8ExistenceObligation hmin remainingNoCutSlack
        arcBoundaryBudget spineCertificate) :
    M8LocalLabels C :=
  (boundaryLabelsOfObligations hmin remainingNoCutSlack arcBoundaryBudget
    spineCertificate lemma8Existence).toM8LocalLabels

/-- Obligation S8.5: Lemma 9 five-start late facts for the derived local
labels. -/
abbrev Lemma9FiveStartLateObligation {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget)
    (lemma8Existence :
      Lemma8ExistenceObligation hmin remainingNoCutSlack
        arcBoundaryBudget spineCertificate) :=
  M8Lemma9FiveStartLateFacts
    (localLabelsOfObligations hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate lemma8Existence).predicates.data

/-- Obligation S8.6: Figure 8 Euclidean facts for the derived local labels and
turn bounds. -/
abbrev Figure8EuclideanObligation {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget)
    (lemma8Existence :
      Lemma8ExistenceObligation hmin remainingNoCutSlack
        arcBoundaryBudget spineCertificate) :=
  HonestFigure8ExplicitEuclideanFacts
    (localLabelsOfObligations hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate lemma8Existence).predicates
    arcBoundaryBudget.toM8TurnBounds.turn

/-- Obligation S8.7: Figure 9 Euclidean facts for the derived local labels and
turn bounds. -/
abbrev Figure9EuclideanObligation {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    (remainingNoCutSlack : RemainingNoCutSlackObligation C hmin)
    (arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin)
    (spineCertificate : SpineCertificateObligation arcBoundaryBudget)
    (lemma8Existence :
      Lemma8ExistenceObligation hmin remainingNoCutSlack
        arcBoundaryBudget spineCertificate) :=
  HonestFigure9AdjacentLeftEuclideanFactWitnesses
    (localLabelsOfObligations hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate lemma8Existence).predicates
    arcBoundaryBudget.toM8TurnBounds.turn

/-! ## Source-obligation row -/

/-- The exact remaining source obligations for one minimal cleared failure.

The positive-cardinality field is intentionally absent: it is derived by
`positiveCard_of_minimalClearedFailure`.
-/
structure MinimalFailureConcreteObligations
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  remainingNoCutSlack : RemainingNoCutSlackObligation C hmin
  arcBoundaryBudget : ArcBoundaryBudgetObligation C hmin
  spineCertificate : SpineCertificateObligation arcBoundaryBudget
  lemma8Existence :
    Lemma8ExistenceObligation hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate
  lemma9FiveStartLateFacts :
    Lemma9FiveStartLateObligation hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate lemma8Existence
  figure8EuclideanFacts :
    Figure8EuclideanObligation hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate lemma8Existence
  figure9EuclideanFacts :
    Figure9EuclideanObligation hmin remainingNoCutSlack arcBoundaryBudget
      spineCertificate lemma8Existence

namespace MinimalFailureConcreteObligations

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The positive-cardinality field derived from minimality. -/
def positiveCard (_P : MinimalFailureConcreteObligations C hmin) :
    PositiveCardField C hmin :=
  positiveCard_of_minimalClearedFailure hmin

/-- The cut-vertex package derived from minimality plus no-cut slack. -/
def cutVertex (P : MinimalFailureConcreteObligations C hmin) :
    MinimalFailureCutVertexFacts C hmin :=
  cutVertexOfObligations hmin P.remainingNoCutSlack

/-- Boundary spine derived from the finite certificate. -/
def spine (P : MinimalFailureConcreteObligations C hmin) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        P.arcBoundaryBudget.planarBoundary.core P.cutVertex.preconnectedNoCut
        hmin) :=
  spineOfObligations hmin P.remainingNoCutSlack P.arcBoundaryBudget
    P.spineCertificate

/-- Lemma 8 combinatorics derived from the Lemma 8 existence obligation. -/
def lemma8 (P : MinimalFailureConcreteObligations C hmin) :
    M8Lemma8Combinatorics P.spine :=
  P.lemma8Existence.toLemma8Combinatorics

/-- Boundary labels derived from the boundary, spine, and Lemma 8 rows. -/
def boundaryLabels (P : MinimalFailureConcreteObligations C hmin) :
    M8BoundaryLabelPackage C :=
  M8BoundaryLabelPackage.ofMinimalClearedFailure
    P.arcBoundaryBudget.planarBoundary.core P.cutVertex.preconnectedNoCut hmin
    P.spine P.lemma8

/-- Local labels derived from boundary labels. -/
def localLabels (P : MinimalFailureConcreteObligations C hmin) :
    M8LocalLabels C :=
  P.boundaryLabels.toM8LocalLabels

/-- Adapter to the refined row currently consumed by the final conditional
composition. -/
def toRefinedPaperFacts
    (P : MinimalFailureConcreteObligations C hmin) :
    RefinedPaperFacts C hmin where
  positiveCard := P.positiveCard
  remainingNoCutSlack := P.remainingNoCutSlack
  arcBoundaryBudget := P.arcBoundaryBudget
  spineCertificate := P.spineCertificate
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  figure8EuclideanFacts := P.figure8EuclideanFacts
  figure9EuclideanFacts := P.figure9EuclideanFacts

@[simp]
theorem toRefinedPaperFacts_positiveCard
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.positiveCard =
      positiveCard_of_minimalClearedFailure hmin :=
  rfl

@[simp]
theorem toRefinedPaperFacts_remainingNoCutSlack
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.remainingNoCutSlack = P.remainingNoCutSlack :=
  rfl

@[simp]
theorem toRefinedPaperFacts_arcBoundaryBudget
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.arcBoundaryBudget = P.arcBoundaryBudget :=
  rfl

@[simp]
theorem toRefinedPaperFacts_spineCertificate
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.spineCertificate = P.spineCertificate :=
  rfl

@[simp]
theorem toRefinedPaperFacts_lemma8Existence
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.lemma8Existence = P.lemma8Existence :=
  rfl

@[simp]
theorem toRefinedPaperFacts_lemma9FiveStartLateFacts
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.lemma9FiveStartLateFacts =
      P.lemma9FiveStartLateFacts :=
  rfl

@[simp]
theorem toRefinedPaperFacts_figure8EuclideanFacts
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.figure8EuclideanFacts =
      P.figure8EuclideanFacts :=
  rfl

@[simp]
theorem toRefinedPaperFacts_figure9EuclideanFacts
    (P : MinimalFailureConcreteObligations C hmin)
    {i : Nat} (hi : 1 <= i) (hi_next : i + 1 <= 10)
    (hbad_i :
      Not (Lemma10Bridge.M8BrokenLatticeGood
        P.toRefinedPaperFacts.localLabels.predicates.data i))
    (hbad_next :
      Not (Lemma10Bridge.M8BrokenLatticeGood
        P.toRefinedPaperFacts.localLabels.predicates.data (i + 1))) :
    P.toRefinedPaperFacts.figure9EuclideanFacts
        hi hi_next hbad_i hbad_next =
      P.figure9EuclideanFacts hi hi_next hbad_i hbad_next :=
  rfl

/-- The cut-vertex row consumes only derived positive cardinality and the
remaining no-cut slack obligation. -/
theorem cutVertex_consumes_positiveCard_remainingSlack
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.cutVertex =
      { positiveCard := positiveCard_of_minimalClearedFailure hmin
        remainingSlack := P.remainingNoCutSlack } :=
  rfl

/-- The planar-boundary row is part of the nonconcave-arc budget obligation. -/
theorem planarBoundary_consumes_arcBoundaryBudget
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.planarBoundary =
      P.arcBoundaryBudget.planarBoundary :=
  rfl

/-- The turn-bound row is derived from the nonconcave-arc budget obligation. -/
theorem turnBounds_consumes_arcBoundaryBudget
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.turnBounds =
      P.arcBoundaryBudget.toM8TurnBounds :=
  rfl

/-- The concrete no-early-triple row is derived from the Lemma 9 obligation. -/
theorem noEarlyTripleEquality_consumes_lemma9
    (P : MinimalFailureConcreteObligations C hmin) :
    P.toRefinedPaperFacts.noEarlyTripleEquality =
      P.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality :=
  rfl

/-- The fixed minimal failure closes through the checked refined assembly once
the source-obligation row is supplied. -/
theorem contradiction
    (P : MinimalFailureConcreteObligations C hmin) :
    False :=
  P.toRefinedPaperFacts.contradiction

end MinimalFailureConcreteObligations

/-! ## Derived field matrix -/

/-- The concrete data matrix for one minimal cleared failure.

The `obligations` field is the only source-facing input.  All other fields are
checked derivations from it, recorded to make final composition auditable.
-/
structure ConcreteDerivedFieldMatrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  obligations : MinimalFailureConcreteObligations C hmin
  positiveCard : PositiveCardField C hmin
  refined : RefinedPaperFacts C hmin
  cutVertex : MinimalFailureCutVertexFacts C hmin
  connectedDegreeRange : CutVertexFinal.ConnectedDegreeRangeCertificate C
  connectedNoCutDegreeRange :
    CutVertexFinal.ConnectedNoCutDegreeRangeCertificate C
  preconnectedNoCut :
    CutVertexClosure.PreconnectedNoCutVertexCertificate C
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)
  boundaryLabels : M8BoundaryLabelPackage C
  localLabels : M8LocalLabels C
  arc : NonconcaveArcTurnData
  turnBounds : M8TurnBounds
  noEarlyTripleEquality :
    M8ConcreteNoEarlyTripleEquality localLabels.predicates.data
  noEarlyTriples : M8ConstructionNoEarlyTriples localLabels
  lateTriples : M8LateTriples localLabels
  windowGeometry : M8WindowGeometry localLabels turnBounds
  constructionData : M8ConstructionData C hmin

namespace ConcreteDerivedFieldMatrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Build the matrix from the explicit source obligations. -/
def ofObligations
    (P : MinimalFailureConcreteObligations C hmin) :
    ConcreteDerivedFieldMatrix C hmin where
  obligations := P
  positiveCard := P.positiveCard
  refined := P.toRefinedPaperFacts
  cutVertex := P.toRefinedPaperFacts.cutVertex
  connectedDegreeRange := P.toRefinedPaperFacts.cutVertex.connectedDegreeRange
  connectedNoCutDegreeRange :=
    P.toRefinedPaperFacts.cutVertex.connectedNoCutDegreeRange
  preconnectedNoCut := P.toRefinedPaperFacts.cutVertex.preconnectedNoCut
  planarBoundary := P.toRefinedPaperFacts.planarBoundary
  boundaryLabels := P.toRefinedPaperFacts.boundaryLabels
  localLabels := P.toRefinedPaperFacts.localLabels
  arc := P.toRefinedPaperFacts.arc
  turnBounds := P.toRefinedPaperFacts.turnBounds
  noEarlyTripleEquality := P.toRefinedPaperFacts.noEarlyTripleEquality
  noEarlyTriples := P.toRefinedPaperFacts.noEarlyTriples
  lateTriples := P.toRefinedPaperFacts.lateTriples
  windowGeometry := P.toRefinedPaperFacts.windowGeometry
  constructionData := P.toRefinedPaperFacts.toM8ConstructionData

@[simp]
theorem ofObligations_obligations
    (P : MinimalFailureConcreteObligations C hmin) :
    (ofObligations P).obligations = P :=
  rfl

@[simp]
theorem ofObligations_positiveCard
    (P : MinimalFailureConcreteObligations C hmin) :
    (ofObligations P).positiveCard =
      positiveCard_of_minimalClearedFailure hmin :=
  rfl

@[simp]
theorem ofObligations_refined
    (P : MinimalFailureConcreteObligations C hmin) :
    (ofObligations P).refined = P.toRefinedPaperFacts :=
  rfl

@[simp]
theorem ofObligations_cutVertex
    (P : MinimalFailureConcreteObligations C hmin) :
    (ofObligations P).cutVertex = P.toRefinedPaperFacts.cutVertex :=
  rfl

@[simp]
theorem ofObligations_planarBoundary
    (P : MinimalFailureConcreteObligations C hmin) :
    (ofObligations P).planarBoundary =
      P.arcBoundaryBudget.planarBoundary :=
  rfl

@[simp]
theorem ofObligations_turnBounds
    (P : MinimalFailureConcreteObligations C hmin) :
    (ofObligations P).turnBounds = P.arcBoundaryBudget.toM8TurnBounds :=
  rfl

@[simp]
theorem ofObligations_constructionData
    (P : MinimalFailureConcreteObligations C hmin) :
    (ofObligations P).constructionData =
      P.toRefinedPaperFacts.toM8ConstructionData :=
  rfl

/-- The matrix is contradiction-producing through the checked refined route;
it does not assert any obligation exists. -/
theorem contradiction
    (M : ConcreteDerivedFieldMatrix C hmin) :
    False :=
  M.refined.contradiction

end ConcreteDerivedFieldMatrix

/-! ## Uniform family for final composition -/

/-- Uniform source obligations for every minimal cleared failure. -/
structure MinimalFailureConcreteObligationFamily where
  obligations :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        MinimalFailureConcreteObligations C hmin

namespace MinimalFailureConcreteObligationFamily

/-- Convert the concrete obligation family to the existing refined family. -/
def toRefinedPaperFactsFamily
    (H : MinimalFailureConcreteObligationFamily) :
    RefinedPaperFactsFamily where
  facts := fun C hmin =>
    (H.obligations C hmin).toRefinedPaperFacts

/-- Pointwise matrix derived from a uniform obligation family. -/
def matrix (H : MinimalFailureConcreteObligationFamily)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    ConcreteDerivedFieldMatrix C hmin :=
  ConcreteDerivedFieldMatrix.ofObligations (H.obligations C hmin)

@[simp]
theorem toRefinedPaperFactsFamily_facts
    (H : MinimalFailureConcreteObligationFamily)
    {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C) :
    H.toRefinedPaperFactsFamily.facts C hmin =
      (H.obligations C hmin).toRefinedPaperFacts :=
  rfl

/-- A uniform concrete obligation family rules out all minimal cleared
failures through the checked refined route. -/
theorem no_minimalClearedFailure
    (H : MinimalFailureConcreteObligationFamily) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toRefinedPaperFactsFamily.no_minimalClearedFailure

/-- Final conditional Swanepoel target from the concrete obligation family. -/
theorem targetLowerBoundEightThirtyOne
    (H : MinimalFailureConcreteObligationFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toRefinedPaperFactsFamily.targetLowerBoundEightThirtyOne

end MinimalFailureConcreteObligationFamily

/-- Top-level theorem form for final composition. -/
theorem targetLowerBoundEightThirtyOne_of_concreteObligationFamily
    (H : MinimalFailureConcreteObligationFamily) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

end

end MinimalFailureConcreteDataMatrix
end Swanepoel
end ErdosProblems1066
