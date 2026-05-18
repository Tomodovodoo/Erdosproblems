import ErdosProblems1066.Swanepoel.BoundaryLabelCertificateAssembly
import ErdosProblems1066.Swanepoel.Lemma8NeighborExtractionConcrete
import ErdosProblems1066.Swanepoel.Lemma10Inequalities
import ErdosProblems1066.Swanepoel.M8MinimalFailureEliminatorInterface
import ErdosProblems1066.Swanepoel.M8TurnBoundsConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureComponentPackage
import ErdosProblems1066.Swanepoel.NoEarlyTripleObstructionConcrete
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Concrete inputs for the refined `m = 8` row

This module fills the pipeline-facing refined M8 row from the strongest
checked projections currently available.

The base row consumes real source data: cut/no-cut slack, a boundary-attached
nonconcave-arc budget, finite boundary labels, and the concrete Lemma 8
missing-existence package.  From those it constructs the downstream
`localLabels` and normalized `arc` fields of
`M8PipelineRefinedFactMatrixRow`.

Two no-early refinements then fill the concrete no-early field either from
Lemma 9 five-start late facts or from a K23 obstruction plus the existing
unit-distance finite local exclusions.  The only field still exposed at the
pipeline row level is Figure 8/Figure 9 window containment.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace M8RefinedInputConcrete

open BoundaryLabelCertificateAssembly
open BoundarySpineFiniteCertificate
open CutVertexFinal
open GraphBridge
open Lemma8ExistenceConcrete
open Lemma8NeighborExtractionConcrete
open Lemma10Inequalities
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8MinimalFailureEliminatorInterface
open M8TurnBoundsConcrete
open M8TurnBoundsFromArc
open M8WindowGeometryFromContainment
open MinimalFailureComponentPackage
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NoEarlyTripleObstructionConcrete
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line graph attached to a configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  MinimalFailureComponentPackage.CanonicalGraph C

/-! ## Boundary, Lemma 8, and turn-bound base row -/

/--
Concrete source data that fills the label and turn fields of the
pipeline-facing refined M8 row.

The boundary side is an actual finite `p/q` spine certificate.  Lemma 8 is
supplied in the strengthened missing-existence form, and is routed through the
neighbor-extraction adapter before labels are built.  The turn side is the
boundary-attached nonconcave-arc budget, whose normalized arc data is exposed
below.
-/
structure M8BoundaryLemma8TurnInput {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  positiveCard : 0 < n
  remainingNoCutSlack : RemainingNoCutSlackFact C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C)
  spineCertificate :
    M8FinitePQSpineCertificate arcBoundaryBudget.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureCutVertexFacts C hmin).preconnectedNoCut hmin)

namespace M8BoundaryLemma8TurnInput

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Cut-vertex facts assembled from the concrete positive-cardinality and
remaining no-cut-slack inputs. -/
def cutVertex
    (B : M8BoundaryLemma8TurnInput C hmin) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard := B.positiveCard
  remainingSlack := B.remainingNoCutSlack

/-- The planar-boundary package attached to the selected nonconcave-arc
budget. -/
def planarBoundary
    (B : M8BoundaryLemma8TurnInput C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  B.arcBoundaryBudget.planarBoundary

/-- Boundary spine produced by the finite `p/q` certificate. -/
def spine
    (B : M8BoundaryLemma8TurnInput C hmin) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        B.planarBoundary.core B.cutVertex.preconnectedNoCut hmin) :=
  B.spineCertificate.toM8BoundarySpine
    B.cutVertex.preconnectedNoCut hmin

/-- Lemma 8 combinatorics routed through the strengthened neighbor-extraction
adapter. -/
def lemma8
    (B : M8BoundaryLemma8TurnInput C hmin) :
    M8Lemma8Combinatorics B.spine :=
  M8ExtraNeighborData.toLemma8CombinatoricsOfMissingExistenceConditions
    B.lemma8Existence

/-- The finite boundary-label certificate assembled from the finite spine and
the extracted Lemma 8 package. -/
def finiteBoundaryLabelCertificate
    (B : M8BoundaryLemma8TurnInput C hmin) :
    M8FiniteBoundaryLabelCertificate
      B.planarBoundary B.cutVertex.preconnectedNoCut hmin where
  finiteLabels := B.spineCertificate
  lemma8 := B.lemma8

/-- Boundary labels determined by the concrete boundary and Lemma 8 inputs. -/
def boundaryLabels
    (B : M8BoundaryLemma8TurnInput C hmin) :
    M8BoundaryLabelPackage C :=
  B.finiteBoundaryLabelCertificate.toBoundaryLabelPackage

/-- Local labels determined by the concrete boundary and Lemma 8 inputs. -/
def localLabels
    (B : M8BoundaryLemma8TurnInput C hmin) :
    M8LocalLabels C :=
  B.finiteBoundaryLabelCertificate.toM8LocalLabels

/-- Full boundary-to-M8 turn-bound projection bundle. -/
def turnBoundFields
    (B : M8BoundaryLemma8TurnInput C hmin) :
    NonconcaveArcBoundaryBudgetData.BoundaryToM8TurnBoundFields
      B.arcBoundaryBudget :=
  B.arcBoundaryBudget.boundaryToM8TurnBoundFields

/-- The normalized nonconcave-arc turn data produced by the boundary budget. -/
def arc
    (B : M8BoundaryLemma8TurnInput C hmin) :
    NonconcaveArcTurnData :=
  B.turnBoundFields.arcData

/-- The construction-level turn bounds produced by the normalized arc data. -/
def turnBounds
    (B : M8BoundaryLemma8TurnInput C hmin) :
    M8TurnBounds :=
  B.arc.toM8TurnBounds

/-- The same turn bounds as the boundary-attached projection. -/
def boundaryTurnBounds
    (B : M8BoundaryLemma8TurnInput C hmin) :
    M8TurnBounds :=
  B.turnBoundFields.m8TurnBounds

@[simp]
theorem finiteBoundaryLabelCertificate_finiteLabels
    (B : M8BoundaryLemma8TurnInput C hmin) :
    B.finiteBoundaryLabelCertificate.finiteLabels =
      B.spineCertificate :=
  rfl

@[simp]
theorem finiteBoundaryLabelCertificate_lemma8
    (B : M8BoundaryLemma8TurnInput C hmin) :
    B.finiteBoundaryLabelCertificate.lemma8 = B.lemma8 :=
  rfl

@[simp]
theorem localLabels_labels_p
    (B : M8BoundaryLemma8TurnInput C hmin)
    (i : M8BoundaryIndex) :
    B.localLabels.labels.p i = B.spineCertificate.p i :=
  rfl

@[simp]
theorem localLabels_labels_q
    (B : M8BoundaryLemma8TurnInput C hmin)
    (i : M8TriangleIndex) :
    B.localLabels.labels.q i = B.spineCertificate.q i :=
  rfl

@[simp]
theorem localLabels_labels_r
    (B : M8BoundaryLemma8TurnInput C hmin)
    (i : M8ExtraIndex) :
    B.localLabels.labels.r i = B.lemma8.r i :=
  rfl

@[simp]
theorem localLabels_labels_s
    (B : M8BoundaryLemma8TurnInput C hmin)
    (i : M8ExtraIndex) :
    B.localLabels.labels.s i = B.lemma8.s i :=
  rfl

/-- The boundary-derived local labels retain the finite boundary-edge facts. -/
theorem localLabels_boundaryEdge
    (B : M8BoundaryLemma8TurnInput C hmin)
    (i : M8TriangleIndex) :
    B.localLabels.predicates.data.boundaryEdge i :=
  B.spineCertificate.boundaryEdge i

/-- The boundary-derived local labels retain the finite triangle witnesses. -/
theorem localLabels_triangleWitness
    (B : M8BoundaryLemma8TurnInput C hmin)
    (i : M8TriangleIndex) :
    B.localLabels.predicates.data.triangleWitness i :=
  B.spineCertificate.triangleWitness i

/-- The boundary-derived local labels retain the Lemma 8 extra-neighbor
witnesses produced through the neighbor-extraction route. -/
theorem localLabels_extraNeighborWitness
    (B : M8BoundaryLemma8TurnInput C hmin)
    (i : M8ExtraIndex) :
    B.localLabels.predicates.data.extraNeighborWitness i :=
  B.lemma8.extraNeighborWitness_holds i

@[simp]
theorem arc_eq_boundary_projection
    (B : M8BoundaryLemma8TurnInput C hmin) :
    B.arc = B.arcBoundaryBudget.toNonconcaveArcTurnData :=
  rfl

@[simp]
theorem boundaryTurnBounds_eq_boundary_projection
    (B : M8BoundaryLemma8TurnInput C hmin) :
    B.boundaryTurnBounds = B.arcBoundaryBudget.toM8TurnBounds :=
  rfl

@[simp]
theorem turnBounds_eq_boundaryTurnBounds
    (B : M8BoundaryLemma8TurnInput C hmin) :
    B.turnBounds = B.boundaryTurnBounds :=
  rfl

/-- Pointwise nonnegativity of the constructed M8 turn field. -/
theorem turn_nonnegative
    (B : M8BoundaryLemma8TurnInput C hmin) (k : Nat) :
    0 <= B.turnBounds.turn k :=
  B.turnBounds.turn_nonnegative k

/-- Strict total-turn bound for the constructed M8 turn field. -/
theorem total_turn_lt_pi_div_three
    (B : M8BoundaryLemma8TurnInput C hmin) :
    totalTurn B.turnBounds.turn < Real.pi / 3 :=
  B.turnBounds.total_turn_lt_pi_div_three

end M8BoundaryLemma8TurnInput

/-! ## Concrete no-early refined row -/

/--
Refined M8 input row after boundary, Lemma 8, and turn-bound construction.

Compared with `M8PipelineRefinedFactMatrixRow`, this row no longer asks for
`localLabels` or `arc`; they are produced from `base`.  It still accepts the
concrete no-early package and the remaining window-containment package.
-/
structure M8ConcreteNoEarlyRefinedInputRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : M8BoundaryLemma8TurnInput.{u} C hmin
  noEarlyTripleEquality :
    M8ConcreteNoEarlyTripleEquality base.localLabels.predicates.data
  windowContainment :
    M8WindowContainment base.localLabels base.turnBounds

namespace M8ConcreteNoEarlyRefinedInputRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The filled pipeline-facing refined row. -/
def toPipelineRefinedFactMatrixRow
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    M8PipelineRefinedFactMatrixRow C hmin where
  localLabels := R.base.localLabels
  arc := R.base.arc
  noEarlyTripleEquality := R.noEarlyTripleEquality
  windowContainment := R.windowContainment

/-- The exact turn/window/no-early package consumed by the current M8 closure.
-/
def toTurnWindowNoEarlyPackage
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    M8TurnWindowNoEarlyFinal.M8TurnWindowNoEarlyPackage C hmin :=
  R.toPipelineRefinedFactMatrixRow.toTurnWindowNoEarlyPackage

/-- Clean construction-interface data produced by the concrete row. -/
def toM8ConstructionData
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    M8ConstructionData C hmin :=
  R.toPipelineRefinedFactMatrixRow.toM8ConstructionData

/-- A fixed minimal cleared failure equipped with the concrete refined row is
contradictory. -/
theorem contradiction
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    False :=
  R.toPipelineRefinedFactMatrixRow.contradiction

@[simp]
theorem toPipelineRefinedFactMatrixRow_localLabels
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    R.toPipelineRefinedFactMatrixRow.localLabels =
      R.base.localLabels :=
  rfl

@[simp]
theorem toPipelineRefinedFactMatrixRow_arc
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    R.toPipelineRefinedFactMatrixRow.arc = R.base.arc :=
  rfl

@[simp]
theorem toPipelineRefinedFactMatrixRow_noEarlyTripleEquality
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    R.toPipelineRefinedFactMatrixRow.noEarlyTripleEquality =
      R.noEarlyTripleEquality :=
  rfl

@[simp]
theorem toPipelineRefinedFactMatrixRow_windowContainment
    (R : M8ConcreteNoEarlyRefinedInputRow C hmin) :
    R.toPipelineRefinedFactMatrixRow.windowContainment =
      R.windowContainment :=
  rfl

end M8ConcreteNoEarlyRefinedInputRow

/-! ## Lemma 9 no-early specialization -/

/--
Source row where the concrete no-early field is filled from Lemma 9
five-start late facts.  The remaining explicit M8 obligation is window
containment for the labels and turn bounds constructed by `base`.
-/
structure M8Lemma9RefinedInputRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : M8BoundaryLemma8TurnInput.{u} C hmin
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts base.localLabels.predicates.data
  windowContainment :
    M8WindowContainment base.localLabels base.turnBounds

namespace M8Lemma9RefinedInputRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Concrete no-early package obtained from Lemma 9 five-start late facts. -/
def noEarlyTripleEquality
    (R : M8Lemma9RefinedInputRow C hmin) :
    M8ConcreteNoEarlyTripleEquality R.base.localLabels.predicates.data :=
  R.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality

/-- Forget the Lemma 9 source row to the concrete no-early refined row. -/
def toConcreteNoEarlyRefinedInputRow
    (R : M8Lemma9RefinedInputRow C hmin) :
    M8ConcreteNoEarlyRefinedInputRow C hmin where
  base := R.base
  noEarlyTripleEquality := R.noEarlyTripleEquality
  windowContainment := R.windowContainment

/-- The filled pipeline-facing refined row. -/
def toPipelineRefinedFactMatrixRow
    (R : M8Lemma9RefinedInputRow C hmin) :
    M8PipelineRefinedFactMatrixRow C hmin :=
  R.toConcreteNoEarlyRefinedInputRow.toPipelineRefinedFactMatrixRow

/-- A fixed minimal cleared failure equipped with this Lemma 9 source row is
contradictory. -/
theorem contradiction
    (R : M8Lemma9RefinedInputRow C hmin) :
    False :=
  R.toConcreteNoEarlyRefinedInputRow.contradiction

@[simp]
theorem toConcreteNoEarlyRefinedInputRow_noEarlyTripleEquality
    (R : M8Lemma9RefinedInputRow C hmin) :
    R.toConcreteNoEarlyRefinedInputRow.noEarlyTripleEquality =
      R.noEarlyTripleEquality :=
  rfl

end M8Lemma9RefinedInputRow

/-! ## K23 no-early specialization -/

/--
Source row where the concrete no-early field is filled from a K23 obstruction.

The finite local-exclusion input is not a field here: the existing
unit-distance finite local-exclusion package supplies it for `UDConfig`s.
-/
structure M8K23RefinedInputRow {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  base : M8BoundaryLemma8TurnInput.{u} C hmin
  k23Obstruction :
    M8ConcreteK23ObstructionInputs base.localLabels.predicates.data
  windowContainment :
    M8WindowContainment base.localLabels base.turnBounds

namespace M8K23RefinedInputRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Concrete no-early package obtained from the K23 obstruction and
unit-distance finite local exclusions. -/
def noEarlyTripleEquality
    (R : M8K23RefinedInputRow C hmin) :
    M8ConcreteNoEarlyTripleEquality R.base.localLabels.predicates.data :=
  concreteNoEarlyTripleEquality_of_K23Obstruction_and_unitDistanceConfig
    (C := C) (P := R.base.localLabels.predicates.data)
    R.k23Obstruction

/-- Forget the K23 source row to the concrete no-early refined row. -/
def toConcreteNoEarlyRefinedInputRow
    (R : M8K23RefinedInputRow C hmin) :
    M8ConcreteNoEarlyRefinedInputRow C hmin where
  base := R.base
  noEarlyTripleEquality := R.noEarlyTripleEquality
  windowContainment := R.windowContainment

/-- The filled pipeline-facing refined row. -/
def toPipelineRefinedFactMatrixRow
    (R : M8K23RefinedInputRow C hmin) :
    M8PipelineRefinedFactMatrixRow C hmin :=
  R.toConcreteNoEarlyRefinedInputRow.toPipelineRefinedFactMatrixRow

/-- A fixed minimal cleared failure equipped with this K23 source row is
contradictory. -/
theorem contradiction
    (R : M8K23RefinedInputRow C hmin) :
    False :=
  R.toConcreteNoEarlyRefinedInputRow.contradiction

@[simp]
theorem toConcreteNoEarlyRefinedInputRow_noEarlyTripleEquality
    (R : M8K23RefinedInputRow C hmin) :
    R.toConcreteNoEarlyRefinedInputRow.noEarlyTripleEquality =
      R.noEarlyTripleEquality :=
  rfl

end M8K23RefinedInputRow

/-! ## Uniform families -/

/-- Uniform concrete no-early refined rows for every minimal cleared failure.
-/
structure M8ConcreteNoEarlyRefinedInputRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8ConcreteNoEarlyRefinedInputRow.{u} C hmin

namespace M8ConcreteNoEarlyRefinedInputRowFamily

/-- Assemble the concrete refined row family into the pipeline-facing row
family. -/
def toPipelineRefinedFactMatrixRowFamily
    (H : M8ConcreteNoEarlyRefinedInputRowFamily.{u}) :
    M8PipelineRefinedFactMatrixRowFamily where
  row := fun C hmin =>
    (H.row C hmin).toPipelineRefinedFactMatrixRow

/-- The concrete refined row family supplies the turn/window/no-early
eliminator. -/
theorem toTurnWindowNoEarlyEliminator
    (H : M8ConcreteNoEarlyRefinedInputRowFamily.{u}) :
    MinimalFailureM8TurnWindowNoEarlyEliminator :=
  H.toPipelineRefinedFactMatrixRowFamily.toTurnWindowNoEarlyEliminator

/-- The concrete refined row family rules out every minimal cleared failure.
-/
theorem no_minimalClearedFailure
    (H : M8ConcreteNoEarlyRefinedInputRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toPipelineRefinedFactMatrixRowFamily.no_minimalClearedFailure

/-- Target wrapper from the concrete refined row family. -/
theorem targetLowerBoundEightThirtyOne
    (H : M8ConcreteNoEarlyRefinedInputRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toPipelineRefinedFactMatrixRowFamily.targetLowerBoundEightThirtyOne

end M8ConcreteNoEarlyRefinedInputRowFamily

/-- Uniform Lemma 9 source rows for every minimal cleared failure. -/
structure M8Lemma9RefinedInputRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8Lemma9RefinedInputRow.{u} C hmin

namespace M8Lemma9RefinedInputRowFamily

/-- Forget the Lemma 9 source family to concrete no-early refined rows. -/
def toConcreteNoEarlyRefinedInputRowFamily
    (H : M8Lemma9RefinedInputRowFamily.{u}) :
    M8ConcreteNoEarlyRefinedInputRowFamily.{u} where
  row := fun C hmin =>
    (H.row C hmin).toConcreteNoEarlyRefinedInputRow

/-- The Lemma 9 source family rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : M8Lemma9RefinedInputRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toConcreteNoEarlyRefinedInputRowFamily.no_minimalClearedFailure

/-- Target wrapper from the Lemma 9 source family. -/
theorem targetLowerBoundEightThirtyOne
    (H : M8Lemma9RefinedInputRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toConcreteNoEarlyRefinedInputRowFamily.targetLowerBoundEightThirtyOne

end M8Lemma9RefinedInputRowFamily

/-- Uniform K23 source rows for every minimal cleared failure. -/
structure M8K23RefinedInputRowFamily where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        M8K23RefinedInputRow.{u} C hmin

namespace M8K23RefinedInputRowFamily

/-- Forget the K23 source family to concrete no-early refined rows. -/
def toConcreteNoEarlyRefinedInputRowFamily
    (H : M8K23RefinedInputRowFamily.{u}) :
    M8ConcreteNoEarlyRefinedInputRowFamily.{u} where
  row := fun C hmin =>
    (H.row C hmin).toConcreteNoEarlyRefinedInputRow

/-- The K23 source family rules out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (H : M8K23RefinedInputRowFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toConcreteNoEarlyRefinedInputRowFamily.no_minimalClearedFailure

/-- Target wrapper from the K23 source family. -/
theorem targetLowerBoundEightThirtyOne
    (H : M8K23RefinedInputRowFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toConcreteNoEarlyRefinedInputRowFamily.targetLowerBoundEightThirtyOne

end M8K23RefinedInputRowFamily

end

end M8RefinedInputConcrete
end Swanepoel
end ErdosProblems1066
