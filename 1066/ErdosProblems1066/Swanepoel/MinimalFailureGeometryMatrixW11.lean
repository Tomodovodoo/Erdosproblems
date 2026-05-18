import ErdosProblems1066.Swanepoel.MinimalFailureDirectMatrixW10
import ErdosProblems1066.Swanepoel.GeometryRemainingFieldsW10
import ErdosProblems1066.Swanepoel.SwanepoelW10ClosureMatrix
import ErdosProblems1066.Swanepoel.MinimalFailureConcreteDataMatrix
import ErdosProblems1066.Swanepoel.MinimalFailurePaperFactMatrix

set_option autoImplicit false
set_option linter.unusedDecidableInType false

/-!
# Minimal-failure geometry matrix, W11

This file is a narrow closure facade over the W10 Swanepoel geometry rows.
It keeps the source geometry split into topology, angle, boundary labels,
window containment, and one of the available no-early routes:

* direct five-start no-early fields;
* K23 obstruction fields;
* common-neighbor obstruction fields.

Each row is lowered through the checked W10 direct-component adapter and then
to the concrete obligation family.  That family is the smallest source-facing
input in this layer; it is also converted to the refined target input recorded
by the paper-fact matrix.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureGeometryMatrixW11

open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open GeometryRemainingFieldsW10
open LateTriplesInterface
open Lemma10Bridge
open LocalConfigurations
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9

universe u v

noncomputable section

variable {n : Nat}

/-- The smallest W11 source-facing closure input: concrete obligations with
positive cardinality derived from minimality. -/
abbrev NarrowClosureInputFamily :=
  MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligationFamily.{u}

/-- The refined target-input family named by the paper-fact matrix. -/
abbrev CheckedClosureInputFamily :=
  MinimalFailurePaperFactMatrix.TargetLowerBoundEightThirtyOneInputs.{u}

/-- Concrete no-early exclusions imply the restricted Lemma 9 late-start row
needed by the refined closure input. -/
def lemma9FiveStartLateFactsOfConcreteNoEarly
    {V : Type u} {G : LocalGraph V}
    {P : BrokenLatticePredicates G 8}
    (N : M8ConcreteNoEarlyTripleEquality P) :
    M8Lemma9FiveStartLateFacts P where
  late_start1 := fun h => False.elim (N.no_start1 h)
  late_start2 := fun h => False.elim (N.no_start2 h)
  late_start3 := fun h => False.elim (N.no_start3 h)
  late_start4 := fun h => False.elim (N.no_start4 h)
  late_start5 := fun h => False.elim (N.no_start5 h)

/-! ## No-early routes -/

/-- The three checked ways W10 geometry can supply no-early data for the same
source labels. -/
inductive NoEarlyRoute
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (source : GeometrySourceFields.{u} C hmin) : Type u where
  | direct (fields : NoStartNoEarlyFields source)
  | k23 (fields : K23NoEarlyFields source)
  | commonNeighbor (fields : CommonNeighborNoEarlyFields source)

namespace NoEarlyRoute

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {source : GeometrySourceFields.{u} C hmin}

/-- The concrete no-early row selected by a direct, K23, or common-neighbor
route. -/
def concreteNoEarly
    (R : NoEarlyRoute.{u} source) :
    M8ConcreteNoEarlyTripleEquality
      source.localLabels.predicates.data :=
  match R with
  | direct fields => fields.noEarly
  | k23 fields => fields.noEarly
  | commonNeighbor fields => fields.noEarly

/-- View the selected no-early route as explicit five-start no-start fields. -/
def toNoStartNoEarlyFields
    (R : NoEarlyRoute.{u} source) :
    NoStartNoEarlyFields source where
  noStart :=
    NoStartInstantiation.constructionExplicitNoStartFields_of_concreteNoEarly
      (localLabels := source.localLabels) R.concreteNoEarly

/-- The Lemma 9-shaped late-start row induced by the selected no-early route.
-/
def toLemma9FiveStartLateFacts
    (R : NoEarlyRoute.{u} source) :
    M8Lemma9FiveStartLateFacts
      source.localLabels.predicates.data :=
  lemma9FiveStartLateFactsOfConcreteNoEarly R.concreteNoEarly

end NoEarlyRoute

/-! ## W11 geometry rows -/

/-- A W11 row: source geometry, window containment, and one selected no-early
route over the same local labels. -/
structure GeometryClosureRow
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  source : GeometrySourceFields.{u} C hmin
  window : ContainmentFields source
  noEarly : NoEarlyRoute source

namespace GeometryClosureRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Package a W10 direct geometry row as a W11 row. -/
def ofDirectGeometryPackage
    (R : DirectGeometryPackage.{u} C hmin) :
    GeometryClosureRow.{u} C hmin where
  source := R.source
  window := R.containment
  noEarly := NoEarlyRoute.direct R.noStartNoEarly

/-- Package a W10 K23 geometry row as a W11 row. -/
def ofK23GeometryPackage
    (R : K23GeometryPackage.{u} C hmin) :
    GeometryClosureRow.{u} C hmin where
  source := R.source
  window := R.containment
  noEarly := NoEarlyRoute.k23 R.k23NoEarly

/-- Package a W10 common-neighbor geometry row as a W11 row. -/
def ofCommonNeighborGeometryPackage
    (R : CommonNeighborGeometryPackage.{u} C hmin) :
    GeometryClosureRow.{u} C hmin where
  source := R.source
  window := R.containment
  noEarly := NoEarlyRoute.commonNeighbor R.commonNeighborNoEarly

/-- Forget the W11 row to the W10 direct geometry package. -/
def toDirectGeometryPackage
    (R : GeometryClosureRow.{u} C hmin) :
    DirectGeometryPackage.{u} C hmin where
  source := R.source
  containment := R.window
  noStartNoEarly := R.noEarly.toNoStartNoEarlyFields

end GeometryClosureRow

/-- Convert a W10 direct geometry package to the component row used by
`MinimalFailureDirectMatrixW10`. -/
def directGeometryPackageToDirectComponentRow
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : DirectGeometryPackage.{u} C hmin) :
    MinimalFailureDirectMatrixW10.DirectComponentRow.{u} C hmin where
  topology := {
    topology := R.source.geometry.topologyFacts
  }
  partitionAngle := {
    outerAngleBounds := R.source.geometry.outerAngleBounds
    Subpolygon := R.source.geometry.Subpolygon
    subpolygonData := R.source.geometry.subpolygonData
    longArc := R.source.geometry.longArc
  }
  labels := {
    remainingNoCutSlack :=
      R.source.boundaryLabels.remainingNoCutSlack
    spineCertificate := R.source.boundaryLabels.spineCertificate
    lemma8Existence := R.source.boundaryLabels.lemma8Existence
  }
  containment := {
    containment := R.containment.windowContainment
  }
  noEarly := {
    noEarly := R.noStartNoEarly.noEarly
  }

namespace GeometryClosureRow

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- Lower the W11 row to the W10 direct component row. -/
def toDirectComponentRow
    (R : GeometryClosureRow.{u} C hmin) :
    MinimalFailureDirectMatrixW10.DirectComponentRow.{u} C hmin :=
  directGeometryPackageToDirectComponentRow R.toDirectGeometryPackage

/-- The narrow concrete closure input selected by this W11 geometry row. -/
def toConcreteObligations
    (R : GeometryClosureRow.{u} C hmin) :
    MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligations.{u}
      C hmin :=
  R.toDirectComponentRow.toConcreteDataObligations

/-- The refined paper-fact target input induced by this W11 geometry row. -/
def toCheckedClosureInput
    (R : GeometryClosureRow.{u} C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.{u}
      C hmin :=
  R.toConcreteObligations.toRefinedPaperFacts

/-- A fixed W11 geometry row closes the corresponding minimal failure. -/
theorem contradiction
    (R : GeometryClosureRow.{u} C hmin) :
    False :=
  R.toConcreteObligations.contradiction

end GeometryClosureRow

/-! ## Uniform matrices -/

/-- Uniform W11 geometry rows for every minimal cleared failure. -/
structure GeometryClosureMatrix where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        GeometryClosureRow.{u} C hmin

namespace GeometryClosureMatrix

/-- Convert W11 geometry rows to the narrow concrete closure-input family. -/
def toNarrowClosureInputFamily
    (M : GeometryClosureMatrix.{u}) :
    NarrowClosureInputFamily.{u} where
  obligations := fun C hmin => (M.row C hmin).toConcreteObligations

/-- Convert W11 geometry rows to the checked refined target-input family. -/
def toCheckedClosureInputFamily
    (M : GeometryClosureMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  M.toNarrowClosureInputFamily.toRefinedPaperFactsFamily

/-- W11 geometry rows rule out every minimal cleared failure. -/
theorem no_minimalClearedFailure
    (M : GeometryClosureMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalFailurePaperFactMatrix.refined_family_noMinimalClearedFailure_consumes_eliminator
    M.toCheckedClosureInputFamily

/-- Conditional target projection from W11 geometry rows. -/
theorem targetLowerBoundEightThirtyOne
    (M : GeometryClosureMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalFailurePaperFactMatrix.targetLowerBoundEightThirtyOne_consumes_exact_inputs
    M.toCheckedClosureInputFamily

end GeometryClosureMatrix

/-! ## Adapters from W10 matrices -/

/-- Existing W10 direct component rows already produce the narrow closure
input. -/
def directComponentMatrixToNarrowClosureInputFamily
    (M : MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u}) :
    NarrowClosureInputFamily.{u} where
  obligations := fun C hmin => (M.row C hmin).toConcreteDataObligations

/-- Existing W10 direct component rows as checked refined target inputs. -/
def directComponentMatrixToCheckedClosureInputFamily
    (M : MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u}) :
    CheckedClosureInputFamily.{u} :=
  (directComponentMatrixToNarrowClosureInputFamily M).toRefinedPaperFactsFamily

/-- W10 direct geometry matrices as W11 geometry matrices. -/
def directGeometryMatrixToGeometryClosureMatrix
    (M : SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin =>
    GeometryClosureRow.ofDirectGeometryPackage (M.row C hmin)

/-- W10 K23 geometry matrices as W11 geometry matrices. -/
def k23GeometryMatrixToGeometryClosureMatrix
    (M : SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin =>
    GeometryClosureRow.ofK23GeometryPackage (M.row C hmin)

/-- W10 common-neighbor geometry matrices as W11 geometry matrices. -/
def commonNeighborGeometryMatrixToGeometryClosureMatrix
    (M : SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) :
    GeometryClosureMatrix.{u} where
  row := fun C hmin =>
    GeometryClosureRow.ofCommonNeighborGeometryPackage (M.row C hmin)

/-! ## Projection rows -/

/-- Projection row spelling reused from the W10 closure matrix. -/
abbrev ProjectionRow (alpha : Type v) : Type v :=
  SwanepoelW10ClosureMatrix.ProjectionRow alpha

/-- The refined target-input projection row from the paper-fact matrix. -/
def checkedClosureInputFamilyRow :
    ProjectionRow (CheckedClosureInputFamily.{u}) where
  noMinimal :=
    MinimalFailurePaperFactMatrix.refined_family_noMinimalClearedFailure_consumes_eliminator
  target :=
    MinimalFailurePaperFactMatrix.targetLowerBoundEightThirtyOne_consumes_exact_inputs

/-- Projection row for the narrow concrete closure-input family. -/
def narrowClosureInputFamilyRow :
    ProjectionRow (NarrowClosureInputFamily.{u}) where
  noMinimal := fun H =>
    MinimalFailurePaperFactMatrix.refined_family_noMinimalClearedFailure_consumes_eliminator
      H.toRefinedPaperFactsFamily
  target := fun H =>
    MinimalFailurePaperFactMatrix.targetLowerBoundEightThirtyOne_consumes_exact_inputs
      H.toRefinedPaperFactsFamily

/-- Projection row for W11 geometry matrices. -/
def geometryClosureMatrixRow :
    ProjectionRow (GeometryClosureMatrix.{u}) where
  noMinimal := GeometryClosureMatrix.no_minimalClearedFailure
  target := GeometryClosureMatrix.targetLowerBoundEightThirtyOne

/-- Projection row for the existing W10 direct component matrix, routed
through the narrow W11 closure input. -/
def directComponentMatrixRow :
    ProjectionRow
      (MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u}) where
  noMinimal := fun M =>
    MinimalFailurePaperFactMatrix.refined_family_noMinimalClearedFailure_consumes_eliminator
      (directComponentMatrixToCheckedClosureInputFamily M)
  target := fun M =>
    MinimalFailurePaperFactMatrix.targetLowerBoundEightThirtyOne_consumes_exact_inputs
      (directComponentMatrixToCheckedClosureInputFamily M)

/-- Projection row for W10 direct geometry matrices, routed through W11. -/
def directGeometryMatrixRow :
    ProjectionRow (SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u}) where
  noMinimal := fun M =>
    (directGeometryMatrixToGeometryClosureMatrix M).no_minimalClearedFailure
  target := fun M =>
    (directGeometryMatrixToGeometryClosureMatrix M).targetLowerBoundEightThirtyOne

/-- Projection row for W10 K23 geometry matrices, routed through W11. -/
def k23GeometryMatrixRow :
    ProjectionRow (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}) where
  noMinimal := fun M =>
    (k23GeometryMatrixToGeometryClosureMatrix M).no_minimalClearedFailure
  target := fun M =>
    (k23GeometryMatrixToGeometryClosureMatrix M).targetLowerBoundEightThirtyOne

/-- Projection row for W10 common-neighbor geometry matrices, routed through
W11. -/
def commonNeighborGeometryMatrixRow :
    ProjectionRow
      (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) where
  noMinimal := fun M =>
    (commonNeighborGeometryMatrixToGeometryClosureMatrix M).no_minimalClearedFailure
  target := fun M =>
    (commonNeighborGeometryMatrixToGeometryClosureMatrix M).targetLowerBoundEightThirtyOne

/-- Consolidated W11 matrix of checked routes into the narrow closure input. -/
structure Matrix where
  checkedInputs : ProjectionRow (CheckedClosureInputFamily.{u})
  narrowInputs : ProjectionRow (NarrowClosureInputFamily.{u})
  geometryClosure : ProjectionRow (GeometryClosureMatrix.{u})
  directComponents :
    ProjectionRow
      (MinimalFailureDirectMatrixW10.DirectComponentMatrix.{u})
  directGeometry :
    ProjectionRow (SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u})
  k23Geometry :
    ProjectionRow (SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u})
  commonNeighborGeometry :
    ProjectionRow
      (SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u})

/-- The checked W11 geometry matrix. -/
def matrix : Matrix.{u} where
  checkedInputs := checkedClosureInputFamilyRow
  narrowInputs := narrowClosureInputFamilyRow
  geometryClosure := geometryClosureMatrixRow
  directComponents := directComponentMatrixRow
  directGeometry := directGeometryMatrixRow
  k23Geometry := k23GeometryMatrixRow
  commonNeighborGeometry := commonNeighborGeometryMatrixRow

/-! ## Public projections -/

/-- Public target projection from the narrow closure input family. -/
theorem targetLowerBoundEightThirtyOne_of_narrowClosureInputFamily
    (H : NarrowClosureInputFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  narrowClosureInputFamilyRow.target H

/-- Public target projection from W11 geometry rows. -/
theorem targetLowerBoundEightThirtyOne_of_geometryClosureMatrix
    (M : GeometryClosureMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  M.targetLowerBoundEightThirtyOne

/-- Public target projection from W10 direct geometry rows via W11. -/
theorem targetLowerBoundEightThirtyOne_of_directGeometryMatrix
    (M : SwanepoelW10ClosureMatrix.DirectGeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  directGeometryMatrixRow.target M

/-- Public target projection from W10 K23 geometry rows via W11. -/
theorem targetLowerBoundEightThirtyOne_of_k23GeometryMatrix
    (M : SwanepoelW10ClosureMatrix.K23GeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  k23GeometryMatrixRow.target M

/-- Public target projection from W10 common-neighbor geometry rows via W11.
-/
theorem targetLowerBoundEightThirtyOne_of_commonNeighborGeometryMatrix
    (M : SwanepoelW10ClosureMatrix.CommonNeighborGeometryMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  commonNeighborGeometryMatrixRow.target M

end

end MinimalFailureGeometryMatrixW11
end Swanepoel
end ErdosProblems1066
