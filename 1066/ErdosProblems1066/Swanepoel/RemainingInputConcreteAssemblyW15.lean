import ErdosProblems1066.Swanepoel.BoundaryAnglesToBudgetW14
import ErdosProblems1066.Swanepoel.BoundaryArcToRemainingInputsW14
import ErdosProblems1066.Swanepoel.Lemma89ToRemainingInputsW14
import ErdosProblems1066.Swanepoel.RemainingInputFamilyBuilderW14

set_option autoImplicit false

/-!
# W15 concrete remaining-input assembly

This file keeps the W15 remaining-input builder close to the checked W14
sources.  The boundary arc and angle-budget data are assembled concretely;
the residual no-cut, Lemma 8, Lemma 9, and local window-containment fields stay
explicit at the point where they are still genuine inputs.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace RemainingInputConcreteAssemblyW15

open BoundaryAnglesToBudgetW14
open BoundaryArcInstantiationW13
open BoundaryArcW12
open BoundaryFaceCountingToM8
open CutVertexInterface
open Lemma8ExistenceConcrete
open Lemma10Inequalities
open M8ConstructionInterface
open M8WindowContainmentConcrete
open M8WindowGeometryFromContainment
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary
open OuterBoundaryInstantiationW13

universe u

noncomputable section

variable {n : Nat}

abbrev PointwiseRemainingInputs {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) :=
  MinimalFailureClosureW13.PointwiseRemainingInputs C hmin

abbrev RemainingInputFamily :=
  MinimalFailureClosureW13.RemainingInputFamily

/--
Concrete pointwise row built from a boundary-arc instantiation and the W14
local-window containment fields.

The fields that W14 does not yet derive uniformly remain visible here:
`noCutVertex`, `lemma8Existence`, `lemma9FiveStartLateFacts`, and
`localWindowContainment`.
-/
structure BoundaryArcLocalWindowInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  planarBoundary :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalUDGraph C)
  boundaryArcInstantiation :
    BoundaryArcInstantiation planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (localLabelsOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc lemma8Existence).predicates.data
  localWindowContainment :
    M8LocalWindowContainmentFields
      (localLabelsOfBoundaryArc hmin noCutVertex
        boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        boundaryArcInstantiation.boundaryArc lemma8Existence)
      (boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData
        |>.toNonconcaveArcTurnData
        |>.toM8TurnBounds)

namespace BoundaryArcLocalWindowInputs

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def arcBoundaryBudget
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalUDGraph C) :=
  P.boundaryArcInstantiation.toNonconcaveArcBoundaryBudgetData

def boundaryArc
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    M8BoundaryArcCertificate P.arcBoundaryBudget.planarBoundary :=
  P.boundaryArcInstantiation.boundaryArc

def localLabels
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    M8LocalLabels C :=
  localLabelsOfBoundaryArc hmin P.noCutVertex P.arcBoundaryBudget
    P.boundaryArc P.lemma8Existence

def turnBounds
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    M8TurnBounds :=
  P.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

def toLemma89LocalWindowInputs
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    Lemma89ToRemainingInputsW14.PointwiseLemma89LocalWindowInputs.{u}
      C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

def toPointwiseRemainingInputs
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    PointwiseRemainingInputs.{u} C hmin :=
  P.toLemma89LocalWindowInputs.toPointwiseRemainingInputs

@[simp]
theorem toPointwiseRemainingInputs_arcBoundaryBudget
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    P.toPointwiseRemainingInputs.arcBoundaryBudget = P.arcBoundaryBudget :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_boundaryArc
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    P.toPointwiseRemainingInputs.boundaryArc = P.boundaryArc :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_localLabels
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    P.toPointwiseRemainingInputs.localLabels = P.localLabels :=
  rfl

@[simp]
theorem toLemma89LocalWindowInputs_localWindowContainment
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    P.toLemma89LocalWindowInputs.localWindowContainment =
      P.localWindowContainment :=
  rfl

theorem contradiction
    (P : BoundaryArcLocalWindowInputs.{u} C hmin) :
    False :=
  P.toPointwiseRemainingInputs.contradiction

end BoundaryArcLocalWindowInputs

/-- Uniform concrete W15 pointwise rows for every minimal cleared failure. -/
structure BoundaryArcLocalWindowInputFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        BoundaryArcLocalWindowInputs.{u} C hmin

namespace BoundaryArcLocalWindowInputFamily

def toRemainingInputFamily
    (H : BoundaryArcLocalWindowInputFamily.{u}) :
    RemainingInputFamily.{u} where
  inputs := fun C hmin =>
    (H.inputs C hmin).toPointwiseRemainingInputs

theorem no_minimalClearedFailure
    (H : BoundaryArcLocalWindowInputFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toRemainingInputFamily.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (H : BoundaryArcLocalWindowInputFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toRemainingInputFamily.targetLowerBoundEightThirtyOne

end BoundaryArcLocalWindowInputFamily

/-! ## Angle-budget concrete variants -/

/--
Pointwise concrete row where the boundary-arc instantiation is built from
explicit outer-boundary angle data and an explicit raw-turn budget.
-/
structure ExplicitAngleBoundaryArcLocalWindowInputs
    {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    {E : ExplicitOuterBoundaryAngleFields.{u} (CanonicalUDGraph C)}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalUDGraph C)}
    {rawTurn : Nat -> Real} where
  noCutVertex : NoCutVertex C
  angleBudgetFields :
    ExplicitOuterBoundaryAngleBudgetFields
      E Subpolygon subpolygonData rawTurn
  boundaryArc :
    M8BoundaryArcCertificate angleBudgetFields.planarBoundary
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin noCutVertex
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc
          |>.toNonconcaveArcBoundaryBudgetData)
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc).boundaryArc)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (localLabelsOfBoundaryArc hmin noCutVertex
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc
          |>.toNonconcaveArcBoundaryBudgetData)
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc).boundaryArc
        lemma8Existence).predicates.data
  localWindowContainment :
    M8LocalWindowContainmentFields
      (localLabelsOfBoundaryArc hmin noCutVertex
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc
          |>.toNonconcaveArcBoundaryBudgetData)
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc).boundaryArc
        lemma8Existence)
      (angleBudgetFields.toBoundaryArcInstantiation
        boundaryArc rawTurn_nonnegative_on_arc
        |>.toNonconcaveArcBoundaryBudgetData
        |>.toNonconcaveArcTurnData
        |>.toM8TurnBounds)

namespace ExplicitAngleBoundaryArcLocalWindowInputs

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {E : ExplicitOuterBoundaryAngleFields.{u} (CanonicalUDGraph C)}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon ->
    SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalUDGraph C)}
variable {rawTurn : Nat -> Real}

def boundaryArcInstantiation
    (P :
      ExplicitAngleBoundaryArcLocalWindowInputs
        hmin (E := E) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    BoundaryArcInstantiation P.angleBudgetFields.planarBoundary :=
  P.angleBudgetFields.toBoundaryArcInstantiation
    P.boundaryArc P.rawTurn_nonnegative_on_arc

def toBoundaryArcLocalWindowInputs
    (P :
      ExplicitAngleBoundaryArcLocalWindowInputs
        hmin (E := E) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    BoundaryArcLocalWindowInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  planarBoundary := P.angleBudgetFields.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

def toPointwiseRemainingInputs
    (P :
      ExplicitAngleBoundaryArcLocalWindowInputs
        hmin (E := E) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    PointwiseRemainingInputs.{u} C hmin :=
  P.toBoundaryArcLocalWindowInputs.toPointwiseRemainingInputs

theorem contradiction
    (P :
      ExplicitAngleBoundaryArcLocalWindowInputs
        hmin (E := E) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    False :=
  P.toPointwiseRemainingInputs.contradiction

end ExplicitAngleBoundaryArcLocalWindowInputs

/--
Pointwise concrete row where the boundary-arc instantiation is built from
actual outer-boundary angle data and an explicit raw-turn budget.
-/
structure ActualAngleBoundaryArcLocalWindowInputs
    {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C)
    {A : ActualOuterBoundaryAngleData (CanonicalUDGraph C)}
    {Subpolygon : Type u}
    {subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData
          (CanonicalUDGraph C)}
    {rawTurn : Nat -> Real} where
  noCutVertex : NoCutVertex C
  angleBudgetFields :
    ActualOuterBoundaryAngleBudgetFields
      A Subpolygon subpolygonData rawTurn
  boundaryArc :
    M8BoundaryArcCertificate angleBudgetFields.planarBoundary
  rawTurn_nonnegative_on_arc :
    forall k : Nat, Membership.mem turnIndexSet k -> 0 <= rawTurn k
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin noCutVertex
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc
          |>.toNonconcaveArcBoundaryBudgetData)
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc).boundaryArc)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (localLabelsOfBoundaryArc hmin noCutVertex
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc
          |>.toNonconcaveArcBoundaryBudgetData)
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc).boundaryArc
        lemma8Existence).predicates.data
  localWindowContainment :
    M8LocalWindowContainmentFields
      (localLabelsOfBoundaryArc hmin noCutVertex
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc
          |>.toNonconcaveArcBoundaryBudgetData)
        (angleBudgetFields.toBoundaryArcInstantiation
          boundaryArc rawTurn_nonnegative_on_arc).boundaryArc
        lemma8Existence)
      (angleBudgetFields.toBoundaryArcInstantiation
        boundaryArc rawTurn_nonnegative_on_arc
        |>.toNonconcaveArcBoundaryBudgetData
        |>.toNonconcaveArcTurnData
        |>.toM8TurnBounds)

namespace ActualAngleBoundaryArcLocalWindowInputs

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
variable {A : ActualOuterBoundaryAngleData (CanonicalUDGraph C)}
variable {Subpolygon : Type u}
variable {subpolygonData :
  Subpolygon ->
    SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalUDGraph C)}
variable {rawTurn : Nat -> Real}

def boundaryArcInstantiation
    (P :
      ActualAngleBoundaryArcLocalWindowInputs
        hmin (A := A) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    BoundaryArcInstantiation P.angleBudgetFields.planarBoundary :=
  P.angleBudgetFields.toBoundaryArcInstantiation
    P.boundaryArc P.rawTurn_nonnegative_on_arc

def toBoundaryArcLocalWindowInputs
    (P :
      ActualAngleBoundaryArcLocalWindowInputs
        hmin (A := A) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    BoundaryArcLocalWindowInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  planarBoundary := P.angleBudgetFields.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  localWindowContainment := P.localWindowContainment

def toPointwiseRemainingInputs
    (P :
      ActualAngleBoundaryArcLocalWindowInputs
        hmin (A := A) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    PointwiseRemainingInputs.{u} C hmin :=
  P.toBoundaryArcLocalWindowInputs.toPointwiseRemainingInputs

theorem contradiction
    (P :
      ActualAngleBoundaryArcLocalWindowInputs
        hmin (A := A) (Subpolygon := Subpolygon)
        (subpolygonData := subpolygonData) (rawTurn := rawTurn)) :
    False :=
  P.toPointwiseRemainingInputs.contradiction

end ActualAngleBoundaryArcLocalWindowInputs

end

end RemainingInputConcreteAssemblyW15
end Swanepoel
end ErdosProblems1066
