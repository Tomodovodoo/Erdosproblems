import ErdosProblems1066.Swanepoel.NoCutMinimalityProofW15
import ErdosProblems1066.Swanepoel.FinalSwanepoelGateW15

set_option autoImplicit false

/-!
# W16 no-cut-from-minimality assembly

This file packages the W15 no-cut localization into the endpoint-facing
minimal-failure-exclusion shape.  Connectedness and the no-cut conclusion are
proved from the W15 minimality-selected pay-for-cut statement.  The remaining
row structure keeps the other pointwise inputs explicit and derives its
`NoCutVertex` field from W15.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace NoCutFromMinimalityW16

open CutVertexInterface
open BoundaryArcW12
open Lemma8ExistenceConcrete
open M8WindowGeometryFromContainment
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

abbrev Target : Prop :=
  FinalSwanepoelGateW15.Target

abbrev LowerBoundAt (n : Nat) (C : _root_.UDConfig n) : Prop :=
  FinalSwanepoelGateW15.LowerBoundAt n C

abbrev MinimalFailureExclusion : Prop :=
  FinalSwanepoelGateW15.MinimalFailureExclusion

abbrev RemainingInputFamily :=
  MinimalFailureClosureW13.RemainingInputFamily

abbrev MinimalitySelectedPayForCut
    {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) : Prop :=
  NoCutMinimalityProofW15.MinimalitySelectedPayForCut hmin

abbrev MinimalitySelectedPayForCutFamily : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : IsMinimalClearedFailure C),
      MinimalitySelectedPayForCut hmin

/-- Minimality-selected pay-for-cut data gives the connected/no-cut package
already checked in W15. -/
structure ConnectedNoCutFromMinimality {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) : Prop where
  minimalitySelectedPayForCut : MinimalitySelectedPayForCut hmin
  connected : (GraphBridge.unitDistanceSimpleGraph C).Connected
  noCutVertex : NoCutVertex C

namespace ConnectedNoCutFromMinimality

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

theorem of_minimalitySelectedPayForCut
    (hpay : MinimalitySelectedPayForCut hmin) :
    ConnectedNoCutFromMinimality C hmin where
  minimalitySelectedPayForCut := hpay
  connected := NoCutMinimalityProofW15.connected_of_minimalFailure hmin
  noCutVertex :=
    NoCutMinimalityProofW15.noCutVertex_of_minimalFailure_minimalitySelectedPayForCut
      hmin hpay

theorem iff_minimalitySelectedPayForCut :
    ConnectedNoCutFromMinimality C hmin <->
      MinimalitySelectedPayForCut hmin := by
  constructor
  case mp =>
    intro H
    exact H.minimalitySelectedPayForCut
  case mpr =>
    exact of_minimalitySelectedPayForCut

end ConnectedNoCutFromMinimality

theorem noCutVertex_of_minimalitySelectedPayForCut
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (hpay : MinimalitySelectedPayForCut hmin) :
    NoCutVertex C :=
  (ConnectedNoCutFromMinimality.of_minimalitySelectedPayForCut
    (C := C) hpay).noCutVertex

theorem connected_of_minimalitySelectedPayForCut
    {n : Nat} {C : _root_.UDConfig n}
    {hmin : IsMinimalClearedFailure C}
    (hpay : MinimalitySelectedPayForCut hmin) :
    (GraphBridge.unitDistanceSimpleGraph C).Connected :=
  (ConnectedNoCutFromMinimality.of_minimalitySelectedPayForCut
    (C := C) hpay).connected

/-- Pointwise remaining-input row whose no-cut proof is supplied by the W15
minimality-selected pay-for-cut theorem. -/
structure PointwiseNoCutMinimalityInputs {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  minimalitySelectedPayForCut : MinimalitySelectedPayForCut hmin
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  boundaryArc :
    M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (MinimalFailureClosureW13.spineOfBoundaryArc hmin
        (noCutVertex_of_minimalitySelectedPayForCut
          minimalitySelectedPayForCut)
        arcBoundaryBudget boundaryArc)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin
        (noCutVertex_of_minimalitySelectedPayForCut
          minimalitySelectedPayForCut)
        arcBoundaryBudget boundaryArc lemma8Existence).predicates.data
  windowContainment :
    M8WindowContainment
      (MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin
        (noCutVertex_of_minimalitySelectedPayForCut
          minimalitySelectedPayForCut)
        arcBoundaryBudget boundaryArc lemma8Existence)
      arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

namespace PointwiseNoCutMinimalityInputs

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

def connectedNoCut
    (P : PointwiseNoCutMinimalityInputs.{u} C hmin) :
    ConnectedNoCutFromMinimality C hmin :=
  ConnectedNoCutFromMinimality.of_minimalitySelectedPayForCut
    P.minimalitySelectedPayForCut

def noCutVertex
    (P : PointwiseNoCutMinimalityInputs.{u} C hmin) :
    NoCutVertex C :=
  noCutVertex_of_minimalitySelectedPayForCut
    P.minimalitySelectedPayForCut

def connected
    (P : PointwiseNoCutMinimalityInputs.{u} C hmin) :
    (GraphBridge.unitDistanceSimpleGraph C).Connected :=
  P.connectedNoCut.connected

def localLabels
    (P : PointwiseNoCutMinimalityInputs.{u} C hmin) :
    M8ConstructionInterface.M8LocalLabels C :=
  MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin
    P.noCutVertex P.arcBoundaryBudget P.boundaryArc P.lemma8Existence

def toPointwiseRemainingInputs
    (P : PointwiseNoCutMinimalityInputs.{u} C hmin) :
    MinimalFailureClosureW13.PointwiseRemainingInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  windowContainment := P.windowContainment

theorem contradiction
    (P : PointwiseNoCutMinimalityInputs.{u} C hmin) :
    False :=
  P.toPointwiseRemainingInputs.contradiction

end PointwiseNoCutMinimalityInputs

/-- Uniform W16 row family.  This is the remaining theorem surface needed to
turn the W15 no-cut localization into the W15 final gate. -/
structure NoCutMinimalityRemainingInputFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseNoCutMinimalityInputs.{u} C hmin

namespace NoCutMinimalityRemainingInputFamily

def minimalitySelectedPayForCutFamily
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    MinimalitySelectedPayForCutFamily :=
  fun C hmin => (H.inputs C hmin).minimalitySelectedPayForCut

def toRemainingInputFamily
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    RemainingInputFamily.{u} where
  inputs := fun C hmin =>
    (H.inputs C hmin).toPointwiseRemainingInputs

theorem minimalFailureExclusion
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    MinimalFailureExclusion :=
  H.toRemainingInputFamily.no_minimalClearedFailure

def finalGate
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    FinalSwanepoelGateW15.FinalGate where
  minimalFailureExclusion := H.minimalFailureExclusion

theorem targetLowerBoundEightThirtyOne
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    Target :=
  H.finalGate.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one
    (H : NoCutMinimalityRemainingInputFamily.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  H.finalGate.lower_bound_eight_thirty_one n C

end NoCutMinimalityRemainingInputFamily

theorem minimalFailureExclusion_of_noCutMinimalityRemainingInputFamily
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    MinimalFailureExclusion :=
  H.minimalFailureExclusion

def finalGate_of_noCutMinimalityRemainingInputFamily
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    FinalSwanepoelGateW15.FinalGate :=
  H.finalGate

theorem targetLowerBoundEightThirtyOne_of_noCutMinimalityRemainingInputFamily
    (H : NoCutMinimalityRemainingInputFamily.{u}) :
    Target :=
  H.targetLowerBoundEightThirtyOne

theorem lower_bound_eight_thirty_one_of_noCutMinimalityRemainingInputFamily
    (H : NoCutMinimalityRemainingInputFamily.{u})
    (n : Nat) (C : _root_.UDConfig n) :
    LowerBoundAt n C :=
  H.lower_bound_eight_thirty_one n C

end

end NoCutFromMinimalityW16
end Swanepoel
end ErdosProblems1066
